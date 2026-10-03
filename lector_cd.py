# -*- coding: utf-8 -*-
"""
Lector de CD para "Mi colección" (Windows 10/11).

Hace de puente entre tu página (BDD.html) y la unidad de CD, física o virtual
(Daemon Tools u otra). Lee la tabla de contenidos (TOC) del disco, calcula su
DiscID de MusicBrainz y busca allí el disco para devolver título, artista,
pistas, sello y código de barras.

- Solo usa la biblioteca estándar de Python (no hay que instalar nada más).
- Solo escucha en 127.0.0.1 (tu propio PC) y solo responde a tu página.
- No modifica ni escribe nada: lee la TOC del disco y, cuando se lo pides desde la página
  ("Ir A Disco"), abre un archivo de imagen de disco (.mdx, .iso…) con el programa que Windows
  tenga asociado (p. ej. Daemon Tools, que lo monta).

Uso: ejecutar iniciar_lector.bat (o "py lector_cd.py") y dejar la ventana abierta.
"""
import base64
import ctypes
import hashlib
import json
import os
import re
import sys
import urllib.error
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

VERSION = "1.1"
PUERTO = 8765
# Páginas autorizadas a hablar con este programa. Si algún día cambias de dirección, añádela aquí.
ORIGENES_PERMITIDOS = {
    "https://isizanper.github.io",
    "http://localhost",
    "http://127.0.0.1",
}
USER_AGENT = "MiColeccionDiscos-LectorCD/%s ( https://github.com/IsiZanPer/mi-coleccion-discos )" % VERSION
MAX_CANDIDATOS = 10
# Solo se permite abrir archivos de imagen de disco (nunca programas, documentos ni scripts).
EXTENSIONES_IMAGEN = {".mdx", ".mds", ".mdf", ".iso", ".isz", ".nrg", ".ccd", ".cue", ".bin", ".img",
                      ".cdi", ".b5t", ".b6t", ".bwt", ".pdi", ".uif"}

# ----------------------------------------------------------------------------------------------
# 1) Lectura de la TOC (Windows)
# ----------------------------------------------------------------------------------------------
IOCTL_CDROM_READ_TOC = 0x00024000
GENERIC_READ = 0x80000000
FILE_SHARE_READ = 0x1
FILE_SHARE_WRITE = 0x2
OPEN_EXISTING = 3
DRIVE_CDROM = 5
INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value
TAM_TOC = 4 + 100 * 8          # estructura CDROM_TOC


def _kernel32():
    k = ctypes.WinDLL("kernel32", use_last_error=True)
    k.CreateFileW.restype = ctypes.c_void_p
    k.CreateFileW.argtypes = [ctypes.c_wchar_p, ctypes.c_uint32, ctypes.c_uint32, ctypes.c_void_p,
                              ctypes.c_uint32, ctypes.c_uint32, ctypes.c_void_p]
    k.DeviceIoControl.restype = ctypes.c_int
    k.DeviceIoControl.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_uint32,
                                  ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint32), ctypes.c_void_p]
    k.CloseHandle.argtypes = [ctypes.c_void_p]
    k.GetLogicalDrives.restype = ctypes.c_uint32
    k.GetDriveTypeW.restype = ctypes.c_uint
    k.GetDriveTypeW.argtypes = [ctypes.c_wchar_p]
    return k


def leer_toc_bruta(letra):
    """Devuelve los 804 bytes de la TOC de la unidad (p. ej. 'E:'), o lanza OSError si no hay disco."""
    k = _kernel32()
    h = k.CreateFileW("\\\\.\\" + letra, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, None, OPEN_EXISTING, 0, None)
    if h is None or h == INVALID_HANDLE_VALUE:
        raise OSError("No se puede abrir la unidad %s." % letra)
    try:
        buf = ctypes.create_string_buffer(TAM_TOC)
        devueltos = ctypes.c_uint32(0)
        ok = k.DeviceIoControl(h, IOCTL_CDROM_READ_TOC, None, 0, buf, TAM_TOC, ctypes.byref(devueltos), None)
        if not ok:
            raise OSError("La unidad %s no tiene ningún disco o no se puede leer su TOC." % letra)
        return buf.raw[:devueltos.value or TAM_TOC]
    finally:
        k.CloseHandle(h)


def listar_unidades():
    """Unidades de CD/DVD (físicas o virtuales) y si tienen disco legible."""
    k = _kernel32()
    mascara = k.GetLogicalDrives()
    unidades = []
    for i in range(26):
        if not (mascara >> i) & 1:
            continue
        letra = "%s:" % chr(65 + i)
        if k.GetDriveTypeW(letra + "\\") != DRIVE_CDROM:
            continue
        try:
            leer_toc_bruta(letra)
            con_disco = True
        except OSError:
            con_disco = False
        unidades.append({"letra": letra, "conDisco": con_disco})
    return unidades


# ----------------------------------------------------------------------------------------------
# 2) TOC -> DiscID de MusicBrainz (funciones puras, sin Windows)
# ----------------------------------------------------------------------------------------------
def parsear_toc(raw):
    """Interpreta los bytes de CDROM_TOC. Devuelve dict con pistas (número, frames absolutos, es_datos) y leadout."""
    if len(raw) < 4:
        raise ValueError("TOC vacía.")
    longitud = (raw[0] << 8) | raw[1]
    entradas = max(0, (longitud - 2) // 8)
    pistas, leadout = [], None
    for i in range(entradas):
        o = 4 + i * 8
        if o + 8 > len(raw):
            break
        control = raw[o + 1] & 0x0F
        numero = raw[o + 2]
        m, s, f = raw[o + 5], raw[o + 6], raw[o + 7]
        frames = (m * 60 + s) * 75 + f          # MSF absoluto: ya incluye los 150 frames iniciales
        if numero == 0xAA:
            leadout = frames
        elif 1 <= numero <= 99:
            pistas.append({"n": numero, "frames": frames, "datos": bool(control & 0x04)})
    if leadout is None or not pistas:
        raise ValueError("No se pudo interpretar la TOC del disco.")
    return {"pistas": pistas, "leadout": leadout}


def preparar_disco(toc):
    """Deja solo las pistas de audio (CD Extra: la pista de datos final se descarta y el leadout se ajusta)."""
    pistas = sorted(toc["pistas"], key=lambda p: p["n"])
    leadout = toc["leadout"]
    # pistas de datos al final (CD Extra / Enhanced CD): se ignoran, y el fin del audio es el inicio de los datos - 11400
    while pistas and pistas[-1]["datos"]:
        leadout = pistas[-1]["frames"] - 11400
        pistas.pop()
    audio = [p for p in pistas if not p["datos"]]
    if not audio:
        raise ValueError("El disco no es un CD de audio (no tiene pistas de audio).")
    return audio, leadout


def calcular_discid(audio, leadout):
    primera, ultima = audio[0]["n"], audio[-1]["n"]
    offsets = {p["n"]: p["frames"] for p in audio}
    s = "%02X%02X%08X" % (primera, ultima, leadout)
    for i in range(1, 100):
        s += "%08X" % offsets.get(i, 0)
    h = hashlib.sha1(s.encode("ascii")).digest()
    return base64.b64encode(h).decode("ascii").replace("+", ".").replace("/", "_").replace("=", "-")


def cadena_toc(audio, leadout):
    partes = [str(audio[0]["n"]), str(audio[-1]["n"]), str(leadout)] + [str(p["frames"]) for p in audio]
    return "+".join(partes)


def duraciones(audio, leadout):
    res = []
    for i, p in enumerate(audio):
        fin = audio[i + 1]["frames"] if i + 1 < len(audio) else leadout
        res.append({"n": p["n"], "segundos": round((fin - p["frames"]) / 75.0)})
    return res


# ----------------------------------------------------------------------------------------------
# 3) MusicBrainz
# ----------------------------------------------------------------------------------------------
def _credito(lista):
    return "".join(((c.get("name") or (c.get("artist") or {}).get("name") or "") + (c.get("joinphrase") or "")) for c in (lista or [])).strip()


def normalizar_release(rel, discid, n_pistas_disco):
    medios = []
    for m in rel.get("media") or []:
        pistas = []
        for t in m.get("tracks") or []:
            ms = t.get("length") or (t.get("recording") or {}).get("length")
            pistas.append({
                "n": t.get("position"),
                "titulo": t.get("title") or (t.get("recording") or {}).get("title") or "",
                "artista": _credito(t.get("artist-credit")),
                "segundos": round(ms / 1000.0) if ms else None,
            })
        medios.append({
            "numero": m.get("position") or (len(medios) + 1),
            "formato": m.get("format") or "",
            "titulo": m.get("title") or "",
            "exacto": any((d.get("id") == discid) for d in (m.get("discs") or [])),
            "pistas": pistas,
        })
    # medio que corresponde al disco leído: el del DiscID exacto o, si no, el que tiene el mismo nº de pistas
    elegido = next((m for m in medios if m["exacto"]), None)
    if elegido is None:
        elegido = next((m for m in medios if len(m["pistas"]) == n_pistas_disco), None)
    li = (rel.get("label-info") or [{}])[0]
    return {
        "mbid": rel.get("id"),
        "titulo": rel.get("title") or "",
        "artista": _credito(rel.get("artist-credit")),
        "fecha": rel.get("date") or "",
        "pais": rel.get("country") or "",
        "sello": ((li.get("label") or {}).get("name")) or "",
        "catalogo": li.get("catalog-number") or "",
        "barcode": rel.get("barcode") or "",
        "totalMedios": len(medios),
        "medioLeido": elegido["numero"] if elegido else None,
        "exacto": bool(elegido and elegido["exacto"]),
        "mismoNumPistas": bool(elegido and len(elegido["pistas"]) == n_pistas_disco),
        "medios": medios,
    }


def consultar_musicbrainz(discid, toc_txt, n_pistas):
    url = ("https://musicbrainz.org/ws/2/discid/%s?fmt=json&inc=artist-credits+recordings+labels&cdstubs=no&toc=%s"
           % (discid, toc_txt))
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=25) as r:
            datos = json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return []
        if e.code in (429, 503):
            raise RuntimeError("MusicBrainz está limitando las consultas. Espera unos segundos y vuelve a intentarlo.")
        raise RuntimeError("MusicBrainz respondió con el error %s." % e.code)
    except urllib.error.URLError:
        raise RuntimeError("No hay conexión con MusicBrainz (¿sin internet?).")
    candidatos = [normalizar_release(r, discid, n_pistas) for r in (datos.get("releases") or [])]
    # primero los de coincidencia exacta, luego los que tienen el mismo nº de pistas
    candidatos.sort(key=lambda c: (not c["exacto"], not c["mismoNumPistas"], c["fecha"] or "9999"))
    return candidatos[:MAX_CANDIDATOS]


def leer_disco(letra):
    toc = parsear_toc(leer_toc_bruta(letra))
    audio, leadout = preparar_disco(toc)
    discid = calcular_discid(audio, leadout)
    toc_txt = cadena_toc(audio, leadout)
    return {
        "ok": True,
        "unidad": letra,
        "discid": discid,
        "toc": toc_txt,
        "pistas": duraciones(audio, leadout),
        "candidatos": consultar_musicbrainz(discid, toc_txt, len(audio)),
    }


# ----------------------------------------------------------------------------------------------
# 3b) Abrir una imagen de disco (Ir A Disco)
# ----------------------------------------------------------------------------------------------
def abrir_imagen(ruta):
    """Abre el archivo con el programa que Windows tenga asociado a su extensión (Daemon Tools para .mdx)."""
    ruta = (ruta or "").strip().strip('"').strip()
    if not ruta:
        raise ValueError("No hay ninguna ruta.")
    ruta = os.path.normpath(ruta)
    if not os.path.isabs(ruta):
        raise ValueError("La ruta debe ser completa (por ejemplo D:\\Discos\\album.mdx).")
    ext = os.path.splitext(ruta)[1].lower()
    if ext not in EXTENSIONES_IMAGEN:
        raise ValueError("Solo se pueden abrir imágenes de disco (%s)." % ", ".join(sorted(EXTENSIONES_IMAGEN)))
    if not os.path.isfile(ruta):
        raise ValueError("No se encuentra el archivo: %s" % ruta)
    try:
        os.startfile(ruta)
    except OSError:
        raise ValueError("Windows no pudo abrirlo. ¿Tiene %s un programa asociado (Daemon Tools)?" % ext)
    return ruta


# ----------------------------------------------------------------------------------------------
# 4) Servidor local
# ----------------------------------------------------------------------------------------------
class Manejador(BaseHTTPRequestHandler):
    server_version = "LectorCD/" + VERSION

    def log_message(self, formato, *args):
        sys.stdout.write("  %s\n" % (formato % args))

    def _origen_ok(self):
        origen = self.headers.get("Origin")
        if origen is None:
            return True        # visita directa desde la barra de direcciones (para probar)
        return origen in ORIGENES_PERMITIDOS or re.match(r"^http://(localhost|127\.0\.0\.1)(:\d+)?$", origen) is not None

    def _cabeceras(self, codigo, tipo="application/json; charset=utf-8", longitud=0):
        self.send_response(codigo)
        origen = self.headers.get("Origin")
        if origen and self._origen_ok():
            self.send_header("Access-Control-Allow-Origin", origen)
            self.send_header("Vary", "Origin")
            self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "*")
            self.send_header("Access-Control-Allow-Private-Network", "true")   # Chrome/Edge: página pública -> red local
            self.send_header("Access-Control-Max-Age", "600")
        self.send_header("Content-Type", tipo)
        self.send_header("Content-Length", str(longitud))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()

    def _json(self, codigo, obj):
        cuerpo = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self._cabeceras(codigo, longitud=len(cuerpo))
        self.wfile.write(cuerpo)

    def do_OPTIONS(self):
        self._cabeceras(204 if self._origen_ok() else 403)

    def do_GET(self):
        if not self._origen_ok():
            return self._json(403, {"ok": False, "error": "Origen no autorizado."})
        ruta = urlparse(self.path)
        params = parse_qs(ruta.query)
        try:
            if ruta.path in ("/", "/estado"):
                return self._json(200, {"ok": True, "version": VERSION, "unidades": listar_unidades()})
            if ruta.path == "/abrir":
                # Protección extra: una página ajena no puede lanzarlo "a ciegas" (p. ej. con una imagen oculta).
                if self.headers.get("Origin") is None and self.headers.get("Sec-Fetch-Site") not in (None, "none", "same-origin"):
                    return self._json(403, {"ok": False, "error": "Origen no autorizado."})
                abierto = abrir_imagen((params.get("ruta") or [""])[0])
                print("  Abierto: %s" % abierto)
                return self._json(200, {"ok": True, "ruta": abierto})
            if ruta.path == "/leer":
                letra = (params.get("unidad") or [""])[0].upper()
                if not re.match(r"^[A-Z]:$", letra):
                    return self._json(400, {"ok": False, "error": "Unidad no válida."})
                if letra not in [u["letra"] for u in listar_unidades()]:
                    return self._json(400, {"ok": False, "error": "%s no es una unidad de CD." % letra})
                return self._json(200, leer_disco(letra))
            return self._json(404, {"ok": False, "error": "No existe."})
        except (OSError, ValueError, RuntimeError) as e:
            return self._json(200, {"ok": False, "error": str(e)})
        except Exception as e:      # cualquier fallo inesperado: se avisa sin tumbar el programa
            return self._json(500, {"ok": False, "error": "Error inesperado: %s" % e})


def main():
    if sys.platform != "win32":
        print("Este programa solo funciona en Windows.")
        return
    try:
        servidor = ThreadingHTTPServer(("127.0.0.1", PUERTO), Manejador)
    except OSError:
        print("No se pudo abrir el puerto %d: ¿ya hay otra ventana del lector abierta?" % PUERTO)
        return
    print("Lector de CD para 'Mi colección' v%s" % VERSION)
    print("Escuchando en http://127.0.0.1:%d  (solo en este PC)" % PUERTO)
    print("Unidades de CD detectadas:", ", ".join("%s%s" % (u["letra"], "" if u["conDisco"] else " (vacía)") for u in listar_unidades()) or "ninguna")
    print("Deja esta ventana abierta mientras añades álbumes. Ctrl+C para cerrar.\n")
    try:
        servidor.serve_forever()
    except KeyboardInterrupt:
        print("\nCerrado.")


if __name__ == "__main__":
    main()
