import asyncio
import base64
import hashlib
import hmac
import math
import os
import re
import secrets
import smtplib
import sqlite3
import ssl
import time
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import edge_tts
import httpx
from fastapi import Depends, FastAPI, HTTPException, Query, Request, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, StreamingResponse
from pydantic import BaseModel, Field

try:
    import psycopg2
    from psycopg2.extras import RealDictCursor
except ImportError:
    psycopg2 = None
    RealDictCursor = None

# =============================================================================
# CONFIGURACIÓN GENERAL Y VARIABLES DE ENTORNO
# =============================================================================
APP_VERSION = "1.2.0-alpha"
BASE_DIR = Path(__file__).resolve().parent
DB_PATH = os.getenv("DB_PATH", str(BASE_DIR / "copiloto.db"))
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
USE_PG = DATABASE_URL.startswith("postgres://") or DATABASE_URL.startswith("postgresql://")

DEBUG = os.getenv("DEBUG", "false").strip().lower() in ("1", "true", "yes", "on")
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "").strip()
GOOGLE_CLIENT_ID = os.getenv("GOOGLE_CLIENT_ID", "").strip()
SUPPORT_EMAIL = os.getenv("SUPPORT_EMAIL", "copilotoseguromx@gmail.com").strip()
SMTP_USER = os.getenv("SMTP_USER", "").strip()
SMTP_PASS = os.getenv("SMTP_PASS", "").strip()
ALLOWED_ORIGINS = [
    o.strip() for o in os.getenv("ALLOWED_ORIGINS", "").split(",") if o.strip()
]

_raw_secret = os.getenv("APP_SECRET", "").strip()
if not _raw_secret:
    if DEBUG:
        _raw_secret = "dev-local-copiloto-secret-change-in-prod"
    else:
        _raw_secret = secrets.token_hex(32)
APP_SECRET = _raw_secret

SESSION_COOKIE = "copiloto_session"
SESSION_MAX_AGE = 60 * 60 * 24 * 30  # 30 días
USERNAME_LOCK_DAYS = 180  # 6 meses
USERNAME_RE = re.compile(r"^[A-Za-z0-9_-]{3,20}$")
MX_TZ = timezone(timedelta(hours=-6))

VALHALLA_URL = os.getenv("VALHALLA_URL", "https://valhalla1.openstreetmap.de/route")
NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"
OVERPASS_URL = "https://overpass-api.de/api/interpreter"
OPEN_METEO_URL = "https://api.open-meteo.com/v1/forecast"
USER_AGENT = f"CopilotoSeguroMX/{APP_VERSION} ({SUPPORT_EMAIL})"

VOCES_MX: List[Dict[str, str]] = [
    {"id": "es-MX-DaliaNeural", "nombre": "Dalia (México · Femenina)"},
    {"id": "es-MX-JorgeNeural", "nombre": "Jorge (México · Masculina)"},
    {"id": "es-MX-BeatrizNeural", "nombre": "Beatriz (México · Femenina)"},
    {"id": "es-MX-CandelaNeural", "nombre": "Candela (México · Femenina)"},
    {"id": "es-MX-CarlotaNeural", "nombre": "Carlota (México · Femenina)"},
    {"id": "es-MX-CecilioNeural", "nombre": "Cecilio (México · Masculina)"},
    {"id": "es-MX-GerardoNeural", "nombre": "Gerardo (México · Masculina)"},
    {"id": "es-MX-LarissaNeural", "nombre": "Larissa (México · Femenina)"},
    {"id": "es-MX-LucianoNeural", "nombre": "Luciano (México · Masculina)"},
    {"id": "es-MX-MarinaNeural", "nombre": "Marina (México · Femenina)"},
    {"id": "es-MX-RenataNeural", "nombre": "Renata (México · Femenina)"},
    {"id": "es-MX-YagoNeural", "nombre": "Yago (México · Masculina)"},
]
VOCES_MX_IDS = {v["id"] for v in VOCES_MX}

TIPOS_REPORTE_GRAVEDAD = {
    "ACCIDENTE": "ALTO",
    "TRAFICO": "MEDIO",
    "BLOQUEO": "CRITICO",
    "RETEN_SOSPECHOSO": "CRITICO",
    "ASALTO": "CRITICO",
    "CIERRE": "ALTO",
    "NEBLINA": "MEDIO",
    "LLUVIA_FUERTE": "MEDIO",
    "BACHE_PELIGROSO": "MEDIO",
    "OBRA": "MEDIO",
}

_last_gps_by_user: Dict[int, Tuple[float, float, float]] = {}
_rate_limit_hits: Dict[str, List[float]] = {}
_speed_cache: Dict[str, Tuple[float, Optional[int]]] = {}

app = FastAPI(title="Copiloto Seguro MX", version=APP_VERSION)

if ALLOWED_ORIGINS:
    app.add_middleware(
        CORSMiddleware,
        allow_origins=ALLOWED_ORIGINS,
        allow_credentials=True,
        allow_methods=["*"],
        allow_headers=["*"],
    )
elif DEBUG:
    app.add_middleware(
        CORSMiddleware,
        allow_origins=["http://localhost:8000", "http://127.0.0.1:8000"],
        allow_credentials=True,
        allow_methods=["*"],
        allow_headers=["*"],
    )


# =============================================================================
# ADAPTADOR DE BASE DE DATOS HÍBRIDO (SQLITE LOCAL / POSTGRESQL NEON-RENDER)
# =============================================================================
class DBConn:
    def __init__(self) -> None:
        self.is_pg = USE_PG
        if self.is_pg:
            if psycopg2 is None:
                raise RuntimeError("Falta instalar psycopg2-binary para conectar con PostgreSQL.")
            dsn = DATABASE_URL.replace("postgres://", "postgresql://", 1)
            self._conn = psycopg2.connect(dsn, cursor_factory=RealDictCursor)
        else:
            self._conn = sqlite3.connect(DB_PATH, timeout=15)
            self._conn.row_factory = sqlite3.Row
            self._conn.execute("PRAGMA journal_mode=WAL;")
            self._conn.execute("PRAGMA foreign_keys=ON;")

    def _adapt_sql(self, sql: str) -> str:
        return sql.replace("?", "%s") if self.is_pg else sql

    def execute(self, sql: str, params: Tuple[Any, ...] = ()) -> Any:
        q = self._adapt_sql(sql)
        if self.is_pg:
            cur = self._conn.cursor()
            cur.execute(q, params)
            return cur
        return self._conn.execute(q, params)

    def fetchone(self, sql: str, params: Tuple[Any, ...] = ()) -> Optional[Dict[str, Any]]:
        cur = self.execute(sql, params)
        row = cur.fetchone()
        if self.is_pg:
            cur.close()
        return dict(row) if row is not None else None

    def fetchall(self, sql: str, params: Tuple[Any, ...] = ()) -> List[Dict[str, Any]]:
        cur = self.execute(sql, params)
        rows = cur.fetchall()
        if self.is_pg:
            cur.close()
        return [dict(r) for r in rows]

    def insert_id(self, sql: str, params: Tuple[Any, ...] = ()) -> int:
        if self.is_pg:
            q = self._adapt_sql(sql).rstrip().rstrip(";") + " RETURNING id"
            cur = self._conn.cursor()
            cur.execute(q, params)
            row = cur.fetchone()
            cur.close()
            return int(row["id"])
        cur = self._conn.execute(sql, params)
        return int(cur.lastrowid)

    def commit(self) -> None:
        self._conn.commit()

    def close(self) -> None:
        self._conn.close()


def get_conn() -> DBConn:
    return DBConn()


def ensure_columns(conn: DBConn, table: str, columns: Dict[str, str]) -> None:
    if conn.is_pg:
        rows = conn.fetchall(
            "SELECT column_name FROM information_schema.columns WHERE table_name = ?",
            (table,),
        )
        existing = {r["column_name"] for r in rows}
    else:
        rows = conn.fetchall(f"PRAGMA table_info({table})")
        existing = {r["name"] for r in rows}

    for col, col_def in columns.items():
        if col not in existing:
            pg_def = col_def.replace("REAL", "DOUBLE PRECISION") if conn.is_pg else col_def
            conn.execute(f"ALTER TABLE {table} ADD COLUMN {col} {pg_def}")


def init_db() -> None:
    conn = get_conn()
    pk = "SERIAL PRIMARY KEY" if conn.is_pg else "INTEGER PRIMARY KEY AUTOINCREMENT"
    flt = "DOUBLE PRECISION" if conn.is_pg else "REAL"

    ddl_statements = [
        f"""
        CREATE TABLE IF NOT EXISTS usuarios (
            id {pk},
            google_sub TEXT UNIQUE,
            email TEXT UNIQUE NOT NULL,
            nombre_real TEXT DEFAULT '',
            username TEXT UNIQUE,
            username_updated_at TEXT,
            reputacion INTEGER DEFAULT 1,
            tipo_vehiculo TEXT DEFAULT 'auto',
            altura_m {flt} DEFAULT 1.8,
            peso_t {flt} DEFAULT 2.0,
            tipo_combustible TEXT DEFAULT 'magna',
            precio_litro {flt} DEFAULT 24.5,
            rendimiento_kml {flt} DEFAULT 12.0,
            capacidad_tanque {flt} DEFAULT 55.0,
            litros_actuales {flt} DEFAULT 40.0,
            mostrar_pildora_combustible INTEGER DEFAULT 1,
            contacto_emergencia_nombre TEXT DEFAULT '',
            contacto_emergencia_tel TEXT DEFAULT '',
            frase_sos_hash TEXT DEFAULT '',
            created_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS reportes (
            id {pk},
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            tipo TEXT NOT NULL,
            gravedad TEXT NOT NULL,
            descripcion TEXT NOT NULL,
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            estado TEXT NOT NULL DEFAULT 'PUBLICO',
            confirmaciones INTEGER NOT NULL DEFAULT 1,
            votos_despejar INTEGER NOT NULL DEFAULT 0,
            activo INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL,
            expires_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS reporte_votos (
            id {pk},
            reporte_id INTEGER NOT NULL REFERENCES reportes(id),
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            accion TEXT NOT NULL,
            created_at TEXT NOT NULL,
            UNIQUE(reporte_id, usuario_id, accion)
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS zonas_sin_senal (
            id {pk},
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            radio_m INTEGER NOT NULL DEFAULT 650,
            conteo INTEGER NOT NULL DEFAULT 1,
            updated_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS paraderos (
            id {pk},
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            nombre TEXT NOT NULL,
            tipo TEXT NOT NULL DEFAULT 'PERNOCTA',
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            tiene_vigilancia INTEGER NOT NULL DEFAULT 1,
            notas TEXT DEFAULT '',
            created_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS canal_cb (
            id {pk},
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            canal_hash TEXT NOT NULL DEFAULT 'PUBLICO_19',
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            audio_b64 TEXT NOT NULL,
            mime_type TEXT NOT NULL DEFAULT 'audio/webm',
            created_at {flt} NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS rastreos (
            codigo TEXT PRIMARY KEY,
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            destino TEXT DEFAULT '',
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            velocidad_kmh INTEGER DEFAULT 0,
            eta_texto TEXT DEFAULT '--:--',
            sos_activo INTEGER NOT NULL DEFAULT 0,
            alerta_detencion INTEGER NOT NULL DEFAULT 0,
            activo INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            expires_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS sos_eventos (
            id {pk},
            usuario_id INTEGER NOT NULL REFERENCES usuarios(id),
            lat {flt} NOT NULL,
            lng {flt} NOT NULL,
            origen TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        f"""
        CREATE TABLE IF NOT EXISTS mensajes_soporte (
            id {pk},
            usuario_id INTEGER REFERENCES usuarios(id),
            correo_remitente TEXT DEFAULT '',
            categoria TEXT NOT NULL DEFAULT 'SUGERENCIA',
            asunto TEXT NOT NULL,
            mensaje TEXT NOT NULL,
            enviado_correo INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL
        )
        """,
    ]

    try:
        for stmt in ddl_statements:
            conn.execute(stmt)

        ensure_columns(
            conn,
            "rastreos",
            {
                "eta_texto": "TEXT DEFAULT '--:--'",
                "sos_activo": "INTEGER NOT NULL DEFAULT 0",
                "alerta_detencion": "INTEGER NOT NULL DEFAULT 0",
            },
        )

        conn.execute("CREATE INDEX IF NOT EXISTS idx_reportes_activo ON reportes(activo, expires_at)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_cb_canal_time ON canal_cb(canal_hash, created_at)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_rastreos_user ON rastreos(usuario_id, activo)")
        conn.commit()
    finally:
        conn.close()


@app.on_event("startup")
def on_startup() -> None:
    init_db()


# =============================================================================
# UTILIDADES CRIPTOGRÁFICAS, TIEMPO, GEOMETRÍA Y CORREO
# =============================================================================
def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def iso_now() -> str:
    return now_utc().isoformat()


def haversine_km(lat1: float, lng1: float, lat2: float, lng2: float) -> float:
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lng2 - lng1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(min(1.0, math.sqrt(a)))


def sign_session(user_id: int) -> str:
    exp = int(time.time()) + SESSION_MAX_AGE
    payload = f"{user_id}.{exp}"
    sig = hmac.new(APP_SECRET.encode(), payload.encode(), hashlib.sha256).hexdigest()
    return f"{payload}.{sig}"


def verify_session(token: Optional[str]) -> Optional[int]:
    if not token:
        return None
    parts = token.split(".")
    if len(parts) != 3:
        return None
    uid_s, exp_s, sig = parts
    payload = f"{uid_s}.{exp_s}"
    expected = hmac.new(APP_SECRET.encode(), payload.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(sig, expected):
        return None
    try:
        if int(exp_s) < int(time.time()):
            return None
        return int(uid_s)
    except ValueError:
        return None


def hash_secret_phrase(user_id: int, phrase: str) -> str:
    norm = re.sub(r"\s+", " ", phrase.strip().lower())
    raw = f"{APP_SECRET}:sos:{user_id}:{norm}".encode()
    return hashlib.sha256(raw).hexdigest()


def hash_private_channel(clave: Optional[str]) -> str:
    if not clave or not clave.strip():
        return "PUBLICO_19"
    clean = clave.strip()
    if len(clean) < 4:
        raise HTTPException(status_code=400, detail="La clave del canal privado debe tener al menos 4 caracteres.")
    raw = f"{APP_SECRET}:cb:{clean}".encode()
    return "PRIV_" + hashlib.sha256(raw).hexdigest()[:32]


def check_rate_limit(key: str, max_hits: int, window_sec: int) -> None:
    now = time.time()
    hits = [t for t in _rate_limit_hits.get(key, []) if now - t < window_sec]
    if len(hits) >= max_hits:
        raise HTTPException(status_code=429, detail="Demasiadas solicitudes. Intenta de nuevo en unos segundos.")
    hits.append(now)
    _rate_limit_hits[key] = hits


def check_anti_teleport(user_id: int, lat: float, lng: float) -> None:
    if not (-90 <= lat <= 90 and -180 <= lng <= 180):
        raise HTTPException(status_code=400, detail="Coordenadas GPS inválidas.")
    now = time.time()
    prev = _last_gps_by_user.get(user_id)
    if prev and not DEBUG:
        plat, plng, pts = prev
        dt_h = max((now - pts) / 3600.0, 1e-6)
        dist = haversine_km(plat, plng, lat, lng)
        if dist > 8.0 and (dist / dt_h) > 260.0:
            raise HTTPException(
                status_code=400,
                detail="Salto de ubicación GPS anómalo detectado. Espera a que tu señal se estabilice.",
            )
    _last_gps_by_user[user_id] = (lat, lng, now)


def decode_polyline(encoded: str, precision: int = 6) -> List[List[float]]:
    coords: List[List[float]] = []
    index = 0
    lat = 0
    lng = 0
    factor = 10**precision
    length = len(encoded)
    while index < length:
        shift = 0
        result = 0
        while True:
            b = ord(encoded[index]) - 63
            index += 1
            result |= (b & 0x1F) << shift
            shift += 5
            if b < 0x20:
                break
        dlat = ~(result >> 1) if (result & 1) else (result >> 1)
        lat += dlat

        shift = 0
        result = 0
        while True:
            b = ord(encoded[index]) - 63
            index += 1
            result |= (b & 0x1F) << shift
            shift += 5
            if b < 0x20:
                break
        dlng = ~(result >> 1) if (result & 1) else (result >> 1)
        lng += dlng

        coords.append([lat / factor, lng / factor])
    return coords


def _enviar_correo_sync(categoria: str, asunto: str, cuerpo: str, reply_to: str = "") -> bool:
    if not SMTP_USER or not SMTP_PASS or not SUPPORT_EMAIL:
        return False
    try:
        msg = EmailMessage()
        msg["Subject"] = f"[Copiloto Seguro MX · {categoria}] {asunto}"
        msg["From"] = SMTP_USER
        msg["To"] = SUPPORT_EMAIL
        if reply_to and "@" in reply_to:
            msg["Reply-To"] = reply_to
        msg.set_content(cuerpo)

        ctx = ssl.create_default_context()
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=ctx, timeout=12) as server:
            server.login(SMTP_USER, SMTP_PASS)
            server.send_message(msg)
        return True
    except Exception:
        return False


def set_session_cookie(response: Response, user_id: int) -> None:
    response.set_cookie(
        key=SESSION_COOKIE,
        value=sign_session(user_id),
        httponly=True,
        samesite="lax",
        secure=not DEBUG,
        max_age=SESSION_MAX_AGE,
        path="/",
    )


def serialize_perfil(row: Dict[str, Any]) -> Dict[str, Any]:
    puede_cambiar = True
    proximo_iso = ""
    proximo_mx = ""
    if row["username"] and row["username_updated_at"]:
        try:
            dt = datetime.fromisoformat(row["username_updated_at"])
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            prox = dt + timedelta(days=USERNAME_LOCK_DAYS)
            if now_utc() < prox:
                puede_cambiar = False
                proximo_iso = prox.strftime("%Y-%m-%d")
                proximo_mx = prox.strftime("%d/%m/%Y")
        except ValueError:
            pass

    return {
        "id": row["id"],
        "email": row["email"],
        "nombre_real": row["nombre_real"] or "",
        "username": row["username"] or "",
        "requiere_username": not bool(row["username"]),
        "puede_cambiar_username": puede_cambiar,
        "proximo_cambio_username": proximo_iso,
        "proximo_cambio_username_mx": proximo_mx,
        "reputacion": row["reputacion"],
        "tipo_vehiculo": row["tipo_vehiculo"] or "auto",
        "altura_m": float(row["altura_m"] or 1.8),
        "peso_t": float(row["peso_t"] or 2.0),
        "tipo_combustible": row["tipo_combustible"] or "magna",
        "precio_litro": float(row["precio_litro"] or 24.5),
        "rendimiento_kml": float(row["rendimiento_kml"] or 12.0),
        "capacidad_tanque": float(row["capacidad_tanque"] or 55.0),
        "litros_actuales": float(row["litros_actuales"] or 40.0),
        "mostrar_pildora_combustible": bool(row["mostrar_pildora_combustible"]),
        "contacto_emergencia_nombre": row["contacto_emergencia_nombre"] or "",
        "contacto_emergencia_tel": row["contacto_emergencia_tel"] or "",
        "tiene_frase_sos": bool(row["frase_sos_hash"]),
    }


def get_optional_user(request: Request) -> Optional[Dict[str, Any]]:
    uid = verify_session(request.cookies.get(SESSION_COOKIE))
    if not uid:
        return None
    conn = get_conn()
    try:
        return conn.fetchone("SELECT * FROM usuarios WHERE id = ?", (uid,))
    finally:
        conn.close()


def require_user(user: Optional[Dict[str, Any]] = Depends(get_optional_user)) -> Dict[str, Any]:
    if not user:
        raise HTTPException(status_code=401, detail="Inicia sesión en Perfil para usar esta función.")
    return user


# =============================================================================
# MODELOS PYDANTIC
# =============================================================================
class GoogleAuthIn(BaseModel):
    id_token: str = Field(..., min_length=20)


class DevAuthIn(BaseModel):
    email: str = Field(..., min_length=5, max_length=120)
    nombre_real: str = Field(default="Conductor Local", max_length=80)


class PerfilUpdateIn(BaseModel):
    nombre_real: Optional[str] = Field(default=None, max_length=80)
    username: Optional[str] = Field(default=None, max_length=20)
    tipo_vehiculo: Optional[str] = None
    altura_m: Optional[float] = Field(default=None, ge=1.2, le=5.5)
    peso_t: Optional[float] = Field(default=None, ge=0.5, le=80.0)
    tipo_combustible: Optional[str] = None
    precio_litro: Optional[float] = Field(default=None, ge=10.0, le=60.0)
    rendimiento_kml: Optional[float] = Field(default=None, ge=1.0, le=40.0)
    capacidad_tanque: Optional[float] = Field(default=None, ge=10.0, le=1500.0)
    litros_actuales: Optional[float] = Field(default=None, ge=0.0, le=1500.0)
    mostrar_pildora_combustible: Optional[bool] = None
    contacto_emergencia_nombre: Optional[str] = Field(default=None, max_length=80)
    contacto_emergencia_tel: Optional[str] = Field(default=None, max_length=25)
    frase_sos: Optional[str] = Field(default=None, max_length=80)


class ReporteCreateIn(BaseModel):
    tipo: str
    descripcion: str = Field(default="", max_length=200)
    lat: float
    lng: float


class AccionGPSIn(BaseModel):
    lat: float
    lng: float


class ZonaSinSenalIn(BaseModel):
    lat: float
    lng: float
    recuperada: bool = False


class RutaCompararIn(BaseModel):
    origen_lat: float
    origen_lng: float
    destino_lat: float
    destino_lng: float


class ParaderoCreateIn(BaseModel):
    nombre: str = Field(..., min_length=2, max_length=90)
    tipo: str = Field(default="PERNOCTA")
    tiene_vigilancia: bool = True
    notas: str = Field(default="", max_length=180)
    lat: float
    lng: float


class CBEnviarIn(BaseModel):
    lat: float
    lng: float
    audio_b64: str = Field(..., min_length=20, max_length=650000)
    mime_type: str = Field(default="audio/webm", max_length=40)
    canal_privado: Optional[str] = Field(default=None, max_length=40)


class RastreoIniciarIn(BaseModel):
    destino: str = Field(default="", max_length=160)
    lat: float
    lng: float
    eta_texto: str = Field(default="--:--", max_length=30)


class RastreoActualizarIn(BaseModel):
    codigo: str = Field(..., min_length=6, max_length=32)
    lat: float
    lng: float
    velocidad_kmh: int = Field(default=0, ge=0, le=260)
    eta_texto: str = Field(default="--:--", max_length=30)


class RastreoDetencionIn(BaseModel):
    codigo: str = Field(..., min_length=6, max_length=32)
    activa: bool = True
    lat: float
    lng: float


class SOSActivarIn(BaseModel):
    lat: float
    lng: float
    origen: str = Field(default="BOTON", max_length=20)


class AgenteIn(BaseModel):
    mensaje: str = Field(..., min_length=1, max_length=280)
    lat: float
    lng: float
    destino_actual: Optional[str] = Field(default=None, max_length=160)


class TTSIn(BaseModel):
    texto: str = Field(..., min_length=1, max_length=420)
    voz: str = Field(default="es-MX-DaliaNeural")
    velocidad: int = Field(default=0, ge=-30, le=40)
    tono: int = Field(default=0, ge=-20, le=20)


class SoporteMensajeIn(BaseModel):
    categoria: str = Field(default="SUGERENCIA", max_length=30)
    asunto: str = Field(..., min_length=3, max_length=120)
    mensaje: str = Field(..., min_length=8, max_length=1500)
    correo_contacto: Optional[str] = Field(default="", max_length=120)


# =============================================================================
# RUTAS BASE, PWA (ANDROID) Y SALUD
# =============================================================================
@app.get("/", response_class=HTMLResponse)
def serve_index():
    idx = BASE_DIR / "index.html"
    if not idx.exists():
        raise HTTPException(status_code=404, detail="Archivo index.html no encontrado.")
    return FileResponse(idx)


@app.get("/manifest.json")
def serve_manifest():
    manifest = {
        "name": "Copiloto Seguro MX",
        "short_name": "Copiloto MX",
        "description": "Asistente de seguridad, rutas y telemetría para carreteras de México.",
        "start_url": "/",
        "display": "standalone",
        "orientation": "portrait",
        "background_color": "#070d19",
        "theme_color": "#0f172a",
        "lang": "es-MX",
        "icons": [
            {
                "src": "/icon.svg",
                "sizes": "any",
                "type": "image/svg+xml",
                "purpose": "any maskable",
            }
        ],
    }
    return JSONResponse(manifest, media_type="application/manifest+json")


@app.get("/icon.svg")
def serve_icon():
    svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512">
  <rect width="512" height="512" rx="112" fill="#0f172a"/>
  <path d="M256 76L404 134V250C404 344 340 422 256 446C172 422 108 344 108 250V134L256 76Z" fill="#1e293b" stroke="#3b82f6" stroke-width="22" stroke-linejoin="round"/>
  <path d="M256 150L318 326L256 290L194 326L256 150Z" fill="#3b82f6"/>
  <circle cx="256" cy="248" r="18" fill="#f8fafc"/>
</svg>"""
    return Response(content=svg, media_type="image/svg+xml")


@app.get("/health")
def health():
    return {
        "status": "ok",
        "version": APP_VERSION,
        "db": "postgresql" if USE_PG else "sqlite",
    }


# =============================================================================
# AUTENTICACIÓN Y PERFIL
# =============================================================================
@app.get("/auth/config")
def auth_config(user: Optional[Dict[str, Any]] = Depends(get_optional_user)):
    return {
        "debug_mode": DEBUG,
        "google_client_id": GOOGLE_CLIENT_ID,
        "support_email": SUPPORT_EMAIL,
        "autenticado": user is not None,
        "perfil": serialize_perfil(user) if user else None,
        "version": APP_VERSION,
    }


@app.post("/auth/google")
async def auth_google(body: GoogleAuthIn, response: Response):
    if not GOOGLE_CLIENT_ID:
        raise HTTPException(status_code=400, detail="GOOGLE_CLIENT_ID no configurado en el servidor.")

    async with httpx.AsyncClient(timeout=10.0) as client:
        r = await client.get(
            "https://oauth2.googleapis.com/tokeninfo",
            params={"id_token": body.id_token},
        )
    if r.status_code != 200:
        raise HTTPException(status_code=401, detail="Token de Google inválido o expirado.")

    info = r.json()
    if info.get("aud") != GOOGLE_CLIENT_ID:
        raise HTTPException(status_code=401, detail="El token no pertenece a esta aplicación.")

    sub = info.get("sub")
    email = (info.get("email") or "").strip().lower()
    nombre = (info.get("name") or "").strip()[:80]
    if not sub or not email:
        raise HTTPException(status_code=401, detail="Cuenta de Google incompleta.")

    conn = get_conn()
    try:
        user = conn.fetchone(
            "SELECT * FROM usuarios WHERE google_sub = ? OR email = ?",
            (sub, email),
        )
        if not user:
            uid = conn.insert_id(
                "INSERT INTO usuarios (google_sub, email, nombre_real, created_at) VALUES (?, ?, ?, ?)",
                (sub, email, nombre, iso_now()),
            )
            conn.commit()
            user = conn.fetchone("SELECT * FROM usuarios WHERE id = ?", (uid,))
        elif not user["google_sub"]:
            conn.execute("UPDATE usuarios SET google_sub = ? WHERE id = ?", (sub, user["id"]))
            conn.commit()
            user = conn.fetchone("SELECT * FROM usuarios WHERE id = ?", (user["id"],))
        set_session_cookie(response, user["id"])
        return {"perfil": serialize_perfil(user)}
    finally:
        conn.close()


@app.post("/auth/dev")
def auth_dev(body: DevAuthIn, response: Response):
    if not DEBUG:
        raise HTTPException(status_code=403, detail="El acceso local solo está habilitado en modo desarrollo.")
    email = body.email.strip().lower()
    if "@" not in email:
        raise HTTPException(status_code=400, detail="Correo inválido.")
    conn = get_conn()
    try:
        user = conn.fetchone("SELECT * FROM usuarios WHERE email = ?", (email,))
        if not user:
            uid = conn.insert_id(
                "INSERT INTO usuarios (email, nombre_real, created_at) VALUES (?, ?, ?)",
                (email, body.nombre_real.strip()[:80], iso_now()),
            )
            conn.commit()
            user = conn.fetchone("SELECT * FROM usuarios WHERE id = ?", (uid,))
        set_session_cookie(response, user["id"])
        return {"perfil": serialize_perfil(user)}
    finally:
        conn.close()


@app.post("/auth/logout")
def auth_logout(response: Response):
    response.delete_cookie(SESSION_COOKIE, path="/")
    return {"ok": True}


@app.get("/perfil")
def get_perfil(user: Dict[str, Any] = Depends(require_user)):
    return serialize_perfil(user)


@app.put("/perfil")
def update_perfil(body: PerfilUpdateIn, user: Dict[str, Any] = Depends(require_user)):
    updates: Dict[str, Any] = {}
    conn = get_conn()
    try:
        if body.username is not None:
            cand = body.username.strip()
            if cand and cand != (user["username"] or ""):
                if not USERNAME_RE.match(cand):
                    raise HTTPException(
                        status_code=400,
                        detail="El usuario debe tener entre 3 y 20 caracteres (letras, números, _ o -).",
                    )
                if user["username"] and user["username_updated_at"]:
                    dt = datetime.fromisoformat(user["username_updated_at"])
                    if dt.tzinfo is None:
                        dt = dt.replace(tzinfo=timezone.utc)
                    prox = dt + timedelta(days=USERNAME_LOCK_DAYS)
                    if now_utc() < prox:
                        raise HTTPException(
                            status_code=400,
                            detail=f"Podrás cambiar tu usuario de nuevo el {prox.strftime('%d/%m/%Y')}.",
                        )
                clash = conn.fetchone(
                    "SELECT id FROM usuarios WHERE LOWER(username) = LOWER(?) AND id != ?",
                    (cand, user["id"]),
                )
                if clash:
                    raise HTTPException(status_code=409, detail="Ese nombre de usuario ya está ocupado.")
                updates["username"] = cand
                updates["username_updated_at"] = iso_now()

        if body.nombre_real is not None:
            updates["nombre_real"] = body.nombre_real.strip()
        if body.tipo_vehiculo in ("auto", "camion", "trailer"):
            updates["tipo_vehiculo"] = body.tipo_vehiculo
        if body.altura_m is not None:
            updates["altura_m"] = body.altura_m
        if body.peso_t is not None:
            updates["peso_t"] = body.peso_t
        if body.tipo_combustible in ("magna", "premium", "diesel"):
            updates["tipo_combustible"] = body.tipo_combustible
        if body.precio_litro is not None:
            updates["precio_litro"] = body.precio_litro
        if body.rendimiento_kml is not None:
            updates["rendimiento_kml"] = body.rendimiento_kml
        if body.capacidad_tanque is not None:
            updates["capacidad_tanque"] = body.capacidad_tanque
        if body.litros_actuales is not None:
            updates["litros_actuales"] = body.litros_actuales
        if body.mostrar_pildora_combustible is not None:
            updates["mostrar_pildora_combustible"] = 1 if body.mostrar_pildora_combustible else 0
        if body.contacto_emergencia_nombre is not None:
            updates["contacto_emergencia_nombre"] = body.contacto_emergencia_nombre.strip()
        if body.contacto_emergencia_tel is not None:
            updates["contacto_emergencia_tel"] = body.contacto_emergencia_tel.strip()
        if body.frase_sos is not None and body.frase_sos.strip():
            if len(body.frase_sos.strip()) < 4:
                raise HTTPException(status_code=400, detail="La frase SOS debe tener al menos 4 caracteres.")
            updates["frase_sos_hash"] = hash_secret_phrase(user["id"], body.frase_sos)

        if updates:
            cols = ", ".join(f"{k} = ?" for k in updates.keys())
            vals = tuple(list(updates.values()) + [user["id"]])
            conn.execute(f"UPDATE usuarios SET {cols} WHERE id = ?", vals)
            conn.commit()

        fresh = conn.fetchone("SELECT * FROM usuarios WHERE id = ?", (user["id"],))
        return serialize_perfil(fresh)
    finally:
        conn.close()


# =============================================================================
# REPORTES COMUNITARIOS (EXCLUYENDO SIN_SENAL)
# =============================================================================
def _serialize_reporte(row: Dict[str, Any], lat: float, lng: float) -> Dict[str, Any]:
    dist = round(haversine_km(lat, lng, row["lat"], row["lng"]), 1)
    votos_req = 2 if row["gravedad"] == "CRITICO" else 1
    desp_req = 2
    return {
        "id": row["id"],
        "tipo": row["tipo"],
        "gravedad": row["gravedad"],
        "descripcion": row["descripcion"],
        "lat": row["lat"],
        "lng": row["lng"],
        "estado": row["estado"],
        "confirmaciones": row["confirmaciones"],
        "votos_requeridos": votos_req,
        "votos_despejar": row["votos_despejar"],
        "despejar_requeridos": desp_req,
        "distancia_km": dist,
        "created_at": row["created_at"],
    }


@app.get("/reportes")
def listar_reportes(lat: float = Query(...), lng: float = Query(...)):
    conn = get_conn()
    try:
        rows = conn.fetchall(
            """
            SELECT * FROM reportes
            WHERE activo = 1 AND expires_at > ? AND tipo != 'SIN_SENAL'
            ORDER BY id DESC LIMIT 120
            """,
            (iso_now(),),
        )
        res = []
        for r in rows:
            d = haversine_km(lat, lng, r["lat"], r["lng"])
            if d <= 90.0:
                res.append(_serialize_reporte(r, lat, lng))
        res.sort(key=lambda x: x["distancia_km"])
        return {"reportes": res[:50]}
    finally:
        conn.close()


@app.post("/reportes")
def crear_reporte(body: ReporteCreateIn, user: Dict[str, Any] = Depends(require_user)):
    check_rate_limit(f"rep:{user['id']}", max_hits=5, window_sec=180)
    check_anti_teleport(user["id"], body.lat, body.lng)

    tipo = body.tipo.strip().upper()
    if tipo not in TIPOS_REPORTE_GRAVEDAD:
        raise HTTPException(status_code=400, detail="Tipo de reporte no permitido.")

    gravedad = TIPOS_REPORTE_GRAVEDAD[tipo]
    desc = body.descripcion.strip() or f"Reporte de {tipo.replace('_', ' ').lower()}"
    estado = "PUBLICO"
    if gravedad == "CRITICO" and int(user["reputacion"]) < 3:
        estado = "EN_REVISION"

    ttl_horas = 6 if gravedad == "CRITICO" else 4
    exp = (now_utc() + timedelta(hours=ttl_horas)).isoformat()

    conn = get_conn()
    try:
        rid = conn.insert_id(
            """
            INSERT INTO reportes (usuario_id, tipo, gravedad, descripcion, lat, lng, estado, confirmaciones, created_at, expires_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, 1, ?, ?)
            """,
            (user["id"], tipo, gravedad, desc, body.lat, body.lng, estado, iso_now(), exp),
        )
        conn.execute("UPDATE usuarios SET reputacion = reputacion + 1 WHERE id = ?", (user["id"],))
        conn.commit()
        return {"id": rid, "estado": estado}
    finally:
        conn.close()


@app.post("/reportes/{reporte_id}/{accion}")
def votar_reporte(
    reporte_id: int,
    accion: str,
    body: AccionGPSIn,
    user: Dict[str, Any] = Depends(require_user),
):
    if accion not in ("votar", "confirmar", "despejar"):
        raise HTTPException(status_code=400, detail="Acción no válida.")
    check_anti_teleport(user["id"], body.lat, body.lng)

    conn = get_conn()
    try:
        rep = conn.fetchone("SELECT * FROM reportes WHERE id = ? AND activo = 1", (reporte_id,))
        if not rep:
            raise HTTPException(status_code=404, detail="Reporte no encontrado o ya despejado.")

        if not DEBUG and haversine_km(body.lat, body.lng, rep["lat"], rep["lng"]) > 25.0:
            raise HTTPException(status_code=400, detail="Debes estar cerca del tramo para validar este aviso.")

        canon = "confirmar" if accion in ("votar", "confirmar") else "despejar"
        dup = conn.fetchone(
            "SELECT id FROM reporte_votos WHERE reporte_id = ? AND usuario_id = ? AND accion = ?",
            (reporte_id, user["id"], canon),
        )
        if dup:
            raise HTTPException(status_code=400, detail="Ya registraste tu voto en este aviso.")

        conn.execute(
            "INSERT INTO reporte_votos (reporte_id, usuario_id, accion, created_at) VALUES (?, ?, ?, ?)",
            (reporte_id, user["id"], canon, iso_now()),
        )

        if canon == "confirmar":
            nuevas = int(rep["confirmaciones"]) + 1
            nuevo_estado = "PUBLICO" if nuevas >= 2 or rep["estado"] == "PUBLICO" else rep["estado"]
            nueva_exp = (now_utc() + timedelta(hours=3)).isoformat()
            conn.execute(
                "UPDATE reportes SET confirmaciones = ?, estado = ?, expires_at = ? WHERE id = ?",
                (nuevas, nuevo_estado, nueva_exp, reporte_id),
            )
            conn.commit()
            return {"ok": True, "confirmaciones": nuevas, "estado": nuevo_estado}

        nuevos_desp = int(rep["votos_despejar"]) + 1
        requeridos = 2
        despejado = nuevos_desp >= requeridos
        conn.execute(
            "UPDATE reportes SET votos_despejar = ?, activo = ? WHERE id = ?",
            (nuevos_desp, 0 if despejado else 1, reporte_id),
        )
        conn.commit()
        return {"ok": True, "despejado": despejado, "votos_despejar": nuevos_desp, "requeridos": requeridos}
    finally:
        conn.close()


# =============================================================================
# ZONAS SIN SEÑAL (100% PASIVO)
# =============================================================================
@app.post("/zonas-sin-senal")
def registrar_zona_sin_senal(body: ZonaSinSenalIn):
    if body.recuperada:
        return {"ok": True}
    conn = get_conn()
    try:
        rows = conn.fetchall("SELECT * FROM zonas_sin_senal")
        for r in rows:
            if haversine_km(body.lat, body.lng, r["lat"], r["lng"]) <= 0.8:
                conn.execute(
                    "UPDATE zonas_sin_senal SET conteo = conteo + 1, updated_at = ? WHERE id = ?",
                    (iso_now(), r["id"]),
                )
                conn.commit()
                return {"ok": True}
        conn.execute(
            "INSERT INTO zonas_sin_senal (lat, lng, radio_m, conteo, updated_at) VALUES (?, ?, 650, 1, ?)",
            (body.lat, body.lng, iso_now()),
        )
        conn.commit()
        return {"ok": True}
    finally:
        conn.close()


@app.get("/zonas-sin-senal")
def listar_zonas_sin_senal(lat: float = Query(...), lng: float = Query(...)):
    conn = get_conn()
    try:
        rows = conn.fetchall("SELECT * FROM zonas_sin_senal ORDER BY conteo DESC LIMIT 200")
        out = [
            {"id": r["id"], "lat": r["lat"], "lng": r["lng"], "radio_m": r["radio_m"], "conteo": r["conteo"]}
            for r in rows
            if haversine_km(lat, lng, r["lat"], r["lng"]) <= 120.0
        ]
        return {"zonas": out}
    finally:
        conn.close()


# =============================================================================
# BUSCADOR ANTI-MONTE, RUTAS Y SEMÁFORO DE HORARIO SEGURO (DESDE 7:30 P.M.)
# =============================================================================
def _clasificar_lugar(item: Dict[str, Any]) -> Tuple[int, str]:
    cls = (item.get("class") or item.get("category") or "").lower()
    typ = (item.get("type") or "").lower()

    if cls == "place" and typ in ("city", "town", "village", "suburb", "neighbourhood", "quarter"):
        etiquetas = {
            "city": "Ciudad",
            "town": "Cabecera / Pueblo",
            "village": "Localidad",
            "suburb": "Colonia",
            "neighbourhood": "Barrio",
            "quarter": "Zona urbana",
        }
        return (1, etiquetas.get(typ, "Localidad"))
    if cls in ("amenity", "tourism", "leisure", "shop", "aeroway", "railway", "building", "office"):
        return (2, "Punto de interés")
    if cls == "highway":
        return (3, "Vialidad / Carretera")
    if cls == "place" and typ in ("hamlet", "isolated_dwelling"):
        return (4, "Comunidad")
    if cls == "boundary" and typ == "administrative":
        return (9, "Límite municipal")
    return (5, "Ubicación")


@app.get("/buscar-lugar")
async def buscar_lugar(q: str = Query(..., min_length=2, max_length=120)):
    params = {
        "q": q,
        "format": "jsonv2",
        "countrycodes": "mx",
        "addressdetails": 1,
        "limit": 12,
        "accept-language": "es",
    }
    try:
        async with httpx.AsyncClient(timeout=10.0, headers={"User-Agent": USER_AGENT}) as client:
            r = await client.get(NOMINATIM_URL, params=params)
            r.raise_for_status()
            data = r.json()
    except Exception:
        raise HTTPException(status_code=502, detail="No se pudo consultar el buscador de direcciones.")

    ranked = []
    seen_coords = set()
    for item in data:
        try:
            lat = float(item["lat"])
            lng = float(item["lon"])
        except (KeyError, ValueError):
            continue
        key = (round(lat, 3), round(lng, 3))
        if key in seen_coords:
            continue
        seen_coords.add(key)

        prio, etiqueta = _clasificar_lugar(item)
        imp = float(item.get("importance") or 0.0)
        ranked.append(
            {
                "prio": prio,
                "imp": imp,
                "nombre": item.get("display_name", q),
                "etiqueta": etiqueta,
                "lat": lat,
                "lng": lng,
            }
        )

    ranked.sort(key=lambda x: (x["prio"], -x["imp"]))
    has_non_boundary = any(x["prio"] < 9 for x in ranked)
    filtered = [x for x in ranked if x["prio"] < 9][:6] if has_non_boundary else ranked[:6]

    return {
        "resultados": [
            {
                "nombre": x["nombre"],
                "etiqueta": x["etiqueta"],
                "lat": x["lat"],
                "lng": x["lng"],
            }
            for x in filtered
        ]
    }


def _minutos_nocturnos(inicio_local: datetime, duracion_min: int) -> int:
    """Cuenta cuántos minutos del recorrido caen entre las 19:30 y las 06:00."""
    nocturnos = 0
    paso = 5
    for m in range(0, duracion_min, paso):
        t = inicio_local + timedelta(minutes=m)
        mins_dia = t.hour * 60 + t.minute
        if mins_dia >= (19 * 60 + 30) or mins_dia < (6 * 60):
            nocturnos += min(paso, duracion_min - m)
    return nocturnos


def _evaluar_semaforo_horario(
    duracion_min: int,
    tiene_critica: bool,
    alertas_ruta: int,
    sin_senal_ruta: int,
) -> Dict[str, Any]:
    salida = datetime.now(MX_TZ)
    min_noche = _minutos_nocturnos(salida, duracion_min)
    es_noche = min_noche > 0
    es_tramo_corto = duracion_min <= 30

    puntos = 0
    if min_noche >= 90:
        puntos += 3
    elif min_noche >= 25:
        puntos += 2
    elif es_noche:
        puntos += 1

    if tiene_critica:
        puntos += 3
    elif alertas_ruta >= 2:
        puntos += 1

    if sin_senal_ruta >= 2:
        puntos += 1

    if puntos >= 4:
        color = "ROJO"
        texto = f"Alto riesgo nocturno ({min_noche} min de noche) · Se recomienda pernoctar antes de cruzar tramos solitarios."
        sugerir_pernocta = True
    elif puntos >= 2:
        color = "AMARILLO"
        texto = (
            f"Precaución · Incluye {min_noche} min en horario nocturno o avisos activos. "
            "Mantén rastreo en vivo encendido."
        )
        sugerir_pernocta = min_noche >= 60
    else:
        color = "VERDE"
        if es_noche and es_tramo_corto:
            texto = f"Tramo nocturno corto ({min_noche} min) · Sin incidentes críticos reportados."
        elif es_noche:
            texto = f"Horario mayormente seguro · Incluye {min_noche} min de noche sin incidentes críticos."
        else:
            texto = "Horario seguro · Recorrido diurno y sin incidentes críticos."
        sugerir_pernocta = False

    return {
        "semaforo_color": color,
        "semaforo_texto": texto,
        "minutos_nocturnos": min_noche,
        "sugerir_pernocta": sugerir_pernocta,
    }


def _detectar_peaje_y_costo(
    trip: Dict[str, Any],
    distancia_km: float,
    tipo_vehiculo: str,
) -> Tuple[bool, int]:
    legs = trip.get("legs") or []
    toll_km = 0.0
    has_toll = bool(trip.get("summary", {}).get("has_toll"))

    for leg in legs:
        for man in leg.get("maneuvers") or []:
            is_toll_seg = bool(man.get("toll"))
            names = " ".join(man.get("street_names") or [])
            if re.search(r"\b\d{1,3}D\b", names) or "autopista" in names.lower() or "cuota" in names.lower():
                is_toll_seg = True
            if is_toll_seg:
                has_toll = True
                toll_km += float(man.get("length") or 0.0)

    if not has_toll:
        return False, 0

    if toll_km < 5.0:
        toll_km = distancia_km * 0.6

    tarifa_km = {"auto": 2.15, "camion": 4.6, "trailer": 7.1}.get(tipo_vehiculo, 2.15)
    costo = max(45, int(round(toll_km * tarifa_km)))
    return True, costo


def _build_valhalla_payload(
    body: RutaCompararIn,
    perfil: Optional[Dict[str, Any]],
    evitar_cuotas: bool,
) -> Dict[str, Any]:
    tipo_veh = (perfil["tipo_vehiculo"] if perfil else "auto") or "auto"
    costing = "truck" if tipo_veh in ("camion", "trailer") else "auto"

    opts: Dict[str, Any] = {
        "exclude_unpaved": True,
        "use_tracks": 0.0,
        "use_living_streets": 0.0,
        "service_penalty": 60,
        "alley_factor": 5.0,
        "use_ferry": 0.0,
        "shortest": False,
    }
    if costing == "truck" and perfil:
        opts["height"] = float(perfil["altura_m"] or 4.1)
        opts["weight"] = float(perfil["peso_t"] or 18.0)

    if evitar_cuotas:
        opts["use_tolls"] = 0.0
        opts["toll_booth_penalty"] = 7200
        opts["toll_booth_cost"] = 15
        opts["use_highways"] = 0.65
    else:
        opts["use_tolls"] = 1.0
        opts["toll_booth_penalty"] = 0
        opts["toll_booth_cost"] = 15
        opts["use_highways"] = 0.92

    return {
        "locations": [
            {"lat": body.origen_lat, "lon": body.origen_lng},
            {"lat": body.destino_lat, "lon": body.destino_lng},
        ],
        "costing": costing,
        "costing_options": {costing: opts},
        "directions_options": {"units": "kilometers", "language": "es-ES"},
        "alternates": 1,
    }


def _extraer_candidatos_valhalla(data: Dict[str, Any]) -> List[Dict[str, Any]]:
    trips: List[Dict[str, Any]] = []
    if "trip" in data:
        trips.append(data["trip"])
    for alt in data.get("alternates") or []:
        if "trip" in alt:
            trips.append(alt["trip"])
    return trips


def _resumen_ruta(
    trip: Dict[str, Any],
    etiqueta_tipo: str,
    perfil: Optional[Dict[str, Any]],
    reportes: List[Dict[str, Any]],
    zonas_sin_senal: List[Dict[str, Any]],
) -> Dict[str, Any]:
    summary = trip.get("summary") or {}
    distancia_km = round(float(summary.get("length") or 0.0), 1)
    duracion_min = max(1, int(round(float(summary.get("time") or 60.0) / 60.0)))

    coords: List[List[float]] = []
    for leg in trip.get("legs") or []:
        shape = leg.get("shape")
        if shape:
            coords.extend(decode_polyline(shape, precision=6))

    tipo_veh = (perfil["tipo_vehiculo"] if perfil else "auto") or "auto"
    rendimiento = float(perfil["rendimiento_kml"]) if perfil else 12.0
    precio_litro = float(perfil["precio_litro"]) if perfil else 24.5
    litros_actuales = float(perfil["litros_actuales"]) if perfil else 40.0

    tiene_peaje, costo_casetas = _detectar_peaje_y_costo(trip, distancia_km, tipo_veh)
    litros_est = round(distancia_km / max(rendimiento, 1.0), 1)
    costo_comb = int(round(litros_est * precio_litro))
    costo_total = costo_casetas + costo_comb
    autonomia_ok = (litros_actuales * rendimiento) >= distancia_km

    step = max(1, len(coords) // 90)
    muestra = coords[::step] if coords else []

    alertas_ruta = 0
    tiene_critica = False
    for rep in reportes:
        for pt in muestra:
            if haversine_km(pt[0], pt[1], rep["lat"], rep["lng"]) <= 3.0:
                alertas_ruta += 1
                if rep["gravedad"] == "CRITICO":
                    tiene_critica = True
                break

    sin_senal_ruta = 0
    for z in zonas_sin_senal:
        for pt in muestra:
            if haversine_km(pt[0], pt[1], z["lat"], z["lng"]) <= 2.5:
                sin_senal_ruta += 1
                break

    riesgo_nivel = "ALTO" if (tiene_critica or alertas_ruta >= 3) else ("MEDIO" if alertas_ruta >= 1 else "BAJO")
    semaforo = _evaluar_semaforo_horario(duracion_min, tiene_critica, alertas_ruta, sin_senal_ruta)

    return {
        "tipo": etiqueta_tipo,
        "tiene_peaje": tiene_peaje,
        "distancia_km": distancia_km,
        "duracion_min": duracion_min,
        "costo_casetas_aprox": costo_casetas,
        "litros_estimados": litros_est,
        "costo_combustible_aprox": costo_comb,
        "costo_total_aprox": costo_total,
        "autonomia_suficiente": autonomia_ok,
        "alertas_ruta": alertas_ruta,
        "zonas_sin_senal": sin_senal_ruta,
        "riesgo_nivel": riesgo_nivel,
        "semaforo_color": semaforo["semaforo_color"],
        "semaforo_texto": semaforo["semaforo_texto"],
        "minutos_nocturnos": semaforo["minutos_nocturnos"],
        "sugerir_pernocta": semaforo["sugerir_pernocta"],
        "coords": coords,
    }


def _son_rutas_iguales(a: Dict[str, Any], b: Dict[str, Any]) -> bool:
    diff_km = abs(a["distancia_km"] - b["distancia_km"])
    diff_min = abs(a["duracion_min"] - b["duracion_min"])
    mismo_peaje = a["tiene_peaje"] == b["tiene_peaje"]
    if mismo_peaje and diff_km <= max(1.5, a["distancia_km"] * 0.05) and diff_min <= 5:
        ca, cb = a["coords"], b["coords"]
        if ca and cb:
            ma = ca[len(ca) // 2]
            mb = cb[len(cb) // 2]
            if haversine_km(ma[0], ma[1], mb[0], mb[1]) <= 2.5:
                return True
    return False


@app.post("/rutas/comparar")
async def comparar_rutas(
    body: RutaCompararIn,
    user: Optional[Dict[str, Any]] = Depends(get_optional_user),
):
    payload_cuota = _build_valhalla_payload(body, user, evitar_cuotas=False)
    payload_libre = _build_valhalla_payload(body, user, evitar_cuotas=True)

    async with httpx.AsyncClient(timeout=18.0, headers={"User-Agent": USER_AGENT}) as client:
        r_cuota = await client.post(VALHALLA_URL, json=payload_cuota)
        r_libre = await client.post(VALHALLA_URL, json=payload_libre)

    trips_cuota = _extraer_candidatos_valhalla(r_cuota.json()) if r_cuota.status_code == 200 else []
    trips_libre = _extraer_candidatos_valhalla(r_libre.json()) if r_libre.status_code == 200 else []

    if not trips_cuota and not trips_libre:
        raise HTTPException(status_code=502, detail="No se pudo calcular la ruta en este momento. Intenta de nuevo.")

    conn = get_conn()
    try:
        reportes = conn.fetchall(
            "SELECT * FROM reportes WHERE activo = 1 AND expires_at > ? AND tipo != 'SIN_SENAL'",
            (iso_now(),),
        )
        zonas = conn.fetchall("SELECT * FROM zonas_sin_senal")
    finally:
        conn.close()

    res_cuota = _resumen_ruta(trips_cuota[0], "cuota", user, reportes, zonas) if trips_cuota else None

    res_libre = None
    for cand in trips_libre + trips_cuota[1:]:
        evaluada = _resumen_ruta(cand, "libre", user, reportes, zonas)
        if not res_cuota or not _son_rutas_iguales(res_cuota, evaluada):
            res_libre = evaluada
            if not evaluada["tiene_peaje"]:
                break

    rutas: List[Dict[str, Any]] = []
    if res_cuota and res_libre:
        if not res_cuota["tiene_peaje"] and res_libre["tiene_peaje"]:
            res_cuota["tipo"] = "libre"
            res_libre["tipo"] = "cuota"
            rutas = [res_libre, res_cuota]
        else:
            if not res_cuota["tiene_peaje"]:
                res_cuota["tipo"] = "directa"
            if res_libre["tiene_peaje"]:
                res_libre["tipo"] = "alterna"
            rutas = [res_cuota, res_libre]
    elif res_cuota:
        res_cuota["tipo"] = "cuota" if res_cuota["tiene_peaje"] else "libre"
        rutas = [res_cuota]
    elif res_libre:
        res_libre["tipo"] = "cuota" if res_libre["tiene_peaje"] else "libre"
        rutas = [res_libre]

    return {"rutas": rutas}


# =============================================================================
# PARADEROS, CLIMA, LÍMITE DE VELOCIDAD Y RIESGOS PESADOS
# =============================================================================
@app.get("/paraderos")
async def listar_paraderos(
    lat: float = Query(...),
    lng: float = Query(...),
    solo_pernocta: bool = Query(default=False),
):
    items: List[Dict[str, Any]] = []
    conn = get_conn()
    try:
        rows = conn.fetchall("SELECT * FROM paraderos ORDER BY id DESC LIMIT 200")
        for r in rows:
            if solo_pernocta and r["tipo"] != "PERNOCTA":
                continue
            d = haversine_km(lat, lng, r["lat"], r["lng"])
            if d <= 80.0:
                items.append(
                    {
                        "nombre": r["nombre"],
                        "tipo": r["tipo"],
                        "lat": r["lat"],
                        "lng": r["lng"],
                        "tiene_vigilancia": bool(r["tiene_vigilancia"]),
                        "notas": r["notas"] or "",
                        "fuente": "Comunidad",
                        "dist_km": round(d, 1),
                    }
                )
    finally:
        conn.close()

    filtro = '["highway"="rest_area"]' if solo_pernocta else '["amenity"="fuel"]'
    q_overpass = (
        f"[out:json][timeout:8];"
        f"(node{filtro}(around:25000,{lat},{lng});"
        f'node["highway"="services"](around:25000,{lat},{lng}););'
        f"out body 15;"
    )
    try:
        async with httpx.AsyncClient(timeout=9.0, headers={"User-Agent": USER_AGENT}) as client:
            r = await client.post(OVERPASS_URL, data={"data": q_overpass})
            if r.status_code == 200:
                for el in (r.json().get("elements") or [])[:15]:
                    tags = el.get("tags") or {}
                    elat, elng = el.get("lat"), el.get("lon")
                    if elat is None or elng is None:
                        continue
                    items.append(
                        {
                            "nombre": tags.get("name") or ("Zona de descanso" if solo_pernocta else "Estación / Paradero"),
                            "tipo": "PERNOCTA" if tags.get("highway") in ("rest_area", "services") else "GASOLINERA",
                            "lat": elat,
                            "lng": elng,
                            "tiene_vigilancia": tags.get("lit") == "yes",
                            "notas": tags.get("brand") or "",
                            "fuente": "OpenStreetMap",
                            "dist_km": round(haversine_km(lat, lng, elat, elng), 1),
                        }
                    )
    except Exception:
        pass

    items.sort(key=lambda x: x["dist_km"])
    return {"paraderos": items[:25]}


@app.post("/paraderos/seguro")
def crear_paradero(body: ParaderoCreateIn, user: Dict[str, Any] = Depends(require_user)):
    check_anti_teleport(user["id"], body.lat, body.lng)
    tipo = body.tipo.upper() if body.tipo.upper() in ("PERNOCTA", "PARADERO", "GASOLINERA") else "PERNOCTA"
    conn = get_conn()
    try:
        pid = conn.insert_id(
            """
            INSERT INTO paraderos (usuario_id, nombre, tipo, lat, lng, tiene_vigilancia, notas, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (user["id"], body.nombre.strip(), tipo, body.lat, body.lng, 1 if body.tiene_vigilancia else 0, body.notas.strip(), iso_now()),
        )
        conn.commit()
        return {"id": pid}
    finally:
        conn.close()


@app.get("/clima")
async def obtener_clima(lat: float = Query(...), lng: float = Query(...)):
    try:
        async with httpx.AsyncClient(timeout=8.0) as client:
            r = await client.get(
                OPEN_METEO_URL,
                params={"latitude": lat, "longitude": lng, "current_weather": "true"},
            )
            r.raise_for_status()
            cw = r.json().get("current_weather") or {}
            return {
                "temp_c": cw.get("temperature"),
                "viento_kmh": cw.get("windspeed"),
                "codigo": cw.get("weathercode"),
            }
    except Exception:
        return {"temp_c": None, "viento_kmh": None, "codigo": None}


@app.get("/limite-velocidad")
async def limite_velocidad(lat: float = Query(...), lng: float = Query(...)):
    key = f"{round(lat, 3)}:{round(lng, 3)}"
    cached = _speed_cache.get(key)
    if cached and (time.time() - cached[0]) < 120:
        return {"limite_kmh": cached[1]}

    q = f'[out:json][timeout:6];way(around:60,{lat},{lng})["maxspeed"];out tags 1;'
    lim: Optional[int] = None
    try:
        async with httpx.AsyncClient(timeout=7.0, headers={"User-Agent": USER_AGENT}) as client:
            r = await client.post(OVERPASS_URL, data={"data": q})
            if r.status_code == 200:
                els = r.json().get("elements") or []
                if els:
                    raw = str((els[0].get("tags") or {}).get("maxspeed", ""))
                    m = re.search(r"\d+", raw)
                    if m:
                        lim = int(m.group(0))
    except Exception:
        pass
    _speed_cache[key] = (time.time(), lim)
    return {"limite_kmh": lim}


@app.get("/riesgos-pesados")
async def riesgos_pesados(lat: float = Query(...), lng: float = Query(...)):
    q = (
        f"[out:json][timeout:7];"
        f'(way(around:12000,{lat},{lng})["maxheight"];'
        f'way(around:12000,{lat},{lng})["incline"];);'
        f"out center 15;"
    )
    riesgos = []
    try:
        async with httpx.AsyncClient(timeout=8.0, headers={"User-Agent": USER_AGENT}) as client:
            r = await client.post(OVERPASS_URL, data={"data": q})
            if r.status_code == 200:
                for el in (r.json().get("elements") or [])[:15]:
                    c = el.get("center") or {}
                    tags = el.get("tags") or {}
                    if "lat" not in c or "lon" not in c:
                        continue
                    if "maxheight" in tags:
                        riesgos.append(
                            {
                                "tipo": "PUENTE_BAJO",
                                "lat": c["lat"],
                                "lng": c["lon"],
                                "detalle": f"Altura máxima señalada: {tags['maxheight']}",
                            }
                        )
                    elif "incline" in tags:
                        riesgos.append(
                            {
                                "tipo": "PENDIENTE",
                                "lat": c["lat"],
                                "lng": c["lon"],
                                "detalle": f"Pendiente registrada: {tags['incline']}",
                            }
                        )
    except Exception:
        pass
    return {"riesgos": riesgos}


# =============================================================================
# RADIO CB 19 Y CANALES PRIVADOS (BLINDADO)
# =============================================================================
@app.post("/cb/enviar")
def cb_enviar(body: CBEnviarIn, user: Dict[str, Any] = Depends(require_user)):
    check_rate_limit(f"cb:{user['id']}", max_hits=6, window_sec=60)
    check_anti_teleport(user["id"], body.lat, body.lng)

    try:
        raw = base64.b64decode(body.audio_b64, validate=True)
        if len(raw) > 480_000:
            raise HTTPException(status_code=400, detail="El audio excede el límite permitido (10s).")
    except HTTPException:
        raise
    except Exception:
        raise HTTPException(status_code=400, detail="Audio inválido.")

    canal_hash = hash_private_channel(body.canal_privado)
    now = time.time()
    conn = get_conn()
    try:
        conn.execute("DELETE FROM canal_cb WHERE created_at < ?", (now - 300,))
        cid = conn.insert_id(
            """
            INSERT INTO canal_cb (usuario_id, canal_hash, lat, lng, audio_b64, mime_type, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (user["id"], canal_hash, body.lat, body.lng, body.audio_b64, body.mime_type, now),
        )
        conn.commit()
        return {"ok": True, "id": cid}
    finally:
        conn.close()


@app.get("/cb/escuchar")
def cb_escuchar(
    lat: float = Query(...),
    lng: float = Query(...),
    ultimo_id: int = Query(default=0),
    canal_privado: Optional[str] = Query(default=None),
    user: Dict[str, Any] = Depends(require_user),
):
    canal_hash = hash_private_channel(canal_privado)
    radio_km = 120.0 if canal_hash.startswith("PRIV_") else 20.0
    now = time.time()

    conn = get_conn()
    try:
        rows = conn.fetchall(
            """
            SELECT id, lat, lng, audio_b64, mime_type
            FROM canal_cb
            WHERE id > ? AND canal_hash = ? AND usuario_id != ? AND created_at >= ?
            ORDER BY id ASC LIMIT 8
            """,
            (ultimo_id, canal_hash, user["id"], now - 180),
        )
        audios = []
        for r in rows:
            dist = haversine_km(lat, lng, r["lat"], r["lng"])
            if dist <= radio_km:
                audios.append(
                    {
                        "id": r["id"],
                        "distancia_km": max(1, int(round(dist))),
                        "audio_b64": r["audio_b64"],
                        "mime_type": r["mime_type"],
                    }
                )
        return {"audios": audios}
    finally:
        conn.close()


# =============================================================================
# RASTREO EN VIVO (/seguir/{codigo}), DETENCIÓN ANÓMALA Y SOS
# =============================================================================
@app.post("/rastreo/iniciar")
def rastreo_iniciar(body: RastreoIniciarIn, user: Dict[str, Any] = Depends(require_user)):
    codigo = secrets.token_urlsafe(8)
    ahora = iso_now()
    exp = (now_utc() + timedelta(hours=24)).isoformat()
    conn = get_conn()
    try:
        conn.execute("UPDATE rastreos SET activo = 0 WHERE usuario_id = ? AND activo = 1", (user["id"],))
        conn.execute(
            """
            INSERT INTO rastreos (codigo, usuario_id, destino, lat, lng, velocidad_kmh, eta_texto, sos_activo, alerta_detencion, activo, created_at, updated_at, expires_at)
            VALUES (?, ?, ?, ?, ?, 0, ?, 0, 0, 1, ?, ?, ?)
            """,
            (codigo, user["id"], body.destino.strip(), body.lat, body.lng, body.eta_texto, ahora, ahora, exp),
        )
        conn.commit()
        return {"codigo": codigo, "ruta_relativa": f"/seguir/{codigo}"}
    finally:
        conn.close()


@app.post("/rastreo/actualizar")
def rastreo_actualizar(body: RastreoActualizarIn, user: Dict[str, Any] = Depends(require_user)):
    conn = get_conn()
    try:
        conn.execute(
            """
            UPDATE rastreos
            SET lat = ?, lng = ?, velocidad_kmh = ?, eta_texto = ?, updated_at = ?
            WHERE codigo = ? AND usuario_id = ? AND activo = 1
            """,
            (body.lat, body.lng, body.velocidad_kmh, body.eta_texto, iso_now(), body.codigo, user["id"]),
        )
        conn.commit()
        return {"ok": True}
    finally:
        conn.close()


@app.post("/rastreo/alerta-detencion")
def rastreo_alerta_detencion(body: RastreoDetencionIn, user: Dict[str, Any] = Depends(require_user)):
    conn = get_conn()
    try:
        conn.execute(
            """
            UPDATE rastreos
            SET alerta_detencion = ?, lat = ?, lng = ?, updated_at = ?
            WHERE codigo = ? AND usuario_id = ? AND activo = 1
            """,
            (1 if body.activa else 0, body.lat, body.lng, iso_now(), body.codigo, user["id"]),
        )
        conn.commit()
        return {"ok": True, "alerta_detencion": body.activa}
    finally:
        conn.close()


@app.post("/rastreo/detener")
def rastreo_detener(user: Dict[str, Any] = Depends(require_user)):
    conn = get_conn()
    try:
        conn.execute("UPDATE rastreos SET activo = 0 WHERE usuario_id = ? AND activo = 1", (user["id"],))
        conn.commit()
        return {"ok": True}
    finally:
        conn.close()


def _registrar_sos_interno(user: Dict[str, Any], lat: float, lng: float, origen: str) -> None:
    conn = get_conn()
    try:
        conn.execute(
            "INSERT INTO sos_eventos (usuario_id, lat, lng, origen, created_at) VALUES (?, ?, ?, ?, ?)",
            (user["id"], lat, lng, origen, iso_now()),
        )
        conn.execute(
            "UPDATE rastreos SET sos_activo = 1, lat = ?, lng = ?, updated_at = ? WHERE usuario_id = ? AND activo = 1",
            (lat, lng, iso_now(), user["id"]),
        )
        conn.commit()
    finally:
        conn.close()


@app.post("/sos/activar")
def sos_activar(body: SOSActivarIn, user: Dict[str, Any] = Depends(require_user)):
    _registrar_sos_interno(user, body.lat, body.lng, body.origen)
    return {
        "ok": True,
        "contacto_emergencia_nombre": user["contacto_emergencia_nombre"] or "",
        "contacto_emergencia_tel": user["contacto_emergencia_tel"] or "",
    }


@app.get("/api/rastreo/{codigo}")
def api_rastreo(codigo: str):
    conn = get_conn()
    try:
        row = conn.fetchone(
            """
            SELECT r.*, u.nombre_real, u.username, u.tipo_vehiculo
            FROM rastreos r
            JOIN usuarios u ON u.id = r.usuario_id
            WHERE r.codigo = ?
            """,
            (codigo,),
        )
        if not row or not row["activo"] or row["expires_at"] < iso_now():
            raise HTTPException(status_code=404, detail="Enlace de seguimiento expirado o detenido.")
        return {
            "conductor": row["nombre_real"] or (f"@{row['username']}" if row["username"] else "Conductor"),
            "vehiculo": row["tipo_vehiculo"],
            "destino": row["destino"] or "En ruta",
            "lat": row["lat"],
            "lng": row["lng"],
            "velocidad_kmh": row["velocidad_kmh"],
            "eta_texto": row["eta_texto"],
            "sos_activo": bool(row["sos_activo"]),
            "alerta_detencion": bool(row["alerta_detencion"]),
            "updated_at": row["updated_at"],
        }
    finally:
        conn.close()


@app.get("/seguir/{codigo}", response_class=HTMLResponse)
def pagina_seguir(codigo: str):
    safe_code = re.sub(r"[^A-Za-z0-9_-]", "", codigo)
    html = f"""<!doctype html>
<html lang="es">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>Seguimiento en vivo · Copiloto Seguro MX</title>
  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" />
  <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
  <style>
    * {{ box-sizing: border-box; }}
    body {{ margin: 0; font-family: system-ui, sans-serif; background: #0b1120; color: #f8fafc; height: 100vh; display: flex; flex-direction: column; }}
    .bar {{ padding: 14px 16px; background: #111827; border-bottom: 1px solid #1e293b; display: flex; justify-content: space-between; align-items: center; gap: 12px; flex-wrap: wrap; }}
    .banner {{ display: none; padding: 12px 16px; font-weight: 800; text-align: center; letter-spacing: .02em; font-size: 13px; }}
    .banner.sos {{ background: #dc2626; color: #fff; }}
    .banner.warn {{ background: #d97706; color: #fff; }}
    .banner.on {{ display: block; }}
    #map {{ flex: 1; width: 100%; background: #0b1120; }}
    .leaflet-tile-pane {{ filter: invert(100%) hue-rotate(180deg) brightness(92%) contrast(92%) saturate(75%); }}
    .leaflet-control-attribution {{ background: rgba(15, 23, 42, 0.85) !important; color: #94a3b8 !important; }}
    .leaflet-control-attribution a {{ color: #60a5fa !important; }}
    .meta {{ font-size: 13px; color: #94a3b8; }}
  </style>
</head>
<body>
  <div id="sos" class="banner sos">ALERTA SOS ACTIVA — COMUNICARSE DE INMEDIATO CON EL CONDUCTOR O LLAMAR AL 911</div>
  <div id="detencion" class="banner warn">DETENCIÓN ANÓMALA EN CARRETERA — EL CONDUCTOR NO CONFIRMÓ RESPUESTA, VERIFICAR POR TELÉFONO</div>
  <div class="bar">
    <div>
      <strong id="nombre">Cargando seguimiento...</strong>
      <div id="destino" class="meta"></div>
    </div>
    <div style="text-align:right;">
      <strong id="vel">-- km/h</strong>
      <div id="eta" class="meta">ETA: --:--</div>
    </div>
  </div>
  <div id="map"></div>
  <script>
    const code = "{safe_code}";
    const map = L.map("map").setView([22.275, -97.862], 13);
    L.tileLayer("https://tile.openstreetmap.org/{{z}}/{{x}}/{{y}}.png", {{
      attribution: "&copy; OpenStreetMap contributors", maxZoom: 19
    }}).addTo(map);
    const mk = L.circleMarker([22.275, -97.862], {{ radius: 9, color: "#fff", weight: 3, fillColor: "#3b82f6", fillOpacity: 1 }}).addTo(map);
    let first = true;
    async function poll() {{
      try {{
        const r = await fetch(`/api/rastreo/${{code}}`);
        if (!r.ok) {{
          document.getElementById("nombre").textContent = "Seguimiento finalizado o expirado";
          return;
        }}
        const d = await r.json();
        document.getElementById("nombre").textContent = d.conductor;
        document.getElementById("destino").textContent = `Destino: ${{d.destino}}`;
        document.getElementById("vel").textContent = `${{d.velocidad_kmh}} km/h`;
        document.getElementById("eta").textContent = `ETA: ${{d.eta_texto}}`;
        document.getElementById("sos").classList.toggle("on", !!d.sos_activo);
        document.getElementById("detencion").classList.toggle("on", !d.sos_activo && !!d.alerta_detencion);
        mk.setLatLng([d.lat, d.lng]);
        if (first) {{ map.setView([d.lat, d.lng], 14); first = false; }}
      }} catch (_) {{}}
    }}
    poll();
    setInterval(poll, 8000);
  </script>
</body>
</html>"""
    return HTMLResponse(html)


# =============================================================================
# MENSAJES, SUGERENCIAS Y ATENCIÓN AL CLIENTE
# =============================================================================
@app.post("/soporte/mensaje")
async def enviar_mensaje_soporte(
    body: SoporteMensajeIn,
    request: Request,
    user: Optional[Dict[str, Any]] = Depends(get_optional_user),
):
    client_key = f"soporte:{user['id']}" if user else f"soporte_ip:{request.client.host if request.client else 'anon'}"
    check_rate_limit(client_key, max_hits=3, window_sec=300)

    cat = body.categoria.strip().upper()
    if cat not in ("SUGERENCIA", "FALLA_TECNICA", "SOPORTE", "NEGOCIOS", "OTRO"):
        cat = "SUGERENCIA"

    correo_rem = (body.correo_contacto or "").strip()
    if not correo_rem and user:
        correo_rem = user.get("email") or ""

    usuario_txt = f"@{user['username']} ({user['email']})" if user and user.get("username") else (
        user["email"] if user else (correo_rem or "Visitante sin correo")
    )

    cuerpo_correo = (
        f"Nuevo mensaje recibido desde Copiloto Seguro MX ({APP_VERSION})\n"
        f"------------------------------------------------------------\n"
        f"Categoría: {cat}\n"
        f"Remitente: {usuario_txt}\n"
        f"Correo de respuesta: {correo_rem or 'No proporcionado'}\n"
        f"Asunto: {body.asunto.strip()}\n"
        f"Fecha (UTC): {iso_now()}\n"
        f"------------------------------------------------------------\n\n"
        f"{body.mensaje.strip()}\n"
    )

    enviado = await asyncio.to_thread(_enviar_correo_sync, cat, body.asunto.strip(), cuerpo_correo, correo_rem)

    conn = get_conn()
    try:
        mid = conn.insert_id(
            """
            INSERT INTO mensajes_soporte (usuario_id, correo_remitente, categoria, asunto, mensaje, enviado_correo, created_at)
            VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (
                user["id"] if user else None,
                correo_rem,
                cat,
                body.asunto.strip(),
                body.mensaje.strip(),
                1 if enviado else 0,
                iso_now(),
            ),
        )
        conn.commit()
        return {
            "ok": True,
            "id": mid,
            "enviado_correo": enviado,
            "destino": SUPPORT_EMAIL,
        }
    finally:
        conn.close()


# =============================================================================
# COPILOTO IA, ANTI-SUEÑO Y VOZ NEURONAL (12 VOCES MX + VELOCIDAD + TONO)
# =============================================================================
async def _llamar_gemini(system_prompt: str, user_prompt: str) -> str:
    if not GEMINI_API_KEY:
        return ""
    url = f"https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-flash:generateContent?key={GEMINI_API_KEY}"
    payload = {
        "system_instruction": {"parts": [{"text": system_prompt}]},
        "contents": [{"role": "user", "parts": [{"text": user_prompt}]}],
        "generationConfig": {"temperature": 0.5, "maxOutputTokens": 260},
    }
    try:
        async with httpx.AsyncClient(timeout=15.0) as client:
            r = await client.post(url, json=payload)
            if r.status_code != 200:
                return ""
            data = r.json()
            cands = data.get("candidates") or []
            if not cands:
                return ""
            parts = cands[0].get("content", {}).get("parts") or []
            return "".join(p.get("text", "") for p in parts).strip()
    except Exception:
        return ""


@app.post("/agente")
async def agente_copiloto(
    body: AgenteIn,
    user: Optional[Dict[str, Any]] = Depends(get_optional_user),
):
    msg = body.mensaje.strip()

    if user and user["frase_sos_hash"]:
        if hmac.compare_digest(hash_secret_phrase(user["id"], msg), user["frase_sos_hash"]):
            _registrar_sos_interno(user, body.lat, body.lng, "ENCUBIERTO")
            return {
                "respuesta": "Recibido. El clima en el tramo se mantiene despejado y sin novedad en el tránsito.",
                "accion": None,
            }

    low = msg.lower()
    accion = None

    if any(k in low for k in ("pernocta", "dormir", "descansar", "paradero", "gasolinera")):
        solo_p = any(k in low for k in ("pernocta", "dormir", "descansar"))
        accion = {"tipo_accion": "BUSCAR_PARADERO", "parametro": {"solo_pernocta": solo_p}}

    sys_prompt = (
        "Eres el Copiloto de carretera de Copiloto Seguro MX para conductores en México. "
        "Responde en español de México, breve (máximo 3 frases), claro, directo y seguro para ir escuchando al volante. "
        "No uses emojis ni listas largas."
    )
    ctx = f"Ubicación aprox: {body.lat:.4f}, {body.lng:.4f}. Destino actual: {body.destino_actual or 'ninguno'}. Mensaje del conductor: {msg}"
    resp = await _llamar_gemini(sys_prompt, ctx)

    if not resp:
        if accion:
            resp = "Buscando zonas de descanso y paraderos cercanos sobre tu mapa ahora mismo."
        else:
            resp = "No pude conectar con el servicio de inteligencia en este momento. Verifica tu conexión o clave de API."

    return {"respuesta": resp, "accion": accion}


@app.post("/antisuenio")
async def antisuenio():
    sys_prompt = (
        "Eres un copiloto mexicano ayudando a un conductor a mantenerse despierto en carretera nocturna. "
        "Haz una pregunta corta e interesante de cultura general mexicana o un reto mental breve, y recuérdale descansar si siente pesadez en los ojos. "
        "Máximo 3 frases, sin emojis."
    )
    texto = await _llamar_gemini(sys_prompt, "Dame una pregunta breve para mantenerme despierto manejando.")
    if not texto:
        texto = (
            "Pregunta rápida para despejar la mente: si manejas a noventa kilómetros por hora, "
            "¿cuántos kilómetros recorres en cuarenta minutos? Si sientes los párpados pesados, "
            "busca el próximo paradero iluminado y estira las piernas diez minutos."
        )
    return {"texto": texto}


@app.get("/tts/voces")
def listar_voces():
    return {"voces": VOCES_MX}


@app.post("/tts")
async def generar_tts(body: TTSIn):
    voz = body.voz if body.voz in VOCES_MX_IDS else "es-MX-DaliaNeural"
    rate_str = f"{body.velocidad:+d}%"
    pitch_str = f"{body.tono:+d}Hz"

    async def audio_stream():
        comm = edge_tts.Communicate(
            text=body.texto,
            voice=voz,
            rate=rate_str,
            pitch=pitch_str,
        )
        async for chunk in comm.stream():
            if chunk["type"] == "audio":
                yield chunk["data"]

    return StreamingResponse(audio_stream(), media_type="audio/mpeg")