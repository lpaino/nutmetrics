# =============================================================================
# NutMetrics - Versão 1.0
# Data: 01/10/2026
# Desenvolvido por: Leandro Dabrins Paino   
# Sistem criado para monitoramento de clusters Nutanix,
# com autenticação segura, auditoria e gestão de utilizadores.    
# =============================================================================
# NutMetrics — versão com correções de segurança
# Variáveis de ambiente opcionais:
#   NUTMETRICS_KEY                  chave Fernet (recomendado em produção)
#   NUTMETRICS_REQUIRE_ENV_KEY=1    recusa iniciar sem NUTMETRICS_KEY
#   NUTMETRICS_ADMIN_PASSWORD       senha inicial do Admin (senão é gerada)
#   NUTMETRICS_ALLOWED_NETWORKS     CIDRs permitidos p/ clusters (ex: 10.0.0.0/8,192.168.0.0/16)
#   NUTMETRICS_SESSION_TIMEOUT_MIN  inatividade máxima (padrão 15)
#   NUTMETRICS_SESSION_MAX_HOURS    duração máxima da sessão (padrão 8)
#   NUTMETRICS_DB / NUTMETRICS_LOG / NUTMETRICS_KEY_FILE  caminhos dos arquivos
# =============================================================================
import streamlit as st
import pandas as pd
import numpy as np
import altair as alt
import sqlite3
import hashlib
import hmac
import secrets
import string
import re
import os
import ssl
import json
import sys
import socket
import ipaddress
import logging
import time
import math
import threading
import requests
from requests.adapters import HTTPAdapter
from datetime import datetime
from cryptography.fernet import Fernet

# Configuração da Página
st.set_page_config(page_title="NutMetrics", layout="wide", initial_sidebar_state="expanded")

# ==========================================
# CONFIGURAÇÃO
# ==========================================
def _env_int(name, default):
    try:
        return int(os.environ.get(name, default))
    except ValueError:
        return default

DB_PATH = os.environ.get("NUTMETRICS_DB", "nutmetrics.db")
KEY_FILE = os.environ.get("NUTMETRICS_KEY_FILE", "nutmetrics.key")
LOG_FILE = os.environ.get("NUTMETRICS_LOG", "nutmetrics.log")
ADMIN_PASS_FILE = "ADMIN_INITIAL_PASSWORD.txt"
# True = seta de recolher o menu lateral ativa; False = menu fixo (sem seta)
SIDEBAR_COLLAPSIBLE = True

SESSION_IDLE_MIN = _env_int("NUTMETRICS_SESSION_TIMEOUT_MIN", 15)
SESSION_MAX_HOURS = _env_int("NUTMETRICS_SESSION_MAX_HOURS", 8)
MAX_FAILED_LOGINS = 5
LOCKOUT_MINUTES = 15
PBKDF2_ITERATIONS = 600_000
MIN_PASSWORD_LEN = 12
ROLES = ("Usuário", "Administrador")
DENIED_MSG = "Acesso negado: requer perfil de Administrador."

# Log técnico (detalhes de erro ficam aqui, nunca na tela)
logger = logging.getLogger("nutmetrics")
if not logger.handlers:
    logger.setLevel(logging.INFO)
    try:
        _handler = logging.FileHandler(LOG_FILE, encoding="utf-8")
        try:
            os.chmod(LOG_FILE, 0o600)
        except OSError:
            pass
    except OSError:
        _handler = logging.StreamHandler()
    _handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    logger.addHandler(_handler)
    logger.propagate = False

def _clean(text, limit=200):
    """Remove caracteres de controle (evita injeção de linhas falsas no log) e limita o tamanho."""
    return re.sub(r"[\x00-\x1f\x7f]", " ", str(text))[:limit]

def _md(text):
    """Escapa Markdown em textos vindos de usuários/APIs externas."""
    return re.sub(r"([\\`*_{}\[\]()#+\-.!|<>~$&])", r"\\\1", str(text))

# ==========================================
# BANCO DE DADOS (helpers)
# ==========================================
def db():
    return sqlite3.connect(DB_PATH, timeout=10)

def _q(sql, params=(), one=False):
    conn = db()
    try:
        cur = conn.execute(sql, params)
        return cur.fetchone() if one else cur.fetchall()
    finally:
        conn.close()

def _x(sql, params=()):
    conn = db()
    try:
        conn.execute(sql, params)
        conn.commit()
    finally:
        conn.close()

# ==========================================
# CRIPTOGRAFIA DAS CREDENCIAIS DOS CLUSTERS
# ==========================================
def key_is_from_env():
    return bool(os.environ.get("NUTMETRICS_KEY"))

@st.cache_resource
def _get_fernet():
    """Chave via NUTMETRICS_KEY (recomendado). Sem ela, usa arquivo local com permissão 600."""
    key = os.environ.get("NUTMETRICS_KEY")
    if not key:
        if os.environ.get("NUTMETRICS_REQUIRE_ENV_KEY") == "1":
            raise RuntimeError("NUTMETRICS_KEY não definida e NUTMETRICS_REQUIRE_ENV_KEY=1.")
        if not os.path.exists(KEY_FILE):
            try:
                fd = os.open(KEY_FILE, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                with os.fdopen(fd, "wb") as f:
                    f.write(Fernet.generate_key())
            except FileExistsError:
                pass
        with open(KEY_FILE, "rb") as f:
            key = f.read().strip()
    return Fernet(key)

def encrypt_secret(text):
    return _get_fernet().encrypt(text.encode()).decode()

def decrypt_secret(token):
    try:
        return _get_fernet().decrypt(token.encode()).decode()
    except Exception:
        return None

# ==========================================
# SENHAS: HASH SEGURO E POLÍTICA
# ==========================================
def hash_password(password, iterations=PBKDF2_ITERATIONS):
    """PBKDF2-HMAC-SHA256 com salt aleatório por utilizador."""
    salt = secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, iterations)
    return f"pbkdf2_sha256${iterations}${salt.hex()}${dk.hex()}"

def _is_legacy_hash(stored):
    return bool(re.fullmatch(r"[0-9a-f]{64}", stored or ""))

def check_password(password, stored):
    """Retorna (senha_correta, precisa_rehash). Aceita o formato antigo (SHA-256 puro) para migração."""
    if not stored:
        return False, False
    if _is_legacy_hash(stored):
        ok = hmac.compare_digest(hashlib.sha256(password.encode()).hexdigest(), stored)
        return ok, ok
    try:
        algo, iterations, salt, expected = stored.split("$")
        if algo != "pbkdf2_sha256":
            return False, False
        iterations = int(iterations)
        dk = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt), iterations)
        ok = hmac.compare_digest(dk.hex(), expected)
        return ok, ok and iterations < PBKDF2_ITERATIONS
    except Exception:
        return False, False

@st.cache_resource
def _dummy_hash():
    """Hash falso usado para gastar o mesmo tempo quando o utilizador não existe."""
    return hash_password(secrets.token_urlsafe(12))

COMMON_PASSWORDS = {
    "mudar@123", "password", "password1", "password123", "password@123", "senha123", "senha@123",
    "admin", "admin123", "admin@123", "qwerty123", "qwerty@123", "12345678", "123456789",
    "1234567890", "letmein", "welcome1", "welcome@123", "nutanix", "nutanix/4u", "nutanix@123",
    "changeme", "changeme123", "p@ssw0rd", "p@ssword", "passw0rd",
}

def validate_password_policy(password, username=None, current_password=None):
    if not password or len(password) < MIN_PASSWORD_LEN:
        return False, f"A palavra-passe deve ter no mínimo {MIN_PASSWORD_LEN} caracteres."
    if (not re.search(r"[A-Z]", password) or not re.search(r"[a-z]", password)
            or not re.search(r"[0-9]", password) or not re.search(r"[!@#$%^&*(),.?\":{}|<>]", password)):
        return False, "A palavra-passe deve incluir maiúsculas, minúsculas, números e símbolos."
    low = password.lower()
    if low in COMMON_PASSWORDS or any(c in low for c in COMMON_PASSWORDS if len(c) >= 8):
        return False, "Esta palavra-passe é muito comum ou contém uma palavra-passe conhecida. Escolha outra."
    if username and len(username) >= 3 and username.lower() in low:
        return False, "A palavra-passe não pode conter o nome de utilizador."
    if current_password and password == current_password:
        return False, "A nova palavra-passe deve ser diferente da atual."
    return True, ""

def generate_password(length=16):
    alphabet = string.ascii_letters + string.digits + "!@#$%&*?"
    while True:
        candidate = "".join(secrets.choice(alphabet) for _ in range(length))
        if validate_password_policy(candidate)[0]:
            return candidate

# ==========================================
# INICIALIZAÇÃO DO BANCO / MIGRAÇÃO
# ==========================================
def _write_initial_admin_file(password):
    try:
        fd = os.open(ADMIN_PASS_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write("Utilizador: Admin\n"
                    f"Palavra-passe inicial: {password}\n"
                    "A troca é obrigatória no primeiro login. O arquivo é apagado após a troca.\n")
        logger.warning("Utilizador Admin criado. Palavra-passe inicial gravada em %s.", ADMIN_PASS_FILE)
    except OSError:
        # Último recurso: sem isto a conta ficaria inacessível.
        print(f"[NutMetrics] Admin criado. Palavra-passe inicial: {password}", file=sys.stderr)

def init_db():
    conn = db()
    cursor = conn.cursor()

    cursor.execute("PRAGMA table_info(users)")
    user_cols = [col[1] for col in cursor.fetchall()]
    if user_cols and "full_name" not in user_cols:
        cursor.execute("DROP TABLE IF EXISTS users")

    cursor.execute('''
        CREATE TABLE IF NOT EXISTS users (
            username TEXT PRIMARY KEY,
            full_name TEXT NOT NULL,
            password TEXT NOT NULL,
            role TEXT NOT NULL,
            must_change INTEGER NOT NULL DEFAULT 0
        )
    ''')
    cursor.execute("PRAGMA table_info(users)")
    if "must_change" not in [col[1] for col in cursor.fetchall()]:
        cursor.execute("ALTER TABLE users ADD COLUMN must_change INTEGER NOT NULL DEFAULT 0")

    cursor.execute("PRAGMA table_info(clusters)")
    cluster_cols = [col[1] for col in cursor.fetchall()]
    if cluster_cols and ("cluster_type" not in cluster_cols or "port" not in cluster_cols or "prism_central_ip" not in cluster_cols):
        cursor.execute("DROP TABLE IF EXISTS clusters")

    cursor.execute('''
        CREATE TABLE IF NOT EXISTS clusters (
            cluster_name TEXT PRIMARY KEY,
            cluster_type TEXT,
            ip_address TEXT NOT NULL,
            port TEXT NOT NULL,
            status TEXT NOT NULL,
            prism_central_ip TEXT
        )
    ''')
    cursor.execute("PRAGMA table_info(clusters)")
    cols_now = [col[1] for col in cursor.fetchall()]
    # element_*: acesso DIRETO ao Prism Element de um cluster gerenciado por Prism Central (usado pelo Storage)
    for col in ("api_user", "api_pass_enc", "cluster_uuid", "cert_fingerprint",
                "element_ip", "element_port", "element_user", "element_pass_enc", "element_fingerprint"):
        if col not in cols_now:
            cursor.execute(f"ALTER TABLE clusters ADD COLUMN {col} TEXT")

    cursor.execute('''
        CREATE TABLE IF NOT EXISTS hosts (
            host_name TEXT PRIMARY KEY,
            cluster_name TEXT NOT NULL,
            ip_address TEXT NOT NULL,
            FOREIGN KEY (cluster_name) REFERENCES clusters (cluster_name) ON DELETE CASCADE
        )
    ''')
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS audit_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ts REAL NOT NULL,
            username TEXT,
            action TEXT NOT NULL,
            detail TEXT,
            ip TEXT
        )
    ''')
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS usage_history (
            cluster_name TEXT NOT NULL,
            ts REAL NOT NULL,
            cpu_total REAL,
            cpu_used REAL,
            mem_total REAL,
            mem_used REAL
        )
    ''')
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_usage_cluster_ts ON usage_history (cluster_name, ts)")
    # Histórico por host (mesma coleta de 5 min do cluster); as colunas vêm de HOST_HIST_COLS
    cursor.execute("CREATE TABLE IF NOT EXISTS host_usage_history (cluster_name TEXT NOT NULL, host_name TEXT NOT NULL, "
                   "ts REAL NOT NULL, " + ", ".join(f"{c} REAL" for c in HOST_HIST_COLS) + ")")
    cursor.execute("PRAGMA table_info(host_usage_history)")
    _host_cols_now = [col[1] for col in cursor.fetchall()]
    for _c in HOST_HIST_COLS:                       # permite acrescentar métricas no futuro sem recriar o banco
        if _c not in _host_cols_now:
            cursor.execute(f"ALTER TABLE host_usage_history ADD COLUMN {_c} REAL")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_host_usage ON host_usage_history (cluster_name, host_name, ts)")
    # Histórico de storage (pool / container / virtual disk / disco físico) + lista de recursos para os dropdowns
    cursor.execute("CREATE TABLE IF NOT EXISTS storage_usage_history (cluster_name TEXT NOT NULL, entity_type TEXT NOT NULL, "
                   "entity_id TEXT NOT NULL, ts REAL NOT NULL, " + ", ".join(f"{c} REAL" for c in STORAGE_COLS) + ")")
    cursor.execute("PRAGMA table_info(storage_usage_history)")
    _stor_cols_now = [col[1] for col in cursor.fetchall()]
    for _c in STORAGE_COLS:
        if _c not in _stor_cols_now:
            cursor.execute(f"ALTER TABLE storage_usage_history ADD COLUMN {_c} REAL")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_storage_usage ON storage_usage_history (cluster_name, entity_type, entity_id, ts)")
    # VMs (capacity / right-sizing): histórico por VM + cadastro com nome e host atuais
    cursor.execute("CREATE TABLE IF NOT EXISTS vm_usage_history (cluster_name TEXT NOT NULL, vm_uuid TEXT NOT NULL, "
                   "ts REAL NOT NULL, " + ", ".join(f"{c} REAL" for c in VM_COLS) + ")")
    cursor.execute("PRAGMA table_info(vm_usage_history)")
    _vm_cols_now = [col[1] for col in cursor.fetchall()]
    for _c in VM_COLS:
        if _c not in _vm_cols_now:
            cursor.execute(f"ALTER TABLE vm_usage_history ADD COLUMN {_c} REAL")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_vm_usage ON vm_usage_history (cluster_name, vm_uuid, ts)")
    cursor.execute("CREATE INDEX IF NOT EXISTS idx_vm_usage_ts ON vm_usage_history (ts)")
    cursor.execute("CREATE TABLE IF NOT EXISTS vm_entities (cluster_name TEXT NOT NULL, vm_uuid TEXT NOT NULL, vm_name TEXT, "
                   "host_uuid TEXT, host_name TEXT, last_seen REAL NOT NULL, PRIMARY KEY (cluster_name, vm_uuid))")
    cursor.execute("CREATE TABLE IF NOT EXISTS storage_entities (cluster_name TEXT NOT NULL, entity_type TEXT NOT NULL, "
                   "entity_id TEXT NOT NULL, entity_name TEXT, info TEXT, last_seen REAL NOT NULL, "
                   "PRIMARY KEY (cluster_name, entity_type, entity_id))")
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS login_failures (
            username TEXT NOT NULL,
            ts REAL NOT NULL
        )
    ''')

    # Utilizador Admin: senha aleatória na primeira execução (nunca mais uma senha fixa no código)
    cursor.execute("SELECT password FROM users WHERE username = 'Admin'")
    row = cursor.fetchone()
    created_password = None
    if row is None:
        env_pass = os.environ.get("NUTMETRICS_ADMIN_PASSWORD")
        created_password = env_pass or generate_password()
        cursor.execute(
            "INSERT INTO users (username, full_name, password, role, must_change) VALUES (?, ?, ?, ?, 1)",
            ("Admin", "Administrador Principal", hash_password(created_password), "Administrador"))
        if env_pass:
            created_password = None
    elif row[0] == hashlib.sha256("Mudar@123".encode()).hexdigest():
        # Instalação antiga ainda com a senha padrão conhecida: força a troca
        cursor.execute("UPDATE users SET must_change = 1 WHERE username = 'Admin'")

    conn.commit()
    conn.close()

    if created_password:
        _write_initial_admin_file(created_password)
    try:
        os.chmod(DB_PATH, 0o600)
    except OSError:
        pass

# ==========================================
# AUDITORIA
# ==========================================
def get_client_ip():
    """IP de origem. Só é confiável atrás de um proxy reverso que defina X-Forwarded-For."""
    try:
        headers = st.context.headers
        forwarded = headers.get("X-Forwarded-For") or headers.get("X-Real-Ip")
        if forwarded:
            return _clean(forwarded.split(",")[0].strip(), 64)
    except Exception:
        pass
    return "-"

def audit(action, detail="", username=None):
    try:
        who = username if username is not None else (st.session_state.get("username") or "-")
        _x("INSERT INTO audit_log (ts, username, action, detail, ip) VALUES (?, ?, ?, ?, ?)",
           (time.time(), _clean(who, 64), action, _clean(detail, 500), get_client_ip()))
        logger.info("AUDIT user=%s action=%s detail=%s", _clean(who, 64), action, _clean(detail, 200))
    except Exception:
        logger.exception("Falha ao gravar auditoria")

def get_audit_log(limit=200):
    if not current_user_is_admin():
        return []
    return _q("SELECT ts, username, action, detail, ip FROM audit_log ORDER BY id DESC LIMIT ?", (limit,))

# ==========================================
# AUTORIZAÇÃO (verificada no banco, não só na sessão)
# ==========================================
def current_user_is_admin():
    if not st.session_state.get("logged_in"):
        return False
    row = _q("SELECT role FROM users WHERE username = ?", (st.session_state.get("username"),), one=True)
    return bool(row and row[0] == "Administrador")

def _require_admin(what=""):
    if current_user_is_admin():
        return True
    audit("ACESSO_NEGADO", what)
    return False

def _admin_count():
    return _q("SELECT COUNT(*) FROM users WHERE role = 'Administrador'", one=True)[0]

# ==========================================
# LOGIN: BLOQUEIO POR TENTATIVAS E AUTENTICAÇÃO
# ==========================================
def _fail_key(username):
    return (username or "").strip().lower()[:64]

def _lock_remaining_minutes(key):
    now = time.time()
    _x("DELETE FROM login_failures WHERE ts < ?", (now - 86400,))
    row = _q("SELECT COUNT(*), MAX(ts) FROM login_failures WHERE username = ? AND ts > ?",
             (key, now - LOCKOUT_MINUTES * 60), one=True)
    if row and row[0] >= MAX_FAILED_LOGINS and row[1]:
        remaining = row[1] + LOCKOUT_MINUTES * 60 - now
        if remaining > 0:
            return max(1, math.ceil(remaining / 60))
    return 0

def _register_failure(key):
    _x("INSERT INTO login_failures (username, ts) VALUES (?, ?)", (key, time.time()))

def _clear_failures(key):
    _x("DELETE FROM login_failures WHERE username = ?", (key,))

def authenticate(username, password):
    """Retorna (status, dados). status: 'ok' | 'invalid' | 'locked'."""
    username = (username or "").strip()
    if not username or not password:
        return "invalid", None
    key = _fail_key(username)

    minutes = _lock_remaining_minutes(key)
    if minutes:
        audit("LOGIN_BLOQUEADO", f"tentativa durante bloqueio ({minutes} min restantes)", username=username)
        return "locked", minutes

    row = _q("SELECT password, role, full_name, must_change FROM users WHERE username = ?", (username,), one=True)
    if row is None:
        check_password(password, _dummy_hash())   # mesmo custo de tempo: não revela se o utilizador existe
        ok = False
    else:
        ok, needs_rehash = check_password(password, row[0])
        if ok and needs_rehash:
            _x("UPDATE users SET password = ? WHERE username = ?", (hash_password(password), username))

    if ok:
        _clear_failures(key)
        return "ok", {"role": row[1], "full_name": row[2], "must_change": bool(row[3])}

    _register_failure(key)
    audit("LOGIN_FALHA", "credenciais inválidas", username=username)
    time.sleep(1)
    return "invalid", None

# ==========================================
# GESTÃO DE UTILIZADORES (todas exigem Administrador, exceto a própria senha)
# ==========================================
USERNAME_RE = re.compile(r"^[A-Za-z0-9_.\-]{3,32}$")

def register_user(username, full_name, password, role):
    if not _require_admin("register_user"):
        return False, DENIED_MSG
    username = (username or "").strip()
    full_name = (full_name or "").strip()
    if not USERNAME_RE.match(username):
        return False, "O identificador deve ter 3 a 32 caracteres (letras, números, ponto, hífen ou underscore)."
    if not (1 <= len(full_name) <= 80):
        return False, "O nome a exibir deve ter entre 1 e 80 caracteres."
    if role not in ROLES:
        return False, "Perfil inválido."
    if _q("SELECT 1 FROM users WHERE username = ?", (username,), one=True):
        return False, "O nome de utilizador já existe!"
    ok, msg = validate_password_policy(password, username=username)
    if not ok:
        return False, msg
    _x("INSERT INTO users (username, full_name, password, role, must_change) VALUES (?, ?, ?, ?, 1)",
       (username, full_name, hash_password(password), role))
    audit("USUARIO_CRIADO", f"{username} perfil={role}")
    return True, "Utilizador cadastrado com sucesso! Ele terá de trocar a palavra-passe no primeiro acesso."

def update_user_info(username, new_full_name, new_role, new_password=None, unlock=False):
    if not _require_admin("update_user_info"):
        return False, DENIED_MSG
    new_full_name = (new_full_name or "").strip()
    if not (1 <= len(new_full_name) <= 80):
        return False, "O nome a exibir deve ter entre 1 e 80 caracteres."
    if new_role not in ROLES:
        return False, "Perfil inválido."
    target = _q("SELECT role FROM users WHERE username = ?", (username,), one=True)
    if not target:
        return False, "Utilizador não encontrado."
    if target[0] == "Administrador" and new_role != "Administrador" and _admin_count() <= 1:
        return False, "Não é possível remover o perfil do último Administrador."

    if new_password:
        ok, msg = validate_password_policy(new_password, username=username)
        if not ok:
            return False, msg
        _x("UPDATE users SET full_name = ?, role = ?, password = ?, must_change = 1 WHERE username = ?",
           (new_full_name, new_role, hash_password(new_password), username))
        _clear_failures(_fail_key(username))
    else:
        _x("UPDATE users SET full_name = ?, role = ? WHERE username = ?", (new_full_name, new_role, username))
    if unlock:
        _clear_failures(_fail_key(username))
    audit("USUARIO_ALTERADO", f"{username} perfil={new_role} senha_redefinida={bool(new_password)} desbloqueado={unlock}")
    return True, "Utilizador atualizado com sucesso!"

def delete_user(username, current_logged_user):
    if not _require_admin("delete_user"):
        return False, DENIED_MSG
    if username == current_logged_user:
        return False, "Não pode excluir a sua própria conta enquanto estiver logado."
    target = _q("SELECT role FROM users WHERE username = ?", (username,), one=True)
    if not target:
        return False, "Utilizador não encontrado."
    if target[0] == "Administrador" and _admin_count() <= 1:
        return False, "Não é possível excluir o último Administrador."
    _x("DELETE FROM users WHERE username = ?", (username,))
    _clear_failures(_fail_key(username))
    audit("USUARIO_EXCLUIDO", username)
    return True, f"Utilizador '{username}' excluído com sucesso!"

def update_own_password(username, current_password, new_password):
    if not st.session_state.get("logged_in") or st.session_state.get("username") != username:
        return False, "Operação não permitida."
    key = _fail_key(username)
    minutes = _lock_remaining_minutes(key)
    if minutes:
        return False, f"Muitas tentativas incorretas. Tente novamente em {minutes} min."

    row = _q("SELECT password FROM users WHERE username = ?", (username,), one=True)
    if not (row and check_password(current_password, row[0])[0]):
        _register_failure(key)
        audit("SENHA_ALTERACAO_FALHA", "palavra-passe atual incorreta")
        time.sleep(1)
        return False, "A palavra-passe atual está incorreta."

    ok, msg = validate_password_policy(new_password, username=username, current_password=current_password)
    if not ok:
        return False, msg
    _x("UPDATE users SET password = ?, must_change = 0 WHERE username = ?", (hash_password(new_password), username))
    _clear_failures(key)
    audit("SENHA_ALTERADA", "o próprio utilizador")
    if username == "Admin":
        try:
            os.remove(ADMIN_PASS_FILE)
        except OSError:
            pass
    return True, "Palavra-passe alterada com sucesso!"

def get_all_users():
    if not current_user_is_admin():
        return []
    return _q("SELECT username, full_name, role FROM users")

# ==========================================
# REDE: VALIDAÇÃO DE DESTINO (anti-SSRF) E CERTIFICADO FIXADO (pinning)
# ==========================================
HOST_RE = re.compile(r"^[A-Za-z0-9.\-:\[\]]{1,253}$")

def _allowed_networks():
    nets = []
    for part in os.environ.get("NUTMETRICS_ALLOWED_NETWORKS", "").split(","):
        part = part.strip()
        if part:
            try:
                nets.append(ipaddress.ip_network(part, strict=False))
            except ValueError:
                logger.error("NUTMETRICS_ALLOWED_NETWORKS contém rede inválida: %s", _clean(part, 50))
    return nets

def _ip_is_forbidden(ip):
    if ip.version == 6 and ip.ipv4_mapped:
        ip = ip.ipv4_mapped
    if ip.version == 4 and ip.packed[0] == 0:        # 0.0.0.0/8
        return True
    return ip.is_loopback or ip.is_link_local or ip.is_multicast or ip.is_unspecified or ip.is_reserved

def validate_cluster_target(host, port):
    """Impede que o servidor seja usado para alcançar loopback, metadados de nuvem (169.254.x.x), etc."""
    host = (host or "").strip()
    if not HOST_RE.match(host):
        return False, "Endereço inválido. Use um IP ou hostname."
    try:
        port_i = int(str(port).strip())
    except ValueError:
        return False, "Porta inválida."
    if not 1 <= port_i <= 65535:
        return False, "Porta inválida (use 1 a 65535)."

    try:
        addrs = [ipaddress.ip_address(host.strip("[]"))]
    except ValueError:
        if ":" in host or "[" in host or "]" in host:
            return False, "Endereço inválido."
        try:
            infos = socket.getaddrinfo(host, port_i, proto=socket.IPPROTO_TCP)
        except socket.gaierror:
            return False, "Não foi possível resolver o hostname informado."
        addrs = list({ipaddress.ip_address(i[4][0]) for i in infos})

    allowed = _allowed_networks()
    for a in addrs:
        if _ip_is_forbidden(a):
            return False, "Destino não permitido (loopback, link-local, multicast ou reservado)."
        if allowed and not any(a in n for n in allowed):
            return False, "Destino fora das redes permitidas pela configuração (NUTMETRICS_ALLOWED_NETWORKS)."
    return True, ""

def normalize_fingerprint(fp):
    fp = re.sub(r"[^0-9a-fA-F]", "", fp or "").lower()
    return fp if len(fp) == 64 else None

def format_fingerprint(fp):
    return ":".join(fp[i:i + 2] for i in range(0, len(fp), 2)).upper()

def fetch_server_fingerprint(host, port):
    """Obtém o SHA-256 do certificado apresentado pelo servidor (para o administrador confirmar)."""
    host = host.strip().strip("[]")
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE
    with socket.create_connection((host, int(port)), timeout=8) as sock:
        with ctx.wrap_socket(sock, server_hostname=host) as ssock:
            der = ssock.getpeercert(binary_form=True)
    return hashlib.sha256(der).hexdigest()

class _PinnedAdapter(HTTPAdapter):
    """Só aceita conexões cujo certificado tenha exatamente o fingerprint SHA-256 confirmado no cadastro."""
    def __init__(self, fingerprint, *args, **kwargs):
        self._fingerprint = fingerprint
        super().__init__(*args, **kwargs)

    def init_poolmanager(self, *args, **kwargs):
        kwargs["assert_fingerprint"] = self._fingerprint
        super().init_poolmanager(*args, **kwargs)

def make_api_session(fingerprint, username, password):
    s = requests.Session()
    s.trust_env = False          # ignora proxies/variáveis de ambiente que contornariam o pinning
    s.verify = False             # a validação é feita pelo fingerprint (adapter abaixo)
    s.auth = (username, password)
    s.mount("https://", _PinnedAdapter(fingerprint))
    return s

def api_error_message(exc, target):
    """Mensagem segura para a tela; o detalhe técnico vai só para o log."""
    logger.warning("Falha na API (%s): %s", _clean(target, 100), _clean(repr(exc), 300))
    if isinstance(exc, requests.exceptions.SSLError):
        return ("O certificado apresentado pelo servidor não confere com o certificado confirmado no cadastro. "
                "Pode ser um certificado renovado ou uma tentativa de interceptação (MITM). "
                "Verifique antes de recadastrar o cluster.")
    if isinstance(exc, requests.exceptions.Timeout):
        return "Tempo esgotado ao comunicar com o servidor."
    if isinstance(exc, requests.exceptions.ConnectionError):
        return "Não foi possível estabelecer conexão com o servidor. Verifique IP, porta e rede."
    return "Erro inesperado ao comunicar com o servidor. Detalhes no log do aplicativo."

# ==========================================
# CLUSTERS
# ==========================================
def save_cluster_and_hosts(cluster_name, cluster_type, ip_address, port, status, pc_ip=None, hosts_list=None,
                           api_user=None, api_pass=None, cluster_uuid=None, fingerprint=None):
    if not _require_admin("save_cluster_and_hosts"):
        return False
    conn = db()
    try:
        pass_enc = encrypt_secret(api_pass) if api_pass else None
        keep = None
        if pc_ip:      # recadastro via Prism Central: preserva o acesso direto já configurado
            keep = conn.execute("SELECT element_ip, element_port, element_user, element_pass_enc, element_fingerprint "
                                "FROM clusters WHERE cluster_name = ?", (cluster_name,)).fetchone()
        conn.execute('''
            INSERT OR REPLACE INTO clusters
            (cluster_name, cluster_type, ip_address, port, status, prism_central_ip, api_user, api_pass_enc, cluster_uuid, cert_fingerprint,
             element_ip, element_port, element_user, element_pass_enc, element_fingerprint)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (cluster_name, cluster_type, ip_address, port, status, pc_ip, api_user, pass_enc, cluster_uuid, fingerprint,
              *(keep or (None,) * 5)))
        for h in (hosts_list or []):
            conn.execute('INSERT OR REPLACE INTO hosts (host_name, cluster_name, ip_address) VALUES (?, ?, ?)',
                         (h.get("name", "Unknown-Host"), cluster_name, h.get("ip", ip_address)))
        conn.commit()
    finally:
        conn.close()
    return True

def fetch_hosts_from_element(session, ip, port):
    url = f"https://{ip}:{port}/api/nutanix/v2.0/hosts"
    hosts_data = []
    try:
        resp = session.get(url, timeout=8, allow_redirects=False)
        if resp.status_code == 200:
            for ent in resp.json().get("entities", []):
                h_name = ent.get("name") or ent.get("host_name")
                h_ip = ent.get("hypervisor_address") or ent.get("service_vm_ip") or ip
                if h_name:
                    hosts_data.append({"name": h_name, "ip": h_ip})
    except Exception as e:
        logger.warning("Falha ao listar hosts do Prism Element %s: %s", _clean(ip, 64), _clean(repr(e), 200))
    return hosts_data

def fetch_hosts_from_central(session, ip, port):
    """Hosts de todos os clusters gerenciados pelo Prism Central, agrupados por UUID do cluster."""
    url = f"https://{ip}:{port}/api/nutanix/v3/hosts/list"
    hosts_by_cluster = {}
    try:
        resp = session.post(url, json={"kind": "host", "length": 500}, timeout=15, allow_redirects=False)
        if resp.status_code == 200:
            for ent in resp.json().get("entities", []):
                status = ent.get("status", {}) or {}
                res = status.get("resources", {}) or {}
                h_name = status.get("name") or res.get("host_name")
                c_uuid = (status.get("cluster_reference") or {}).get("uuid")
                h_ip = ((res.get("hypervisor") or {}).get("ip")
                        or (res.get("controller_vm") or {}).get("ip") or ip)
                if h_name and c_uuid:
                    hosts_by_cluster.setdefault(c_uuid, []).append({"name": h_name, "ip": h_ip})
    except Exception as e:
        logger.warning("Falha ao listar hosts do Prism Central %s: %s", _clean(ip, 64), _clean(repr(e), 200))
    return hosts_by_cluster

def test_and_register_cluster(cluster_type, ip_address, port, username, password, fingerprint):
    if not _require_admin("test_and_register_cluster"):
        return False, DENIED_MSG
    ok, msg = validate_cluster_target(ip_address, port)
    if not ok:
        return False, msg
    fp = normalize_fingerprint(fingerprint)
    if not fp:
        return False, "Fingerprint do certificado ausente ou inválido."

    session = make_api_session(fp, username, password)
    target = f"{ip_address}:{port}"

    if cluster_type == "Prism Element":
        url = f"https://{ip_address}:{port}/api/nutanix/v2.0/cluster"
        try:
            response = session.get(url, timeout=8, allow_redirects=False)
            if response.status_code == 200:
                cluster_name = response.json().get("name")
                if not cluster_name:
                    return False, "Conexão bem-sucedida, mas não foi possível recuperar o nome do cluster."
                hosts_found = fetch_hosts_from_element(session, ip_address, port)
                save_cluster_and_hosts(cluster_name, "Prism Element", ip_address, port, "Saudável", None,
                                       hosts_found, username, password, fingerprint=fp)
                audit("CLUSTER_CADASTRADO", f"{cluster_name} (Prism Element {target})")
                return True, f"Prism Element conectado! Cluster '{cluster_name}' e {len(hosts_found)} host(s) registados com sucesso."
            elif response.status_code == 401:
                audit("CLUSTER_CADASTRO_FALHA", f"{target}: autenticação recusada")
                return False, "Erro de Autenticação: Utilizador ou palavra-passe inválidos."
            return False, f"Falha na conexão. Código HTTP: {response.status_code}"
        except Exception as e:
            return False, api_error_message(e, target)

    # Prism Central
    url_pc = f"https://{ip_address}:{port}/api/nutanix/v2.0/cluster"
    try:
        resp_pc = session.get(url_pc, timeout=8, allow_redirects=False)
        if resp_pc.status_code == 401:
            audit("CLUSTER_CADASTRO_FALHA", f"{target}: autenticação recusada")
            return False, "Erro de Autenticação: Utilizador ou palavra-passe inválidos."
        if resp_pc.status_code != 200:
            return False, f"Falha ao conectar no Prism Central. Código HTTP: {resp_pc.status_code}"
        pc_name = resp_pc.json().get("name", "Prism-Central")
        save_cluster_and_hosts(pc_name, "Prism Central", ip_address, port, "Saudável", None, [],
                               username, password, fingerprint=fp)

        resp_cl = session.post(f"https://{ip_address}:{port}/api/nutanix/v3/clusters/list",
                               json={"kind": "cluster"}, timeout=10, allow_redirects=False)
        registered_count = 0
        if resp_cl.status_code == 200:
            hosts_by_cluster = fetch_hosts_from_central(session, ip_address, port)
            for entity in resp_cl.json().get("entities", []):
                c_name = entity.get("status", {}).get("name")
                c_uuid = (entity.get("metadata") or {}).get("uuid")
                if c_name and c_name != pc_name:
                    save_cluster_and_hosts(c_name, "Prism Element", ip_address, port, "Saudável", ip_address,
                                           hosts_by_cluster.get(c_uuid, []), username, password,
                                           cluster_uuid=c_uuid, fingerprint=fp)
                    registered_count += 1
        audit("CLUSTER_CADASTRADO", f"{pc_name} (Prism Central {target}) com {registered_count} cluster(s)")
        return True, f"Prism Central conectado! {registered_count} cluster(s) gerido(s) descoberto(s) e associados."
    except Exception as e:
        return False, api_error_message(e, target)

def delete_cluster(cluster_name):
    if not _require_admin("delete_cluster"):
        return False, DENIED_MSG
    conn = db()
    try:
        conn.execute("DELETE FROM clusters WHERE cluster_name = ?", (cluster_name,))
        conn.execute("DELETE FROM hosts WHERE cluster_name = ?", (cluster_name,))
        conn.commit()
    finally:
        conn.close()
    audit("CLUSTER_EXCLUIDO", cluster_name)
    return True, f"Cluster '{cluster_name}' excluído com sucesso!"

def get_all_clusters():
    return _q("SELECT cluster_name, cluster_type, ip_address, port, status, prism_central_ip FROM clusters")

def get_hosts_by_cluster(cluster_name):
    return _q("SELECT host_name, ip_address FROM hosts WHERE cluster_name = ?", (cluster_name,))

# ==========================================
# ACESSO DIRETO AO PRISM ELEMENT (clusters gerenciados por Prism Central)
# ==========================================
def get_element_access(cluster_name):
    """(ip, porta, usuário) do acesso direto configurado, ou None."""
    row = _q("SELECT element_ip, element_port, element_user FROM clusters WHERE cluster_name = ? "
             "AND element_ip IS NOT NULL AND element_pass_enc IS NOT NULL", (cluster_name,), one=True)
    return row if row else None

def discover_element_ip(cluster_name):
    """Pergunta ao Prism Central qual é o IP do cluster (VIP). Retorna (ip ou None, mensagem)."""
    if not _require_admin("discover_element_ip"):
        return None, DENIED_MSG
    creds = get_cluster_credentials(cluster_name)
    if not creds or not creds[3] or not creds[6]:
        return None, "Cluster não é gerenciado por um Prism Central cadastrado."
    _t, pc_ip, pc_port, _pc, _u, _p, c_uuid, _fp = creds
    session, err = _endpoint_session(pc_ip, pc_port)
    if session is None:
        return None, err
    try:
        resp = session.post(f"https://{pc_ip}:{pc_port}/api/nutanix/v3/clusters/list", json={"kind": "cluster"},
                            timeout=15, allow_redirects=False)
        resp.raise_for_status()
        for ent in resp.json().get("entities", []):
            if (ent.get("metadata") or {}).get("uuid") != c_uuid:
                continue
            net = ((ent.get("status") or {}).get("resources") or {}).get("network") or {}
            cvms = net.get("controller_vm_ip_list") or []
            ip = net.get("external_ip") or (cvms[0] if cvms else None)
            if ip:
                return str(ip), "IP encontrado pelo Prism Central. Confira antes de continuar."
            return None, "O Prism Central não informou o IP deste cluster. Digite o IP manualmente."
        return None, "Cluster não encontrado no Prism Central."
    except Exception as e:
        return None, api_error_message(e, f"{pc_ip}:{pc_port}")
    finally:
        session.close()

def save_element_access(cluster_name, ip, port, user, password, fingerprint, reuse_pc_credentials=False):
    """Valida e grava o acesso direto ao Prism Element de um cluster gerenciado.
    Confere que o endereço responde como ESSE cluster (UUID ou nome) antes de gravar."""
    if not _require_admin("save_element_access"):
        return False, DENIED_MSG
    ok, msg = validate_cluster_target(ip, port)
    if not ok:
        return False, msg
    fp = normalize_fingerprint(fingerprint)
    if not fp:
        return False, "Fingerprint do certificado ausente ou inválido."
    creds = get_cluster_credentials(cluster_name)
    if not creds or not creds[3]:
        return False, "Cluster não é gerenciado por um Prism Central cadastrado."
    c_uuid, pc_user, pc_pass_enc = creds[6], creds[4], creds[5]
    if reuse_pc_credentials:
        user = pc_user
        password = decrypt_secret(pc_pass_enc) if pc_pass_enc else None
    if not user or not password:
        return False, "Utilizador e palavra-passe são obrigatórios."
    target = f"{ip}:{port}"
    session = make_api_session(fp, user, password)
    try:
        resp = session.get(f"https://{ip}:{port}/api/nutanix/v2.0/cluster", timeout=10, allow_redirects=False)
        if resp.status_code == 401:
            audit("CLUSTER_ACESSO_DIRETO_FALHA", f"{cluster_name} -> {target}: autenticação recusada")
            return False, "Erro de Autenticação: Utilizador ou palavra-passe inválidos para este Prism Element."
        if resp.status_code != 200:
            return False, f"Falha na conexão. Código HTTP: {resp.status_code}"
        info = resp.json()
        found = {str(info[k]) for k in ("cluster_uuid", "uuid") if info.get(k)}
        if c_uuid and found:
            same = c_uuid in found
        else:
            same = info.get("name") == cluster_name
        if not same:
            audit("CLUSTER_ACESSO_DIRETO_FALHA", f"{cluster_name} -> {target}: responde como outro cluster")
            return False, (f"Esse endereço responde como outro cluster ('{_clean(info.get('name'), 60)}'), "
                           f"e não como '{_clean(cluster_name, 60)}'. Confira o IP.")
    except Exception as e:
        return False, api_error_message(e, target)
    finally:
        session.close()
    conn = db()
    try:
        conn.execute("UPDATE clusters SET element_ip = ?, element_port = ?, element_user = ?, element_pass_enc = ?, "
                     "element_fingerprint = ? WHERE cluster_name = ?",
                     (ip.strip(), str(port).strip(), user, encrypt_secret(password), fp, cluster_name))
        conn.commit()
    finally:
        conn.close()
    audit("CLUSTER_ACESSO_DIRETO", f"{cluster_name} -> Prism Element {target}")
    fetch_storage_entities.clear()
    return True, f"Acesso direto ao Prism Element {target} configurado para '{cluster_name}'."

def clear_element_access(cluster_name):
    if not _require_admin("clear_element_access"):
        return False, DENIED_MSG
    conn = db()
    try:
        conn.execute("UPDATE clusters SET element_ip = NULL, element_port = NULL, element_user = NULL, "
                     "element_pass_enc = NULL, element_fingerprint = NULL WHERE cluster_name = ?", (cluster_name,))
        conn.commit()
    finally:
        conn.close()
    audit("CLUSTER_ACESSO_DIRETO_REMOVIDO", cluster_name)
    fetch_storage_entities.clear()
    return True, "Acesso direto removido."

# ==========================================
# ALERTAS ATIVOS VIA API
# ==========================================
SEVERITY_LABELS = {
    "kcritical": "🔴 Crítico", "critical": "🔴 Crítico",
    "kwarning": "🟠 Aviso", "warning": "🟠 Aviso",
    "kinfo": "🔵 Informativo", "info": "🔵 Informativo",
}

def _severity_label(raw):
    return SEVERITY_LABELS.get(str(raw or "").lower(), str(raw) if raw else "-")

def _format_usecs(usecs):
    try:
        return datetime.fromtimestamp(int(usecs) / 1_000_000).strftime("%d/%m/%Y %H:%M:%S")
    except (TypeError, ValueError, OSError):
        return "-"

def _render_template(text, names, values):
    """Substitui {campo} pelos parâmetros do alerta, como o Prism faz."""
    if not text:
        return text
    mapping = dict(zip(names or [], values or []))
    return re.sub(r"\{(\w+)\}", lambda m: str(mapping.get(m.group(1), m.group(0))), str(text))

def get_cluster_credentials(cluster_name):
    return _q("SELECT cluster_type, ip_address, port, prism_central_ip, api_user, api_pass_enc, cluster_uuid, cert_fingerprint "
              "FROM clusters WHERE cluster_name = ?", (cluster_name,), one=True)

def _fetch_alerts_element(session, ip, port):
    """Prism Element (API v2.0): alertas não resolvidos."""
    resp = session.get(f"https://{ip}:{port}/api/nutanix/v2.0/alerts/",
                       params={"resolved": "false", "count": 500}, timeout=15, allow_redirects=False)
    resp.raise_for_status()
    alerts = []
    for ent in resp.json().get("entities", []):
        if ent.get("resolved"):
            continue
        ts = ent.get("created_time_stamp_in_usecs") or ent.get("last_occurrence_time_stamp_in_usecs") or 0
        alerts.append({
            "ts": ts,
            "Título": _render_template(ent.get("title") or ent.get("alert_title") or ent.get("message"),
                                       ent.get("context_types"), ent.get("context_values")) or "Sem título",
            "Data": _format_usecs(ts),
            "Severidade": _severity_label(ent.get("severity")),
            "Descrição": _render_template(ent.get("message"), ent.get("context_types"), ent.get("context_values")) or "-",
        })
    return alerts

def _fetch_alerts_central(session, ip, port, cluster_uuid=None, cluster_name=None):
    """Prism Central (API v3 /groups): alertas com resolved==false, opcionalmente filtrados por cluster.
    Retorna (alertas, filtrado)."""
    payload = {
        "entity_type": "alert",
        "group_member_count": 500,
        "group_member_offset": 0,
        "group_member_sort_attribute": "_created_timestamp_usecs_",
        "group_member_sort_order": "DESCENDING",
        "group_member_attributes": [
            {"attribute": "title"}, {"attribute": "severity"}, {"attribute": "_created_timestamp_usecs_"},
            {"attribute": "resolved"}, {"attribute": "cluster"}, {"attribute": "default_message"},
            {"attribute": "param_name_list"}, {"attribute": "param_value_list"},
        ],
        "filter_criteria": "resolved==false",
    }
    resp = session.post(f"https://{ip}:{port}/api/nutanix/v3/groups", json=payload, timeout=20, allow_redirects=False)
    resp.raise_for_status()
    rows = []
    for group in resp.json().get("group_results", []):
        for ent in group.get("entity_results", []):
            row = {}
            for d in ent.get("data", []):
                vals = d.get("values") or []
                inner = vals[0].get("values") if vals else None
                row[d.get("name")] = inner[0] if inner else None
                row[str(d.get("name")) + "__all"] = inner or []
            if str(row.get("resolved")).lower() != "true":
                rows.append(row)

    filtered = False
    if cluster_uuid or cluster_name:
        keys = [k.lower() for k in (cluster_uuid, cluster_name) if k]
        if any(r.get("cluster") for r in rows):
            rows = [r for r in rows if any(k in str(r.get("cluster") or "").lower() for k in keys)]
            filtered = True

    alerts = []
    for row in rows:
        names = row.get("param_name_list__all") or []
        vals = row.get("param_value_list__all") or []
        ts = row.get("_created_timestamp_usecs_") or 0
        alerts.append({
            "ts": ts,
            "Título": _render_template(row.get("title"), names, vals) or "Sem título",
            "Data": _format_usecs(ts),
            "Severidade": _severity_label(row.get("severity")),
            "Descrição": _render_template(row.get("default_message"), names, vals) or "-",
            "cluster_raw": row.get("cluster"),
        })
    return alerts, filtered

@st.cache_data(ttl=30, show_spinner=False)
def fetch_active_alerts(cluster_name):
    """Retorna (ok, lista_de_alertas, mensagem, fonte). Cache de 30s para não consultar a API a cada clique."""
    creds = get_cluster_credentials(cluster_name)
    if not creds:
        return False, [], "Cluster não encontrado.", ""
    c_type, ip, port, pc_ip, user, pass_enc, c_uuid, fingerprint = creds
    pwd = decrypt_secret(pass_enc) if pass_enc else None
    if not user or not pwd:
        return False, [], ("Credenciais da API não encontradas para este cluster. "
                           "Exclua e cadastre o cluster novamente em 'Gerenciar Cluster'."), ""
    fp = normalize_fingerprint(fingerprint)
    if not fp:
        return False, [], ("Este cluster não tem certificado confirmado (cadastro antigo). "
                           "Exclua e cadastre o cluster novamente em 'Gerenciar Cluster'."), ""

    session = make_api_session(fp, user, pwd)
    use_central = (c_type == "Prism Central") or bool(pc_ip)
    source = f"Prism Central ({ip})" if use_central else f"Prism Element ({ip})"
    try:
        if use_central:
            if c_type == "Prism Central":
                alerts, _ = _fetch_alerts_central(session, ip, port)
                source += " — todos os clusters gerenciados"
            else:
                alerts, scoped = _fetch_alerts_central(session, ip, port, c_uuid, cluster_name)
                source += " — filtrado pelo cluster" if scoped else \
                          " — ⚠️ a API não informou o cluster de cada alerta; exibindo todos do Prism Central"
        else:
            alerts = _fetch_alerts_element(session, ip, port)
    except requests.exceptions.HTTPError as e:
        code = e.response.status_code if e.response is not None else "?"
        logger.warning("API de alertas retornou HTTP %s (%s)", code, _clean(source, 100))
        if code == 401:
            return False, [], "Erro de autenticação ao consultar alertas (credenciais inválidas).", source
        return False, [], f"A API de alertas retornou HTTP {code}.", source
    except Exception as e:
        return False, [], api_error_message(e, source), source
    finally:
        session.close()

    alerts.sort(key=lambda a: a["ts"], reverse=True)

    names_by_uuid = {}
    if c_type == "Prism Central":
        names_by_uuid = {u: n for u, n in _q("SELECT cluster_uuid, cluster_name FROM clusters WHERE cluster_uuid IS NOT NULL")}

    for a in alerts:
        a.pop("ts")
        raw = a.pop("cluster_raw", None)
        if c_type == "Prism Central":
            raw_s = str(raw or "")
            a["Cluster"] = next((n for u, n in names_by_uuid.items() if u and u.lower() in raw_s.lower()), raw_s or "-")
    return True, alerts, "", source

# ==========================================
# RECURSOS (CPU / MEMÓRIA / HOSTS) PARA O DASHBOARD
# ==========================================
def _to_float(v):
    """Converte para float; a API usa strings e -1 para 'indisponível'."""
    try:
        f = float(v)
    except (TypeError, ValueError):
        return None
    return f if f >= 0 else None

def _find_stat(obj, key, depth=0):
    """Procura uma estatística em dicts aninhados (stats / usage_stats mudam de lugar entre versões da API).
    Devolve o primeiro valor válido (>= 0) encontrado."""
    if depth > 5 or not isinstance(obj, dict):
        return None
    if key in obj and _to_float(obj[key]) is not None:
        return _to_float(obj[key])
    for v in obj.values():
        if isinstance(v, dict):
            found = _find_stat(v, key, depth + 1)
            if found is not None:
                return found
    return None

def _host_record(name, cluster_uuid, cpu_total_hz, mem_total_bytes, cpu_ppm, mem_ppm):
    """Uso = capacidade x ppm / 1.000.000 (a API informa o uso em partes por milhão)."""
    return {
        "name": name, "cluster_uuid": cluster_uuid,
        "cpu_total": cpu_total_hz, "mem_total": mem_total_bytes,
        "cpu_used": cpu_total_hz * cpu_ppm / 1e6 if cpu_total_hz and cpu_ppm is not None else None,
        "mem_used": mem_total_bytes * mem_ppm / 1e6 if mem_total_bytes and mem_ppm is not None else None,
    }

def _fix_cpu_capacity(cap_hz, cores):
    """Alguns endpoints devolvem a FREQUÊNCIA de um core (ex.: 2,78 GHz) em vez da capacidade total.
    Um core nunca roda abaixo de ~1 GHz; se a 'capacidade' for menor que cores x 1 GHz, ela é a frequência por core."""
    if cap_hz and cores and cap_hz < cores * 1e9:
        return cap_hz * cores
    return cap_hz

def _parse_host_element(ent):
    """Host do Prism Element (API v2.0)."""
    cores = _to_float(ent.get("num_cpu_cores"))
    freq = _to_float(ent.get("cpu_frequency_in_hz"))
    cpu_total = _fix_cpu_capacity(_to_float(ent.get("cpu_capacity_in_hz")), cores) or (cores * freq if cores and freq else None)
    return _host_record(
        ent.get("name") or ent.get("host_name"), None, cpu_total,
        _to_float(ent.get("memory_capacity_in_bytes")),
        _find_stat(ent, "hypervisor_cpu_usage_ppm"), _find_stat(ent, "hypervisor_memory_usage_ppm"))

def _parse_host_central(ent):
    """Host do Prism Central (API v3)."""
    status = ent.get("status") or {}
    res = status.get("resources") or {}
    mem_mib = _to_float(res.get("memory_capacity_mib"))
    cpu_total = _fix_cpu_capacity(_to_float(res.get("cpu_capacity_hz")), _to_float(res.get("num_cpu_cores")))
    rec = _host_record(
        status.get("name") or res.get("host_name"),
        (status.get("cluster_reference") or {}).get("uuid"),
        cpu_total,
        mem_mib * 1024 * 1024 if mem_mib else None,
        _find_stat(ent, "hypervisor_cpu_usage_ppm"), _find_stat(ent, "hypervisor_memory_usage_ppm"))
    rec["uuid"] = (ent.get("metadata") or {}).get("uuid")
    return rec

def _stat_key_paths(obj, prefix="", depth=0, out=None):
    """Caminhos das chaves que parecem estatísticas (só nomes, nunca valores) - usado no diagnóstico."""
    out = [] if out is None else out
    if depth > 4 or not isinstance(obj, dict) or len(out) >= 20:
        return out
    for k, v in obj.items():
        if isinstance(v, dict):
            _stat_key_paths(v, f"{prefix}{k}.", depth + 1, out)
        elif any(t in str(k).lower() for t in ("ppm", "usage", "cpu", "mem")):
            out.append(f"{prefix}{k}")
    return out[:20]

def _missing_usage(hosts):
    return any(h["cpu_used"] is None or h["mem_used"] is None for h in hosts)

def _apply_ppm(hosts, ppm_for, override=False):
    """Calcula o uso dos hosts a partir de (cpu_ppm, mem_ppm) devolvido por ppm_for(host).
    override=False só preenche o que falta; override=True substitui (usado com o uso do CLUSTER,
    que é o número que o próprio Nutanix mostra em 'Cluster CPU/Memory Usage')."""
    for h in hosts:
        cpu_ppm, mem_ppm = ppm_for(h)
        if cpu_ppm is not None and h["cpu_total"] and (override or h["cpu_used"] is None):
            h["cpu_used"] = h["cpu_total"] * cpu_ppm / 1e6
        if mem_ppm is not None and h["mem_total"] and (override or h["mem_used"] is None):
            h["mem_used"] = h["mem_total"] * mem_ppm / 1e6

def _groups_usage(session, ip, port, entity_type):
    """Uso (ppm) via API /groups do Prism Central. Retorna ({entity_id: (cpu_ppm, mem_ppm)}, texto_diagnóstico)."""
    payload = {
        "entity_type": entity_type, "group_member_count": 500, "group_member_offset": 0,
        "group_member_attributes": [{"attribute": "hypervisor_cpu_usage_ppm"},
                                    {"attribute": "hypervisor_memory_usage_ppm"}],
    }
    resp = session.post(f"https://{ip}:{port}/api/nutanix/v3/groups", json=payload, timeout=20, allow_redirects=False)
    if resp.status_code != 200:
        return {}, f"/groups ({entity_type}): HTTP {resp.status_code}"
    usage = {}
    for group in resp.json().get("group_results", []):
        for ent in group.get("entity_results", []):
            vals = {}
            for d in ent.get("data", []):
                v = d.get("values") or []
                inner = v[0].get("values") if v else None
                vals[d.get("name")] = inner[0] if inner else None
            usage[ent.get("entity_id")] = (_to_float(vals.get("hypervisor_cpu_usage_ppm")),
                                           _to_float(vals.get("hypervisor_memory_usage_ppm")))
    with_cpu = sum(1 for c, _m in usage.values() if c is not None)
    sample = "; ".join(f"{str(k)[:8]}: cpu_ppm={c}, mem_ppm={m}" for k, (c, m) in list(usage.items())[:6])
    return usage, f"/groups ({entity_type}): {len(usage)} entidade(s), {with_cpu} com uso de CPU. {sample}"

@st.cache_data(ttl=60, show_spinner=False)
def fetch_host_stats(ip, port, kind):
    """Lista os hosts (com capacidade e uso) de um endpoint. kind: 'element' (v2.0) ou 'central' (v3).
    O cache é por endpoint: vários clusters do mesmo Prism Central geram UMA só consulta.
    O uso do CLUSTER (mesmo número exibido no Nutanix) tem prioridade; o uso por host é o plano B.
    Retorna (ok, lista_de_hosts, mensagem, diagnóstico)."""
    row = _q("SELECT api_user, api_pass_enc, cert_fingerprint FROM clusters "
             "WHERE ip_address = ? AND port = ? AND api_pass_enc IS NOT NULL LIMIT 1", (ip, port), one=True)
    if not row:
        return False, [], "Credenciais da API não encontradas. Exclua e cadastre o cluster novamente em 'Gerenciar Cluster'.", []
    user, pass_enc, fingerprint = row
    pwd = decrypt_secret(pass_enc) if pass_enc else None
    fp = normalize_fingerprint(fingerprint)
    if not user or not pwd:
        return False, [], "Credenciais da API inválidas. Cadastre o cluster novamente em 'Gerenciar Cluster'.", []
    if not fp:
        return False, [], "Cluster sem certificado confirmado (cadastro antigo). Cadastre-o novamente em 'Gerenciar Cluster'.", []

    target = f"{ip}:{port}"
    diag = []
    session = make_api_session(fp, user, pwd)
    try:
        if kind == "central":
            resp = session.post(f"https://{ip}:{port}/api/nutanix/v3/hosts/list",
                                json={"kind": "host", "length": 500}, timeout=20, allow_redirects=False)
            resp.raise_for_status()
            entities = resp.json().get("entities", [])
            hosts = [_parse_host_central(e) for e in entities]
            diag.append(f"v3 hosts/list: {len(hosts)} host(s), {sum(1 for h in hosts if h['cpu_used'] is not None)} com uso de CPU")
            for e in entities[:6]:
                st_ = e.get("status") or {}
                r = st_.get("resources") or {}
                diag.append(f"  host {_clean(st_.get('name'), 40)}: cpu_capacity_hz={_clean(r.get('cpu_capacity_hz'), 30)}, "
                            f"num_cpu_cores={_clean(r.get('num_cpu_cores'), 10)}, "
                            f"num_cpu_sockets={_clean(r.get('num_cpu_sockets'), 10)}, "
                            f"memory_capacity_mib={_clean(r.get('memory_capacity_mib'), 20)}")
            diag.append("campos de estatística no 1º host: " + (", ".join(_stat_key_paths(entities[0])) if entities else "-"))
            # 1) Uso do cluster (prioridade): igual ao 'Cluster CPU/Memory Usage' do Nutanix
            try:
                usage_c, d = _groups_usage(session, ip, port, "cluster")
                diag.append(d)
                _apply_ppm(hosts, lambda h: usage_c.get(h.get("cluster_uuid"), (None, None)), override=True)
            except Exception as e:
                logger.warning("Falha em /groups (cluster) %s: %s", _clean(target, 100), _clean(repr(e), 200))
                diag.append("/groups (cluster): falhou (detalhes no log)")
            # 2) Plano B: uso por host
            if hosts and _missing_usage(hosts):
                try:
                    usage_h, d = _groups_usage(session, ip, port, "host")
                    diag.append(d)
                    _apply_ppm(hosts, lambda h: usage_h.get(h.get("uuid"), (None, None)))
                except Exception as e:
                    logger.warning("Falha em /groups (host) %s: %s", _clean(target, 100), _clean(repr(e), 200))
                    diag.append("/groups (host): falhou (detalhes no log)")
        else:
            resp = session.get(f"https://{ip}:{port}/api/nutanix/v2.0/hosts", timeout=15, allow_redirects=False)
            resp.raise_for_status()
            entities = resp.json().get("entities", [])
            hosts = [_parse_host_element(e) for e in entities]
            diag.append(f"v2.0 hosts: {len(hosts)} host(s), {sum(1 for h in hosts if h['cpu_used'] is not None)} com uso de CPU")
            for e in entities[:6]:
                diag.append(f"  host {_clean(e.get('name'), 40)}: cpu_capacity_in_hz={_clean(e.get('cpu_capacity_in_hz'), 30)}, "
                            f"num_cpu_cores={_clean(e.get('num_cpu_cores'), 10)}, "
                            f"cpu_frequency_in_hz={_clean(e.get('cpu_frequency_in_hz'), 30)}, "
                            f"memory_capacity_in_bytes={_clean(e.get('memory_capacity_in_bytes'), 30)}")
            diag.append("campos de estatística no 1º host: " + (", ".join(_stat_key_paths(entities[0])) if entities else "-"))
            # Uso do cluster (prioridade) - o host só é usado se o cluster não informar
            try:
                rc = session.get(f"https://{ip}:{port}/api/nutanix/v2.0/cluster", timeout=10, allow_redirects=False)
                rc.raise_for_status()
                body = rc.json()
                cpu_ppm = _find_stat(body, "hypervisor_cpu_usage_ppm")
                mem_ppm = _find_stat(body, "hypervisor_memory_usage_ppm")
                diag.append(f"v2.0 cluster: cpu_ppm={cpu_ppm}, mem_ppm={mem_ppm}")
                _apply_ppm(hosts, lambda h: (cpu_ppm, mem_ppm), override=True)
            except Exception as e:
                logger.warning("Falha em v2.0/cluster %s: %s", _clean(target, 100), _clean(repr(e), 200))
                diag.append("v2.0 cluster: falhou (detalhes no log)")
    except requests.exceptions.HTTPError as e:
        code = e.response.status_code if e.response is not None else "?"
        logger.warning("API de hosts retornou HTTP %s (%s)", code, _clean(target, 100))
        if code == 401:
            return False, [], "Erro de autenticação ao consultar os hosts (credenciais inválidas).", diag
        return False, [], f"A API de hosts retornou HTTP {code}.", diag
    except Exception as e:
        return False, [], api_error_message(e, target), diag
    finally:
        session.close()
    return True, hosts, "", diag

def _sum_hosts(hosts):
    """Totaliza capacidade e uso. Uso fica None se nenhum host informou estatística."""
    def total(field):
        vals = [h[field] for h in hosts if h[field] is not None]
        return sum(vals) if vals else None
    return {"hosts": len(hosts),
            "cpu_total": total("cpu_total"), "cpu_used": total("cpu_used"),
            "mem_total": total("mem_total"), "mem_used": total("mem_used")}

def get_cluster_resources(cluster_name):
    """Recursos de UM cluster (Prism Element). Retorna (ok, dados, mensagem); dados["diag"] = diagnóstico da API."""
    creds = get_cluster_credentials(cluster_name)
    if not creds:
        return False, None, "Cluster não encontrado."
    c_type, ip, port, pc_ip, _u, _p, c_uuid, _fp = creds
    if pc_ip:                                   # cluster gerenciado: dados vêm do Prism Central
        if not c_uuid:
            return False, None, "Cluster sem UUID registado. Cadastre o Prism Central novamente."
        ok, hosts, msg, diag = fetch_host_stats(ip, port, "central")
        if not ok:
            return False, None, msg
        data = _sum_hosts([h for h in hosts if h["cluster_uuid"] == c_uuid])
    else:
        ok, hosts, msg, diag = fetch_host_stats(ip, port, "element")
        if not ok:
            return False, None, msg
        data = _sum_hosts(hosts)
    data["diag"] = diag
    return True, data, ""

def get_global_resources():
    """Soma os recursos de todos os clusters (sem contar o Prism Central). Retorna (dados, falhas)."""
    acc = {"hosts": 0, "cpu_total": None, "cpu_used": None, "mem_total": None, "mem_used": None}
    failures = []
    for (name, c_type, *_rest) in get_all_clusters():
        if c_type == "Prism Central":
            continue
        ok, data, msg = get_cluster_resources(name)
        if not ok:
            failures.append((name, msg))
            continue
        acc["hosts"] += data["hosts"]
        for k in ("cpu_total", "cpu_used", "mem_total", "mem_used"):
            if data[k] is not None:
                acc[k] = (acc[k] or 0) + data[k]
    return acc, failures

def _br(num, decimals=1):
    """Formato numérico brasileiro (1.234,5)."""
    return f"{num:,.{decimals}f}".replace(",", "X").replace(".", ",").replace("X", ".")

def _fmt_ghz(hz):
    return f"{_br(hz / 1e9)} GHz"

def _fmt_bytes(b):
    return f"{_br(b / 1024**4, 2)} TiB" if b >= 1024**4 else f"{_br(b / 1024**3)} GiB"


# ==========================================
# MÉTRICAS POR HOST (CPU / MEMÓRIA / I/O / LATÊNCIA / VMs)
# ==========================================
# coluna do banco -> nomes da estatística na API (o 1º é o preferido; os demais são plano B).
# Unidades da API: *_ppm = partes por milhão | *_usecs = microssegundos | *_kBps = kilobytes por segundo
HOST_STAT_MAP = {
    "cpu_ppm":    ["hypervisor_cpu_usage_ppm"],
    "mem_ppm":    ["hypervisor_memory_usage_ppm"],
    "iops_total": ["controller_num_iops", "num_iops"],
    "iops_read":  ["controller_num_read_iops"],
    "iops_write": ["controller_num_write_iops"],
    "bw_total":   ["controller_io_bandwidth_kBps", "io_bandwidth_kBps"],
    "bw_read":    ["controller_read_io_bandwidth_kBps"],
    "bw_write":   ["controller_write_io_bandwidth_kBps"],
    "lat_avg":    ["controller_avg_io_latency_usecs", "avg_io_latency_usecs"],
    "lat_read":   ["controller_avg_read_io_latency_usecs"],
    "lat_write":  ["controller_avg_write_io_latency_usecs"],
    "hyp_lat":    ["hypervisor_avg_io_latency_usecs"],
    "num_vms":    ["num_vms"],
}
# Colunas gravadas em host_usage_history (capacidade e uso já convertidos para Hz / bytes)
HOST_HIST_COLS = ["cpu_total", "cpu_used", "mem_total", "mem_used",
                  "iops_total", "iops_read", "iops_write",
                  "bw_total", "bw_read", "bw_write",
                  "lat_avg", "lat_read", "lat_write", "hyp_lat", "num_vms"]
# Consulta em blocos (usada só se o Prism Central recusar o pedido completo, ex.: nome de atributo inválido)
HOST_GROUP_BLOCKS = [("CPU/memória/VMs", ["cpu_ppm", "mem_ppm", "num_vms"]),
                     ("I/O", ["iops_total", "iops_read", "iops_write", "bw_total", "bw_read", "bw_write"]),
                     ("latência", ["lat_avg", "lat_read", "lat_write", "hyp_lat"])]

def _host_metrics_from_entity(ent):
    """Extrai as métricas conhecidas de um host (Prism Element v2.0 traz tudo em 'stats')."""
    out = {}
    for col, keys in HOST_STAT_MAP.items():
        for k in keys:
            v = _find_stat(ent, k)
            if v is not None:
                out[col] = v
                break
    return out

def _finalize_host(rec):
    """Converte ppm em Hz/bytes usados e monta rec['values'] com exatamente as colunas de HOST_HIST_COLS."""
    m = rec.pop("metrics", {}) or {}
    cpu_total, mem_total = rec.get("cpu_total"), rec.get("mem_total")
    vals = {"cpu_total": cpu_total, "mem_total": mem_total,
            "cpu_used": cpu_total * m["cpu_ppm"] / 1e6 if cpu_total and m.get("cpu_ppm") is not None else None,
            "mem_used": mem_total * m["mem_ppm"] / 1e6 if mem_total and m.get("mem_ppm") is not None else None}
    for c in HOST_HIST_COLS:
        vals.setdefault(c, m.get(c))
    rec["values"] = vals
    return rec

def _groups_host_metrics(session, ip, port):
    """Métricas por host via /groups do Prism Central. Retorna ({uuid_do_host: {coluna: valor}}, diagnóstico)."""
    attr_to_col = {keys[0]: col for col, keys in HOST_STAT_MAP.items()}
    diag = []

    def _request(cols):
        payload = {"entity_type": "host", "group_member_count": 500, "group_member_offset": 0,
                   "group_member_attributes": [{"attribute": HOST_STAT_MAP[c][0]} for c in cols]}
        resp = session.post(f"https://{ip}:{port}/api/nutanix/v3/groups", json=payload, timeout=20, allow_redirects=False)
        if resp.status_code != 200:
            return None, resp.status_code
        found = {}
        for group in resp.json().get("group_results", []):
            for ent in group.get("entity_results", []):
                vals = {}
                for d in ent.get("data", []):
                    v = d.get("values") or []
                    inner = v[0].get("values") if v else None
                    vals[d.get("name")] = inner[0] if inner else None
                found[ent.get("entity_id")] = vals
        return found, 200

    raw, code = _request(list(HOST_STAT_MAP))
    if raw is None:
        diag.append(f"/groups (host, todas as métricas): HTTP {code}; tentando em blocos menores")
        raw = {}
        for label, cols in HOST_GROUP_BLOCKS:
            part, code = _request(cols)
            if part is None:
                diag.append(f"/groups (host, {label}): HTTP {code} - bloco ignorado")
                continue
            for ent_id, vals in part.items():
                raw.setdefault(ent_id, {}).update(vals)
    result = {}
    for ent_id, vals in raw.items():
        metrics = {}
        for attr, v in vals.items():
            fv = _to_float(v)
            if attr in attr_to_col and fv is not None:
                metrics[attr_to_col[attr]] = fv
        result[ent_id] = metrics
    diag.append(f"/groups (host): {len(result)} host(s) com métricas")
    return result, diag

def _endpoint_session(ip, port):
    """Sessão autenticada (certificado fixado) para um endpoint. Retorna (sessão, mensagem_de_erro)."""
    row = _q("SELECT element_user, element_pass_enc, element_fingerprint FROM clusters "
             "WHERE element_ip = ? AND element_port = ? AND element_pass_enc IS NOT NULL LIMIT 1", (ip, port), one=True)
    if not row:
        row = _q("SELECT api_user, api_pass_enc, cert_fingerprint FROM clusters "
                 "WHERE ip_address = ? AND port = ? AND api_pass_enc IS NOT NULL LIMIT 1", (ip, port), one=True)
    if not row:
        return None, "Credenciais da API não encontradas. Exclua e cadastre o cluster novamente em 'Gerenciar Cluster'."
    user, pass_enc, fingerprint = row
    pwd = decrypt_secret(pass_enc) if pass_enc else None
    fp = normalize_fingerprint(fingerprint)
    if not user or not pwd:
        return None, "Credenciais da API inválidas. Cadastre o cluster novamente em 'Gerenciar Cluster'."
    if not fp:
        return None, "Cluster sem certificado confirmado (cadastro antigo). Cadastre-o novamente em 'Gerenciar Cluster'."
    return make_api_session(fp, user, pwd), ""

@st.cache_data(ttl=60, show_spinner=False)
def fetch_host_metrics(ip, port, kind):
    """Métricas de CADA host de um endpoint (valores reais por host, sem a média do cluster).
    kind: 'element' (v2.0) ou 'central' (v3). Cache por endpoint, como em fetch_host_stats.
    Retorna (ok, lista_de_hosts, mensagem, diagnóstico); cada host traz 'values' com as colunas de HOST_HIST_COLS."""
    session, err = _endpoint_session(ip, port)
    if session is None:
        return False, [], err, []
    target = f"{ip}:{port}"
    diag = []
    try:
        if kind == "central":
            resp = session.post(f"https://{ip}:{port}/api/nutanix/v3/hosts/list",
                                json={"kind": "host", "length": 500}, timeout=20, allow_redirects=False)
            resp.raise_for_status()
            hosts = []
            for e in resp.json().get("entities", []):
                rec = _parse_host_central(e)
                rec["metrics"] = _host_metrics_from_entity(e)
                hosts.append(rec)
            diag.append(f"v3 hosts/list: {len(hosts)} host(s)")
            try:
                by_uuid, d = _groups_host_metrics(session, ip, port)
                diag.extend(d)
                for h in hosts:
                    h["metrics"].update(by_uuid.get(h.get("uuid"), {}))
            except Exception as e:
                logger.warning("Falha em /groups (métricas de host) %s: %s", _clean(target, 100), _clean(repr(e), 200))
                diag.append("/groups (host): falhou (detalhes no log)")
        else:
            resp = session.get(f"https://{ip}:{port}/api/nutanix/v2.0/hosts", timeout=15, allow_redirects=False)
            resp.raise_for_status()
            hosts = []
            for e in resp.json().get("entities", []):
                rec = _parse_host_element(e)
                rec["metrics"] = _host_metrics_from_entity(e)
                hosts.append(rec)
            diag.append(f"v2.0 hosts: {len(hosts)} host(s)")
        hosts = [_finalize_host(h) for h in hosts if h.get("name")]
        for h in hosts[:6]:
            found = ", ".join(f"{c}={h['values'][c]:.4g}" for c in HOST_HIST_COLS if h["values"].get(c) is not None)
            diag.append(f"  host {_clean(h['name'], 40)}: {found or 'nenhuma métrica retornada'}")
        missing = [c for c in HOST_HIST_COLS if hosts and all(h["values"].get(c) is None for h in hosts)]
        if missing:
            diag.append("métricas sem dado em nenhum host: " + ", ".join(missing))
    except requests.exceptions.HTTPError as e:
        code = e.response.status_code if e.response is not None else "?"
        logger.warning("API de métricas de host retornou HTTP %s (%s)", code, _clean(target, 100))
        if code == 401:
            return False, [], "Erro de autenticação ao consultar os hosts (credenciais inválidas).", diag
        return False, [], f"A API de hosts retornou HTTP {code}.", diag
    except Exception as e:
        return False, [], api_error_message(e, target), diag
    finally:
        session.close()
    return True, hosts, "", diag

def get_host_metrics(cluster_name):
    """Métricas de todos os hosts de UM cluster. Retorna (ok, hosts, mensagem, diagnóstico)."""
    creds = get_cluster_credentials(cluster_name)
    if not creds:
        return False, [], "Cluster não encontrado.", []
    _type, ip, port, pc_ip, _u, _p, c_uuid, _fp = creds
    if pc_ip:                                   # cluster gerenciado: dados vêm do Prism Central
        if not c_uuid:
            return False, [], "Cluster sem UUID registado. Cadastre o Prism Central novamente.", []
        ok, hosts, msg, diag = fetch_host_metrics(ip, port, "central")
        if not ok:
            return False, [], msg, diag
        return True, [h for h in hosts if h.get("cluster_uuid") == c_uuid], "", diag
    return fetch_host_metrics(ip, port, "element")

# ==========================================
# STORAGE: POOL / CONTAINER / VIRTUAL DISK / DISCO FÍSICO
# ==========================================
STORAGE_ETYPES = {
    "pool":      {"label": "Storage Pool",  "resource": "storage_pools"},
    "container": {"label": "Container",     "resource": "storage_containers"},
    "vdisk":     {"label": "Virtual Disk",  "resource": "virtual_disks"},
    "pdisk":     {"label": "Disco Físico",  "resource": "disks"},
}
# coluna -> (nomes possíveis da estatística na API, fator de conversão). Vale o 1º nome que existir no registro.
# Unidades da API: bytes | *_usecs = µs | *_kBps = kB/s | *_ppm = partes por milhão | *_kbytes = KB
STORAGE_STAT_MAP = {
    "cap_bytes":          (["storage.capacity_bytes", "disk_capacity_in_bytes", "disk_size", "max_capacity", "capacity"], 1),
    "used_bytes":         (["storage.usage_bytes", "controller_user_bytes"], 1),
    "free_bytes":         (["storage.free_bytes"], 1),
    "logical_used_bytes": (["storage.logical_usage_bytes"], 1),
    "saving_bytes":       (["data_reduction.overall.saving_bytes"], 1),
    "saving_ratio":       (["data_reduction.saving_ratio_ppm"], 1e-6),              # 1.000.000 ppm = 1:1
    "iops_total":         (["controller_num_iops", "num_iops"], 1),
    "iops_read":          (["controller_num_read_iops"], 1),
    "iops_write":         (["controller_num_write_iops"], 1),
    "bw_total":           (["controller_io_bandwidth_kBps", "io_bandwidth_kBps"], 1),
    "bw_read":            (["controller_read_io_bandwidth_kBps"], 1),
    "bw_write":           (["controller_write_io_bandwidth_kBps"], 1),
    "lat_avg":            (["controller_avg_io_latency_usecs", "avg_io_latency_usecs"], 1),
    "lat_read":           (["controller_avg_read_io_latency_usecs"], 1),
    "lat_write":          (["controller_avg_write_io_latency_usecs"], 1),
    "io_size_kb":         (["controller_avg_io_size_kbytes"], 1),
    "read_pct":           (["controller_read_io_ppm"], 1e-4),                       # ppm -> %
    "random_pct":         (["controller_random_io_ppm"], 1e-4),
}
STORAGE_COLS = list(STORAGE_STAT_MAP)
# Onde estão o id e o nome de cada tipo de recurso no registro da API
STORAGE_ID_KEYS = {"pool": ["storage_pool_uuid", "id", "uuid"],
                   "container": ["storage_container_uuid", "id", "uuid"],
                   "vdisk": ["uuid", "virtual_disk_id", "nutanix_nfsfile_path"],
                   "pdisk": ["disk_uuid", "id", "uuid", "disk_id"]}
STORAGE_PAGE_SIZE = 500
STORAGE_MAX_PAGES = 40
VDISK_MAX = max(100, _env_int("NUTMETRICS_VDISK_MAX", 3000))                  # máximo de virtual disks gravados por cluster
VDISK_INTERVAL_SEC = max(5, _env_int("NUTMETRICS_VDISK_INTERVAL_MIN", 15)) * 60  # virtual disks são muitos: coleta mais espaçada
# Por quantos dias as amostras ficam no detalhe de 5 min (depois viram média por hora)
STORAGE_FULLRES_DAYS = {"pool": 35, "container": 35, "pdisk": 35, "vdisk": 7}

def _first_value(ent, keys):
    for k in keys:
        v = ent.get(k)
        if v not in (None, "", []):
            return str(v)
    return None

def _storage_name(etype, ent, ent_id):
    if etype in ("pool", "container"):
        return ent.get("name") or str(ent_id)
    if etype == "vdisk":
        vm = ent.get("attached_vmname") or "sem VM"
        disk = ent.get("disk_address") or ent.get("virtual_disk_id") or str(ent_id)[:8]
        return f"{vm} · {disk}"
    host = ent.get("host_name") or (ent.get("cvm_ip_address") or "")
    loc = ent.get("location")
    tier = ent.get("storage_tier_name") or ent.get("tier_name") or ""
    base = " · ".join(str(x) for x in (host, f"disco {loc}" if loc is not None else None, tier) if x)
    return base or str(ent_id)

def _storage_info(etype, ent):
    """Detalhes descritivos (texto) mostrados no cartão do recurso."""
    info = {}
    if etype == "pool":
        if isinstance(ent.get("disks"), list):
            info["Discos"] = len(ent["disks"])
    elif etype == "container":
        for label, key in (("Fator de replicação", "replication_factor"), ("Compressão", "compression_enabled"),
                           ("Dedup", "on_disk_dedup"), ("Erasure coding", "erasure_code")):
            if ent.get(key) is not None:
                info[label] = ent[key]
    elif etype == "vdisk":
        if ent.get("attached_vmname"):
            info["VM"] = ent["attached_vmname"]
        cap = _to_float(ent.get("disk_capacity_in_bytes"))
        if cap:
            info["Tamanho"] = _fmt_bytes(cap)
    else:
        hw = ent.get("disk_hardware_config") or {}
        for label, val in (("Tier", ent.get("storage_tier_name") or ent.get("tier_name")), ("Host", ent.get("host_name")),
                           ("Status", ent.get("disk_status")), ("Modelo", hw.get("model") if isinstance(hw, dict) else None),
                           ("Online", ent.get("online"))):
            if val is not None:
                info[label] = val
    return {k: _clean(v, 60) for k, v in info.items()}

def _parse_storage_entity(etype, ent):
    """Registro da API -> {'id', 'name', 'info', 'values'} com exatamente as colunas de STORAGE_COLS."""
    ent_id = _first_value(ent, STORAGE_ID_KEYS[etype])
    if not ent_id:
        return None
    vals = {}
    for col, (keys, factor) in STORAGE_STAT_MAP.items():
        v = None
        for k in keys:
            v = _find_stat(ent, k)
            if v is not None:
                break
        vals[col] = v * factor if v is not None else None
    cap, used, free = vals["cap_bytes"], vals["used_bytes"], vals["free_bytes"]
    if cap is None and used is not None and free is not None:
        vals["cap_bytes"] = used + free
    if free is None and cap is not None and used is not None:
        vals["free_bytes"] = max(cap - used, 0.0)
    if used is None and cap is not None and free is not None:
        vals["used_bytes"] = max(cap - free, 0.0)
    return {"id": ent_id, "name": _clean(_storage_name(etype, ent, ent_id), 120),
            "info": _storage_info(etype, ent), "values": vals}

# nome do recurso na API v1 (usada só como plano B quando a v2.0 recusa)
STORAGE_V1_RESOURCES = {"storage_containers": "containers"}

def _fetch_pages(session, base, extra, paged):
    """Lê todas as páginas de uma URL. Retorna (registros ou None, status HTTP, trecho do corpo do erro)."""
    entities, seen, page = [], set(), 1
    while page <= STORAGE_MAX_PAGES:
        params = dict(extra)
        if paged:
            params.update(count=STORAGE_PAGE_SIZE, page=page)
        resp = session.get(base, params=params, timeout=25, allow_redirects=False)
        if resp.status_code != 200:
            if page > 1:                       # já veio algo: mantém o que foi lido
                break
            return None, resp.status_code, str(getattr(resp, "text", "") or "")[:160]
        batch = resp.json().get("entities") or []
        new = 0
        for e in batch:
            key = _first_value(e, ["uuid", "id", "storage_pool_uuid", "storage_container_uuid", "disk_uuid"]) \
                or repr(sorted(e.items(), key=lambda kv: kv[0]))[:200]
            if key not in seen:                # se a API ignorar 'page', as páginas repetem e o laço para aqui
                seen.add(key)
                entities.append(e)
                new += 1
        if not paged or new == 0 or len(batch) < STORAGE_PAGE_SIZE:
            break
        page += 1
    return entities, 200, ""

def _storage_list(session, ip, port, kind, proxy_uuid, resource, v1_first=False):
    """Lista um recurso de storage tentando, em ordem, v2.0 e v1 (no Prism Central, com proxy para o cluster).
    Se a v2.0 recusar a paginação (HTTP 400), repete sem ela. Retorna (registros, diagnóstico, status): 200 = ok."""
    host = f"https://{ip}:{port}"
    v1 = STORAGE_V1_RESOURCES.get(resource, resource)
    extra = {"proxyClusterUuid": proxy_uuid} if kind == "central" else {}
    v1_url = f"{host}/PrismGateway/services/rest/v1/{v1}/"
    if kind == "central":
        v2_urls = [f"{host}/PrismGateway/services/rest/v2.0/{resource}/", f"{host}/api/nutanix/v2.0/{resource}/"]
    else:
        v2_urls = [f"{host}/api/nutanix/v2.0/{resource}/", f"{host}/PrismGateway/services/rest/v2.0/{resource}/"]
    bases = [v1_url] + v2_urls if v1_first else v2_urls + [v1_url]
    diag, last = [], None
    for base in bases:
        path = base.split(f"{ip}:{port}", 1)[1]
        for paged in (True, False):
            ents, code, body = _fetch_pages(session, base, extra, paged)
            if ents is not None:
                diag.append(f"{resource}: {len(ents)} registro(s) via {path}")
                return ents, diag, 200
            last = code
            diag.append(f"{resource}: HTTP {code} em {path}" + ("" if paged else " (sem paginação)")
                        + (f" - {_clean(body, 160)}" if body.strip() else ""))
            if code != 400:                    # só repete sem paginação quando a paginada foi recusada (400)
                break
    return [], diag, last

def _storage_error_message(kind, status):
    who = "Prism Central" if kind == "central" else "Prism Element"
    if status == 401:
        return f"Autenticação recusada pelo {who}. Confira utilizador e palavra-passe (veja o diagnóstico)."
    if status == 403:
        return f"A conta não tem permissão de leitura do storage no {who} (veja o diagnóstico)."
    if status == 404:
        return f"O {who} não encontrou o endereço de storage nesta versão (veja o diagnóstico)."
    if kind == "central":
        return ("O Prism Central não encaminhou a consulta de storage deste cluster (veja o diagnóstico). "
                "Configure o acesso direto ao Prism Element em Gerenciar Cluster > Acesso direto.")
    return f"O {who} retornou HTTP {status} na consulta de storage (veja o diagnóstico)."

@st.cache_data(ttl=60, show_spinner=False)
def fetch_storage_entities(ip, port, kind, proxy_uuid, etype):
    """Todos os recursos de um tipo (pool, container, vdisk, pdisk) de UM cluster, com as métricas atuais.
    Retorna (ok, lista, mensagem, diagnóstico)."""
    session, err = _endpoint_session(ip, port)
    if session is None:
        return False, [], err, []
    target = f"{ip}:{port}"
    try:
        raw, diag, status = _storage_list(session, ip, port, kind, proxy_uuid, STORAGE_ETYPES[etype]["resource"])
        if status != 200:
            return False, [], _storage_error_message(kind, status), diag
        parsed = [p for p in (_parse_storage_entity(etype, e) for e in raw) if p]
        if etype == "vdisk":
            parsed = [p for p in parsed if any(v is not None for v in p["values"].values())]
            if len(parsed) > VDISK_MAX:
                parsed.sort(key=lambda p: p["values"].get("iops_total") or 0, reverse=True)
                diag.append(f"virtual disks: {len(parsed)} encontrados; gravando só os {VDISK_MAX} com mais IOPS "
                            f"(ajuste NUTMETRICS_VDISK_MAX)")
                parsed = parsed[:VDISK_MAX]
        for p in parsed[:4]:
            found = ", ".join(f"{c}={p['values'][c]:.4g}" for c in STORAGE_COLS if p["values"].get(c) is not None)
            diag.append(f"  {_clean(p['name'], 50)}: {found or 'nenhuma métrica retornada'}")
        missing = [c for c in STORAGE_COLS if parsed and all(p["values"].get(c) is None for p in parsed)]
        if missing:
            diag.append("métricas sem dado em nenhum registro: " + ", ".join(missing))
    except requests.exceptions.HTTPError as e:
        code = e.response.status_code if e.response is not None else "?"
        logger.warning("API de storage retornou HTTP %s (%s)", code, _clean(target, 100))
        return False, [], f"A API de storage retornou HTTP {code}.", []
    except Exception as e:
        return False, [], api_error_message(e, target), []
    finally:
        session.close()
    return True, parsed, "", diag

def _route_cluster_fetch(cluster_name, fetcher, *args):
    """Executa fetcher(ip, porta, tipo, proxy_uuid, *args) pelo melhor caminho do cluster: acesso direto ao Prism Element,
    depois o proxy do Prism Central; cluster cadastrado direto no Prism Element usa o próprio endereço.
    Retorna (ok, lista, mensagem, diagnóstico)."""
    creds = get_cluster_credentials(cluster_name)
    if not creds:
        return False, [], "Cluster não encontrado.", []
    _type, ip, port, pc_ip, _u, _p, c_uuid, _fp = creds
    direct = get_element_access(cluster_name) if pc_ip else None
    direct_fail = None
    if direct:                                   # 1º: direto no Prism Element (mais confiável que o proxy do PC)
        ok, ents, msg, diag = fetcher(direct[0], direct[1] or "9440", "element", "", *args)
        if ok:
            return True, ents, "", [f"via acesso direto ao Prism Element {direct[0]}"] + diag
        direct_fail = (msg, [f"acesso direto ({direct[0]}): {msg}"] + diag)
    if pc_ip:
        if not c_uuid:
            return False, [], "Cluster sem UUID registado. Cadastre o Prism Central novamente.", []
        ok, ents, msg, diag = fetcher(ip, port, "central", c_uuid, *args)
        if ok:
            return True, ents, "", ["via proxy do Prism Central"] + diag
        if direct_fail:
            return False, [], direct_fail[0], direct_fail[1] + ["proxy do Prism Central:"] + diag
        return False, [], msg, ["acesso direto ao Prism Element: NÃO configurado", "proxy do Prism Central:"] + diag
    return fetcher(ip, port, "element", "", *args)

def get_storage_metrics(cluster_name, etype):
    """Recursos de storage de um tipo para UM cluster. Retorna (ok, lista, mensagem, diagnóstico)."""
    return _route_cluster_fetch(cluster_name, fetch_storage_entities, etype)

# ==========================================
# HISTÓRICO DE UTILIZAÇÃO (coleta a cada 5 min)
# ==========================================
SAMPLE_INTERVAL_SEC = 300
USAGE_RETENTION_DAYS = 400

def collect_usage_samples():
    """Grava uma amostra (CPU/memória total e em uso) de cada cluster cadastrado."""
    now = time.time()
    for (name, c_type, *_rest) in get_all_clusters():
        if c_type == "Prism Central":
            continue
        try:
            ok, data, _msg = get_cluster_resources(name)
        except Exception as e:
            logger.warning("Coleta de utilização falhou (%s): %s", _clean(name, 60), _clean(repr(e), 200))
            continue
        if ok and data and data["cpu_total"] and data["mem_total"]:
            _x("INSERT INTO usage_history (cluster_name, ts, cpu_total, cpu_used, mem_total, mem_used) "
               "VALUES (?, ?, ?, ?, ?, ?)",
               (name, now, data["cpu_total"], data["cpu_used"], data["mem_total"], data["mem_used"]))
        try:                                        # hosts: falha aqui não atrapalha a amostra do cluster
            _collect_host_samples(name, now)
        except Exception as e:
            logger.warning("Coleta de hosts falhou (%s): %s", _clean(name, 60), _clean(repr(e), 200))
        try:                                        # storage: idem
            _collect_storage_samples(name, now)
        except Exception as e:
            logger.warning("Coleta de storage falhou (%s): %s", _clean(name, 60), _clean(repr(e), 200))
        if VM_COLLECT_ENABLED:
            try:                                    # VMs: idem
                _collect_vm_samples(name, now)
            except Exception as e:
                logger.warning("Coleta de VMs falhou (%s): %s", _clean(name, 60), _clean(repr(e), 200))
    _x("DELETE FROM usage_history WHERE ts < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    _x("DELETE FROM host_usage_history WHERE ts < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    _x("DELETE FROM storage_usage_history WHERE ts < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    _x("DELETE FROM storage_entities WHERE last_seen < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    _x("DELETE FROM vm_usage_history WHERE ts < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    _x("DELETE FROM vm_entities WHERE last_seen < ?", (now - USAGE_RETENTION_DAYS * 86400,))
    global _last_host_compaction
    if now - _last_host_compaction > 86400:         # compacta o histórico antigo dos hosts no máximo 1x por dia
        for _compact in (compact_host_history, compact_storage_history, compact_vm_history):
            try:                                    # cada uma isolada: se uma falhar, as outras seguem
                _compact(now)
            except Exception as e:
                logger.warning("Compactação (%s) falhou: %s", _compact.__name__, _clean(repr(e), 200))
        _last_host_compaction = now

@st.cache_resource
def _start_usage_collector():
    """Inicia (uma única vez por processo) a thread que coleta o histórico a cada 5 minutos."""
    def _loop():
        while True:
            try:
                collect_usage_samples()
            except Exception as e:
                logger.warning("Coletor de utilização: %s", _clean(repr(e), 200))
            time.sleep(SAMPLE_INTERVAL_SEC)
    t = threading.Thread(target=_loop, name="nutmetrics-collector", daemon=True)
    t.start()
    return t

# (rótulo da aba, dias de janela, agregação)
USAGE_PERIODS = [("Diário", 1, None), ("Semanal", 7, "60min"), ("Mensal", 30, "360min"), ("Anual", 365, "1D")]

def load_usage_df(cluster_name, days, rule=None):
    rows = _q("SELECT ts, cpu_total, cpu_used, mem_total, mem_used FROM usage_history "
              "WHERE cluster_name = ? AND ts >= ? ORDER BY ts", (cluster_name, time.time() - days * 86400))
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows, columns=["ts", "cpu_total", "cpu_used", "mem_total", "mem_used"])
    local_tz = datetime.now().astimezone().tzinfo
    df["ts"] = pd.to_datetime(df["ts"], unit="s", utc=True).dt.tz_convert(local_tz).dt.tz_localize(None)
    if rule:
        df = df.set_index("ts").resample(rule).mean().dropna(how="all").reset_index()
    df["cpu_used_ghz"] = df["cpu_used"] / 1e9
    df["cpu_total_ghz"] = df["cpu_total"] / 1e9
    df["cpu_pct"] = df["cpu_used"] / df["cpu_total"] * 100
    df["mem_used_gib"] = df["mem_used"] / 1024**3
    df["mem_total_gib"] = df["mem_total"] / 1024**3
    df["mem_pct"] = df["mem_used"] / df["mem_total"] * 100
    return df

def _usage_chart(df, series, ytitle, is_pct=False, trend=False):
    """series: {rótulo: coluna}. Com trend=True acrescenta uma reta de tendência da 1ª série."""
    cols = list(series.values())
    long = df.melt(id_vars="ts", value_vars=cols, var_name="col", value_name="valor")
    long["Série"] = long["col"].map({v: k for k, v in series.items()})
    scale = alt.Scale(domain=[0, 100]) if is_pct else alt.Scale(zero=True)
    enc_y = alt.Y("valor:Q", title=ytitle, scale=scale)
    enc_c = alt.Color("Série:N", legend=alt.Legend(orient="bottom", title=None))
    layers = [alt.Chart(long).mark_line().encode(
        x=alt.X("ts:T", title=None), y=enc_y, color=enc_c,
        tooltip=[alt.Tooltip("ts:T", title="Data", format="%d/%m/%Y %H:%M"), "Série:N",
                 alt.Tooltip("valor:Q", title=ytitle, format=",.2f")])]
    if trend:
        base = df.dropna(subset=[cols[0]])
        if len(base) >= 3:
            xs = (base["ts"] - base["ts"].min()).dt.total_seconds().to_numpy()
            coef = np.polyfit(xs, base[cols[0]].to_numpy(dtype=float), 1)
            tdf = pd.DataFrame({"ts": base["ts"], "valor": np.polyval(coef, xs), "Série": "Tendência"})
            layers.append(alt.Chart(tdf).mark_line(strokeDash=[6, 4], clip=True).encode(
                x="ts:T", y=enc_y, color=enc_c))
    return alt.layer(*layers).properties(height=260)

def _usage_card(title, total, used, fmt):
    """Desenha dentro do container atual: Total, Em uso e barra de percentual."""
    st.markdown(f"**{title}**")
    c_total, c_used = st.columns(2)
    c_total.metric("Total", fmt(total) if total else "—")
    if total and used is not None:
        pct = min(max(used / total, 0.0), 1.0)
        c_used.metric("Em uso", fmt(used))
        st.progress(pct, text=f"{_br(pct * 100, 2)}% em uso")
    else:
        c_used.metric("Em uso", "—")
        st.caption("Uso indisponível na API.")

# ==========================================
# HISTÓRICO POR HOST (mesmo padrão do histórico do cluster)
# ==========================================
HOST_FULLRES_DAYS = 35          # amostras de 5 min são mantidas assim por 35 dias; depois viram média por hora
_last_host_compaction = 0.0

def _collect_host_samples(cluster_name, now):
    """Grava uma amostra de cada host do cluster (uma linha por host)."""
    ok, hosts, _msg, _diag = get_host_metrics(cluster_name)
    if not ok:
        return 0
    rows = [(cluster_name, h["name"], now) + tuple(h["values"].get(c) for c in HOST_HIST_COLS) for h in hosts]
    if not rows:
        return 0
    cols = ", ".join(HOST_HIST_COLS)
    marks = ", ".join("?" for _ in range(3 + len(HOST_HIST_COLS)))
    conn = db()
    try:
        conn.executemany(f"INSERT INTO host_usage_history (cluster_name, host_name, ts, {cols}) VALUES ({marks})", rows)
        conn.commit()
    finally:
        conn.close()
    return len(rows)

def compact_host_history(now=None):
    """Troca as amostras de 5 min mais antigas que HOST_FULLRES_DAYS por UMA média por hora (o banco cresce ~12x menos).
    Idempotente: linhas que já são médias horárias continuam iguais. Os gráficos Semanal/Mensal/Anual já agregam por hora ou mais."""
    cutoff = (now or time.time()) - HOST_FULLRES_DAYS * 86400
    cols = ", ".join(HOST_HIST_COLS)
    avgs = ", ".join(f"AVG({c}) AS {c}" for c in HOST_HIST_COLS)
    conn = db()
    try:
        conn.execute("BEGIN IMMEDIATE")
        conn.execute("DROP TABLE IF EXISTS temp._hh")
        conn.execute(f"CREATE TEMP TABLE _hh AS SELECT cluster_name, host_name, "
                     f"CAST(ts / 3600 AS INTEGER) * 3600.0 AS ts, {avgs} FROM host_usage_history "
                     f"WHERE ts < ? GROUP BY cluster_name, host_name, CAST(ts / 3600 AS INTEGER)", (cutoff,))
        conn.execute("DELETE FROM host_usage_history WHERE ts < ?", (cutoff,))
        conn.execute(f"INSERT INTO host_usage_history (cluster_name, host_name, ts, {cols}) "
                     f"SELECT cluster_name, host_name, ts, {cols} FROM _hh")
        conn.execute("DROP TABLE _hh")
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()

def load_host_usage_df(cluster_name, host_name, days, rule=None):
    """Histórico de UM host já com as colunas derivadas (GHz, GiB, %, MB/s, ms).
    Em períodos agregados (rule) acrescenta '<coluna>_max' com o PICO do intervalo (a média esconde picos)."""
    cols = ", ".join(HOST_HIST_COLS)
    rows = _q(f"SELECT ts, {cols} FROM host_usage_history WHERE cluster_name = ? AND host_name = ? AND ts >= ? ORDER BY ts",
              (cluster_name, host_name, time.time() - days * 86400))
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows, columns=["ts"] + HOST_HIST_COLS)
    df[HOST_HIST_COLS] = df[HOST_HIST_COLS].apply(pd.to_numeric, errors="coerce")
    local_tz = datetime.now().astimezone().tzinfo
    df["ts"] = pd.to_datetime(df["ts"], unit="s", utc=True).dt.tz_convert(local_tz).dt.tz_localize(None)
    df["cpu_used_ghz"] = df["cpu_used"] / 1e9
    df["cpu_total_ghz"] = df["cpu_total"] / 1e9
    df["cpu_pct"] = df["cpu_used"] / df["cpu_total"] * 100
    df["mem_used_gib"] = df["mem_used"] / 1024**3
    df["mem_total_gib"] = df["mem_total"] / 1024**3
    df["mem_pct"] = df["mem_used"] / df["mem_total"] * 100
    for c in ("bw_total", "bw_read", "bw_write"):
        df[f"{c}_mbs"] = df[c] / 1024                      # kB/s -> MB/s
    for c in ("lat_avg", "lat_read", "lat_write", "hyp_lat"):
        df[f"{c}_ms"] = df[c] / 1000                       # µs -> ms
    df = df.replace([np.inf, -np.inf], np.nan)
    if rule:
        idx = df.set_index("ts")
        peak = idx[HOST_PEAK_COLS].resample(rule).max().add_suffix("_max")
        df = idx.resample(rule).mean().join(peak).dropna(how="all").reset_index()
    return df

HOST_PEAK_COLS = ["cpu_pct", "mem_pct", "lat_avg_ms", "iops_total"]

def _host_chart(title, df, series, ytitle, is_pct=False, trend=False, empty_msg=None):
    """Título + gráfico (mesmo estilo do cluster). Séries sem nenhum dado são omitidas."""
    st.markdown(f"**{title}**")
    avail = {label: col for label, col in series.items() if col in df.columns and df[col].notna().any()}
    if not avail:
        st.caption(empty_msg or "Métrica não disponível na API para este recurso.")
        return
    st.altair_chart(_usage_chart(df, avail, ytitle, is_pct=is_pct, trend=trend), **_FULL)

def _render_host_charts(df, is_year, has_peak):
    """Todos os gráficos de um período do host."""
    g1, g2 = st.columns(2)
    with g1:
        _host_chart("⚙️ CPU (GHz)", df, {"Em uso": "cpu_used_ghz", "Total": "cpu_total_ghz"}, "GHz", trend=is_year)
    with g2:
        s = {"Média": "cpu_pct", "Pico": "cpu_pct_max"} if has_peak else {"Uso %": "cpu_pct"}
        _host_chart("⚙️ CPU (%)", df, s, "%", is_pct=True, trend=is_year)
    g3, g4 = st.columns(2)
    with g3:
        _host_chart("🧠 Memória (GiB)", df, {"Em uso": "mem_used_gib", "Total": "mem_total_gib"}, "GiB", trend=is_year)
    with g4:
        s = {"Média": "mem_pct", "Pico": "mem_pct_max"} if has_peak else {"Uso %": "mem_pct"}
        _host_chart("🧠 Memória (%)", df, s, "%", is_pct=True, trend=is_year)
    g5, g6 = st.columns(2)
    with g5:
        s = {"Leitura": "iops_read", "Escrita": "iops_write", "Total": "iops_total"}
        if has_peak:
            s["Pico (total)"] = "iops_total_max"
        _host_chart("💽 IOPS", df, s, "IOPS")
    with g6:
        _host_chart("💽 Throughput (MB/s)", df,
                    {"Leitura": "bw_read_mbs", "Escrita": "bw_write_mbs", "Total": "bw_total_mbs"}, "MB/s")
    g7, g8 = st.columns(2)
    with g7:
        s = {"Média": "lat_avg_ms", "Leitura": "lat_read_ms", "Escrita": "lat_write_ms"}
        if has_peak:
            s["Pico (média)"] = "lat_avg_ms_max"
        _host_chart("⏱️ Latência de I/O (ms)", df, s, "ms")
    with g8:
        _host_chart("⏱️ Latência no hypervisor (ms)", df, {"Hypervisor": "hyp_lat_ms"}, "ms")
    g9, _g10 = st.columns(2)
    with g9:
        _host_chart("🗂️ VMs no host", df, {"VMs": "num_vms"}, "VMs")

def _fmt_num(v, decimals=0, suffix=""):
    return f"{_br(v, decimals)}{suffix}" if v is not None else "—"

# ==========================================
# HISTÓRICO DE STORAGE (mesma coleta de 5 min; virtual disks em intervalo maior)
# ==========================================
_last_vdisk_collect = {}
_last_storage_compaction = 0.0

def _collect_storage_samples(cluster_name, now):
    """Grava uma amostra de cada recurso de storage do cluster e atualiza a lista de recursos (dropdowns)."""
    cols = ", ".join(STORAGE_COLS)
    marks = ", ".join("?" for _ in range(4 + len(STORAGE_COLS)))
    for etype in STORAGE_ETYPES:
        if etype == "vdisk" and now - _last_vdisk_collect.get(cluster_name, 0) < VDISK_INTERVAL_SEC - 30:
            continue
        try:
            ok, ents, _msg, _diag = get_storage_metrics(cluster_name, etype)
        except Exception as e:
            logger.warning("Coleta de storage falhou (%s/%s): %s", _clean(cluster_name, 60), etype, _clean(repr(e), 200))
            continue
        if not ok or not ents:
            continue
        if etype == "vdisk":
            _last_vdisk_collect[cluster_name] = now
        rows = [(cluster_name, etype, p["id"], now) + tuple(p["values"].get(c) for c in STORAGE_COLS) for p in ents]
        meta = [(cluster_name, etype, p["id"], p["name"], json.dumps(p["info"], ensure_ascii=False), now) for p in ents]
        conn = db()
        try:
            conn.executemany(f"INSERT INTO storage_usage_history (cluster_name, entity_type, entity_id, ts, {cols}) "
                             f"VALUES ({marks})", rows)
            conn.executemany("INSERT OR REPLACE INTO storage_entities (cluster_name, entity_type, entity_id, entity_name, info, last_seen) "
                             "VALUES (?, ?, ?, ?, ?, ?)", meta)
            conn.commit()
        finally:
            conn.close()

def compact_storage_history(now=None):
    """Troca amostras antigas (ver STORAGE_FULLRES_DAYS) por UMA média por hora. Idempotente."""
    now = now or time.time()
    cols = ", ".join(STORAGE_COLS)
    avgs = ", ".join(f"AVG({c}) AS {c}" for c in STORAGE_COLS)
    for etype, days in STORAGE_FULLRES_DAYS.items():
        cutoff = now - days * 86400
        conn = db()
        try:
            conn.execute("BEGIN IMMEDIATE")
            conn.execute("DROP TABLE IF EXISTS temp._sh")
            conn.execute(f"CREATE TEMP TABLE _sh AS SELECT cluster_name, entity_type, entity_id, "
                         f"CAST(ts / 3600 AS INTEGER) * 3600.0 AS ts, {avgs} FROM storage_usage_history "
                         f"WHERE entity_type = ? AND ts < ? "
                         f"GROUP BY cluster_name, entity_type, entity_id, CAST(ts / 3600 AS INTEGER)", (etype, cutoff))
            conn.execute("DELETE FROM storage_usage_history WHERE entity_type = ? AND ts < ?", (etype, cutoff))
            conn.execute(f"INSERT INTO storage_usage_history (cluster_name, entity_type, entity_id, ts, {cols}) "
                         f"SELECT cluster_name, entity_type, entity_id, ts, {cols} FROM _sh")
            conn.execute("DROP TABLE _sh")
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()

STORAGE_PEAK_COLS = ["lat_avg_ms", "iops_total"]

def load_storage_df(cluster_name, etype, entity_id, days, rule=None):
    """Histórico de UM recurso de storage com colunas derivadas (GiB, %, MB/s, ms); picos '<col>_max' nos períodos agregados."""
    cols = ", ".join(STORAGE_COLS)
    rows = _q(f"SELECT ts, {cols} FROM storage_usage_history WHERE cluster_name = ? AND entity_type = ? AND entity_id = ? "
              f"AND ts >= ? ORDER BY ts", (cluster_name, etype, entity_id, time.time() - days * 86400))
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows, columns=["ts"] + STORAGE_COLS)
    df[STORAGE_COLS] = df[STORAGE_COLS].apply(pd.to_numeric, errors="coerce")
    local_tz = datetime.now().astimezone().tzinfo
    df["ts"] = pd.to_datetime(df["ts"], unit="s", utc=True).dt.tz_convert(local_tz).dt.tz_localize(None)
    for c in ("used", "cap", "free", "logical_used", "saving"):
        df[f"{c}_gib"] = df[f"{c}_bytes"] / 1024**3
    df["used_pct"] = df["used_bytes"] / df["cap_bytes"] * 100
    for c in ("bw_total", "bw_read", "bw_write"):
        df[f"{c}_mbs"] = df[c] / 1024
    for c in ("lat_avg", "lat_read", "lat_write"):
        df[f"{c}_ms"] = df[c] / 1000
    df = df.replace([np.inf, -np.inf], np.nan)
    if rule:
        idx = df.set_index("ts")
        peak = idx[STORAGE_PEAK_COLS].resample(rule).max().add_suffix("_max")
        df = idx.resample(rule).mean().join(peak).dropna(how="all").reset_index()
    return df

def storage_forecast(cluster_name, etype, entity_id):
    """Crescimento do espaço usado (últimos 30 dias, médias diárias) e dias até encher. None se faltar histórico."""
    df = load_storage_df(cluster_name, etype, entity_id, 30, "1D")
    if df.empty or "used_bytes" not in df:
        return None
    d = df.dropna(subset=["used_bytes"])
    if len(d) < 4:
        return None
    xs = (d["ts"] - d["ts"].min()).dt.total_seconds().to_numpy() / 86400
    slope = float(np.polyfit(xs, d["used_bytes"].to_numpy(dtype=float), 1)[0])       # bytes por dia
    # valor ATUAL = última amostra bruta (a média do dia corrente ficaria atrasada em relação ao uso real)
    recent = load_storage_df(cluster_name, etype, entity_id, 2, None).dropna(subset=["used_bytes"])
    last = recent.iloc[-1] if len(recent) else d.iloc[-1]
    used_now = float(last["used_bytes"])
    cap_now = last["cap_bytes"] if pd.notna(last["cap_bytes"]) else None
    days_left = None
    if slope > 0 and cap_now:
        days_left = max((float(cap_now) - used_now) / slope, 0.0)
    return {"slope_bytes_day": slope, "days_left": days_left, "points": len(d)}

def _storage_options(cluster_name, etype, live):
    """Recursos para o dropdown: os já gravados (vistos nos últimos 30 dias) + os que a API acabou de devolver.
    Retorna ({id: nome}, {id: info}) ordenado pelo nome."""
    names, infos = {}, {}
    for ent_id, name, info in _q("SELECT entity_id, entity_name, info FROM storage_entities WHERE cluster_name = ? "
                                 "AND entity_type = ? AND last_seen >= ?", (cluster_name, etype, time.time() - 30 * 86400)):
        names[ent_id] = name
        try:
            infos[ent_id] = json.loads(info or "{}")
        except ValueError:
            infos[ent_id] = {}
    for p in live:
        names[p["id"]] = p["name"]
        infos[p["id"]] = p["info"]
    order = sorted(names, key=lambda i: (str(names[i]).lower(), i))
    return {i: names[i] for i in order}, infos

def _render_storage_charts(df, etype, is_year, has_peak):
    """Gráficos de um período para um recurso de storage."""
    g1, g2 = st.columns(2)
    with g1:
        s = {"Usado": "used_gib", "Capacidade": "cap_gib"}
        if etype in ("pool", "container"):
            s["Uso lógico"] = "logical_used_gib"
        _host_chart("💾 Espaço (GiB)", df, s, "GiB", trend=is_year)
    with g2:
        _host_chart("💾 Espaço usado (%)", df, {"Uso %": "used_pct"}, "%", is_pct=True, trend=is_year)
    g3, g4 = st.columns(2)
    with g3:
        s = {"Leitura": "iops_read", "Escrita": "iops_write", "Total": "iops_total"}
        if has_peak:
            s["Pico (total)"] = "iops_total_max"
        _host_chart("💽 IOPS", df, s, "IOPS")
    with g4:
        _host_chart("💽 Throughput (MB/s)", df,
                    {"Leitura": "bw_read_mbs", "Escrita": "bw_write_mbs", "Total": "bw_total_mbs"}, "MB/s")
    g5, g6 = st.columns(2)
    with g5:
        s = {"Média": "lat_avg_ms", "Leitura": "lat_read_ms", "Escrita": "lat_write_ms"}
        if has_peak:
            s["Pico (média)"] = "lat_avg_ms_max"
        _host_chart("⏱️ Latência de I/O (ms)", df, s, "ms")
    with g6:
        _host_chart("📏 Tamanho médio de I/O (KB)", df, {"Médio": "io_size_kb"}, "KB")
    g7, g8 = st.columns(2)
    with g7:
        _host_chart("🔀 Perfil de I/O (%)", df, {"Leitura %": "read_pct", "Aleatório %": "random_pct"}, "%", is_pct=True)
    with g8:
        if etype == "container":
            _host_chart("🗜️ Redução de dados (razão)", df, {"Razão (x:1)": "saving_ratio"}, "x:1")
        elif etype == "pool":
            _host_chart("🗜️ Economia de dados (GiB)", df, {"Economizado": "saving_gib"}, "GiB")

def _render_storage_entity(cluster_name, etype, is_admin):
    """Dropdown + cartões atuais + gráficos por período de um tipo de recurso de storage."""
    label = STORAGE_ETYPES[etype]["label"]
    with st.spinner(f"Consultando {label}..."):
        ok, live, msg, diag = get_storage_metrics(cluster_name, etype)
    if not ok:
        st.warning(f"Situação atual indisponível: {_md(msg)} Os gráficos usam o histórico gravado.")
        _c = get_cluster_credentials(cluster_name)
        if _c and _c[3] and not get_element_access(cluster_name):
            st.info("Este cluster é gerenciado por um Prism Central e **ainda não tem acesso direto ao Prism Element** "
                    "configurado. Vá em **Gerenciar Cluster > Acesso direto ao Prism Element**.")
    names, infos = _storage_options(cluster_name, etype, live if ok else [])
    if not names:
        st.info(f"Nenhum recurso do tipo {label} encontrado ainda neste cluster.")
        if is_admin and diag:
            with st.expander("🔧 Diagnóstico da API", expanded=True):
                st.code("\n".join(diag), language=None)
        return
    ids = list(names)
    dup = {n for n in names.values() if list(names.values()).count(n) > 1}
    sel = st.selectbox(label, ids, key=f"stor_sel_{cluster_name}_{etype}", help="Digite para filtrar a lista.",
                       format_func=lambda i: names[i] + (f" [{i[:8]}]" if names[i] in dup else ""))
    cur = next((p for p in live if p["id"] == sel), None) if ok else None
    if ok and cur is None:
        st.caption("A API não retornou este recurso agora; os gráficos usam o histórico gravado.")
    v = cur["values"] if cur else {}
    info = (cur["info"] if cur else infos.get(sel)) or {}

    if etype in ("pool", "container") and ok:
        with st.expander(f"⚖️ Todos os {label}s do cluster (agora)"):
            rows = []
            for p in live:
                pv = p["values"]
                pct = pv["used_bytes"] / pv["cap_bytes"] * 100 if pv.get("used_bytes") is not None and pv.get("cap_bytes") else None
                rows.append({label: p["name"], "Usado %": pct,
                             "Usado (GiB)": pv["used_bytes"] / 1024**3 if pv.get("used_bytes") is not None else None,
                             "Capacidade (GiB)": pv["cap_bytes"] / 1024**3 if pv.get("cap_bytes") else None,
                             "IOPS": pv.get("iops_total"),
                             "Latência (ms)": pv["lat_avg"] / 1000 if pv.get("lat_avg") is not None else None})
            st.dataframe(pd.DataFrame(rows).round(2), hide_index=True, **_FULL)

    a1, a2 = st.columns(2)
    with a1:
        with st.container(border=True):
            _usage_card("💾 Espaço", v.get("cap_bytes"), v.get("used_bytes"), _fmt_bytes)
            if v.get("free_bytes") is not None:
                st.caption(f"Livre: {_fmt_bytes(v['free_bytes'])}")
    with a2:
        with st.container(border=True):
            if etype in ("pool", "container"):
                st.markdown("**📅 Tendência de crescimento (30 dias)**")
                fc = storage_forecast(cluster_name, etype, sel)
                if fc is None:
                    st.caption("Histórico insuficiente (precisa de alguns dias de coleta).")
                else:
                    c1, c2 = st.columns(2)
                    c1.metric("Crescimento", f"{_br(fc['slope_bytes_day'] / 1024**3, 2)} GiB/dia")
                    if fc["slope_bytes_day"] <= 0:
                        c2.metric("Previsão de esgotamento", "Estável")
                    elif fc["days_left"] is None:
                        c2.metric("Previsão de esgotamento", "—")
                    elif fc["days_left"] > 3650:
                        c2.metric("Previsão de esgotamento", "> 10 anos")
                    else:
                        c2.metric("Previsão de esgotamento", f"{_br(fc['days_left'], 0)} dias")
                    st.caption(f"Estimativa linear com {fc['points']} dia(s) de histórico; não considera sazonalidade.")
            else:
                st.markdown("**ℹ️ Detalhes**")
            if info:
                st.caption(" · ".join(f"{_md(k)}: {_md(x)}" for k, x in info.items()))

    k1, k2, k3, k4 = st.columns(4)
    with k1:
        with st.container(border=True):
            st.metric("💽 IOPS", _fmt_num(v.get("iops_total")))
            st.caption(f"Leitura {_fmt_num(v.get('iops_read'))} · Escrita {_fmt_num(v.get('iops_write'))}")
    with k2:
        with st.container(border=True):
            mb = lambda x: x / 1024 if x is not None else None
            st.metric("💽 Throughput", _fmt_num(mb(v.get("bw_total")), 1, " MB/s"))
            st.caption(f"Leitura {_fmt_num(mb(v.get('bw_read')), 1)} · Escrita {_fmt_num(mb(v.get('bw_write')), 1)}")
    with k3:
        with st.container(border=True):
            ms = lambda x: x / 1000 if x is not None else None
            st.metric("⏱️ Latência de I/O", _fmt_num(ms(v.get("lat_avg")), 2, " ms"))
            st.caption(f"Leitura {_fmt_num(ms(v.get('lat_read')), 2)} · Escrita {_fmt_num(ms(v.get('lat_write')), 2)}")
    with k4:
        with st.container(border=True):
            if etype == "container" and v.get("saving_ratio") is not None:
                st.metric("🗜️ Redução de dados", f"{_br(v['saving_ratio'], 2)} : 1")
                st.caption(f"Economizado: {_fmt_bytes(v['saving_bytes'])}" if v.get("saving_bytes") is not None else "—")
            else:
                st.metric("📏 Tamanho médio de I/O", _fmt_num(v.get("io_size_kb"), 1, " KB"))
                st.caption(f"Leitura {_fmt_num(v.get('read_pct'), 0)}% · Aleatório {_fmt_num(v.get('random_pct'), 0)}%")

    period_tabs = st.tabs([p[0] for p in USAGE_PERIODS])
    for tab, (p_label, p_days, p_rule) in zip(period_tabs, USAGE_PERIODS):
        with tab:
            s_df = load_storage_df(cluster_name, etype, sel, p_days, p_rule)
            if s_df.empty:
                st.info("Ainda não há amostras deste recurso neste período. A coleta é feita a cada 5 minutos"
                        + (f" (virtual disks: a cada {VDISK_INTERVAL_SEC // 60} min)" if etype == "vdisk" else "")
                        + " e o histórico vai se formando aos poucos.")
                continue
            is_year = p_label == "Anual"
            _render_storage_charts(s_df, etype, is_year=is_year, has_peak=bool(p_rule))
            st.caption(f"{len(s_df)} ponto(s) no período"
                       + (" · médias de 1 dia · linha tracejada = tendência · 'Pico' = maior valor do dia" if is_year else
                          f" · médias de {p_rule.replace('min', ' min')} · 'Pico' = maior valor do intervalo" if p_rule
                          else " · amostras de 5 min"))
    if is_admin and diag:
        with st.expander("🔧 Diagnóstico da API (storage)", expanded=not ok):
            st.caption("Mostra só nomes de métricas e valores numéricos (sem credenciais). "
                       "Métricas sem dado em nenhum registro aparecem na última linha.")
            st.code("\n".join(diag) or "-", language=None)

# ==========================================
# VMs: COLETA PARA CAPACITY / RIGHT-SIZING (CPU e memória por VM, a cada 5 min)
# ==========================================
VM_COLLECT_ENABLED = _env_int("NUTMETRICS_COLLECT_VMS", 1) == 1
VM_FULLRES_DAYS = max(1, _env_int("NUTMETRICS_VM_FULLRES_DAYS", 7))    # dias no detalhe de 5 min; depois 1 linha por hora
# coluna -> função de agregação ao compactar para hora. Os picos (*_max) são preservados: right-sizing depende deles.
VM_AGG = {"powered_on": "AVG", "vcpu": "MAX", "mem_cfg_bytes": "MAX",
          "cpu_pct": "AVG", "cpu_pct_max": "MAX",
          "mem_used_bytes": "AVG", "mem_pct": "AVG", "mem_pct_max": "MAX", "mem_hyp_pct": "AVG",
          "iops_total": "AVG", "bw_total": "AVG", "lat_avg": "AVG"}
VM_COLS = list(VM_AGG)
_last_vm_compaction = 0.0

def _vm_stat(ent, key):
    return _find_stat(ent, key)

def _parse_vm(ent):
    """VM da API (v1: vmName/numVCpus/memoryCapacityInBytes/powerState/hostUuid; v2.0: name/num_vcpus/memory_mb/...)
    -> {'id', 'name', 'host_uuid', 'host_name', 'values'} ou None (sem uuid ou VM de controle do cluster)."""
    if ent.get("controllerVm") or ent.get("controller_vm"):
        return None
    vm_id = _first_value(ent, ["uuid", "vmId", "vm_uuid"])
    if not vm_id:
        return None
    power = str(ent.get("powerState") or ent.get("power_state") or "").lower()
    on = power == "on"
    vcpu = _to_float(ent.get("numVCpus") if ent.get("numVCpus") is not None else ent.get("num_vcpus"))
    mem_cfg = _to_float(ent.get("memoryCapacityInBytes"))
    if mem_cfg is None and _to_float(ent.get("memory_mb")) is not None:
        mem_cfg = _to_float(ent.get("memory_mb")) * 1024 * 1024
    v = {c: None for c in VM_COLS}
    v.update(powered_on=1.0 if on else 0.0, vcpu=vcpu, mem_cfg_bytes=mem_cfg)
    if on:
        cpu_ppm = _vm_stat(ent, "hypervisor_cpu_usage_ppm")
        if cpu_ppm is not None:
            v["cpu_pct"] = v["cpu_pct_max"] = min(cpu_ppm / 10000.0, 100.0)          # 1.000.000 ppm = 100%
        # memória do convidado (exige NGT/driver). Valor 0 = "sem informação", não "0% de uso" (o script antigo gravava 0%).
        used = _vm_stat(ent, "guest.memory_usage_bytes")
        if used is not None and used > 0:
            v["mem_used_bytes"] = used
            if mem_cfg:
                v["mem_pct"] = v["mem_pct_max"] = min(used / mem_cfg * 100.0, 100.0)
        hyp = _vm_stat(ent, "hypervisor_memory_usage_ppm")
        if hyp is not None:
            v["mem_hyp_pct"] = min(hyp / 10000.0, 100.0)
        for col, key in (("iops_total", "controller_num_iops"), ("bw_total", "controller_io_bandwidth_kBps"),
                         ("lat_avg", "controller_avg_io_latency_usecs")):
            v[col] = _vm_stat(ent, key)
    return {"id": vm_id, "name": _clean(ent.get("vmName") or ent.get("name") or "SEM_NOME", 120),
            "host_uuid": _first_value(ent, ["hostUuid", "host_uuid"]),
            "host_name": _clean(ent.get("hostName") or "", 80) or None, "values": v}

@st.cache_data(ttl=60, show_spinner=False)
def fetch_vm_entities(ip, port, kind, proxy_uuid):
    """Todas as VMs de UM cluster com CPU/memória atuais, em UMA consulta paginada à API v1 (/vms)
    (o script antigo fazia 1 consulta por VM). Retorna (ok, lista, mensagem, diagnóstico)."""
    session, err = _endpoint_session(ip, port)
    if session is None:
        return False, [], err, []
    target = f"{ip}:{port}"
    try:
        raw, diag, status = _storage_list(session, ip, port, kind, proxy_uuid, "vms", v1_first=True)
        if status != 200:
            return False, [], _storage_error_message(kind, status).replace("de storage", "de VMs"), diag
        parsed = [p for p in (_parse_vm(e) for e in raw) if p]
        if parsed and all(p["values"]["cpu_pct"] is None and p["values"]["powered_on"] for p in parsed):
            diag.append("nenhuma VM ligada trouxe hypervisor_cpu_usage_ppm: a lista da API pode não incluir 'stats'")
        no_mem = sum(1 for p in parsed if p["values"]["powered_on"] and p["values"]["mem_pct"] is None)
        diag.append(f"VMs: {len(parsed)} (sem memória do convidado, ex.: sem NGT: {no_mem})")
    except requests.exceptions.HTTPError as e:
        code = e.response.status_code if e.response is not None else "?"
        logger.warning("API de VMs retornou HTTP %s (%s)", code, _clean(target, 100))
        return False, [], f"A API de VMs retornou HTTP {code}.", []
    except Exception as e:
        return False, [], api_error_message(e, target), []
    finally:
        session.close()
    return True, parsed, "", diag

def get_vm_metrics(cluster_name):
    """VMs de UM cluster (direto no Prism Element quando houver acesso direto). Retorna (ok, lista, mensagem, diagnóstico)."""
    return _route_cluster_fetch(cluster_name, fetch_vm_entities)

def _collect_vm_samples(cluster_name, now):
    """Grava uma amostra de cada VM do cluster e atualiza o cadastro de VMs (nome/host atuais)."""
    ok, vms, msg, _diag = get_vm_metrics(cluster_name)
    if not ok:
        logger.warning("Coleta de VMs indisponível (%s): %s", _clean(cluster_name, 60), _clean(msg, 200))
        return 0
    if not vms:
        return 0
    cols = ", ".join(VM_COLS)
    marks = ", ".join("?" for _ in range(3 + len(VM_COLS)))
    rows = [(cluster_name, p["id"], now) + tuple(p["values"].get(c) for c in VM_COLS) for p in vms]
    meta = [(cluster_name, p["id"], p["name"], p["host_uuid"], p["host_name"], now) for p in vms]
    conn = db()
    try:
        conn.executemany(f"INSERT INTO vm_usage_history (cluster_name, vm_uuid, ts, {cols}) VALUES ({marks})", rows)
        conn.executemany("INSERT OR REPLACE INTO vm_entities (cluster_name, vm_uuid, vm_name, host_uuid, host_name, last_seen) "
                         "VALUES (?, ?, ?, ?, ?, ?)", meta)
        conn.commit()
    finally:
        conn.close()
    logger.info("VMs coletadas (%s): %d", _clean(cluster_name, 60), len(rows))
    return len(rows)

def compact_vm_history(now=None):
    """Amostras de 5 min mais antigas que VM_FULLRES_DAYS viram UMA linha por hora: média das métricas e MÁXIMO dos picos
    (cpu_pct_max, mem_pct_max). Idempotente."""
    cutoff = (now or time.time()) - VM_FULLRES_DAYS * 86400
    cols = ", ".join(VM_COLS)
    aggs = ", ".join(f"{fn}({c}) AS {c}" for c, fn in VM_AGG.items())
    conn = db()
    try:
        conn.execute("BEGIN IMMEDIATE")
        conn.execute("DROP TABLE IF EXISTS temp._vh")
        conn.execute(f"CREATE TEMP TABLE _vh AS SELECT cluster_name, vm_uuid, CAST(ts / 3600 AS INTEGER) * 3600.0 AS ts, {aggs} "
                     f"FROM vm_usage_history WHERE ts < ? GROUP BY cluster_name, vm_uuid, CAST(ts / 3600 AS INTEGER)", (cutoff,))
        conn.execute("DELETE FROM vm_usage_history WHERE ts < ?", (cutoff,))
        conn.execute(f"INSERT INTO vm_usage_history (cluster_name, vm_uuid, ts, {cols}) "
                     f"SELECT cluster_name, vm_uuid, ts, {cols} FROM _vh")
        conn.execute("DROP TABLE _vh")
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()

# ==========================================
# DASHBOARD DE VMs (histórico em vm_usage_history; mesmo padrão dos dashboards de Host e Storage)
# ==========================================
def _vm_options(cluster_name, include_id=None):
    """VMs do cluster para os menus de seleção: as vistas nos últimos 30 dias (+ a indicada em include_id).
    Retorna ({vm_uuid: nome}, {vm_uuid: nome do host}) ordenado pelo nome."""
    rows = _q("SELECT vm_uuid, vm_name, host_name FROM vm_entities WHERE cluster_name = ? AND last_seen >= ?",
              (cluster_name, time.time() - 30 * 86400))
    if include_id and include_id not in {r[0] for r in rows}:
        rows = rows + _q("SELECT vm_uuid, vm_name, host_name FROM vm_entities WHERE cluster_name = ? AND vm_uuid = ?",
                         (cluster_name, include_id))
    rows = sorted(rows, key=lambda r: (str(r[1] or "").lower(), r[0]))
    return {r[0]: (r[1] or r[0]) for r in rows}, {r[0]: r[2] for r in rows}

def _vm_label_fn(names):
    """Rótulo do dropdown; acrescenta o início do UUID quando há nomes repetidos."""
    values = list(names.values())
    return lambda i: names[i] + (f" [{i[:8]}]" if values.count(names[i]) > 1 else "")

def load_vm_df(cluster_name, vm_uuid, days, rule=None):
    """Histórico de UMA VM com colunas derivadas (vCPUs em uso, GiB, MB/s, ms). Nos períodos agregados os picos
    (cpu_pct_max, mem_pct_max) usam o MÁXIMO do intervalo; as demais métricas, a média."""
    cols = ", ".join(VM_COLS)
    rows = _q(f"SELECT ts, {cols} FROM vm_usage_history WHERE cluster_name = ? AND vm_uuid = ? AND ts >= ? ORDER BY ts",
              (cluster_name, vm_uuid, time.time() - days * 86400))
    if not rows:
        return pd.DataFrame()
    df = pd.DataFrame(rows, columns=["ts"] + VM_COLS)
    df[VM_COLS] = df[VM_COLS].apply(pd.to_numeric, errors="coerce")
    local_tz = datetime.now().astimezone().tzinfo
    df["ts"] = pd.to_datetime(df["ts"], unit="s", utc=True).dt.tz_convert(local_tz).dt.tz_localize(None)
    if rule:
        agg = {c: ("max" if fn == "MAX" else "mean") for c, fn in VM_AGG.items()}
        df = df.set_index("ts").resample(rule).agg(agg).dropna(how="all").reset_index()
    df["vcpu_used"] = df["cpu_pct"] / 100 * df["vcpu"]
    df["vcpu_used_max"] = df["cpu_pct_max"] / 100 * df["vcpu"]
    df["mem_used_gib"] = df["mem_used_bytes"] / 1024**3
    df["mem_cfg_gib"] = df["mem_cfg_bytes"] / 1024**3
    df["mem_free_gib"] = (df["mem_cfg_bytes"] - df["mem_used_bytes"]) / 1024**3
    df["bw_mbs"] = df["bw_total"] / 1024
    df["lat_ms"] = df["lat_avg"] / 1000
    df["on_pct"] = df["powered_on"] * 100
    return df.replace([np.inf, -np.inf], np.nan)

def _render_vm_charts(df, is_year, has_peak):
    """Resumo do período + todos os gráficos de uma aba de período da VM."""
    cpu_avg, cpu_peak = df["cpu_pct"].mean(), df["cpu_pct_max"].max()
    mem_avg, mem_peak = df["mem_pct"].mean(), df["mem_pct_max"].max()
    s1, s2, s3, s4 = st.columns(4)
    s1.metric("CPU média", _fmt_num(None if pd.isna(cpu_avg) else cpu_avg, 1, "%"))
    s2.metric("CPU pico", _fmt_num(None if pd.isna(cpu_peak) else cpu_peak, 1, "%"))
    s3.metric("Memória média", _fmt_num(None if pd.isna(mem_avg) else mem_avg, 1, "%"))
    s4.metric("Memória pico", _fmt_num(None if pd.isna(mem_peak) else mem_peak, 1, "%"))
    if pd.isna(mem_avg):
        st.caption("Sem memória do convidado neste período (a VM precisa do NGT/driver para informar o uso real).")
    none_msg = "Sem dados desta métrica neste período."
    g1, g2 = st.columns(2)
    with g1:
        s = {"Média": "cpu_pct", "Pico": "cpu_pct_max"} if has_peak else {"Uso %": "cpu_pct"}
        _host_chart("⚙️ CPU (%)", df, s, "%", is_pct=True, trend=is_year, empty_msg=none_msg)
    with g2:
        s = {"Em uso": "vcpu_used", "Configuradas": "vcpu"}
        if has_peak:
            s["Pico"] = "vcpu_used_max"
        _host_chart("⚙️ vCPUs em uso", df, s, "vCPU", empty_msg=none_msg)
    g3, g4 = st.columns(2)
    with g3:
        _host_chart("🧠 Memória (GiB)", df, {"Usada": "mem_used_gib", "Configurada": "mem_cfg_gib"}, "GiB",
                    trend=is_year, empty_msg=none_msg)
    with g4:
        s = {"Convidado": "mem_pct"}
        if has_peak:
            s["Pico (convidado)"] = "mem_pct_max"
        s["Hypervisor"] = "mem_hyp_pct"
        _host_chart("🧠 Memória (%)", df, s, "%", is_pct=True, trend=is_year, empty_msg=none_msg)
    g5, g6 = st.columns(2)
    with g5:
        _host_chart("🧠 Memória livre (GiB)", df, {"Livre": "mem_free_gib"}, "GiB", empty_msg=none_msg)
    with g6:
        _host_chart("🔌 Tempo ligada (%)", df, {"Ligada": "on_pct"}, "%", is_pct=True, empty_msg=none_msg)
    g7, g8 = st.columns(2)
    with g7:
        _host_chart("💽 IOPS", df, {"Total": "iops_total"}, "IOPS", empty_msg=none_msg)
    with g8:
        _host_chart("💽 Throughput (MB/s)", df, {"Total": "bw_mbs"}, "MB/s", empty_msg=none_msg)
    g9, _g10 = st.columns(2)
    with g9:
        _host_chart("⏱️ Latência de I/O (ms)", df, {"Média": "lat_ms"}, "ms", empty_msg=none_msg)

def _open_vm(cluster_name, vm_uuid):
    """Abre o dashboard da VM (usado por botões e pelo menu de seleção)."""
    names, _hosts = _vm_options(cluster_name, include_id=vm_uuid)
    st.session_state.vm_view = (cluster_name, vm_uuid)
    st.session_state.host_view = None
    st.session_state.storage_cluster = None
    st.session_state.usage_cluster = None
    st.session_state.alerts_cluster = None
    st.session_state.show_cluster_management = False
    st.session_state.show_user_management = False
    audit("VM_ABERTA", f"{cluster_name}/{_clean(names.get(vm_uuid, vm_uuid), 80)}")

def _on_vm_pick(cluster_name, widget_key):
    """Chamado quando uma VM é escolhida no menu lateral: abre o dashboard dela."""
    vm_uuid = st.session_state.get(widget_key)
    if vm_uuid:
        _open_vm(cluster_name, vm_uuid)

# ==========================================
# COMPATIBILIDADE DE VERSÕES DO STREAMLIT
# ==========================================
try:
    _ST_VER = tuple(int(x) for x in st.__version__.split(".")[:2])
except Exception:
    _ST_VER = (0, 0)
_FULL = {"width": "stretch"} if _ST_VER >= (1, 50) else {"use_container_width": True}

# ==========================================
# ESTADO DE SESSÃO
# ==========================================
SESSION_DEFAULTS = {
    "logged_in": False, "username": "", "full_name": "", "role": "", "must_change": False,
    "show_user_management": False, "show_cluster_management": False, "alerts_cluster": None, "usage_cluster": None, "host_view": None, "storage_cluster": None, "vm_view": None,
    "pending_cluster": None, "pending_direct": None, "direct_ip_guess": None, "direct_msg": None, "cluster_msg": None, "last_activity": 0.0, "login_time": 0.0, "session_msg": None,
}

def _logout(message=None):
    for k, v in SESSION_DEFAULTS.items():
        st.session_state[k] = v
    fetch_active_alerts.clear()
    fetch_host_stats.clear()
    fetch_host_metrics.clear()
    fetch_storage_entities.clear()
    fetch_vm_entities.clear()
    if message:
        st.session_state.session_msg = message

def _open_usage(name):
    st.session_state.usage_cluster = name
    st.session_state.alerts_cluster = None
    st.session_state.host_view = None
    st.session_state.storage_cluster = None
    st.session_state.vm_view = None
    st.session_state.show_cluster_management = False
    st.session_state.show_user_management = False
    audit("UTILIZACAO_ABERTA", name)
    st.rerun()

def _sidebar_cluster(el, key_prefix):
    """Bloco de um cluster no menu lateral (usado tanto sob um Prism Central quanto em 'Clusters Isolados')."""
    cluster_name = el[0]
    hosts_in_cluster = get_hosts_by_cluster(cluster_name)
    with st.expander(f"  **{_md(cluster_name)}**", expanded=True):
        if st.button("🔔 Alertas", key=f"alerts_{key_prefix}_{cluster_name}", **_FULL):
            _open_alerts(cluster_name)
        if st.button("📈 Utilização", key=f"usage_{key_prefix}_{cluster_name}", **_FULL):
            _open_usage(cluster_name)
        if st.button("💾 Storage", key=f"storage_{key_prefix}_{cluster_name}", **_FULL):
            _open_storage(cluster_name)
        with st.expander("VMs", expanded=False):
            vm_names, _vm_hosts = _vm_options(cluster_name)
            if vm_names:
                pick_key = f"vmpick_{key_prefix}_{cluster_name}"
                pick_kw = {"index": None, "placeholder": "Escolher VM..."} if _ST_VER >= (1, 29) else {}
                st.selectbox("Escolha a VM", list(vm_names), key=pick_key, format_func=_vm_label_fn(vm_names),
                             label_visibility="collapsed", on_change=_on_vm_pick, args=(cluster_name, pick_key), **pick_kw)
                picked = st.session_state.get(pick_key)
                if picked and st.session_state.vm_view != (cluster_name, picked):
                    if st.button("📊 Abrir dashboard da VM", key=f"vmopen_{key_prefix}_{cluster_name}", **_FULL):
                        _open_vm(cluster_name, picked)
                        st.rerun()
                st.caption(f"{len(vm_names)} VM(s)")
            else:
                st.text("           Nenhuma VM coletada ainda")
        with st.expander("Host", expanded=False):
            if hosts_in_cluster:
                for h_name, h_ip in hosts_in_cluster:
                    if st.button(f"🖥️ {_md(h_name)}", key=f"host_{key_prefix}_{cluster_name}_{h_name}", **_FULL):
                        _open_host(cluster_name, h_name)
            else:
                st.text("           Nenhum host")

def _open_storage(cluster_name):
    st.session_state.storage_cluster = cluster_name
    st.session_state.vm_view = None
    st.session_state.host_view = None
    st.session_state.usage_cluster = None
    st.session_state.alerts_cluster = None
    st.session_state.show_cluster_management = False
    st.session_state.show_user_management = False
    audit("STORAGE_ABERTO", cluster_name)
    st.rerun()

def _open_host(cluster_name, host_name):
    st.session_state.storage_cluster = None
    st.session_state.vm_view = None
    st.session_state.host_view = (cluster_name, host_name)
    st.session_state.usage_cluster = None
    st.session_state.alerts_cluster = None
    st.session_state.show_cluster_management = False
    st.session_state.show_user_management = False
    audit("HOST_ABERTO", f"{cluster_name}/{host_name}")
    st.rerun()

def _open_alerts(name):
    st.session_state.alerts_cluster = name
    st.session_state.usage_cluster = None
    st.session_state.host_view = None
    st.session_state.storage_cluster = None
    st.session_state.vm_view = None
    st.session_state.show_cluster_management = False
    st.session_state.show_user_management = False
    audit("ALERTAS_ABERTOS", name)
    st.rerun()

init_db()
_start_usage_collector()

for _k, _v in SESSION_DEFAULTS.items():
    if _k not in st.session_state:
        st.session_state[_k] = _v

# Expiração por inatividade/duração máxima e revalidação do utilizador a cada interação
if st.session_state.logged_in:
    _now = time.time()
    if (_now - st.session_state.last_activity > SESSION_IDLE_MIN * 60
            or _now - st.session_state.login_time > SESSION_MAX_HOURS * 3600):
        audit("SESSAO_EXPIRADA")
        _logout("Sessão expirada por inatividade. Faça login novamente.")
        st.rerun()
    _row = _q("SELECT role, full_name FROM users WHERE username = ?", (st.session_state.username,), one=True)
    if _row is None:
        audit("SESSAO_ENCERRADA", "utilizador removido")
        _logout("A sua sessão foi encerrada.")
        st.rerun()
    st.session_state.role, st.session_state.full_name = _row[0], _row[1]
    st.session_state.last_activity = _now

# ==========================================
# 1. TELA DE LOGIN
# ==========================================
if not st.session_state.logged_in:
    st.markdown("""
        <style>
            .stApp {
                background-color: #1f3324;
            }
            .stDeployButton {display:none;}
            header {visibility: hidden;}
            .stTextInput label {
                color: #ffffff !important;
            }
        </style>
    """, unsafe_allow_html=True)

    _, col_centro, _ = st.columns([1.2, 1.5, 1.2])

    with col_centro:
        st.markdown("<br><br>", unsafe_allow_html=True)

        try:
            st.image("logo.svg", **_FULL)
        except Exception:
            st.markdown("<h1 style='text-align: center; color: white;'>NUTMETRICS</h1>", unsafe_allow_html=True)

        st.markdown("<br>", unsafe_allow_html=True)

        if st.session_state.session_msg:
            st.warning(st.session_state.session_msg)
            st.session_state.session_msg = None

        st.markdown("<h3 style='color: white; text-align: center;'>Iniciar Sessão</h3>", unsafe_allow_html=True)
        username = st.text_input("Utilizador", placeholder="Digite seu utilizador", key="login_user")
        password = st.text_input("Palavra-passe", type="password", placeholder="Digite sua palavra-passe", key="login_pass")

        st.markdown("<br>", unsafe_allow_html=True)

        if st.button("ENTRAR", type="primary", key="login_btn", **_FULL):
            status, data = authenticate(username, password)
            if status == "ok":
                _t = time.time()
                st.session_state.logged_in = True
                st.session_state.username = username.strip()
                st.session_state.full_name = data["full_name"]
                st.session_state.role = data["role"]
                st.session_state.must_change = data["must_change"]
                st.session_state.last_activity = _t
                st.session_state.login_time = _t
                audit("LOGIN_OK", username=username.strip())
                st.rerun()
            elif status == "locked":
                st.error(f"Conta temporariamente bloqueada por excesso de tentativas. Tente novamente em {data} min.")
            else:
                st.error("Utilizador ou palavra-passe incorretos.")

# ==========================================
# 2. DASHBOARD PRINCIPAL
# ==========================================
else:
    st.markdown("""
        <style>
            .stDeployButton {display:none !important;}
            /* O header e a toolbar NÃO podem ser escondidos por inteiro: o botão de reabrir o menu mora neles. */
            header[data-testid="stHeader"] {background: transparent !important;}
            [data-testid="stToolbarActions"], [data-testid="stMainMenu"],
            [data-testid="stAppDeployButton"], [data-testid="stDecoration"],
            [data-testid="stStatusWidget"] {display: none !important;}
            [data-testid="stToolbar"],
            [data-testid="collapsedControl"],
            [data-testid="stSidebarCollapsedControl"],
            [data-testid="stExpandSidebarButton"] {
                visibility: visible !important;
                opacity: 1 !important;
            }
            [data-testid="stExpandSidebarButton"], [data-testid="stSidebarCollapsedControl"] {
                display: flex !important;
                z-index: 999999 !important;
            }
            .block-container {
                padding-top: 4rem;
                padding-bottom: 0rem;
            }
            [data-testid="stSidebar"] {
                background-color: #1f3324;
            }
            [data-testid="stSidebar"], [data-testid="stSidebar"] label, [data-testid="stSidebar"] span {
                color: #e2e8f0;
            }
            
            /* Remove completamente bordas, sombras e fundos brancos de TODOS os expanders na barra lateral */
            [data-testid="stSidebar"] div[data-testid="stExpander"],
            [data-testid="stSidebar"] details[data-testid="stExpander"],
            [data-testid="stSidebar"] .streamlit-expander,
            [data-testid="stSidebar"] [data-baseweb="card"] {
                background-color: transparent !important;
                border: none !important;
                box-shadow: none !important;
            }
            [data-testid="stSidebar"] [data-testid="stExpander"] summary,
            [data-testid="stSidebar"] details[data-testid="stExpander"] summary {
                background-color: transparent !important;
                color: #e2e8f0 !important;
                border: none !important;
                box-shadow: none !important;
            }
            [data-testid="stSidebar"] [data-testid="stExpander"] summary:hover,
            [data-testid="stSidebar"] details[data-testid="stExpander"] summary:hover {
                color: #00e676 !important;
            }
            [data-testid="stSidebar"] [data-testid="stExpander"] [data-testid="stExpanderDetails"],
            [data-testid="stSidebar"] details[data-testid="stExpander"] div {
                background-color: transparent !important;
                border: none !important;
            }

            [data-testid="stSidebar"] button {
                background-color: #2e4d35 !important;
                color: #ffffff !important;
                border: 1px solid #3e6648 !important;
            }
            [data-testid="stSidebar"] button:hover {
                background-color: #3b6346 !important;
                color: #ffffff !important;
                border-color: #00e676 !important;
            }
            [data-testid="stSidebar"] button:active, [data-testid="stSidebar"] button:focus {
                background-color: #1f3324 !important;
                color: #ffffff !important;
            }
        </style>
    """, unsafe_allow_html=True)

    # Cards do dashboard principal: fonte menor e sem cortar valores (sem "...")
    st.markdown("""
        <style>
            [data-testid="stVerticalBlockBorderWrapper"] {padding: 0.6rem 0.7rem !important;}
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetric"],
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricValue"],
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricLabel"],
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricValue"] > div,
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricLabel"] > div {
                overflow: visible !important;
                text-overflow: clip !important;
                white-space: normal !important;
                word-break: keep-all;
            }
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricValue"],
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricValue"] * {
                font-size: clamp(0.95rem, 1.5vw, 1.25rem) !important;
                line-height: 1.2 !important;
            }
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricLabel"],
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMetricLabel"] * {font-size: 0.75rem !important;}
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stMarkdownContainer"] p {font-size: 0.85rem;}
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stProgress"] p {font-size: 0.75rem !important;}
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stCaptionContainer"] {font-size: 0.72rem !important;}
            [data-testid="stVerticalBlockBorderWrapper"] [data-testid="stHorizontalBlock"] {gap: 0.5rem !important;}
        </style>
    """, unsafe_allow_html=True)

    if not SIDEBAR_COLLAPSIBLE:   # menu fixo: remove a seta de recolher/expandir
        st.markdown("""
            <style>
                [data-testid="stSidebarCollapseButton"], [data-testid="stSidebarCollapsedControl"],
                [data-testid="stExpandSidebarButton"], [data-testid="collapsedControl"] {display: none !important;}
            </style>
        """, unsafe_allow_html=True)

    # --- TROCA OBRIGATÓRIA DE SENHA (primeiro acesso / senha redefinida pelo administrador) ---
    if st.session_state.must_change:
        st.markdown("## 🔐 Alteração obrigatória de palavra-passe")
        st.info(f"Por segurança, defina uma nova palavra-passe antes de continuar. "
                f"Mínimo de {MIN_PASSWORD_LEN} caracteres, com maiúsculas, minúsculas, números e símbolos.")
        with st.form("force_change_form"):
            fc_cur = st.text_input("Palavra-passe atual", type="password")
            fc_new = st.text_input("Nova palavra-passe", type="password")
            fc_conf = st.text_input("Confirmar nova palavra-passe", type="password")
            fc_submit = st.form_submit_button("Definir nova palavra-passe", type="primary")
        if fc_submit:
            if fc_new != fc_conf:
                st.error("A confirmação não coincide com a nova palavra-passe.")
            else:
                ok, msg = update_own_password(st.session_state.username, fc_cur, fc_new)
                if ok:
                    st.session_state.must_change = False
                    st.rerun()
                else:
                    st.error(msg)
        if st.button("🚪 Sair", key="force_logout"):
            audit("LOGOUT")
            _logout()
            st.rerun()
        st.stop()

    is_admin = st.session_state.role == "Administrador"

    # --- BARRA LATERAL (Sidebar) ---
    with st.sidebar:
        try:
            st.image("logo.svg", **_FULL)
        except Exception:
            st.title("NUTMETRICS")

        st.markdown(f"👤 **{_md(st.session_state.full_name)}**  \n🛡️ **Perfil:** {_md(st.session_state.role)}")

        st.markdown("---")

        st.markdown("**DASHBOARD**")
        #st.markdown("**CLUSTER**")

        all_clusters = get_all_clusters()

        prism_centrals = [c for c in all_clusters if c[1] == "Prism Central"]
        prism_elements = [c for c in all_clusters if c[1] != "Prism Central"]
        pc_ips = {pc[2] for pc in prism_centrals}
        # Cluster cadastrado direto (sem Prism Central) -> "Clusters Isolados"
        isolated_clusters = [el for el in prism_elements if el[5] not in pc_ips]

        for pc in prism_centrals:
            pc_name, pc_type, pc_ip, pc_port, pc_status, _ = pc
            managed_clusters = [el for el in prism_elements if el[5] == pc_ip]
            with st.expander(_md(pc_name), expanded=True):
                if st.button("🔔 Alertas", key=f"alerts_pc_{pc_name}", **_FULL):
                    _open_alerts(pc_name)
                if managed_clusters:
                    for el in managed_clusters:
                        _sidebar_cluster(el, pc_name)
                else:
                    st.text("  ↳ Nenhum cluster gerido")

        if isolated_clusters:
            with st.expander("Clusters Isolados", expanded=True):
                for el in isolated_clusters:
                    _sidebar_cluster(el, "iso")

        if not prism_centrals and not prism_elements:
            st.text("  ↳ Nenhum cluster cadastrado")

        st.markdown("**REPORT**")

        st.markdown("---")

        if is_admin:
            if st.button("🖥️ Gerenciar Cluster", key="nav_clusters", **_FULL):
                st.session_state.show_cluster_management = True
                st.session_state.show_user_management = False
                st.session_state.alerts_cluster = None
                st.session_state.usage_cluster = None
                st.session_state.host_view = None
                st.session_state.storage_cluster = None
                st.session_state.vm_view = None
                st.rerun()

            if st.button("👥 Gerenciar Utilizador", key="nav_users", **_FULL):
                st.session_state.show_user_management = True
                st.session_state.show_cluster_management = False
                st.session_state.alerts_cluster = None
                st.session_state.usage_cluster = None
                st.session_state.host_view = None
                st.session_state.storage_cluster = None
                st.session_state.vm_view = None
                st.rerun()

        if st.button("🚪 SAIR", key="nav_logout", **_FULL):
            audit("LOGOUT")
            _logout()
            st.rerun()

    # --- CONTEÚDO PRINCIPAL ---

    col_titulo, col_vazia, col_perfil = st.columns([6, 1.5, 0.5])

    with col_titulo:
        st.markdown("### Nutanix &nbsp;|&nbsp; **Dashboard**")

    with col_perfil:
        with st.popover("👤", help="Perfil do Utilizador"):
            st.markdown(f"**Nome:** {_md(st.session_state.full_name)}")
            st.markdown(f"**Utilizador:** {_md(st.session_state.username)}")
            st.markdown(f"**Perfil:** {_md(st.session_state.role)}")
            st.markdown("---")
            st.markdown("**Alterar a minha Palavra-passe**")

            with st.form("change_own_pass_form"):
                curr_pass = st.text_input("Palavra-passe Atual", type="password")
                new_pass = st.text_input("Nova Palavra-passe", type="password",
                                         placeholder=f"Mín. {MIN_PASSWORD_LEN} chars, maiúscula, número, símbolo")
                new_pass2 = st.text_input("Confirmar Nova Palavra-passe", type="password")
                sub_change = st.form_submit_button("Atualizar Palavra-passe", type="primary")

                if sub_change:
                    if new_pass != new_pass2:
                        st.error("A confirmação não coincide com a nova palavra-passe.")
                    else:
                        success, msg = update_own_password(st.session_state.username, curr_pass, new_pass)
                        if success:
                            st.success(msg)
                        else:
                            st.error(msg)

    # --- TELA DE GERENCIAMENTO DE CLUSTERS (Admin) ---
    if st.session_state.show_cluster_management and is_admin:
        st.markdown("## 🖥 Gestão de Clusters")
        if not key_is_from_env():
            st.warning("⚠️ A chave que protege as credenciais dos clusters está num arquivo local. "
                       "Em produção, defina a variável de ambiente NUTMETRICS_KEY e mantenha a chave fora da pasta do banco.")

        tab_c_list, tab_c_create, tab_c_direct, tab_c_delete = st.tabs(
            ["Clusters Cadastrados", "Cadastrar Novo Cluster", "Acesso direto ao Prism Element", "Excluir Cluster"])

        with tab_c_list:
            st.markdown("### Lista de Clusters Ativos")
            clusters_data = get_all_clusters()
            if clusters_data:
                df_clusters = pd.DataFrame(clusters_data, columns=["Nome", "Tipo", "IP", "Porta", "Status", "Prism Central IP"])
                st.dataframe(df_clusters, hide_index=True, **_FULL)
            else:
                st.info("Nenhum cluster cadastrado no momento.")

        with tab_c_create:
            st.markdown("### Registar e Testar Conexão com Cluster")
            st.info("🔒 Use no Nutanix um utilizador com perfil **somente leitura (Viewer)**. "
                    "O NutMetrics só consulta dados; uma conta administrativa aumenta muito o estrago se o sistema for comprometido.")

            if st.session_state.cluster_msg:
                _ok, _msg = st.session_state.cluster_msg
                (st.success if _ok else st.error)(_msg)
                st.session_state.cluster_msg = None

            pending = st.session_state.pending_cluster
            if not pending:
                with st.form("create_cluster_form"):
                    c_type = st.selectbox("Tipo de Plataforma", ["Prism Element", "Prism Central"])
                    c_ip = st.text_input("Endereço IP / Hostname", placeholder="Ex: 192.168.100.50")
                    c_port = st.text_input("Porta", value="9440")
                    c_user = st.text_input("Utilizador", placeholder="Ex: nutmetrics-ro")
                    c_pass = st.text_input("Palavra-passe", type="password", placeholder="Insira a palavra-passe")
                    submitted_cluster = st.form_submit_button("1) Obter certificado do servidor", type="primary")

                if submitted_cluster:
                    if c_ip.strip() and c_user.strip() and c_pass.strip():
                        ok_t, msg_t = validate_cluster_target(c_ip, c_port)
                        if not ok_t:
                            st.error(msg_t)
                        else:
                            fp_found = None
                            try:
                                with st.spinner("Obtendo o certificado do servidor..."):
                                    fp_found = fetch_server_fingerprint(c_ip, c_port.strip())
                            except Exception as e:
                                logger.warning("Falha ao obter certificado de %s:%s: %s",
                                               _clean(c_ip, 64), _clean(c_port, 8), _clean(repr(e), 200))
                                st.error("Não foi possível obter o certificado do servidor. Verifique IP, porta e rede.")
                            if fp_found:
                                st.session_state.pending_cluster = {
                                    "type": c_type, "ip": c_ip.strip(), "port": c_port.strip(),
                                    "user": c_user.strip(), "pass": c_pass, "fingerprint": fp_found,
                                    "nonce": secrets.token_hex(4),
                                }
                                st.rerun()
                    else:
                        st.error("Preencha todos os campos obrigatórios.")
            else:
                st.warning("**Confirme a identidade do servidor** antes de continuar. "
                           "O NutMetrics só voltará a aceitar conexões com este mesmo certificado.")
                st.code(f"{pending['ip']}:{pending['port']}  ({pending['type']})", language=None)
                st.markdown("**Fingerprint SHA-256 do certificado apresentado:**")
                st.code(format_fingerprint(pending["fingerprint"]), language=None)
                st.caption("Compare com o certificado exibido no próprio Nutanix ou obtido por outro caminho, por exemplo: "
                           "`openssl s_client -connect IP:PORTA < /dev/null | openssl x509 -noout -fingerprint -sha256`. "
                           "Só confirme se forem idênticos.")
                confirm_fp = st.checkbox("Confirmo que o fingerprint acima confere com o do meu Nutanix",
                                         key=f"confirm_fp_{pending['nonce']}")
                col_ok, col_cancel, _sp = st.columns([2, 1, 5])
                if col_ok.button("2) Confirmar e cadastrar", type="primary", disabled=not confirm_fp, key="cluster_confirm"):
                    with st.spinner("Testando conexão via API, listando hosts e descobrindo clusters..."):
                        ok_r, msg_r = test_and_register_cluster(
                            pending["type"], pending["ip"], pending["port"],
                            pending["user"], pending["pass"], pending["fingerprint"])
                    st.session_state.cluster_msg = (ok_r, msg_r)
                    st.session_state.pending_cluster = None
                    st.rerun()
                if col_cancel.button("Cancelar", key="cluster_cancel"):
                    st.session_state.pending_cluster = None
                    st.rerun()

        with tab_c_direct:
            st.markdown("### Acesso direto ao Prism Element")
            st.caption("Para clusters gerenciados por um Prism Central. O Storage (Pool, Container, Virtual Disk, Disco Físico) "
                       "passa a ser consultado direto no Prism Element, que é mais confiável que o proxy do Prism Central. "
                       "Se falhar, o NutMetrics volta a tentar pelo Prism Central.")
            managed = [c[0] for c in get_all_clusters() if c[5]]
            if not managed:
                st.info("Nenhum cluster gerenciado por Prism Central cadastrado.")
            else:
                d_cluster = st.selectbox("Cluster", managed, key="direct_cluster")
                cur_direct = get_element_access(d_cluster)
                if cur_direct:
                    st.success(f"Acesso direto ativo: {_md(cur_direct[0])}:{_md(cur_direct[1])} (utilizador {_md(cur_direct[2])})")
                    if st.button("Remover acesso direto", key="direct_remove"):
                        ok_d, msg_d = clear_element_access(d_cluster)
                        st.session_state.direct_msg = (ok_d, msg_d)
                        st.rerun()
                if st.session_state.direct_msg:
                    _okd, _msgd = st.session_state.direct_msg
                    (st.success if _okd else st.error)(_msgd)
                    st.session_state.direct_msg = None

                pend_d = st.session_state.pending_direct
                if not pend_d or pend_d["cluster"] != d_cluster:
                    guesses = st.session_state.direct_ip_guess or {}
                    if st.button("🔎 Descobrir o IP pelo Prism Central", key="direct_discover"):
                        with st.spinner("Consultando o Prism Central..."):
                            ip_found, msg_found = discover_element_ip(d_cluster)
                        if ip_found:
                            guesses[d_cluster] = ip_found
                            st.session_state.direct_ip_guess = guesses
                            st.rerun()
                        st.error(msg_found)
                    with st.form("direct_form"):
                        d_ip = st.text_input("IP do Prism Element (VIP do cluster)", value=guesses.get(d_cluster, ""),
                                             placeholder="Ex: 192.168.100.60")
                        d_port = st.text_input("Porta", value="9440", key="direct_port")
                        d_same = st.checkbox("Usar as mesmas credenciais do Prism Central", value=True)
                        d_user = st.text_input("Utilizador (se não usar as do Prism Central)", key="direct_user")
                        d_pass = st.text_input("Palavra-passe (se não usar as do Prism Central)", type="password", key="direct_pass")
                        sub_d = st.form_submit_button("1) Obter certificado do Prism Element", type="primary")
                    if sub_d:
                        ok_t, msg_t = validate_cluster_target(d_ip, d_port)
                        if not d_ip.strip():
                            st.error("Informe o IP do Prism Element.")
                        elif not ok_t:
                            st.error(msg_t)
                        elif not d_same and not (d_user.strip() and d_pass.strip()):
                            st.error("Informe utilizador e palavra-passe, ou use as credenciais do Prism Central.")
                        else:
                            fp_d = None
                            try:
                                with st.spinner("Obtendo o certificado do servidor..."):
                                    fp_d = fetch_server_fingerprint(d_ip, d_port.strip())
                            except Exception as e:
                                logger.warning("Falha ao obter certificado de %s:%s: %s",
                                               _clean(d_ip, 64), _clean(d_port, 8), _clean(repr(e), 200))
                                st.error("Não foi possível obter o certificado do servidor. Verifique IP, porta e rede.")
                            if fp_d:
                                st.session_state.pending_direct = {
                                    "cluster": d_cluster, "ip": d_ip.strip(), "port": d_port.strip(), "same": d_same,
                                    "user": d_user.strip(), "pass": d_pass, "fingerprint": fp_d, "nonce": secrets.token_hex(4)}
                                st.rerun()
                else:
                    st.warning("**Confirme a identidade do servidor** antes de continuar. "
                               "O NutMetrics só voltará a aceitar conexões com este mesmo certificado.")
                    st.code(f"{pend_d['ip']}:{pend_d['port']}  (Prism Element de {pend_d['cluster']})", language=None)
                    st.markdown("**Fingerprint SHA-256 do certificado apresentado:**")
                    st.code(format_fingerprint(pend_d["fingerprint"]), language=None)
                    st.caption("Compare com o certificado exibido no próprio Nutanix ou obtido por outro caminho, por exemplo: "
                               "`openssl s_client -connect IP:PORTA < /dev/null | openssl x509 -noout -fingerprint -sha256`. "
                               "Só confirme se forem idênticos.")
                    confirm_d = st.checkbox("Confirmo que o fingerprint acima confere com o do meu Nutanix",
                                            key=f"confirm_direct_{pend_d['nonce']}")
                    col_ok_d, col_cancel_d, _spd = st.columns([2, 1, 5])
                    if col_ok_d.button("2) Confirmar e salvar", type="primary", disabled=not confirm_d, key="direct_confirm"):
                        with st.spinner("Testando conexão e conferindo o cluster..."):
                            ok_s, msg_s = save_element_access(pend_d["cluster"], pend_d["ip"], pend_d["port"],
                                                              pend_d["user"], pend_d["pass"], pend_d["fingerprint"],
                                                              reuse_pc_credentials=pend_d["same"])
                        st.session_state.direct_msg = (ok_s, msg_s)
                        st.session_state.pending_direct = None
                        st.rerun()
                    if col_cancel_d.button("Cancelar", key="direct_cancel"):
                        st.session_state.pending_direct = None
                        st.rerun()

        with tab_c_delete:
            st.markdown("### Excluir Cluster Cadastrado")
            clusters_data = get_all_clusters()
            if clusters_data:
                cluster_dict = {c[0]: c for c in clusters_data}
                selected_cluster_to_delete = st.selectbox("Selecione o Cluster para Excluir", list(cluster_dict.keys()))

                with st.form("delete_cluster_form"):
                    st.warning(f"Atenção: Tem certeza que deseja remover o cluster **{_md(selected_cluster_to_delete)}**?")
                    submitted_delete_cluster = st.form_submit_button("Confirmar Exclusão", type="primary")
                    if submitted_delete_cluster:
                        ok, msg = delete_cluster(selected_cluster_to_delete)
                        if ok:
                            st.success(msg)
                            st.rerun()
                        else:
                            st.error(msg)
            else:
                st.info("Não existem clusters cadastrados para excluir.")

        st.markdown("---")
        if st.button("⬅ Voltar ao Dashboard", key="back_from_clusters"):
            st.session_state.show_cluster_management = False
            st.session_state.pending_cluster = None
            st.session_state.pending_direct = None
            st.rerun()

    # --- TELA DE GERENCIAMENTO DE UTILIZADORES (Admin) ---
    elif st.session_state.show_user_management and is_admin:
        st.markdown("## ⚙️ Gestão de Utilizadores")

        tab_create, tab_edit, tab_delete, tab_audit = st.tabs(
            ["Criar Novo Utilizador", "Alterar Utilizador Existente", "Excluir Utilizador", "Auditoria"])

        with tab_create:
            st.markdown("### Registar Novo Utilizador")
            with st.form("create_user_form"):
                new_user = st.text_input("Identificador (Login)", placeholder="3 a 32 caracteres: letras, números, . - _")
                new_full = st.text_input("Nome a ser Exibido")
                new_pass = st.text_input("Palavra-passe Inicial", type="password",
                                         placeholder=f"Mín. {MIN_PASSWORD_LEN} chars, maiúscula, número, símbolo")
                new_role = st.selectbox("Perfil de Acesso", list(ROLES))

                submitted_create = st.form_submit_button("Criar Utilizador", type="primary")
                if submitted_create:
                    success, msg = register_user(new_user, new_full, new_pass, new_role)
                    if success:
                        st.success(msg)
                    else:
                        st.error(msg)

        with tab_edit:
            st.markdown("### Alterar Dados de Utilizador")
            users_list = get_all_users()
            user_dict = {f"{u[1]} ({u[0]}) - {u[2]}": u for u in users_list}

            selected_user_str = st.selectbox("Selecione o Utilizador", list(user_dict.keys()))
            if selected_user_str:
                selected_data = user_dict[selected_user_str]
                target_username = selected_data[0]

                with st.form("edit_user_form"):
                    edit_full = st.text_input("Nome a ser Exibido", value=selected_data[1])
                    edit_role = st.selectbox("Perfil de Acesso", list(ROLES), index=0 if selected_data[2] == "Usuário" else 1)
                    edit_unlock = st.checkbox("Desbloquear conta (limpar tentativas de login falhas)")

                    st.markdown("---")
                    st.markdown("**Redefinir Palavra-passe (Opcional)**")
                    edit_pass = st.text_input("Nova Palavra-passe (Deixe em branco para manter a atual)", type="password")
                    st.caption("Ao redefinir, o utilizador terá de trocar a palavra-passe no próximo acesso.")

                    submitted_edit = st.form_submit_button("Guardar Alterações", type="primary")
                    if submitted_edit:
                        p_arg = edit_pass if edit_pass.strip() != "" else None
                        ok, msg = update_user_info(target_username, edit_full, edit_role, p_arg, edit_unlock)
                        if ok:
                            st.success(msg)
                            if target_username == st.session_state.username:
                                st.session_state.full_name = edit_full
                        else:
                            st.error(msg)

        with tab_delete:
            st.markdown("### Excluir Utilizador")
            users_list = get_all_users()
            user_dict_del = {f"{u[1]} ({u[0]}) - {u[2]}": u[0] for u in users_list}

            selected_user_to_del_str = st.selectbox("Selecione o Utilizador para Excluir", list(user_dict_del.keys()))
            if selected_user_to_del_str:
                target_del_username = user_dict_del[selected_user_to_del_str]

                with st.form("delete_user_form"):
                    st.warning(f"Atenção: Tem certeza que deseja excluir o utilizador **{_md(target_del_username)}**?")
                    submitted_delete_user = st.form_submit_button("Confirmar Exclusão", type="primary")
                    if submitted_delete_user:
                        ok, msg = delete_user(target_del_username, st.session_state.username)
                        if ok:
                            st.success(msg)
                            st.rerun()
                        else:
                            st.error(msg)

        with tab_audit:
            st.markdown("### Registo de Auditoria (últimos 200 eventos)")
            audit_rows = get_audit_log(200)
            if audit_rows:
                df_audit = pd.DataFrame(
                    [(datetime.fromtimestamp(r[0]).strftime("%d/%m/%Y %H:%M:%S"), r[1], r[2], r[3], r[4]) for r in audit_rows],
                    columns=["Data", "Utilizador", "Ação", "Detalhe", "IP"])
                st.dataframe(df_audit, hide_index=True, **_FULL)
            else:
                st.info("Ainda não há eventos registados.")

        st.markdown("---")
        if st.button("⬅ Voltar ao Dashboard", key="back_from_users"):
            st.session_state.show_user_management = False
            st.rerun()

    # --- TELA DE VM ---
    elif st.session_state.vm_view:
        v_cluster, v_id = st.session_state.vm_view
        if v_cluster not in [c[0] for c in get_all_clusters()]:
            st.session_state.vm_view = None
            st.rerun()
        v_names, v_hosts = _vm_options(v_cluster, include_id=v_id)
        if v_id not in v_names:
            st.session_state.vm_view = None
            st.rerun()
        st.markdown(f"## 🖧 VM — {_md(v_names[v_id])}")
        st.caption(f"Cluster: {_md(v_cluster)}")

        col_ref, col_back, col_sel, _sp = st.columns([1.2, 1.2, 3.6, 3])
        with col_ref:
            if st.button("🔄 Atualizar", key="vm_refresh", **_FULL):
                fetch_vm_entities.clear()
                st.rerun()
        with col_back:
            if st.button("⬅ Voltar", key="vm_back", **_FULL):
                st.session_state.vm_view = None
                st.rerun()
        with col_sel:
            # a chave inclui a VM: ao abrir outra VM pelo menu, o seletor passa a apontar para ela
            v_list = list(v_names)
            sel_vm = st.selectbox("Trocar de VM", v_list, index=v_list.index(v_id), key=f"vm_sel_{v_cluster}_{v_id}",
                                  format_func=_vm_label_fn(v_names), label_visibility="collapsed",
                                  help="Digite para filtrar a lista.")
            if sel_vm != v_id:
                _open_vm(v_cluster, sel_vm)
                st.rerun()

        # ---------- Situação atual (consulta ao vivo, cache de 60 s) ----------
        with st.spinner("Consultando as VMs..."):
            ok_v, live_vms, msg_v, diag_v = get_vm_metrics(v_cluster)
        cur_vm = next((x for x in live_vms if x["id"] == v_id), None) if ok_v else None
        if not ok_v:
            st.warning(f"Situação atual indisponível: {_md(msg_v)} Os gráficos abaixo usam o histórico gravado.")
        elif cur_vm is None:
            st.warning("A API não retornou esta VM agora (excluída ou fora do cluster?). Os gráficos abaixo usam o histórico gravado.")
        vv = cur_vm["values"] if cur_vm else {}
        vcpu_n = vv.get("vcpu")
        vcpu_used_now = vv["cpu_pct"] / 100 * vcpu_n if vv.get("cpu_pct") is not None and vcpu_n else None

        k_cpu, k_mem = st.columns(2)
        with k_cpu:
            with st.container(border=True):
                _usage_card("⚙️ CPU", vcpu_n, vcpu_used_now, lambda x: f"{_br(x, 2)} vCPU")
        with k_mem:
            with st.container(border=True):
                _usage_card("🧠 Memória (convidado)", vv.get("mem_cfg_bytes"), vv.get("mem_used_bytes"), _fmt_bytes)
                if vv.get("mem_used_bytes") is None and cur_vm is not None and vv.get("powered_on"):
                    st.caption("A VM não informa a memória do convidado (sem NGT?)."
                               + (f" Visão do hypervisor: {_br(vv['mem_hyp_pct'], 1)}%." if vv.get("mem_hyp_pct") is not None else ""))
        m1, m2, m3, m4 = st.columns(4)
        with m1:
            with st.container(border=True):
                st.metric("🔌 Estado", ("Ligada" if vv.get("powered_on") else "Desligada") if cur_vm else "—")
        with m2:
            with st.container(border=True):
                host_txt = (cur_vm.get("host_name") or (cur_vm.get("host_uuid") or "")[:8]) if cur_vm else v_hosts.get(v_id)
                st.metric("🖥️ Host", _md(host_txt) if host_txt else "—")
        with m3:
            with st.container(border=True):
                st.metric("💽 IOPS", _fmt_num(vv.get("iops_total")))
                st.caption(f"Throughput {_fmt_num(vv['bw_total'] / 1024 if vv.get('bw_total') is not None else None, 1)} MB/s")
        with m4:
            with st.container(border=True):
                st.metric("⏱️ Latência de I/O", _fmt_num(vv["lat_avg"] / 1000 if vv.get("lat_avg") is not None else None, 2, " ms"))

        # ---------- Histórico: mesmas abas por período dos outros dashboards ----------
        period_tabs = st.tabs([p[0] for p in USAGE_PERIODS])
        for tab, (p_label, p_days, p_rule) in zip(period_tabs, USAGE_PERIODS):
            with tab:
                v_df = load_vm_df(v_cluster, v_id, p_days, p_rule)
                if v_df.empty:
                    st.info("Ainda não há amostras desta VM neste período. A coleta é feita a cada 5 minutos "
                            "e o histórico vai se formando aos poucos.")
                    continue
                is_year = p_label == "Anual"
                _render_vm_charts(v_df, is_year=is_year, has_peak=bool(p_rule))
                st.caption(f"{len(v_df)} ponto(s) no período"
                           + (" · médias de 1 dia · linha tracejada = tendência · 'Pico' = maior valor do dia" if is_year else
                              f" · médias de {p_rule.replace('min', ' min')} · 'Pico' = maior valor do intervalo" if p_rule
                              else " · amostras de 5 min"))
        if is_admin and diag_v:
            with st.expander("🔧 Diagnóstico da API (VMs)", expanded=not ok_v):
                st.code("\n".join(diag_v), language=None)

    # --- TELA DE STORAGE ---
    elif st.session_state.storage_cluster:
        s_cluster = st.session_state.storage_cluster
        if s_cluster not in [c[0] for c in get_all_clusters()]:
            st.session_state.storage_cluster = None
            st.session_state.vm_view = None
            st.rerun()
        st.markdown(f"## 💾 Storage — {_md(s_cluster)}")

        col_ref, col_back, _sp = st.columns([1.2, 1.2, 6])
        with col_ref:
            if st.button("🔄 Atualizar", key="storage_refresh", **_FULL):
                fetch_storage_entities.clear()
                st.rerun()
        with col_back:
            if st.button("⬅ Voltar", key="storage_back", **_FULL):
                st.session_state.storage_cluster = None
                st.session_state.vm_view = None
                st.rerun()

        s_type = st.radio("Recurso", list(STORAGE_ETYPES), format_func=lambda k: STORAGE_ETYPES[k]["label"],
                          horizontal=True, key=f"stor_type_{s_cluster}", label_visibility="collapsed")
        _render_storage_entity(s_cluster, s_type, is_admin)

    # --- TELA DE HOST ---
    elif st.session_state.host_view:
        h_cluster, h_name = st.session_state.host_view
        h_all = [h[0] for h in get_hosts_by_cluster(h_cluster)] if h_cluster in [c[0] for c in get_all_clusters()] else []
        if h_name not in h_all:
            st.session_state.host_view = None
            st.rerun()
        st.markdown(f"## 🖥️ Host — {_md(h_name)}")
        st.caption(f"Cluster: {_md(h_cluster)}")

        col_ref, col_back, col_sel, _sp = st.columns([1.2, 1.2, 3, 3.6])
        with col_ref:
            if st.button("🔄 Atualizar", key="host_refresh", **_FULL):
                fetch_host_metrics.clear()
                st.rerun()
        with col_back:
            if st.button("⬅ Voltar", key="host_back", **_FULL):
                st.session_state.host_view = None
                st.session_state.storage_cluster = None
                st.session_state.vm_view = None
                st.rerun()
        with col_sel:
            # a chave inclui o host: ao abrir outro host pelo menu, o seletor passa a apontar para ele
            sel_host = st.selectbox("Trocar de host", h_all, index=h_all.index(h_name),
                                    key=f"host_sel_{h_cluster}_{h_name}", label_visibility="collapsed")
            if sel_host != h_name:
                _open_host(h_cluster, sel_host)

        # ---------- Situação atual (consulta ao vivo, cache de 60 s) ----------
        with st.spinner("Consultando métricas dos hosts..."):
            ok_h, live_hosts, msg_h, diag_h = get_host_metrics(h_cluster)
        cur = next((x for x in live_hosts if x["name"] == h_name), None) if ok_h else None
        if not ok_h:
            st.warning(f"Situação atual indisponível: {_md(msg_h)} Os gráficos abaixo usam o histórico gravado.")
        elif cur is None:
            st.warning("A API não retornou este host agora. Os gráficos abaixo usam o histórico gravado.")
        v = cur["values"] if cur else {}

        k_cpu, k_mem = st.columns(2)
        with k_cpu:
            with st.container(border=True):
                _usage_card("⚙️ CPU", v.get("cpu_total"), v.get("cpu_used"), _fmt_ghz)
        with k_mem:
            with st.container(border=True):
                _usage_card("🧠 Memória", v.get("mem_total"), v.get("mem_used"), _fmt_bytes)

        def _kb(x):
            return x / 1024 if x is not None else None
        def _ms(x):
            return x / 1000 if x is not None else None

        k1, k2, k3, k4 = st.columns(4)
        with k1:
            with st.container(border=True):
                st.metric("💽 IOPS", _fmt_num(v.get("iops_total")))
                st.caption(f"Leitura {_fmt_num(v.get('iops_read'))} · Escrita {_fmt_num(v.get('iops_write'))}")
        with k2:
            with st.container(border=True):
                st.metric("💽 Throughput", _fmt_num(_kb(v.get("bw_total")), 1, " MB/s"))
                st.caption(f"Leitura {_fmt_num(_kb(v.get('bw_read')), 1)} · Escrita {_fmt_num(_kb(v.get('bw_write')), 1)}")
        with k3:
            with st.container(border=True):
                st.metric("⏱️ Latência de I/O", _fmt_num(_ms(v.get("lat_avg")), 2, " ms"))
                st.caption(f"Leitura {_fmt_num(_ms(v.get('lat_read')), 2)} · Escrita {_fmt_num(_ms(v.get('lat_write')), 2)}")
        with k4:
            with st.container(border=True):
                st.metric("🗂️ VMs no host", _fmt_num(v.get("num_vms")))
                st.caption(f"Latência no hypervisor {_fmt_num(_ms(v.get('hyp_lat')), 2)} ms")

        if ok_h and live_hosts:
            with st.expander("⚖️ Comparativo entre os hosts do cluster (agora)"):
                cmp_rows = []
                for x in sorted(live_hosts, key=lambda r: str(r["name"])):
                    xv = x["values"]
                    cpu_p = xv["cpu_used"] / xv["cpu_total"] * 100 if xv.get("cpu_used") is not None and xv.get("cpu_total") else None
                    mem_p = xv["mem_used"] / xv["mem_total"] * 100 if xv.get("mem_used") is not None and xv.get("mem_total") else None
                    cmp_rows.append({"Host": x["name"], "CPU %": cpu_p, "Memória %": mem_p, "IOPS": xv.get("iops_total"),
                                     "Throughput (MB/s)": _kb(xv.get("bw_total")), "Latência (ms)": _ms(xv.get("lat_avg")),
                                     "VMs": xv.get("num_vms")})
                st.dataframe(pd.DataFrame(cmp_rows).round(2), hide_index=True, **_FULL)
                st.caption("Útil para enxergar hosts desbalanceados (muito acima ou abaixo dos demais).")

        # ---------- Histórico: mesmas abas por período do cluster ----------
        period_tabs = st.tabs([p[0] for p in USAGE_PERIODS])
        for tab, (p_label, p_days, p_rule) in zip(period_tabs, USAGE_PERIODS):
            with tab:
                h_df = load_host_usage_df(h_cluster, h_name, p_days, p_rule)
                if h_df.empty:
                    st.info("Ainda não há amostras deste host neste período. A coleta é feita a cada 5 minutos "
                            "e o histórico vai se formando aos poucos.")
                    continue
                is_year = p_label == "Anual"
                _render_host_charts(h_df, is_year=is_year, has_peak=bool(p_rule))
                st.caption(f"{len(h_df)} ponto(s) no período"
                           + (" · médias de 1 dia · linha tracejada = tendência · 'Pico' = maior valor do dia" if is_year else
                              f" · médias de {p_rule.replace('min', ' min')} · 'Pico' = maior valor do intervalo" if p_rule
                              else " · amostras de 5 min"))

        if is_admin and diag_h:
            with st.expander("🔧 Diagnóstico da API (métricas por host)", expanded=not ok_h):
                st.caption("Mostra só nomes de métricas e valores numéricos (sem credenciais). "
                           "Métricas sem dado em nenhum host aparecem na última linha.")
                st.code("\n".join(diag_h) or "-", language=None)

    # --- TELA DE UTILIZAÇÃO ---
    elif st.session_state.usage_cluster:
        u_cluster = st.session_state.usage_cluster
        if u_cluster not in [c[0] for c in get_all_clusters()]:
            st.session_state.usage_cluster = None
            st.rerun()
        st.markdown(f"## 📈 Utilização — {_md(u_cluster)}")

        col_ref, col_back, _sp = st.columns([1.2, 1.2, 6])
        with col_ref:
            if st.button("🔄 Atualizar", key="usage_refresh", **_FULL):
                st.rerun()
        with col_back:
            if st.button("⬅ Voltar", key="usage_back", **_FULL):
                st.session_state.usage_cluster = None
                st.rerun()

        period_tabs = st.tabs([p[0] for p in USAGE_PERIODS])
        for tab, (p_label, p_days, p_rule) in zip(period_tabs, USAGE_PERIODS):
            with tab:
                u_df = load_usage_df(u_cluster, p_days, p_rule)
                if u_df.empty:
                    st.info("Ainda não há amostras neste período. A coleta é feita a cada 5 minutos "
                            "e o histórico vai se formando aos poucos.")
                    continue
                is_year = p_label == "Anual"
                g1, g2 = st.columns(2)
                with g1:
                    st.markdown("**⚙️ CPU (GHz)**")
                    st.altair_chart(_usage_chart(u_df, {"Em uso": "cpu_used_ghz", "Total": "cpu_total_ghz"},
                                                 "GHz", trend=is_year), **_FULL)
                with g2:
                    st.markdown("**⚙️ CPU (%)**")
                    st.altair_chart(_usage_chart(u_df, {"Uso %": "cpu_pct"}, "%", is_pct=True, trend=is_year), **_FULL)
                g3, g4 = st.columns(2)
                with g3:
                    st.markdown("**🧠 Memória (GiB)**")
                    st.altair_chart(_usage_chart(u_df, {"Em uso": "mem_used_gib", "Total": "mem_total_gib"},
                                                 "GiB", trend=is_year), **_FULL)
                with g4:
                    st.markdown("**🧠 Memória (%)**")
                    st.altair_chart(_usage_chart(u_df, {"Uso %": "mem_pct"}, "%", is_pct=True, trend=is_year), **_FULL)
                st.caption(f"{len(u_df)} ponto(s) no período"
                           + (" · médias de 1 dia · linha tracejada = tendência" if is_year else
                              f" · médias de {p_rule.replace('min', ' min')}" if p_rule else " · amostras de 5 min"))

    # --- TELA DE ALERTAS ATIVOS ---
    elif st.session_state.alerts_cluster:
        cl_name = st.session_state.alerts_cluster
        st.markdown(f"## 🔔 Alertas Ativos — {_md(cl_name)}")

        col_ref, col_back, _sp = st.columns([1.2, 1.2, 6])
        with col_ref:
            if st.button("🔄 Atualizar", key="alerts_refresh", **_FULL):
                fetch_active_alerts.clear()
                st.rerun()
        with col_back:
            if st.button("⬅ Voltar", key="alerts_back", **_FULL):
                st.session_state.alerts_cluster = None
                st.session_state.usage_cluster = None
                st.session_state.host_view = None
                st.session_state.storage_cluster = None
                st.session_state.vm_view = None
                st.rerun()

        with st.spinner("Consultando alertas via API..."):
            ok, alerts, msg, source = fetch_active_alerts(cl_name)

        if not ok:
            st.error(msg)
        else:
            if source:
                st.caption(f"Fonte: {source}")
            if not alerts:
                st.success("Nenhum alerta ativo no momento. ✅")
            else:
                df_alerts = pd.DataFrame(
                    alerts, columns=["Título", "Data", "Severidade"] + [c for c in ("Cluster", "Descrição") if c in alerts[0]])

                k1, k2, k3, k4 = st.columns(4)
                k1.metric("Total ativos", len(df_alerts))
                k2.metric("🔴 Críticos", int((df_alerts["Severidade"] == "🔴 Crítico").sum()))
                k3.metric("🟠 Avisos", int((df_alerts["Severidade"] == "🟠 Aviso").sum()))
                k4.metric("🔵 Informativos", int((df_alerts["Severidade"] == "🔵 Informativo").sum()))

                sev_options = list(df_alerts["Severidade"].unique())
                sev_sel = st.multiselect("Filtrar por severidade", sev_options, default=sev_options)
                st.dataframe(df_alerts[df_alerts["Severidade"].isin(sev_sel)], hide_index=True, **_FULL)

    else:
        dash_all = get_all_clusters()
        dash_elements = [c for c in dash_all if c[1] != "Prism Central"]

        col_dash_t, col_dash_r = st.columns([8, 1.3])
        with col_dash_r:
            if st.button("🔄 Atualizar", key="dash_refresh", **_FULL):
                fetch_host_stats.clear()
                fetch_host_metrics.clear()
                fetch_storage_entities.clear()
                fetch_vm_entities.clear()
                st.rerun()

        if not dash_elements:
            st.info("Nenhum cluster cadastrado. Acesse 'Gerenciar Cluster' no menu lateral para adicionar o seu primeiro ambiente Nutanix.")
        else:
            # ---------- LINHA 1: visão geral de todos os clusters ----------
            with st.spinner("Consultando recursos dos clusters..."):
                g, g_fail = get_global_resources()

            r1_clusters, r1_cpu, r1_mem = st.columns([1, 1.2, 1.2])
            with r1_clusters:
                with st.container(border=True):
                    st.markdown("**🖥️ Clusters**")
                    k_total, k_managed = st.columns(2)
                    k_total.metric("Total", len(dash_elements))
                    k_managed.metric("Gerenciados", sum(1 for c in dash_elements if c[5]))
                    st.caption(f"Hosts no total: {g['hosts']}")
            with r1_cpu:
                with st.container(border=True):
                    _usage_card("⚙️ CPU", g["cpu_total"], g["cpu_used"], _fmt_ghz)
            with r1_mem:
                with st.container(border=True):
                    _usage_card("🧠 Memória", g["mem_total"], g["mem_used"], _fmt_bytes)

            if g_fail:
                with st.expander(f"⚠️ {len(g_fail)} cluster(s) sem dados nos totais acima"):
                    for f_name, f_msg in g_fail:
                        st.markdown(f"- **{_md(f_name)}**: {_md(f_msg)}")

            # ---------- LINHA 2: cluster selecionado ----------
            names = [c[0] for c in dash_elements]
            if st.session_state.get("dash_cluster") not in names:
                st.session_state.pop("dash_cluster", None)

            r2_sel, r2_cpu, r2_mem = st.columns([1, 1.2, 1.2])
            with r2_sel:
                with st.container(border=True):
                    sel_cluster = st.selectbox("Cluster", names, key="dash_cluster")
                    ok_c, c_data, c_msg = get_cluster_resources(sel_cluster)
                    st.metric("Total de Hosts", c_data["hosts"] if ok_c else "—")
            with r2_cpu:
                with st.container(border=True):
                    _usage_card("⚙️ CPU", c_data["cpu_total"] if ok_c else None,
                                c_data["cpu_used"] if ok_c else None, _fmt_ghz)
            with r2_mem:
                with st.container(border=True):
                    _usage_card("🧠 Memória", c_data["mem_total"] if ok_c else None,
                                c_data["mem_used"] if ok_c else None, _fmt_bytes)
            if not ok_c:
                st.error(c_msg)
            elif is_admin:
                with st.expander("🔧 Diagnóstico da API (valores brutos de capacidade e uso)"):
                    st.caption("Mostra apenas capacidades, percentuais e nomes de campos (sem credenciais). "
                               "Útil para conferir com os números do Nutanix.")
                    st.code("\n".join(c_data["diag"]) or "-", language=None)
            st.caption("Dados em cache por 60 s. Use 'Atualizar' para consultar novamente.")
