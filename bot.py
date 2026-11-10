import asyncio
import ast
import hashlib
import itertools
import json
import os
import re
import time
from datetime import datetime, date, timedelta
from typing import Dict, Any, Optional, Tuple, Sequence, List

import httpx

# =====================================================================
# 1. JSON DATABASE & FILE MANAGEMENT ENGINE
# =====================================================================

FILES = {
    "config": "config.json",
    "users": "users.json",
    "logs": "logs.json",
    "sessions": "sessions.json",
}

DEFAULT_CONFIG = {
    "bot_token": os.getenv("BOT_TOKEN", "9071346261:AAECfzDiHqctxKhHaCvCNQ2PEYTCcqj4xmA"),
    "owner_id": int(os.getenv("OWNER_ID", "8684812026")),
    "maintenance_mode": False,
    "free_daily_limit": 2,
    "premium_daily_limit": 5,
    "welcome_media": {
        "enabled": False,
        "media_type": "photo",  # "photo" or "video"
        "file_id": ""
    },
    # Evaluated safely via Python's AST engine against incoming emails
    "ast_email_policy": "'@' in email and '.' in domain and len(local) >= 2 and not email.endswith('.invalid')",
    "ig_app_id": "936619743392459",
    # --- Proxy rotation for Instagram requests ---
    "instagram_proxies": [],  # e.g. ["http://user:pass@host:8080", "socks5://user:pass@host:1080"]
    # --- Premium monetization ---
    "premium_stars_price": 100,   # Telegram Stars amount for 30-day premium
    "premium_duration_days": 30,
    "upi_id": "",                 # UPI VPA for manual fallback (e.g. "merchant@upi")
    "upi_price_inr": 199,         # Displayed INR price for UPI
}


class JSONDatabaseManager:
    """Thread-safe JSON file creation, reading, and atomic writing."""

    def __init__(self):
        self._ensure_files()

    def _ensure_files(self) -> None:
        if not os.path.exists(FILES["config"]):
            self.save("config", DEFAULT_CONFIG)
        if not os.path.exists(FILES["users"]):
            self.save("users", {})
        if not os.path.exists(FILES["logs"]):
            self.save("logs", {"queries": [], "resets_sent": 0, "checks_run": 0})
        if not os.path.exists(FILES["sessions"]):
            self.save("sessions", {"user_states": {}, "ig_csrf_cache": {}})

    def load(self, key: str) -> Dict[str, Any]:
        path = FILES[key]
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            # Non-destructive migration: add missing default config keys
            if key == "config" and isinstance(data, dict):
                changed = False
                for k, v in DEFAULT_CONFIG.items():
                    if k not in data:
                        data[k] = v
                        changed = True
                if changed:
                    self.save(key, data)
            return data
        except (FileNotFoundError, json.JSONDecodeError):
            default = DEFAULT_CONFIG if key == "config" else {}
            self.save(key, default)
            return default

    def save(self, key: str, data: Dict[str, Any]) -> None:
        path = FILES[key]
        temp_path = f"{path}.tmp"
        with open(temp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(temp_path, path)

    # --- User Management ---
    def get_user(self, user_id: int) -> Optional[Dict[str, Any]]:
        users = self.load("users")
        return users.get(str(user_id))

    def save_user(self, user_id: int, user_data: Dict[str, Any]) -> None:
        users = self.load("users")
        users[str(user_id)] = user_data
        self.save("users", users)

    def check_and_reset_daily_quota(self, user_id: int) -> Dict[str, Any]:
        user = self.get_user(user_id)
        if not user:
            return {}
        today_str = date.today().isoformat()
        if user.get("last_quota_date") != today_str:
            user["daily_used"] = 0
            user["last_quota_date"] = today_str
            self.save_user(user_id, user)
        return user

    # --- Session State Management ---
    def get_state(self, user_id: int) -> Dict[str, Any]:
        sessions = self.load("sessions")
        return sessions.get("user_states", {}).get(str(user_id), {"step": "idle"})

    def set_state(self, user_id: int, step: str, payload: Optional[Dict[str, Any]] = None) -> None:
        sessions = self.load("sessions")
        if "user_states" not in sessions:
            sessions["user_states"] = {}
        sessions["user_states"][str(user_id)] = {
            "step": step,
            "payload": payload or {},
            "updated_at": int(time.time())
        }
        self.save("sessions", sessions)

    def clear_state(self, user_id: int) -> None:
        self.set_state(user_id, "idle", {})

    # --- Real-Time Audit & Email Logging ---
    def log_event(self, user_id: int, email: str, action: str, status: str, detail: str) -> None:
        logs = self.load("logs")
        entry = {
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "user_id": user_id,
            "email": email,
            "action": action,
            "status": status,
            "detail": detail
        }
        logs.setdefault("queries", []).insert(0, entry)
        logs["queries"] = logs["queries"][:250]  # Keep latest 250 logs
        if action == "send_reset" and status == "SUCCESS":
            logs["resets_sent"] = logs.get("resets_sent", 0) + 1
        elif action == "check_email":
            logs["checks_run"] = logs.get("checks_run", 0) + 1
        self.save("logs", logs)


db = JSONDatabaseManager()


# =====================================================================
# 2. AST EMAIL VALIDATION & SECURITY POLICY ENGINE
# =====================================================================

class ASTEmailValidator:
    """
    Uses Python's native `ast` module to parse and safely evaluate
    email syntax and custom owner-defined policy rules without unsafe eval().
    """

    ALLOWED_NODES = (
        ast.Expression, ast.BoolOp, ast.BinOp, ast.UnaryOp, ast.Compare,
        ast.Name, ast.Load, ast.Constant, ast.And, ast.Or, ast.Not,
        ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.In, ast.NotIn,
        ast.Call, ast.Attribute
    )
    ALLOWED_METHODS = {"endswith", "startswith", "isdigit", "isalpha", "lower"}
    ALLOWED_FUNCS = {"len"}

    @classmethod
    def validate_rule_syntax(cls, rule_expr: str) -> Tuple[bool, str]:
        try:
            tree = ast.parse(rule_expr, mode="eval")
            for node in ast.walk(tree):
                if not isinstance(node, cls.ALLOWED_NODES):
                    return False, f"Disallowed AST node: {type(node).__name__}"
                if isinstance(node, ast.Call):
                    if isinstance(node.func, ast.Name) and node.func.id not in cls.ALLOWED_FUNCS:
                        return False, f"Disallowed function call: {node.func.id}"
                    elif isinstance(node.func, ast.Attribute) and node.func.attr not in cls.ALLOWED_METHODS:
                        return False, f"Disallowed attribute method: {node.func.attr}"
            return True, "Valid AST policy expression."
        except SyntaxError as e:
            return False, f"Syntax error: {e}"

    @classmethod
    def check_email(cls, raw_email: str, policy_expr: str) -> Tuple[bool, str]:
        email = raw_email.strip().lower()
        basic_regex = r"^[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+$"
        if not re.match(basic_regex, email):
            return False, "Failed RFC syntax check."

        local, _, domain = email.partition("@")
        is_safe, msg = cls.validate_rule_syntax(policy_expr)
        if not is_safe:
            return False, f"AST Policy Error: {msg}"

        tree = ast.parse(policy_expr, mode="eval")
        code = compile(tree, "<ast_email_policy>", "eval")
        safe_env = {
            "__builtins__": {},
            "len": len,
            "email": email,
            "local": local,
            "domain": domain,
        }
        try:
            passed = bool(eval(code, safe_env))
            return (True, "Passed AST validation") if passed else (False, "Blocked by AST email policy.")
        except Exception as exc:
            return False, f"AST evaluation exception: {exc}"


# =====================================================================
# 3. REAL-TIME INSTAGRAM WEB API HANDLER (WITH PROXY ROTATION)
# =====================================================================

class RotatingProxyTransport(httpx.AsyncBaseTransport):
    """
    Persistent round-robin proxy transport for httpx.
    Keeps child AsyncHTTPTransport pools open so response streams can be read
    safely without premature socket closure, and automatically fails over to
    the next proxy if a proxy connection drops.
    """

    def __init__(self, proxies: Sequence[str]):
        self._proxy_urls: List[str] = [p.strip() for p in proxies if p.strip()]
        self._transports: List[Tuple[str, httpx.AsyncHTTPTransport]] = [
            (url, httpx.AsyncHTTPTransport(proxy=url, retries=1))
            for url in self._proxy_urls
        ]
        self._cycle = itertools.cycle(self._transports)
        self.last_used_proxy: Optional[str] = None

    async def handle_async_request(self, request: httpx.Request) -> httpx.Response:
        if not self._transports:
            default_transport = httpx.AsyncHTTPTransport()
            return await default_transport.handle_async_request(request)

        last_exc: Optional[Exception] = None
        for _ in range(len(self._transports)):
            proxy_url, transport = next(self._cycle)
            self.last_used_proxy = proxy_url
            try:
                return await transport.handle_async_request(request)
            except httpx.TransportError as exc:
                last_exc = exc
                continue

        raise last_exc or httpx.ConnectError("All configured proxies failed.")

    async def aclose(self) -> None:
        for _, transport in self._transports:
            await transport.aclose()


class InstagramWebAPIClient:
    """
    Handles real-time HTTP interaction with Instagram's web endpoints:
    1. Acquires a live CSRF token (`csrftoken`) and session cookies.
    2. Checks if an email is registered in Instagram's database via the
       password-recovery flow endpoint (`send_recovery_flow_email/`).
    3. Triggers Instagram's real-time password recovery email via `send_password_reset/`.
    """

    USER_AGENT = (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/131.0.0.0 Safari/537.36"
    )

    def __init__(self):
        self.csrf_token: Optional[str] = None
        self.proxy_transport: Optional[RotatingProxyTransport] = None
        self.client: httpx.AsyncClient = self._build_client()

    def _build_client(self) -> httpx.AsyncClient:
        cfg = db.load("config")
        proxies = cfg.get("instagram_proxies", []) or []
        self.proxy_transport = RotatingProxyTransport(proxies) if proxies else None
        return httpx.AsyncClient(
            timeout=15.0,
            follow_redirects=True,
            headers={"User-Agent": self.USER_AGENT},
            transport=self.proxy_transport,
        )

    async def reload_proxies(self) -> int:
        """Hot-reloads the proxy pool from config.json without restarting the bot."""
        old_client = self.client
        self.client = self._build_client()
        await old_client.aclose()
        cfg = db.load("config")
        return len(cfg.get("instagram_proxies", []) or [])

    async def refresh_csrf_session(self) -> Tuple[bool, str]:
        """Fetches fresh cookies and csrftoken from Instagram's signup page."""
        try:
            resp = await self.client.get("https://www.instagram.com/accounts/emailsignup/")
            csrf = self.client.cookies.get("csrftoken")
            if not csrf:
                match = re.search(r'"csrf_token":"([a-zA-Z0-9_-]+)"', resp.text)
                if match:
                    csrf = match.group(1)
            if csrf:
                self.csrf_token = csrf
                sessions = db.load("sessions")
                sessions["ig_csrf_cache"] = {
                    "csrf_token": csrf[:10] + "...",
                    "proxy": (self.proxy_transport.last_used_proxy if self.proxy_transport else "direct"),
                    "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                }
                db.save("sessions", sessions)
                return True, csrf
            return False, "CSRF token not returned by server (IP may be rate-limited)."
        except Exception as e:
            return False, f"Network error acquiring CSRF: {e}"

    def _build_ajax_headers(self, referer: str) -> Dict[str, str]:
        cfg = db.load("config")
        return {
            "User-Agent": self.USER_AGENT,
            "Accept": "*/*",
            "Accept-Language": "en-US,en;q=0.9",
            "Content-Type": "application/x-www-form-urlencoded",
            "X-CSRFToken": self.csrf_token or "",
            "X-IG-App-ID": cfg.get("ig_app_id", "936619743392459"),
            "X-Instagram-AJAX": "1018880011",
            "X-Requested-With": "XMLHttpRequest",
            "Origin": "https://www.instagram.com",
            "Referer": referer,
        }

    async def check_email_availability(self, email: str) -> Dict[str, Any]:
        """
        Checks if an email is associated with a recoverable Instagram account
        by querying the password-recovery flow endpoint. This is far more
        accurate than the signup-validation endpoint, which merely reports
        whether an email has ever been "taken" during signup.
        """
        if not self.csrf_token:
            ok, info = await self.refresh_csrf_session()
            if not ok:
                return {"ok": False, "registered": False, "message": info}

        url = "https://www.instagram.com/api/v1/accounts/send_recovery_flow_email/"
        headers = self._build_ajax_headers("https://www.instagram.com/accounts/password/reset/")
        payload = {"email": email}

        try:
            resp = await self.client.post(url, data=payload, headers=headers)
            if resp.status_code == 403:
                await self.refresh_csrf_session()
                headers = self._build_ajax_headers("https://www.instagram.com/accounts/password/reset/")
                resp = await self.client.post(url, data=payload, headers=headers)

            data = resp.json()
            error_msg = (data.get("message") or "").lower()
            errors = data.get("errors", {}) or {}

            # Look for explicit "not found" / "no account" indications
            not_found_signals = (
                "user not found",
                "no account",
                "couldn't find",
                "could not find",
                "not associated",
                "no users found",
            )
            if any(sig in error_msg for sig in not_found_signals):
                return {
                    "ok": True,
                    "registered": False,
                    "code": "not_found",
                    "message": "No recoverable Instagram account is associated with this email."
                }

            # Some responses nest error information in the errors dict
            for field_errors in errors.values():
                if isinstance(field_errors, list):
                    for err in field_errors:
                        msg = (err.get("message") or "").lower()
                        if any(sig in msg for sig in not_found_signals):
                            return {
                                "ok": True,
                                "registered": False,
                                "code": err.get("code", "not_found"),
                                "message": "No recoverable Instagram account is associated with this email."
                            }

            # A successful recovery flow response indicates the account exists
            if resp.status_code == 200 and (
                data.get("status") == "ok"
                or "sent" in error_msg
                or data.get("flow")
                or data.get("email")
            ):
                return {
                    "ok": True,
                    "registered": True,
                    "code": "recoverable",
                    "message": "A recoverable Instagram account is associated with this email."
                }

            # Any response that reaches here is ambiguous (e.g. rate-limited)
            return {
                "ok": False,
                "registered": False,
                "code": f"http_{resp.status_code}",
                "message": error_msg or "Rate-limited or unexpected response from Instagram."
            }
        except Exception as e:
            return {"ok": False, "registered": False, "code": "exception", "message": str(e)}

    async def send_password_reset_email(self, email: str) -> Dict[str, Any]:
        """
        Sends a real-time POST request to Instagram's web account recovery endpoint
        (`send_password_reset`) to dispatch a reset link to the target email/Gmail.
        """
        if not self.csrf_token:
            ok, info = await self.refresh_csrf_session()
            if not ok:
                return {"ok": False, "sent": False, "message": info}

        url = "https://www.instagram.com/api/v1/accounts/send_password_reset/"
        headers = self._build_ajax_headers("https://www.instagram.com/accounts/password/reset/")
        payload = {"user_email": email}

        try:
            resp = await self.client.post(url, data=payload, headers=headers)
            if resp.status_code == 403:
                await self.refresh_csrf_session()
                headers = self._build_ajax_headers("https://www.instagram.com/accounts/password/reset/")
                resp = await self.client.post(url, data=payload, headers=headers)

            data = resp.json()
            status = data.get("status")
            toast_msg = data.get("toast_message") or data.get("message") or ""
            obfuscated = data.get("obfuscated_email", email)

            if resp.status_code == 200 and (status == "ok" or "sent" in toast_msg.lower()):
                return {
                    "ok": True,
                    "sent": True,
                    "obfuscated_email": obfuscated,
                    "message": toast_msg or f"Reset link dispatched to {obfuscated}."
                }

            return {
                "ok": False,
                "sent": False,
                "message": toast_msg or f"Instagram rejected reset request (HTTP {resp.status_code})."
            }
        except Exception as e:
            return {"ok": False, "sent": False, "message": f"Request error: {e}"}


ig_client = InstagramWebAPIClient()


# =====================================================================
# 4. TELEGRAM BOT API 9.4+ COLORED INLINE KEYBOARD BUILDER
# =====================================================================

def btn(text: str, callback_data: str, style: str = "") -> Dict[str, Any]:
    """
    Builds a Telegram Bot API 9.4+ InlineKeyboardButton supporting native colored buttons:
    style values: "primary" (blue), "success" (green), "danger" (red), or "" (default).
    """
    button: Dict[str, Any] = {"text": text, "callback_data": callback_data}
    if style in ("primary", "success", "danger"):
        button["style"] = style
    return button


def build_auth_gate_keyboard(is_registered: bool) -> Dict[str, Any]:
    """Shows Register button for new users, or Login button if already registered."""
    if not is_registered:
        return {
            "inline_keyboard": [
                [btn("📝 Register New Account", "auth_register", style="success")],
                [btn("ℹ️ Bot Status & Info", "auth_info", style="primary")]
            ]
        }
    return {
        "inline_keyboard": [
            [btn("🔐 Login to Account", "auth_login", style="primary")],
            [btn("ℹ️ Bot Status & Info", "auth_info", style="success")]
        ]
    }


def build_main_menu_keyboard(user_id: int) -> Dict[str, Any]:
    cfg = db.load("config")
    user = db.get_user(user_id) or {}
    is_premium = (user.get("tier") == "premium")

    rows = [
        [btn("🔍 Check Email & Reset Flow", "menu_start_email", style="primary")],
        [
            btn("📜 My Email Logs", "menu_email_logs", style="success"),
            btn("📨 Reset Links Sent", "menu_reset_stats", style="primary")
        ],
        [
            btn("⚙️ Settings & Quota", "menu_settings", style="success"),
            btn("🚪 Logout", "menu_logout", style="danger")
        ]
    ]

    if not is_premium:
        rows.append([
            btn("⭐ Upgrade via Telegram Stars", "buy_premium", style="success"),
            btn("🇮🇳 Upgrade via UPI", "buy_upi", style="primary")
        ])

    if user_id == cfg.get("owner_id"):
        rows.append([btn("👑 Owner Control Panel", "owner_panel", style="danger")])
    return {"inline_keyboard": rows}


def build_email_action_keyboard(email: str) -> Dict[str, Any]:
    """
    Two core real-time workflow buttons:
    1. Sending Reset Mail
    2. Check Email & Back
    """
    return {
        "inline_keyboard": [
            [btn("1️⃣ Send Reset Mail (Real-Time API)", f"act_reset|{email}", style="success")],
            [btn("2️⃣ Check Email & Back", f"act_recheck|{email}", style="primary")],
            [btn("⬅️ Back to Main Menu", "menu_home", style="danger")]
        ]
    }


def build_owner_keyboard() -> Dict[str, Any]:
    cfg = db.load("config")
    maint_status = "ON 🔴" if cfg.get("maintenance_mode") else "OFF 🟢"
    proxy_count = len(cfg.get("instagram_proxies", []) or [])
    return {
        "inline_keyboard": [
            [
                btn(f"🛠 Maintenance: {maint_status}", "own_toggle_maint", style="danger"),
                btn("📡 Real-Time View", "own_realtime", style="primary")
            ],
            [
                btn("🖼 Set Welcome Photo/Video", "own_set_media", style="success"),
                btn("🗑 Clear Welcome Media", "own_clear_media", style="danger")
            ],
            [
                btn(f"🌐 Proxies ({proxy_count})", "own_proxies", style="success"),
                btn("🇮🇳 Set UPI ID & Price", "own_set_upi", style="primary")
            ],
            [
                btn("🔑 Session & CSRF Manager", "own_sessions", style="primary"),
                btn("🧠 AST Email Policy", "own_ast_policy", style="success")
            ],
            [
                btn("🚫 Ban / Unban User", "own_ban_user", style="danger"),
                btn("⭐ Toggle User Premium", "own_toggle_prem", style="primary")
            ],
            [
                btn("📋 All Data Logs", "own_all_logs", style="success"),
                btn("⬅️ Back to User Menu", "menu_home", style="primary")
            ]
        ]
    }


# =====================================================================
# 5. TELEGRAM ASYNC BOT ENGINE (POLLING & MEDIA FRAME RENDERER)
# =====================================================================

class TelegramBotApp:
    def __init__(self):
        cfg = db.load("config")
        self.token = cfg["bot_token"]
        self.base_url = f"https://api.telegram.org/bot{self.token}"
        self.http = httpx.AsyncClient(timeout=30.0)
        self.offset = 0

    async def api(self, method: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        resp = await self.http.post(f"{self.base_url}/{method}", json=payload)
        return resp.json()

    async def send_menu_with_frame(
        self,
        chat_id: int,
        text: str,
        reply_markup: Dict[str, Any]
    ) -> None:
        """
        Renders the Owner-configured photo/video welcome frame at the top of the menu
        if enabled, falling back to a clean HTML message.
        """
        cfg = db.load("config")
        media = cfg.get("welcome_media", {})
        if media.get("enabled") and media.get("file_id"):
            m_type = media.get("media_type", "photo")
            if m_type == "video":
                await self.api("sendVideo", {
                    "chat_id": chat_id,
                    "video": media["file_id"],
                    "caption": text,
                    "parse_mode": "HTML",
                    "reply_markup": reply_markup
                })
                return
            else:
                await self.api("sendPhoto", {
                    "chat_id": chat_id,
                    "photo": media["file_id"],
                    "caption": text,
                    "parse_mode": "HTML",
                    "reply_markup": reply_markup
                })
                return

        await self.api("sendMessage", {
            "chat_id": chat_id,
            "text": text,
            "parse_mode": "HTML",
            "reply_markup": reply_markup
        })

    def _hash_pass(self, raw: str) -> str:
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    def _get_quota_info(self, user_id: int) -> Tuple[int, int, int]:
        cfg = db.load("config")
        user = db.check_and_reset_daily_quota(user_id)
        tier = user.get("tier", "free")

        # Auto-downgrade if premium expired
        if tier == "premium" and user.get("premium_expiry"):
            try:
                if datetime.fromisoformat(user["premium_expiry"]) < datetime.now():
                    user["tier"] = "free"
                    user.pop("premium_expiry", None)
                    db.save_user(user_id, user)
                    tier = "free"
            except Exception:
                pass

        limit = cfg["premium_daily_limit"] if tier == "premium" else cfg["free_daily_limit"]
        used = user.get("daily_used", 0)
        return used, limit, max(0, limit - used)

    # -----------------------------------------------------------------
    # Telegram Stars Payment Lifecycle
    # -----------------------------------------------------------------
    async def handle_pre_checkout_query(self, pcq: Dict[str, Any]) -> None:
        """Answer pre_checkout_query immediately so Telegram does not time out."""
        await self.api("answerPreCheckoutQuery", {
            "pre_checkout_query_id": pcq["id"],
            "ok": True,
        })

    async def _handle_successful_payment(self, msg: Dict[str, Any]) -> None:
        """Upgrade the payer to premium upon successful Telegram Stars payment."""
        user_id = msg["from"]["id"]
        chat_id = msg["chat"]["id"]
        payment = msg["successful_payment"]

        cfg = db.load("config")
        duration = int(cfg.get("premium_duration_days", 30))

        user = db.get_user(user_id)
        if not user:
            return

        charge_id = payment.get("telegram_payment_charge_id")
        if user.get("last_charge_id") == charge_id:
            return  # Idempotency guard

        user["tier"] = "premium"
        user["premium_expiry"] = (datetime.now() + timedelta(days=duration)).isoformat()
        user["last_charge_id"] = charge_id
        db.save_user(user_id, user)

        db.log_event(
            user_id, "", "stars_payment", "SUCCESS",
            f"Upgraded to premium for {duration} days. Charge: {charge_id}",
        )

        await self.api("sendMessage", {
            "chat_id": chat_id,
            "text": (
                f"🎉 <b>Premium Activated via Telegram Stars!</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"💎 <b>Tier:</b> PREMIUM\n"
                f"⚡ <b>Daily Quota:</b> {cfg.get('premium_daily_limit', 5)} requests/day\n"
                f"📅 <b>Valid Until:</b> <code>{user['premium_expiry'][:10]}</code>"
            ),
            "parse_mode": "HTML",
            "reply_markup": build_main_menu_keyboard(user_id),
        })

    # -----------------------------------------------------------------
    # Incoming Message Handler
    # -----------------------------------------------------------------
    async def handle_message(self, msg: Dict[str, Any]) -> None:
        chat_id = msg["chat"]["id"]
        user_id = msg["from"]["id"]
        username = msg["from"].get("username", "User")
        text = msg.get("text", "").strip()

        # Always process payments first so they complete even during maintenance
        if "successful_payment" in msg:
            await self._handle_successful_payment(msg)
            return

        cfg = db.load("config")
        is_owner = (user_id == cfg.get("owner_id"))

        # Check Maintenance Mode
        if cfg.get("maintenance_mode") and not is_owner:
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🛠 <b>Maintenance Mode Active</b>\nThe bot is currently undergoing scheduled maintenance. Please try again later.",
                "parse_mode": "HTML"
            })
            return

        user = db.get_user(user_id)
        if user and user.get("banned") and not is_owner:
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🚫 <b>Access Denied:</b> Your account has been suspended by the administrator.",
                "parse_mode": "HTML"
            })
            return

        state = db.get_state(user_id)
        step = state.get("step", "idle")

        # Handle /start command
        if text.startswith("/start"):
            db.clear_state(user_id)
            if not user or not user.get("registered"):
                welcome_text = (
                    f"✨ <b>Welcome, @{username}!</b>\n"
                    "━━━━━━━━━━━━━━━━━━━━━━\n"
                    "You are not registered in our database yet.\n"
                    "Tap <b>Register New Account</b> below to create your credentials."
                )
                await self.send_menu_with_frame(chat_id, welcome_text, build_auth_gate_keyboard(False))
                return

            if not user.get("logged_in"):
                welcome_text = (
                    f"👋 <b>Welcome back, @{username}!</b>\n"
                    "━━━━━━━━━━━━━━━━━━━━━━\n"
                    "Your account is already registered. No need to register again.\n"
                    "Tap <b>Login to Account</b> to unlock the dashboard."
                )
                await self.send_menu_with_frame(chat_id, welcome_text, build_auth_gate_keyboard(True))
                return

            used, limit, rem = self._get_quota_info(user_id)
            menu_text = (
                f"🎛 <b>Main Control Dashboard</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"👤 <b>User:</b> @{username} (<code>{user_id}</code>)\n"
                f"💎 <b>Tier:</b> {user.get('tier', 'free').upper()}\n"
                f"⚡ <b>Daily Quota:</b> {used}/{limit} used ({rem} remaining)\n"
                f"📨 <b>Total Resets Sent:</b> {user.get('reset_sent_count', 0)}"
            )
            await self.send_menu_with_frame(chat_id, menu_text, build_main_menu_keyboard(user_id))
            return

        # Handle Owner Media Upload (Photo / Video Frame)
        if step == "owner_awaiting_media" and is_owner:
            file_id = None
            m_type = "photo"
            if "photo" in msg and msg["photo"]:
                file_id = msg["photo"][-1]["file_id"]
                m_type = "photo"
            elif "video" in msg and msg["video"]:
                file_id = msg["video"]["file_id"]
                m_type = "video"

            if not file_id:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "⚠️ Please upload a valid <b>Photo</b> or <b>Video</b>.",
                    "parse_mode": "HTML"
                })
                return

            cfg["welcome_media"] = {"enabled": True, "media_type": m_type, "file_id": file_id}
            db.save("config", cfg)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"✅ <b>Welcome {m_type.upper()} Frame Updated!</b>\nAll users will now see this media frame at the top of the bot menu.",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # Handle Owner Proxy Pool Update
        if step == "owner_awaiting_proxies" and is_owner:
            if text.lower() == "clear":
                cfg["instagram_proxies"] = []
            else:
                proxies = [line.strip() for line in text.splitlines() if line.strip()]
                cfg["instagram_proxies"] = proxies
            db.save("config", cfg)
            count = await ig_client.reload_proxies()
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"✅ <b>Instagram Proxy Pool Reloaded!</b>\nActive proxies in rotation: <b>{count}</b>",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # Handle Owner UPI Settings Update
        if step == "owner_awaiting_upi" and is_owner:
            parts = [p.strip() for p in text.split("|")]
            cfg["upi_id"] = parts[0]
            if len(parts) > 1 and parts[1].isdigit():
                cfg["upi_price_inr"] = int(parts[1])
            db.save("config", cfg)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"✅ <b>UPI Config Updated!</b>\nVPA: <code>{cfg['upi_id']}</code> | Price: ₹{cfg['upi_price_inr']}",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # Handle UPI Proof (screenshot or UTR forwarded to owner with 1-click Approve/Reject)
        if step == "awaiting_upi_proof":
            owner_id = cfg.get("owner_id")
            if owner_id:
                await self.api("forwardMessage", {
                    "chat_id": owner_id,
                    "from_chat_id": chat_id,
                    "message_id": msg["message_id"],
                })
                await self.api("sendMessage", {
                    "chat_id": owner_id,
                    "text": (
                        f"💳 <b>UPI Payment Verification Request</b>\n"
                        f"👤 <b>User:</b> @{username} (<code>{user_id}</code>)\n"
                        f"💰 <b>Expected Amount:</b> ₹{cfg.get('upi_price_inr', 199)}\n"
                        f"Tap below to instantly upgrade or reject:"
                    ),
                    "parse_mode": "HTML",
                    "reply_markup": {
                        "inline_keyboard": [
                            [
                                btn("✅ Approve Premium", f"upi_ok|{user_id}", style="success"),
                                btn("❌ Reject", f"upi_no|{user_id}", style="danger")
                            ]
                        ]
                    }
                })
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "✅ Payment proof sent to the administrator! You will receive a notification here as soon as it is approved.",
                "reply_markup": build_main_menu_keyboard(user_id)
            })
            return

        # Handle Registration Password Setup
        if step == "awaiting_register_pass":
            if len(text) < 4:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "⚠️ Password must be at least 4 characters. Send again:"
                })
                return
            new_user = {
                "user_id": user_id,
                "username": username,
                "registered": True,
                "logged_in": True,
                "password_hash": self._hash_pass(text),
                "tier": "premium" if is_owner else "free",
                "banned": False,
                "daily_used": 0,
                "last_quota_date": date.today().isoformat(),
                "reset_sent_count": 0,
                "email_checks_count": 0,
                "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            }
            db.save_user(user_id, new_user)
            db.clear_state(user_id)
            await self.send_menu_with_frame(
                chat_id,
                "✅ <b>Registration Complete & Logged In!</b>\nWelcome to the main dashboard.",
                build_main_menu_keyboard(user_id)
            )
            return

        # Handle Login Password Verification
        if step == "awaiting_login_pass":
            if not user or self._hash_pass(text) != user.get("password_hash"):
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "❌ <b>Invalid password.</b> Please try again or press /start:",
                    "parse_mode": "HTML"
                })
                return
            user["logged_in"] = True
            db.save_user(user_id, user)
            db.clear_state(user_id)
            await self.send_menu_with_frame(
                chat_id,
                "🔓 <b>Login Successful!</b>\nSelect an action from the menu below:",
                build_main_menu_keyboard(user_id)
            )
            return

        # Handle Email Submission for Instagram Check & Reset Flow
        if step == "awaiting_email":
            if not user or not user.get("logged_in"):
                await self.api("sendMessage", {"chat_id": chat_id, "text": "Please login first via /start."})
                return

            used, limit, rem = self._get_quota_info(user_id)
            if rem <= 0 and not is_owner:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": (
                        f"⛔ <b>Daily Limit Reached ({used}/{limit})</b>\n"
                        "Free users get 2 queries/day and Premium users get 5 queries/day."
                    ),
                    "parse_mode": "HTML",
                    "reply_markup": build_main_menu_keyboard(user_id)
                })
                db.clear_state(user_id)
                return

            # 1. Run AST Email Validation
            ast_ok, ast_msg = ASTEmailValidator.check_email(text, cfg.get("ast_email_policy", ""))
            if not ast_ok:
                db.log_event(user_id, text, "ast_check", "BLOCKED", ast_msg)
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": f"🛡 <b>AST Security Validator Rejected Email:</b>\n<code>{ast_msg}</code>",
                    "parse_mode": "HTML"
                })
                return

            # 2. Query Instagram Server for Email Availability
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"⏳ <b>Connecting to Instagram API...</b>\nChecking database status for <code>{text}</code>",
                "parse_mode": "HTML"
            })

            ig_res = await ig_client.check_email_availability(text)
            user["email_checks_count"] = user.get("email_checks_count", 0) + 1
            db.save_user(user_id, user)
            db.log_event(
                user_id, text, "check_email",
                "FOUND" if ig_res.get("registered") else "NOT_FOUND",
                ig_res.get("message", "")
            )
            db.clear_state(user_id)

            status_badge = "🟢 <b>REGISTERED IN INSTAGRAM DB</b>" if ig_res.get("registered") else "🟡 <b>NOT REGISTERED (AVAILABLE)</b>"
            if not ig_res.get("ok"):
                status_badge = "🔴 <b>API / RATE-LIMIT NOTICE</b>"

            result_text = (
                f"📡 <b>Instagram Live Query Result</b>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"📧 <b>Email:</b> <code>{text}</code>\n"
                f"🧠 <b>AST Check:</b> Passed\n"
                f"📊 <b>Database Status:</b> {status_badge}\n"
                f"💬 <b>Server Response:</b> <code>{ig_res.get('message')}</code>\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"Choose your next real-time action below:"
            )
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": result_text,
                "parse_mode": "HTML",
                "reply_markup": build_email_action_keyboard(text)
            })
            return

        # Handle Owner Ban/Unban Input
        if step == "owner_awaiting_ban" and is_owner:
            target_id_str = text.strip()
            users = db.load("users")
            if target_id_str not in users:
                await self.api("sendMessage", {"chat_id": chat_id, "text": "❌ User ID not found in database."})
                return
            users[target_id_str]["banned"] = not users[target_id_str].get("banned", False)
            new_state = "BANNED 🚫" if users[target_id_str]["banned"] else "UNBANNED ✅"
            db.save("users", users)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"User <code>{target_id_str}</code> is now <b>{new_state}</b>.",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # Handle Owner Toggle Premium Input
        if step == "owner_awaiting_prem" and is_owner:
            target_id_str = text.strip()
            users = db.load("users")
            if target_id_str not in users:
                await self.api("sendMessage", {"chat_id": chat_id, "text": "❌ User ID not found in database."})
                return
            cur = users[target_id_str].get("tier", "free")
            users[target_id_str]["tier"] = "premium" if cur == "free" else "free"
            if users[target_id_str]["tier"] == "premium":
                users[target_id_str]["premium_expiry"] = (
                    datetime.now() + timedelta(days=cfg.get("premium_duration_days", 30))
                ).isoformat()
            else:
                users[target_id_str].pop("premium_expiry", None)
            db.save("users", users)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"⭐ User <code>{target_id_str}</code> tier set to <b>{users[target_id_str]['tier'].upper()}</b> (Quota: {5 if users[target_id_str]['tier']=='premium' else 2}/day).",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # Handle Owner AST Policy Update
        if step == "owner_awaiting_ast" and is_owner:
            valid, msg = ASTEmailValidator.validate_rule_syntax(text)
            if not valid:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": f"❌ <b>Rejected AST Expression:</b>\n<code>{msg}</code>",
                    "parse_mode": "HTML"
                })
                return
            cfg["ast_email_policy"] = text
            db.save("config", cfg)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"✅ <b>AST Email Policy Updated:</b>\n<code>{text}</code>",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

    # -----------------------------------------------------------------
    # Callback Query (Inline Button) Handler
    # -----------------------------------------------------------------
    async def handle_callback(self, cb: Dict[str, Any]) -> None:
        cb_id = cb["id"]
        user_id = cb["from"]["id"]
        chat_id = cb["message"]["chat"]["id"]
        data = cb.get("data", "")

        cfg = db.load("config")
        is_owner = (user_id == cfg.get("owner_id"))
        user = db.get_user(user_id)

        await self.api("answerCallbackQuery", {"callback_query_id": cb_id})

        if cfg.get("maintenance_mode") and not is_owner:
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🛠 Bot is currently under maintenance."
            })
            return

        # --- Registration & Login Callbacks ---
        if data == "auth_register":
            if user and user.get("registered"):
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "ℹ️ You are already registered! Use the Login button.",
                    "reply_markup": build_auth_gate_keyboard(True)
                })
                return
            db.set_state(user_id, "awaiting_register_pass")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "📝 <b>Account Registration</b>\nPlease send a password (min 4 characters) to register your account:",
                "parse_mode": "HTML"
            })
            return

        if data == "auth_login":
            if not user or not user.get("registered"):
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "⚠️ Please register first.",
                    "reply_markup": build_auth_gate_keyboard(False)
                })
                return
            db.set_state(user_id, "awaiting_login_pass")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🔐 <b>Account Login</b>\nPlease enter your password:",
                "parse_mode": "HTML"
            })
            return

        if data == "auth_info":
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    "ℹ️ <b>Service Quotas & Architecture</b>\n"
                    "• <b>Free Users:</b> 2 real-time reset/check dispatches per day\n"
                    "• <b>Premium Users:</b> 5 real-time dispatches per day\n"
                    "• <b>Security:</b> AST Syntax & Policy Validation"
                ),
                "parse_mode": "HTML"
            })
            return

        # Require logged-in state for menu actions
        if not user or not user.get("logged_in"):
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🔒 Session expired or logged out. Send /start to log in."
            })
            return

        # --- Main User Menu Callbacks ---
        if data == "menu_home":
            db.clear_state(user_id)
            used, limit, rem = self._get_quota_info(user_id)
            await self.send_menu_with_frame(
                chat_id,
                (
                    f"🎛 <b>Main Dashboard</b>\n"
                    f"💎 <b>Tier:</b> {user.get('tier', 'free').upper()} | "
                    f"⚡ <b>Quota:</b> {used}/{limit} used today"
                ),
                build_main_menu_keyboard(user_id)
            )
            return

        if data == "menu_start_email":
            db.set_state(user_id, "awaiting_email")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    "📧 <b>Send Target Email / Gmail Address</b>\n"
                    "Enter the email address you want to check against Instagram's server:"
                ),
                "parse_mode": "HTML"
            })
            return

        # --- Premium: Telegram Stars ---
        if data == "buy_premium":
            price = int(cfg.get("premium_stars_price", 100))
            duration = int(cfg.get("premium_duration_days", 30))
            await self.api("sendInvoice", {
                "chat_id": chat_id,
                "title": f"Premium Access ({duration} Days)",
                "description": (
                    f"Unlock {cfg.get('premium_daily_limit', 5)} daily real-time reset/check requests "
                    f"for {duration} days."
                ),
                "payload": f"premium:{user_id}",
                "provider_token": "",
                "currency": "XTR",
                "prices": [{"label": "Premium Plan", "amount": price}],
                "start_parameter": "premium_upgrade",
            })
            return

        # --- Premium: UPI ---
        if data == "buy_upi":
            upi_id = cfg.get("upi_id")
            price = cfg.get("upi_price_inr", 199)
            if not upi_id:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": "⚠️ UPI ID is not configured yet. Please use Telegram Stars or contact the owner.",
                })
                return
            db.set_state(user_id, "awaiting_upi_proof")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"🇮🇳 <b>Upgrade to Premium via UPI</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"• <b>UPI ID (VPA):</b> <code>{upi_id}</code>\n"
                    f"• <b>Amount:</b> ₹{price}\n"
                    f"• <b>Plan:</b> {cfg.get('premium_daily_limit', 5)} requests/day for {cfg.get('premium_duration_days', 30)} days\n\n"
                    f"📸 <b>Next Step:</b> Send your payment screenshot or 12-digit UTR number here to trigger instant owner verification."
                ),
                "parse_mode": "HTML",
            })
            return

        # Button 1: Real-Time Password Reset Link Dispatch
        if data.startswith("act_reset|"):
            email = data.split("|", 1)[1]
            used, limit, rem = self._get_quota_info(user_id)
            if rem <= 0 and not is_owner:
                await self.api("sendMessage", {
                    "chat_id": chat_id,
                    "text": f"⛔ Daily quota exhausted ({used}/{limit}). Upgrade to Premium for 5 daily uses.",
                    "reply_markup": build_main_menu_keyboard(user_id)
                })
                return

            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"📨 <b>Dispatching Real-Time Reset Request...</b>\nTarget: <code>{email}</code>",
                "parse_mode": "HTML"
            })

            res = await ig_client.send_password_reset_email(email)

            user = db.check_and_reset_daily_quota(user_id)
            user["daily_used"] = user.get("daily_used", 0) + 1
            if res.get("sent"):
                user["reset_sent_count"] = user.get("reset_sent_count", 0) + 1
            db.save_user(user_id, user)

            db.log_event(
                user_id, email, "send_reset",
                "SUCCESS" if res.get("sent") else "FAILED",
                res.get("message", "")
            )

            used, limit, rem = self._get_quota_info(user_id)
            status_header = "✅ <b>Reset Email Dispatched!</b>" if res.get("sent") else "⚠️ <b>Reset Dispatch Notice</b>"
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"{status_header}\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"📧 <b>Target Email:</b> <code>{email}</code>\n"
                    f"🔒 <b>Obfuscated Route:</b> <code>{res.get('obfuscated_email', 'N/A')}</code>\n"
                    f"📡 <b>API Response:</b> <code>{res.get('message')}</code>\n"
                    f"⚡ <b>Daily Quota Left:</b> {rem}/{limit}"
                ),
                "parse_mode": "HTML",
                "reply_markup": build_email_action_keyboard(email)
            })
            return

        # Button 2: Just Check Email Available or Not & Go Back
        if data.startswith("act_recheck|"):
            email = data.split("|", 1)[1]
            ig_res = await ig_client.check_email_availability(email)
            db.log_event(
                user_id, email, "check_email",
                "FOUND" if ig_res.get("registered") else "NOT_FOUND",
                ig_res.get("message", "")
            )
            status_str = "REGISTERED (Account Exists)" if ig_res.get("registered") else "AVAILABLE (No Account Found)"
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"🔍 <b>Availability Check Complete</b>\n"
                    f"📧 <b>Email:</b> <code>{email}</code>\n"
                    f"📌 <b>Status:</b> <b>{status_str}</b>\n"
                    f"💬 <b>Detail:</b> <code>{ig_res.get('message')}</code>\n\n"
                    f"Returning to Main Menu..."
                ),
                "parse_mode": "HTML",
                "reply_markup": build_main_menu_keyboard(user_id)
            })
            return

        if data == "menu_email_logs":
            logs = db.load("logs").get("queries", [])
            user_logs = [l for l in logs if l.get("user_id") == user_id][:10]
            if not user_logs:
                txt = "📜 <b>Your Email Logs:</b>\nNo queries recorded yet."
            else:
                lines = [
                    f"• <code>{l['time']}</code> | <b>{l['action']}</b> | <code>{l['email']}</code> ({l['status']})"
                    for l in user_logs
                ]
                txt = "📜 <b>Your Recent 10 Email Logs:</b>\n" + "\n".join(lines)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": txt,
                "parse_mode": "HTML",
                "reply_markup": build_main_menu_keyboard(user_id)
            })
            return

        if data == "menu_reset_stats":
            used, limit, rem = self._get_quota_info(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"📨 <b>Reset Link & Check Statistics</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"• <b>Reset Links Sent:</b> {user.get('reset_sent_count', 0)}\n"
                    f"• <b>Email Availability Checks:</b> {user.get('email_checks_count', 0)}\n"
                    f"• <b>Today's Quota Used:</b> {used}/{limit} ({rem} left)"
                ),
                "parse_mode": "HTML",
                "reply_markup": build_main_menu_keyboard(user_id)
            })
            return

        if data == "menu_settings":
            used, limit, rem = self._get_quota_info(user_id)
            expiry = user.get("premium_expiry", "N/A")[:10] if user.get("premium_expiry") else "N/A"
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"⚙️ <b>Account Settings & Plan</b>\n"
                    f"━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"• <b>User ID:</b> <code>{user_id}</code>\n"
                    f"• <b>Plan Tier:</b> {user.get('tier', 'free').upper()}\n"
                    f"• <b>Premium Expiry:</b> <code>{expiry}</code>\n"
                    f"• <b>Daily Allowance:</b> {limit} requests/day (Free=2, Premium=5)\n"
                    f"• <b>Registered On:</b> {user.get('created_at', 'N/A')}"
                ),
                "parse_mode": "HTML",
                "reply_markup": build_main_menu_keyboard(user_id)
            })
            return

        if data == "menu_logout":
            user["logged_in"] = False
            db.save_user(user_id, user)
            db.clear_state(user_id)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🚪 <b>Logged Out Successfully.</b>\nTap Login below whenever you want to return.",
                "parse_mode": "HTML",
                "reply_markup": build_auth_gate_keyboard(True)
            })
            return

        # =============================================================
        # OWNER CONTROL PANEL HANDLERS
        # =============================================================
        if not is_owner:
            return

        if data == "owner_panel":
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "👑 <b>Owner Administration & Real-Time Control Panel</b>",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        # One-click UPI Approve / Reject callbacks
        if data.startswith("upi_ok|"):
            target_uid = int(data.split("|", 1)[1])
            t_user = db.get_user(target_uid)
            if not t_user:
                await self.api("sendMessage", {"chat_id": chat_id, "text": "❌ User not found."})
                return
            duration = int(cfg.get("premium_duration_days", 30))
            t_user["tier"] = "premium"
            t_user["premium_expiry"] = (datetime.now() + timedelta(days=duration)).isoformat()
            db.save_user(target_uid, t_user)
            db.log_event(target_uid, "", "upi_payment", "APPROVED", f"Approved by owner for {duration} days")

            await self.api("sendMessage", {
                "chat_id": target_uid,
                "text": (
                    f"🎉 <b>UPI Payment Approved!</b>\n"
                    f"Your account is now upgraded to <b>PREMIUM</b> ({cfg.get('premium_daily_limit', 5)} requests/day) "
                    f"until <code>{t_user['premium_expiry'][:10]}</code>."
                ),
                "parse_mode": "HTML",
                "reply_markup": build_main_menu_keyboard(target_uid)
            })
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"✅ Approved Premium for UID <code>{target_uid}</code>.",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        if data.startswith("upi_no|"):
            target_uid = int(data.split("|", 1)[1])
            await self.api("sendMessage", {
                "chat_id": target_uid,
                "text": "❌ <b>UPI Payment Verification Failed:</b> Could not verify your receipt. Please contact the administrator.",
                "parse_mode": "HTML"
            })
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"🚫 Rejected UPI request for UID <code>{target_uid}</code>.",
                "parse_mode": "HTML"
            })
            return

        if data == "own_proxies":
            proxies = cfg.get("instagram_proxies", []) or []
            p_list = "\n".join(f"• <code>{p}</code>" for p in proxies) if proxies else "None (Direct Connection)"
            db.set_state(user_id, "owner_awaiting_proxies")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"🌐 <b>Instagram Proxy Rotation Pool</b>\n"
                    f"Current proxies:\n{p_list}\n\n"
                    f"Send proxy URLs (one per line, e.g. <code>http://user:pass@ip:port</code>) "
                    f"or send <code>clear</code> to disable proxies:"
                ),
                "parse_mode": "HTML"
            })
            return

        if data == "own_set_upi":
            db.set_state(user_id, "owner_awaiting_upi")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"🇮🇳 <b>Configure UPI VPA & Price</b>\n"
                    f"Current: <code>{cfg.get('upi_id') or 'Not set'}</code> | ₹{cfg.get('upi_price_inr', 199)}\n\n"
                    f"Send in format: <code>yourname@upi | 199</code>"
                ),
                "parse_mode": "HTML"
            })
            return

        if data == "own_toggle_maint":
            cfg["maintenance_mode"] = not cfg.get("maintenance_mode", False)
            db.save("config", cfg)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": f"🛠 Maintenance Mode set to: <b>{'ON 🔴' if cfg['maintenance_mode'] else 'OFF 🟢'}</b>",
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        if data == "own_realtime":
            users = db.load("users")
            logs = db.load("logs")
            sessions = db.load("sessions")
            total_u = len(users)
            online_u = sum(1 for u in users.values() if u.get("logged_in"))
            prem_u = sum(1 for u in users.values() if u.get("tier") == "premium")
            banned_u = sum(1 for u in users.values() if u.get("banned"))
            active_flows = sum(1 for s in sessions.get("user_states", {}).values() if s.get("step") != "idle")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    "📡 <b>Real-Time System Monitor</b>\n"
                    "━━━━━━━━━━━━━━━━━━━━━━\n"
                    f"👥 <b>Total Registered Users:</b> {total_u}\n"
                    f"🟢 <b>Logged-In Sessions:</b> {online_u}\n"
                    f"⭐ <b>Premium Users:</b> {prem_u}\n"
                    f"🚫 <b>Banned Users:</b> {banned_u}\n"
                    f"🔄 <b>Active Input Flows:</b> {active_flows}\n"
                    f"🌐 <b>Proxies Active:</b> {len(cfg.get('instagram_proxies', []))}\n"
                    f"📨 <b>Global Resets Sent:</b> {logs.get('resets_sent', 0)}\n"
                    f"🔍 <b>Global Email Checks:</b> {logs.get('checks_run', 0)}"
                ),
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        if data == "own_set_media":
            db.set_state(user_id, "owner_awaiting_media")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🖼 <b>Upload Welcome Frame Media</b>\nSend a <b>Photo</b> or <b>Video</b> now. It will be displayed at the top of the menu when users start the bot:",
                "parse_mode": "HTML"
            })
            return

        if data == "own_clear_media":
            cfg["welcome_media"] = {"enabled": False, "media_type": "photo", "file_id": ""}
            db.save("config", cfg)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🗑 Welcome media frame disabled and cleared.",
                "reply_markup": build_owner_keyboard()
            })
            return

        if data == "own_sessions":
            ok, csrf_info = await ig_client.refresh_csrf_session()
            sessions = db.load("sessions")
            sessions["user_states"] = {}
            db.save("sessions", sessions)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    f"🔑 <b>Session & CSRF Manager</b>\n"
                    f"• User conversation states flushed.\n"
                    f"• Instagram CSRF Refresh: <b>{'SUCCESS' if ok else 'FAILED'}</b>\n"
                    f"• Token/Info: <code>{csrf_info[:30]}</code>"
                ),
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

        if data == "own_ast_policy":
            db.set_state(user_id, "owner_awaiting_ast")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": (
                    "🧠 <b>AST Email Filter Policy</b>\n"
                    f"Current AST Expression:\n<code>{cfg.get('ast_email_policy')}</code>\n\n"
                    "Send a new valid Python boolean expression using variables <code>email</code>, <code>local</code>, <code>domain</code>:"
                ),
                "parse_mode": "HTML"
            })
            return

        if data == "own_ban_user":
            db.set_state(user_id, "owner_awaiting_ban")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "🚫 Send the <b>Telegram User ID</b> to toggle Ban/Unban:",
                "parse_mode": "HTML"
            })
            return

        if data == "own_toggle_prem":
            db.set_state(user_id, "owner_awaiting_prem")
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": "⭐ Send the <b>Telegram User ID</b> to toggle between Free (2/day) and Premium (5/day):",
                "parse_mode": "HTML"
            })
            return

        if data == "own_all_logs":
            logs = db.load("logs").get("queries", [])[:15]
            if not logs:
                txt = "📋 <b>Global Data Logs:</b> Empty."
            else:
                lines = [
                    f"• <code>{l['time']}</code> | UID:<code>{l['user_id']}</code> | {l['action']} | <code>{l['email']}</code> -> <b>{l['status']}</b>"
                    for l in logs
                ]
                txt = "📋 <b>Latest 15 Global Logs:</b>\n" + "\n".join(lines)
            await self.api("sendMessage", {
                "chat_id": chat_id,
                "text": txt,
                "parse_mode": "HTML",
                "reply_markup": build_owner_keyboard()
            })
            return

    # -----------------------------------------------------------------
    # Main Long-Polling Loop
    # -----------------------------------------------------------------
    async def run(self) -> None:
        print("[+] Initializing Instagram CSRF session...")
        await ig_client.refresh_csrf_session()
        print("[+] Telegram Bot Polling Started (Bot API 9.4+ Colored Buttons Ready)...")
        while True:
            try:
                resp = await self.api("getUpdates", {
                    "offset": self.offset,
                    "timeout": 20,
                    "allowed_updates": ["message", "callback_query", "pre_checkout_query"]
                })
                if not resp.get("ok"):
                    await asyncio.sleep(3)
                    continue
                for upd in resp.get("result", []):
                    self.offset = upd["update_id"] + 1
                    if "message" in upd:
                        await self.handle_message(upd["message"])
                    elif "callback_query" in upd:
                        await self.handle_callback(upd["callback_query"])
                    elif "pre_checkout_query" in upd:
                        await self.handle_pre_checkout_query(upd["pre_checkout_query"])
            except Exception as exc:
                print(f"[!] Polling error: {exc}")
                await asyncio.sleep(3)


if __name__ == "__main__":
    app = TelegramBotApp()
    asyncio.run(app.run())
