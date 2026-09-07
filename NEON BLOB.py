from flask import Flask, request, jsonify, Response
import random
import threading
import time
import socket
import json
import os
import hashlib
import hmac
import secrets
import re
from collections import defaultdict, deque

app = Flask(__name__)

# ============================================================
# CONFIG
# ============================================================

WORLD_WIDTH = 5000
WORLD_HEIGHT = 5000

COIN_COUNT = 100
PLAYER_SPEED = 1                 # px per 1/60s tick (keeps old feel)
PLAYER_TIMEOUT = 30
MAX_PLAYERS = 100
MIN_KILL_RATIO = 1.18
BASE_PLAYER_RADIUS = 29
MAX_PLAYER_RADIUS = 85
SPEED_BOOST_MULTIPLIER = 1.85
POWERUP_COUNT = 18
POWERUP_DURATION = 6.0
SESSION_TIMEOUT = 60 * 60 * 24 * 7  # 7 days
PASSWORD_ITERATIONS = 310_000
MOVE_MIN_INTERVAL = 0.025          # server-side movement throttle
RATE_LIMIT_WINDOW = 60
RATE_LIMIT_MAX = 120

ACCOUNT_FILE = "accounts.json"
MAX_USERNAME_LENGTH = 16
MAX_AVATAR_BYTES = 750_000
AVATAR_MAX_DIM = 256
ALLOWED_AVATAR_TYPES = {
    "image/png": "png",
    "image/jpeg": "jpeg",
    "image/webp": "webp",
    "image/gif": "gif",
}

DEFAULT_OPTIONS = {
    "resolution": "auto",
    "quality": "high",
    "effects": "on",
    "coins": "on",
    "fps": "off",
    "joystick": "medium",
    "ui": "normal",
}

# ============================================================
# DATA
# ============================================================

players = {}  # legacy alias for the default public lobby
coins = []
servers = {}
server_counter = 0


accounts = {}
sessions = {}  # token -> {"username": str, "created": float, "last_seen": float}
request_history = defaultdict(deque)

lock = threading.RLock()

COLORS = [
    "#ff4d6d",
    "#4dabf7",
    "#51cf66",
    "#ffd43b",
    "#cc5de8",
    "#20c997",
    "#ff922b",
    "#f06595",
    "#00ffff",
    "#ffffff",
]

SKINS = [
    "normal",
    "ghost",
    "fire",
    "ice",
    "rainbow",
    "void",
    "verty",
    "colorchanging",
]

SECRET_NAMES = {
    "verity",
    "verty",
    "verity!",
    "verty!",
    "theverity",
}


# ============================================================
# ACCOUNT SYSTEM
# ============================================================

def hash_password(password, salt=None, iterations=PASSWORD_ITERATIONS):
    if salt is None:
        salt = secrets.token_hex(16)

    password_hash = hashlib.pbkdf2_hmac(
        "sha256",
        password.encode("utf-8"),
        salt.encode("utf-8"),
        iterations,
    ).hex()

    return salt, password_hash


def verify_password(password, account):
    salt = account.get("salt", "")
    stored = account.get("password_hash", "")
    iterations = int(account.get("iterations", 120_000))

    _, candidate = hash_password(
        password,
        salt=salt,
        iterations=iterations,
    )

    return hmac.compare_digest(candidate, stored)


def load_accounts():
    global accounts

    if not os.path.exists(ACCOUNT_FILE):
        accounts = {}
        return

    try:
        with open(ACCOUNT_FILE, "r", encoding="utf-8") as f:
            accounts = json.load(f)

        if not isinstance(accounts, dict):
            accounts = {}

    except Exception:
        accounts = {}


def save_accounts():
    try:
        temp_file = ACCOUNT_FILE + ".tmp"

        with open(temp_file, "w", encoding="utf-8") as f:
            json.dump(accounts, f, indent=2)

        os.replace(temp_file, ACCOUNT_FILE)

    except Exception as e:
        print("⚠️ Account save error:", e)


load_accounts()
for _account in accounts.values():
    if isinstance(_account, dict):
        _account["options"] = {**DEFAULT_OPTIONS, **(_account.get("options") or {})}


# ============================================================
# LOBBIES / SERVERS
# ============================================================

def make_server(private=False, name=None, code=None):
    global server_counter
    server_counter += 1
    server_id = f"srv-{server_counter}-{secrets.token_hex(3)}"
    server = {
        "id": server_id,
        "name": name or ("Private Server" if private else f"Public Lobby #{server_counter}"),
        "private": bool(private),
        "code": code,
        "players": {},
        "coins": [],
        "powerups": [],
        "created": time.time(),
    }
    server["coins"] = [create_coin_for_world() for _ in range(COIN_COUNT)] if 'create_coin_for_world' in globals() else []
    servers[server_id] = server
    return server

def get_server_for_player(username):
    for server in servers.values():
        if username in server["players"]:
            return server
    return None

def public_server(server):
    return {
        "id": server["id"],
        "name": server["name"],
        "private": server["private"],
        "players": len(server["players"]),
        "max_players": MAX_PLAYERS,
    }

# ============================================================
# COINS
# ============================================================

def create_coin_for_world():
    return {"x": random.randint(60, WORLD_WIDTH - 60), "y": random.randint(60, WORLD_HEIGHT - 60)}

def create_coin():
    return create_coin_for_world()

def create_powerup():
    kind = random.choice(["speed", "growth"])
    return {"id": secrets.token_hex(5), "type": kind, "x": random.randint(100, WORLD_WIDTH-100), "y": random.randint(100, WORLD_HEIGHT-100)}

def refill_powerups(server):
    while len(server["powerups"]) < POWERUP_COUNT:
        server["powerups"].append(create_powerup())

def generate_coins():
    global coins
    with lock:
        coins = [create_coin() for _ in range(COIN_COUNT)]

def ensure_public_server():
    public = [x for x in servers.values() if not x["private"] and len(x["players"]) < MAX_PLAYERS]
    if public:
        return random.choice(public)
    server = make_server(False)
    server["coins"] = [create_coin() for _ in range(COIN_COUNT)]
    refill_powerups(server)
    return server

generate_coins()
with lock:
    _initial = make_server(False)
    _initial["coins"] = [create_coin() for _ in range(COIN_COUNT)]
    refill_powerups(_initial)


# ============================================================
# HELPERS
# ============================================================

def clean_username(username):
    if not isinstance(username, str):
        return ""

    username = username.strip()

    if not username:
        return ""

    if len(username) > MAX_USERNAME_LENGTH:
        return ""

    allowed = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"

    if any(char not in allowed for char in username):
        return ""

    return username


def get_session():
    token = request.headers.get("X-Session", "")

    if not token:
        return None

    now = time.time()

    with lock:
        session = sessions.get(token)

        # Accept legacy in-memory sessions created by older versions.
        if isinstance(session, str):
            sessions[token] = {
                "username": session,
                "created": now,
                "last_seen": now,
            }
            return session

        if not isinstance(session, dict):
            return None

        if now - session.get("created", now) > SESSION_TIMEOUT:
            sessions.pop(token, None)
            return None

        session["last_seen"] = now
        return session.get("username")


def rate_limited():
    ip = request.remote_addr or "unknown"
    now = time.time()

    with lock:
        history = request_history[ip]

        while history and now - history[0] > RATE_LIMIT_WINDOW:
            history.popleft()

        if len(history) >= RATE_LIMIT_MAX:
            return True

        history.append(now)
        return False


def public_player(player):
    return {
        "username": player["username"],
        "name": player["name"],
        "x": player["x"],
        "y": player["y"],
        "score": player["score"],
        "coins": player["coins"],
        "color": player["color"],
        "skin": player["skin"],
        "avatar": bool(player.get("avatar_data")),
        "radius": player.get("radius", BASE_PLAYER_RADIUS),
        "speed_boost": max(0, player.get("speed_boost_until", 0) - time.time()),
    }


def clamp(value, minimum, maximum):
    return max(minimum, min(maximum, value))


# ============================================================
# HTML
# ============================================================

HTML = r"""
<!DOCTYPE html>
<html lang="en">
<head>

<meta charset="UTF-8">
<meta
    name="viewport"
    content="width=device-width,
             initial-scale=1.0,
             maximum-scale=1.0,
             user-scalable=no"
>

<title>LAN Blob Arena</title>

<style>

* {
    box-sizing: border-box;
    -webkit-tap-highlight-color: transparent;
}

html,
body {
    width: 100%;
    height: 100%;
    margin: 0;
    overflow: hidden;
    background: #080b12;
    color: white;
    font-family: Arial, Helvetica, sans-serif;
}

button,
input,
select {
    font: inherit;
}

button {
    cursor: pointer;
}

.hidden {
    display: none !important;
}


/* =========================================================
   MENUS
   ========================================================= */

#mainMenu,
#loginMenu,
#registerMenu,
#profileMenu,
#optionsMenu {

    position: fixed;
    inset: 0;

    display: flex;
    align-items: center;
    justify-content: center;

    background:
        radial-gradient(
            circle at center,
            #18233a 0%,
            #080b12 70%
        );

    z-index: 1000;
}

.panel {

    width: min(92vw, 480px);

    max-height: 92vh;
    overflow-y: auto;

    padding: 28px;

    border-radius: 24px;

    background: rgba(18, 24, 38, 0.96);

    border: 2px solid rgba(255,255,255,0.12);

    box-shadow:
        0 20px 70px rgba(0,0,0,0.6);

    text-align: center;
}

.title {

    margin: 0 0 8px;

    font-size: clamp(34px, 8vw, 58px);

    font-weight: 900;

    background:
        linear-gradient(
            90deg,
            #ff4d6d,
            #cc5de8,
            #4dabf7,
            #20c997,
            #ffd43b
        );

    background-size: 300%;

    color: transparent;

    background-clip: text;
    -webkit-background-clip: text;

    animation: titleGradient 6s linear infinite;
}

@keyframes titleGradient {

    0% {
        background-position: 0%;
    }

    100% {
        background-position: 300%;
    }

}

.subtitle {
    color: #aeb8cc;
    margin-bottom: 25px;
}

.menuButton {

    width: 100%;

    border: 0;

    padding: 15px;

    margin-top: 10px;

    border-radius: 14px;

    background: #263451;

    color: white;

    font-size: 17px;
    font-weight: bold;

    transition: 0.15s;
}

.menuButton:focus-visible,
.smallButton:focus-visible,
input:focus-visible,
select:focus-visible {
    outline: 3px solid rgba(109,124,255,0.65);
    outline-offset: 2px;
}

.menuButton:hover {
    transform: translateY(-2px);
    background: #33476e;
}

.menuButton:active {
    transform: scale(0.97);
}

.primary {
    background:
        linear-gradient(
            135deg,
            #7c3aed,
            #2563eb
        );
}

.danger {
    background: #7f1d1d;
}

input,
select {

    width: 100%;

    padding: 14px;

    margin-top: 10px;

    border: 2px solid #33415f;

    border-radius: 12px;

    background: #101727;

    color: white;

    outline: none;
}

input:focus,
select:focus {
    border-color: #6d7cff;
}

.error {
    color: #ff6b6b;
    min-height: 22px;
    margin-top: 10px;
}

.info {
    color: #9da9c2;
    font-size: 14px;
    margin-top: 15px;
}


/* =========================================================
   GAME
   ========================================================= */

#game {

    position: fixed;
    inset: 0;

    overflow: hidden;

    background: #0a0e17;

    display: none;

    touch-action: none;
}

#world {

    position: absolute;

    left: 0;
    top: 0;

    width: 5000px;
    height: 5000px;

    transform-origin: 0 0;

    background-color: #101725;

    background-image:
        linear-gradient(
            rgba(255,255,255,0.025) 1px,
            transparent 1px
        ),
        linear-gradient(
            90deg,
            rgba(255,255,255,0.025) 1px,
            transparent 1px
        );

    background-size: 100px 100px;

    will-change: transform;
}


/* =========================================================
   COINS
   ========================================================= */

.coin {

    position: absolute;

    width: 28px;
    height: 28px;

    transform: translate(-50%, -50%);

    border-radius: 50%;

    background:
        radial-gradient(
            circle at 35% 30%,
            #fff7a8,
            #ffd43b 40%,
            #f59f00 100%
        );

    border: 3px solid #fff1a8;

    box-shadow:
        0 0 10px #ffd43b,
        0 0 25px rgba(255,212,59,0.7);

    animation: coinFloat 1.2s ease-in-out infinite alternate;

    z-index: 5;
}

@keyframes coinFloat {

    from {
        margin-top: -3px;
    }

    to {
        margin-top: 3px;
    }

}


/* =========================================================
   PLAYERS
   ========================================================= */

.player {

    position: absolute;

    width: 58px;
    height: 58px;

    transform: translate(-50%, -50%);

    border-radius: 50%;

    border: 3px solid rgba(255,255,255,0.45);

    display: flex;
    align-items: center;
    justify-content: center;

    font-size: 24px;

    font-weight: 900;

    user-select: none;

    z-index: 20;

    will-change: transform;
}

.player.me {

    width: 66px;
    height: 66px;

    border: 4px solid white;

    z-index: 100;

    box-shadow:
        0 0 15px rgba(255,255,255,0.7),
        0 0 35px rgba(100,150,255,0.7);
}

.player-name {
.player-size {

    display: block;

    margin-top: 2px;

    font-size: 11px;

    font-weight: 600;

    opacity: 0.9;

    letter-spacing: 0.2px;
}


    position: absolute;

    top: 70px;

    left: 50%;

    transform: translateX(-50%);

    white-space: nowrap;

    max-width: 150px;

    overflow: hidden;
    text-overflow: ellipsis;

    font-size: 13px;

    font-weight: bold;

    color: white;

    text-shadow:
        0 2px 5px black,
        0 0 5px black;
}


/* =========================================================
   SKINS
   ========================================================= */

.skin-normal {
    background: var(--player-color);
}

.skin-ghost {

    background: var(--player-color);

    opacity: 0.55;

    border-style: dashed;
}

.skin-fire {

    background:
        radial-gradient(
            circle,
            #fff 0%,
            #ff922b 30%,
            #f03e3e 70%,
            #7f1d1d 100%
        );

    box-shadow:
        0 0 12px #ff922b,
        0 0 30px #f03e3e;
}

.skin-ice {

    background:
        radial-gradient(
            circle,
            #e7f5ff,
            #74c0fc,
            #1971c2
        );

    box-shadow:
        0 0 12px #74c0fc,
        0 0 30px #1971c2;
}

.skin-rainbow {

    background:
        linear-gradient(
            135deg,
            red,
            orange,
            yellow,
            lime,
            cyan,
            blue,
            violet
        );

    background-size: 400% 400%;

    animation: rainbowMove 3s linear infinite;
}

@keyframes rainbowMove {

    0% {
        background-position: 0% 50%;
    }

    100% {
        background-position: 400% 50%;
    }

}

.skin-void {

    background:
        radial-gradient(
            circle,
            #1a1028,
            #050507
        );

    border-color: #9d4edd;

    box-shadow:
        0 0 12px #7b2cbf,
        0 0 30px #3c096c;
}

.skin-verty {

    background:
        repeating-linear-gradient(
            45deg,
            #00ffff 0px,
            #00ffff 10px,
            #ff00ff 10px,
            #ff00ff 20px
        );

    animation: vertyPulse 1s ease-in-out infinite alternate;
}

@keyframes vertyPulse {

    from {
        box-shadow:
            0 0 8px #00ffff;
    }

    to {
        box-shadow:
            0 0 25px #ff00ff;
    }

}

.skin-colorchanging {

    background:
        linear-gradient(
            135deg,
            red,
            orange,
            yellow,
            lime,
            cyan,
            blue,
            violet,
            red
        );

    background-size: 500% 500%;

    animation:
        colorChanging 2.5s linear infinite;

    box-shadow:
        0 0 15px rgba(255,255,255,0.7),
        0 0 35px rgba(255,255,255,0.35);
}

@keyframes colorChanging {

    0% {
        background-position: 0% 50%;
    }

    50% {
        background-position: 100% 50%;
    }

    100% {
        background-position: 0% 50%;
    }

}


/* =========================================================
   HUD
   ========================================================= */

#hud {

    position: fixed;

    left: 12px;
    top: 12px;

    z-index: 500;

    display: flex;

    gap: 8px;

    flex-wrap: wrap;

    pointer-events: none;
}

.hudBox {

    padding: 10px 14px;

    border-radius: 12px;

    background: rgba(8,12,20,0.82);

    border: 1px solid rgba(255,255,255,0.12);

    backdrop-filter: blur(8px);

    font-weight: bold;
}

#connectionStatus {
    color: #69db7c;
}


/* =========================================================
   TOP BUTTONS
   ========================================================= */

#topButtons {

    position: fixed;

    top: 12px;
    right: 12px;

    z-index: 600;

    display: flex;

    gap: 8px;
}

.smallButton {

    border: 0;

    padding: 10px 13px;

    border-radius: 11px;

    background: rgba(15,23,42,0.9);

    color: white;

    border: 1px solid rgba(255,255,255,0.12);
}


/* Smooth network interpolation + mechanics */
.player {
    transition: width 0.18s ease, height 0.18s ease, box-shadow 0.18s ease;
}
.powerup { position:absolute; width:34px; height:34px; transform:translate(-50%,-50%); border-radius:50%; z-index:8; animation: powerPulse .8s ease-in-out infinite alternate; }
.powerup.speed { background:#74c0fc; box-shadow:0 0 24px #339af0; }
.powerup.growth { background:#69db7c; box-shadow:0 0 24px #2f9e44; }
@keyframes powerPulse { from { transform:translate(-50%,-50%) scale(.9); } to { transform:translate(-50%,-50%) scale(1.12); } }
#minimap { position:fixed; right:16px; bottom:16px; width:170px; height:170px; border:2px solid rgba(255,255,255,.35); border-radius:14px; background:rgba(5,8,14,.78); z-index:300; overflow:hidden; backdrop-filter:blur(6px); }
#minimapCanvas { width:100%; height:100%; display:block; }
#serverBadge { position:fixed; left:16px; bottom:16px; z-index:300; padding:8px 12px; border-radius:10px; background:rgba(5,8,14,.75); font-size:12px; }

/* =========================================================
   LEADERBOARD
   ========================================================= */

#leaderboard {

    position: fixed;

    top: 72px;
    right: 12px;

    width: 190px;

    max-height: 300px;

    overflow-y: auto;

    z-index: 500;

    padding: 12px;

    border-radius: 14px;

    background: rgba(8,12,20,0.82);

    border: 1px solid rgba(255,255,255,0.1);

    backdrop-filter: blur(8px);
}

.leaderTitle {
    font-weight: 900;
    margin-bottom: 8px;
}

.leaderRow {

    display: flex;

    justify-content: space-between;

    gap: 5px;

    padding: 5px 0;

    font-size: 13px;
}


/* =========================================================
   JOYSTICK
   ========================================================= */

#joystick {

    position: fixed;

    left: 25px;
    bottom: 25px;

    width: 150px;
    height: 150px;

    border-radius: 50%;

    background: rgba(255,255,255,0.08);

    border: 2px solid rgba(255,255,255,0.15);

    z-index: 700;

    touch-action: none;
}

#stick {

    position: absolute;

    width: 70px;
    height: 70px;

    left: 50%;
    top: 50%;

    transform: translate(-50%, -50%);

    border-radius: 50%;

    background: rgba(255,255,255,0.25);

    border: 2px solid rgba(255,255,255,0.35);

    box-shadow: 0 5px 20px rgba(0,0,0,0.3);
}


/* =========================================================
   OPTIONS
   ========================================================= */

.optionRow {

    display: flex;

    align-items: center;
    justify-content: space-between;

    gap: 15px;

    padding: 12px 0;

    border-bottom: 1px solid rgba(255,255,255,0.08);

    text-align: left;
}

.optionRow label {
    font-weight: bold;
}

.optionRow select {
    width: 160px;
    margin: 0;
}


/* =========================================================
   PROFILE
   ========================================================= */

.colorPreview {

    width: 70px;
    height: 70px;

    margin: 15px auto;

    border-radius: 50%;

    border: 4px solid white;
}


/* =========================================================
   MOBILE
   ========================================================= */

@media (max-width: 700px) {

    .panel {
        width: min(94vw, 480px);
        padding: 22px;
        border-radius: 20px;
    }

    #leaderboard {
        width: 145px;
        top: 65px;
    }

    .hudBox {
        padding: 8px 10px;
        font-size: 13px;
    }

    #joystick {
        width: 135px;
        height: 135px;
    }

    #stick {
        width: 62px;
        height: 62px;
    }

}


#avatarPreview {
    width: 92px;
    height: 92px;
    margin: 10px auto 8px;
    border-radius: 50%;
    border: 3px solid rgba(255,255,255,0.6);
    background: radial-gradient(circle at 35% 30%, #fff8, #4dabf7 65%, #18304d);
    background-size: cover;
    background-position: center;
    box-shadow: 0 0 20px rgba(77,171,247,0.35);
}

.customBallBox {
    margin-top: 14px;
    padding: 12px;
    border: 1px solid rgba(255,255,255,0.12);
    border-radius: 14px;
    background: rgba(255,255,255,0.04);
}

.customBallHint {
    font-size: 12px;
    opacity: 0.65;
    margin-top: 6px;
}

.avatarActions {
    display: flex;
    gap: 8px;
    justify-content: center;
    flex-wrap: wrap;
}
</style>
</head>

<body>


<!-- ========================================================
     MAIN MENU
========================================================= -->

<div id="mainMenu">

    <div class="panel">

        <h1 class="title">LAN BLOB ARENA</h1>

        <div class="subtitle">
            🟣 Multiplayer Blob Madness
        </div>

        <button
            class="menuButton primary"
            onclick="openLogin()"
        >
            🎮 PLAY
        </button>

        <button class="menuButton" onclick="openServerMenu()">🛰️ SERVERS</button>

        <button
            class="menuButton"
            onclick="openRegister()"
        >
            📝 CREATE ACCOUNT
        </button>

        <button
            class="menuButton"
            onclick="openOptions(false)"
        >
            ⚙️ OPTIONS
        </button>

        <div class="info">
            📱 Joystick<br>
            ⌨️ WASD / Arrow Keys<br>
            🪙 Collect coins and get the highest score!
        </div>

    </div>

</div>


<div id="serverMenu" class="hidden">
    <div class="panel">
        <h2>🛰️ SERVERS</h2>
        <div class="info">Public matchmaking automatically picks an open lobby. Create a private lobby and share its code with friends.</div>
        <button class="menuButton primary" onclick="quickPlay()">🎮 QUICK PLAY</button>
        <input id="privateServerName" class="textInput" placeholder="Private server name">
        <button class="menuButton" onclick="createPrivateServer()">🔒 CREATE PRIVATE</button>
        <input id="privateServerCode" class="textInput" placeholder="Enter private code">
        <button class="menuButton" onclick="joinPrivateServer()">🔑 JOIN PRIVATE</button>
        <div id="serverList" class="info"></div>
        <button class="menuButton" onclick="showMain()">BACK</button>
    </div>
</div>

<!-- ========================================================
     LOGIN
========================================================= -->

<div id="loginMenu" class="hidden">

    <div class="panel">

        <h2>🔐 Login</h2>

        <input
            id="loginUsername"
            maxlength="16"
            placeholder="Username"
            autocomplete="username"
        >

        <input
            id="loginPassword"
            type="password"
            placeholder="Password"
            autocomplete="current-password"
        >

        <div
            id="loginError"
            class="error"
        ></div>

        <button
            class="menuButton primary"
            onclick="login()"
        >
            LOGIN
        </button>

        <button
            class="menuButton"
            onclick="showMain()"
        >
            BACK
        </button>

    </div>

</div>


<!-- ========================================================
     REGISTER
========================================================= -->

<div id="registerMenu" class="hidden">

    <div class="panel">

        <h2>📝 Create Account</h2>

        <input
            id="registerUsername"
            maxlength="16"
            placeholder="Username"
            autocomplete="username"
        >

        <input
            id="registerPassword"
            type="password"
            placeholder="Password"
            autocomplete="new-password"
        >

        <input
            id="registerPassword2"
            type="password"
            placeholder="Repeat Password"
            autocomplete="new-password"
        >

        <div
            id="registerError"
            class="error"
        ></div>

        <button
            class="menuButton primary"
            onclick="register()"
        >
            CREATE
        </button>

        <button
            class="menuButton"
            onclick="showMain()"
        >
            BACK
        </button>

    </div>

</div>


<!-- ========================================================
     PROFILE
========================================================= -->

<div id="profileMenu" class="hidden">

    <div class="panel">

        <h2>🎨 Profile</h2>

        <input
            id="nicknameInput"
            maxlength="16"
            placeholder="Nickname"
        >

        <div
            id="colorPreview"
            class="colorPreview"
        ></div>

        <input
            id="colorInput"
            type="color"
            value="#4dabf7"
        >

        <h3>🧬 Skin</h3>

        <select id="skinInput">

            <option value="normal">Normal</option>
            <option value="ghost">Ghost</option>
            <option value="fire">Fire</option>
            <option value="ice">Ice</option>
            <option value="rainbow">Rainbow</option>
            <option value="void">Void</option>
            <option value="verty">Verty</option>
            <option value="colorchanging">
                🌈 Color-Changing
            </option>

        </select>

        <div class="customBallBox">
            <h3>🖼️ Custom Ball</h3>
            <input id="avatarInput" type="file" accept="image/png,image/jpeg,image/webp,image/gif">
            <div class="customBallHint">PNG, JPG, WEBP or GIF • max 750 KB</div>
            <div id="avatarPreview" class="avatarPreview"></div>
            <div class="avatarActions">
                <button type="button" class="menuButton" onclick="uploadAvatar()">⬆️ Upload Image</button>
                <button type="button" class="menuButton" onclick="deleteAvatar()">🗑️ Remove</button>
            </div>
        </div>

        <div
            id="profileError"
            class="error"
        ></div>

        <button
            class="menuButton primary"
            onclick="saveProfile()"
        >
            💾 SAVE
        </button>

        <button
            class="menuButton"
            onclick="closeProfile()"
        >
            BACK
        </button>

    </div>

</div>


<!-- ========================================================
     OPTIONS
========================================================= -->

<div id="optionsMenu" class="hidden">

    <div class="panel">

        <h2>⚙️ Options</h2>

        <div class="optionRow">

            <label>Resolution</label>

            <select id="resolutionOption">

                <option value="auto">Auto</option>
                <option value="720">720p</option>
                <option value="1080">1080p</option>
                <option value="1440">1440p</option>

            </select>

        </div>

        <div class="optionRow">

            <label>Quality</label>

            <select id="qualityOption">

                <option value="low">Low</option>
                <option value="medium">Medium</option>
                <option value="high">High</option>

            </select>

        </div>

        <div class="optionRow">

            <label>Effects</label>

            <select id="effectsOption">

                <option value="on">On</option>
                <option value="off">Off</option>

            </select>

        </div>

        <div class="optionRow">

            <label>Coins</label>

            <select id="coinsOption">

                <option value="on">Show</option>
                <option value="off">Hide</option>

            </select>

        </div>

        <div class="optionRow">

            <label>FPS Counter</label>

            <select id="fpsOption">

                <option value="off">Off</option>
                <option value="on">On</option>

            </select>

        </div>

        <div class="optionRow">

            <label>Joystick Size</label>

            <select id="joystickOption">

                <option value="small">Small</option>
                <option value="medium">Medium</option>
                <option value="large">Large</option>

            </select>

        </div>

        <div class="optionRow">

            <label>UI Scale</label>

            <select id="uiOption">

                <option value="small">Small</option>
                <option value="normal">Normal</option>
                <option value="large">Large</option>

            </select>

        </div>

        <button
            class="menuButton"
            onclick="toggleFullscreen()"
        >
            ⛶ FULLSCREEN
        </button>

        <button
            class="menuButton"
            onclick="saveOptions()"
        >
            💾 SAVE OPTIONS
        </button>

        <button
            class="menuButton"
            onclick="resetOptions()"
        >
            ♻️ RESET OPTIONS
        </button>

        <button
            id="profileButton"
            class="menuButton"
            onclick="openProfile()"
        >
            🎨 PROFILE
        </button>

        <button
            id="leaveButton"
            class="menuButton danger hidden"
            onclick="leaveGame()"
        >
            🚪 LEAVE GAME
        </button>

        <button
            class="menuButton"
            onclick="closeOptions()"
        >
            BACK
        </button>

    </div>

</div>


<!-- ========================================================
     GAME
========================================================= -->

<div id="game">

    <div id="world"></div>

    <div id="hud">

        <div class="hudBox">
            🏆 <span id="score">0</span>
        </div>

        <div class="hudBox">
            🪙 <span id="coinCount">0</span>
        </div>

        <div class="hudBox">
            👥 <span id="playerCount">0</span>
        </div>

        <div
            id="connectionStatus"
            class="hudBox"
        >
            ● Connected
        </div>

        <div
            id="fpsCounter"
            class="hudBox hidden"
        >
            FPS: 0
        </div>

    </div>


    <div id="topButtons">

        <button
            class="smallButton"
            onclick="openProfile()"
        >
            🎨
        </button>

        <button
            class="smallButton"
            onclick="openOptions(true)"
        >
            ⚙️
        </button>

    </div>


    <div id="leaderboard">

        <div class="leaderTitle">
            🏆 LEADERBOARD
        </div>

        <div id="leaderRows"></div>

    </div>


    <div id="serverBadge">Lobby</div>
    <div id="minimap"><canvas id="minimapCanvas" width="170" height="170"></canvas></div>

    <div id="joystick">

        <div id="stick"></div>

    </div>

</div>


<script>

/* =========================================================
   GLOBALS
========================================================= */

let sessionToken = "";
let username = "";
let gameRunning = false;

let stateTimer = null;
let moveTimer = null;
let fpsTimer = null;
let moveInFlight = false;
let localPrediction = {x: 0, y: 0, initialized: false};
let lastServerStateAt = 0;
let lastMinimapAt = 0;
let networkStateBusy = false;

let keys = {};

let joystickX = 0;
let joystickY = 0;
let joystickActive = false;

let playerElements = {};
let coinElements = {};
let powerupElements = {};
let renderTargets = {};
let renderFrame = null;
let selectedServerId = null;
let selectedServerCode = "";

let lastFrameCount = 0;
let fps = 0;

let cameraX = 0;
let cameraY = 0;
let targetCameraX = 0;
let targetCameraY = 0;
let gameWorldWidth = 5000;
let gameWorldHeight = 5000;

let options = {

    resolution: "auto",
    quality: "high",
    effects: "on",
    coins: "on",
    fps: "off",
    joystick: "medium",
    ui: "normal"

};


/* =========================================================
   DOM
========================================================= */

const game = document.getElementById("game");
const world = document.getElementById("world");

const scoreElement = document.getElementById("score");
const coinCountElement = document.getElementById("coinCount");
const playerCountElement = document.getElementById("playerCount");

const connectionStatus =
    document.getElementById("connectionStatus");

const leaderRows =
    document.getElementById("leaderRows");

const joystick =
    document.getElementById("joystick");

const stick =
    document.getElementById("stick");

const fpsCounter =
    document.getElementById("fpsCounter");


/* =========================================================
   MENU HELPERS
========================================================= */

function hideAllMenus() {

    document
        .querySelectorAll(
            "#mainMenu, #serverMenu, #loginMenu, #registerMenu, #profileMenu, #optionsMenu"
        )
        .forEach(el => {
            el.classList.add("hidden");
        });

}

function showMain() {

    hideAllMenus();

    document
        .getElementById("mainMenu")
        .classList.remove("hidden");

}

function openLogin() {

    hideAllMenus();

    document
        .getElementById("loginMenu")
        .classList.remove("hidden");

}

function openRegister() {

    hideAllMenus();

    document
        .getElementById("registerMenu")
        .classList.remove("hidden");

}

function openOptions(fromGame = false) {

    loadOptions();

    hideAllMenus();

    document
        .getElementById("optionsMenu")
        .classList.remove("hidden");

    const leaveButton =
        document.getElementById("leaveButton");

    if (gameRunning && fromGame) {

        leaveButton.classList.remove("hidden");

    } else {

        leaveButton.classList.add("hidden");

    }

}

function closeOptions() {

    document
        .getElementById("optionsMenu")
        .classList.add("hidden");

    if (gameRunning) {

        game.style.display = "block";

    } else {

        showMain();

    }

}

function openProfile() {

    hideAllMenus();

    document
        .getElementById("profileMenu")
        .classList.remove("hidden");

    loadProfile();

}

function closeProfile() {

    document
        .getElementById("profileMenu")
        .classList.add("hidden");

    if (gameRunning) {

        game.style.display = "block";

    } else {

        showMain();

    }

}


async function openServerMenu(){
    if (!sessionToken) { openLogin(); return; }
    hideAllMenus();
    document.getElementById("serverMenu").classList.remove("hidden");
    await refreshServers();
}
async function refreshServers(){ try { const r=await fetch("/servers",{headers:{"X-Session":sessionToken}}); const d=await r.json(); document.getElementById("serverList").innerHTML=(d.servers||[]).map(s=>`<div style="margin:6px 0">${s.name} — ${s.players}/${s.max_players} <button onclick="selectServer('${s.id}')">JOIN</button></div>`).join("") || "No public lobbies yet."; } catch(e){} }
function selectServer(id){ selectedServerId=id; selectedServerCode=""; startGame(); }
function quickPlay(){ selectedServerId=null; selectedServerCode=""; startGame(); }
async function createPrivateServer(){ try { const r=await fetch("/create_server",{method:"POST",headers:{"Content-Type":"application/json","X-Session":sessionToken},body:JSON.stringify({name:document.getElementById("privateServerName").value})}); const d=await r.json(); if(!d.success){alert(d.error);return;} selectedServerId=d.server.id; selectedServerCode=d.code; alert("Private server code: "+d.code); startGame(); } catch(e){alert("Could not create server.");} }
async function joinPrivateServer(){ selectedServerId=null; selectedServerCode=document.getElementById("privateServerCode").value.trim().toUpperCase(); if(!selectedServerCode){return;} startGame(); }

/* =========================================================
   REGISTER
========================================================= */

async function register() {

    const usernameInput =
        document.getElementById("registerUsername");

    const passwordInput =
        document.getElementById("registerPassword");

    const password2Input =
        document.getElementById("registerPassword2");

    const error =
        document.getElementById("registerError");

    const name =
        usernameInput.value.trim();

    const password =
        passwordInput.value;

    const password2 =
        password2Input.value;

    error.textContent = "";

    if (!name) {

        error.textContent =
            "Enter a username.";

        return;

    }

    if (password.length < 8) {

        error.textContent =
            "Password must be at least 8 characters.";

        return;

    }

    if (password !== password2) {

        error.textContent =
            "Passwords do not match.";

        return;

    }

    try {

        const response = await fetch(
            "/register",
            {
                method: "POST",

                headers: {
                    "Content-Type":
                        "application/json"
                },

                body: JSON.stringify({
                    username: name,
                    password: password
                })
            }
        );

        const data =
            await response.json();

        if (!data.success) {

            error.textContent =
                data.error || "Registration failed.";

            return;

        }

        document
            .getElementById("loginUsername")
            .value = name;

        document
            .getElementById("loginPassword")
            .value = password;

        openLogin();

    } catch (e) {

        error.textContent =
            "Connection error.";

    }

}


/* =========================================================
   LOGIN
========================================================= */

async function login() {

    const name =
        document
            .getElementById("loginUsername")
            .value
            .trim();

    const password =
        document
            .getElementById("loginPassword")
            .value;

    const error =
        document.getElementById("loginError");

    error.textContent = "";

    if (!name || !password) {

        error.textContent =
            "Enter username and password.";

        return;

    }

    try {

        const response = await fetch(
            "/login",
            {
                method: "POST",

                headers: {
                    "Content-Type":
                        "application/json"
                },

                body: JSON.stringify({
                    username: name,
                    password: password
                })
            }
        );

        const data =
            await response.json();

        if (!data.success) {

            error.textContent =
                data.error || "Login failed.";

            return;

        }

        username = data.username;
        sessionToken = data.token;

        localStorage.setItem(
            "lan_blob_username",
            username
        );

        localStorage.setItem(
            "lan_blob_token",
            sessionToken
        );

        openServerMenu();

    } catch (e) {

        error.textContent =
            "Connection error.";

        console.error(e);

    }

}


/* =========================================================
   START GAME
========================================================= */

async function startGame() {

    try {

        const response = await fetch(
            "/join",
            {
                method: "POST",

                headers: {
                    "X-Session":
                        sessionToken,
                    "Content-Type": "application/json"
                },
                body: JSON.stringify({
                    server_id: selectedServerId,
                    code: selectedServerCode
                })
            }
        );

        const data =
            await response.json();

        if (!data.success) {

            alert(
                data.error ||
                "Could not join the game."
            );

            return;

        }

        gameRunning = true;

        hideAllMenus();

        game.style.display = "block";

        document
            .getElementById("leaveButton")
            .classList.remove("hidden");

        clearLoops();

        stateTimer = setInterval(
            requestState,
            100
        );

        moveTimer = setInterval(
            sendMovement,
            50
        );

        fpsTimer = setInterval(
            updateFPS,
            1000
        );

        requestState();
        if (!renderFrame) renderFrame = requestAnimationFrame(animateNetworkPlayers);

    } catch (e) {

        console.error(e);

        alert(
            "Could not connect to the game."
        );

    }

}


/* =========================================================
   LEAVE GAME
========================================================= */

async function leaveGame() {

    if (!gameRunning) {

        closeOptions();
        return;

    }

    gameRunning = false;

    clearLoops();
    if (renderFrame) { cancelAnimationFrame(renderFrame); renderFrame=null; }

    try {

        await fetch(
            "/leave",
            {
                method: "POST",

                headers: {
                    "X-Session":
                        sessionToken
                }
            }
        );

    } catch (e) {

        console.log(e);

    }

    playerElements = {};
    coinElements = {};

    world.innerHTML = "";

    game.style.display = "none";

    document
        .getElementById("optionsMenu")
        .classList.add("hidden");

    document
        .getElementById("profileMenu")
        .classList.add("hidden");

    showMain();

}


/* =========================================================
   CLEAR LOOPS
========================================================= */

function clearLoops() {

    if (stateTimer) {

        clearInterval(stateTimer);
        stateTimer = null;

    }

    if (moveTimer) {

        clearInterval(moveTimer);
        moveTimer = null;

    }

    if (fpsTimer) {

        clearInterval(fpsTimer);
        fpsTimer = null;

    }

}


/* =========================================================
   REQUEST STATE
========================================================= */

async function requestState() {
    if (!gameRunning || networkStateBusy) return;
    networkStateBusy = true;
    try {
        const response = await fetch("/state", {
            headers: {"X-Session": sessionToken},
            cache: "no-store"
        });
        if (!response.ok) throw new Error("State request failed: " + response.status);
        const data = await response.json();
        connectionStatus.textContent = "● Connected";
        connectionStatus.style.color = "#69db7c";
        lastServerStateAt = performance.now();
        try {
            renderWorld(data);
        } catch (renderError) {
            console.error("Render error:", renderError);
            // The network connection is still alive; don't falsely show "Connection lost".
        }
        if (data.server) {
            document.getElementById("serverBadge").textContent =
                (data.server.name || "Lobby") + (data.server_code ? " • " + data.server_code : "");
        }
    } catch (e) {
        connectionStatus.textContent = "● Connection lost";
        connectionStatus.style.color = "#ff6b6b";
    } finally {
        networkStateBusy = false;
    }
}

function animateNetworkPlayers(now) {
    if (!gameRunning) return;
    now = now || performance.now();
    const dt = Math.min(0.05, Math.max(0.001, (now - (animateNetworkPlayers.lastNow || now)) / 1000));
    animateNetworkPlayers.lastNow = now;

    // Critically damped-ish interpolation independent of FPS.
    const alpha = 1 - Math.exp(-14 * dt);
    // Local player: predict continuously from keyboard/joystick input.
    if (localPrediction.initialized && gameRunning) {
        const m = getMovement();
        const len = Math.hypot(m.dx, m.dy);
        if (len > 0.001) {
            const speed = 600; // matches server-side PLAYER_SPEED * 60
            localPrediction.x = Math.max(40, Math.min(gameWorldWidth - 40, localPrediction.x + (m.dx / len) * speed * dt));
            localPrediction.y = Math.max(40, Math.min(gameWorldHeight - 40, localPrediction.y + (m.dy / len) * speed * dt));
        }
        renderTargets[username] = renderTargets[username] || {color:"#4dabf7"};
        renderTargets[username].x = localPrediction.x;
        renderTargets[username].y = localPrediction.y;
        const meEl = playerElements[username];
        if (meEl) {
            meEl.style.transform = `translate3d(${localPrediction.x}px,${localPrediction.y}px,0) translate(-50%,-50%)`;
        }
        moveCamera(localPrediction.x, localPrediction.y);
    }

    for (const id in renderTargets) {
        if (id === username) continue;
        const t = renderTargets[id];
        const el = playerElements[id];
        if (!el || t.x == null) continue;
        const currentX = Number(el.dataset.rx ?? t.x);
        const currentY = Number(el.dataset.ry ?? t.y);
        const nx = currentX + (t.x - currentX) * alpha;
        const ny = currentY + (t.y - currentY) * alpha;
        el.dataset.rx = nx;
        el.dataset.ry = ny;
        el.style.transform = `translate3d(${nx}px,${ny}px,0) translate(-50%,-50%)`;
    }

    cameraX += (targetCameraX - cameraX) * alpha;
    cameraY += (targetCameraY - cameraY) * alpha;
    world.style.transform = `translate3d(${cameraX}px,${cameraY}px,0)`;

    if (now - lastMinimapAt > 120) {
        updateMinimap();
        lastMinimapAt = now;
    }
    renderFrame = requestAnimationFrame(animateNetworkPlayers);
}

function updateMinimap() {
    const c = document.getElementById("minimapCanvas");
    if (!c) return;
    const ctx = c.getContext("2d");
    ctx.clearRect(0, 0, c.width, c.height);
    const sx = c.width / gameWorldWidth;
    const sy = c.height / gameWorldHeight;
    for (const id in renderTargets) {
        const p = renderTargets[id];
        const x = p.x * sx, y = p.y * sy;
        ctx.beginPath();
        ctx.arc(x, y, id === username ? 5 : 3, 0, Math.PI * 2);
        ctx.fillStyle = id === username ? "#ffffff" : (p.color || "#4dabf7");
        ctx.fill();
    }
}

function escapeHtml(value) {
    return String(value ?? "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;");
}

function renderWorld(data) {

    if (!data) {
        return;
    }

    if (data.world) {
        gameWorldWidth = Number(data.world.width) || gameWorldWidth;
        gameWorldHeight = Number(data.world.height) || gameWorldHeight;

        world.style.width = gameWorldWidth + "px";
        world.style.height = gameWorldHeight + "px";
    }

    const players =
        Array.isArray(data.players)
            ? data.players
            : [];

    const coins =
        Array.isArray(data.coins)
            ? data.coins
            : [];

    let me = data.me;

    if (!me) {

        me = players.find(
            p => p.username === username
        );

    }

    /*
        IMPORTANT:
        We do NOT use world.innerHTML = "" here.

        Rebuilding the whole DOM every 70ms can cause
        players to disappear/flicker on mobile browsers.
    */


    /* -----------------------------------------------------
       MY HUD
    ----------------------------------------------------- */

    if (me) {
        const sx = Number(me.x) || 0;
        const sy = Number(me.y) || 0;
        if (!localPrediction.initialized) {
            localPrediction.x = sx;
            localPrediction.y = sy;
            localPrediction.initialized = true;
        } else {
            // Soft reconciliation prevents the local blob from snapping backwards.
            localPrediction.x += (sx - localPrediction.x) * 0.18;
            localPrediction.y += (sy - localPrediction.y) * 0.18;
        }
        scoreElement.textContent = me.score ?? 0;
        coinCountElement.textContent = me.coins ?? 0;
        moveCamera(localPrediction.x, localPrediction.y);
    }

    playerCountElement.textContent =
        players.length;


    /* -----------------------------------------------------
       PLAYERS
    ----------------------------------------------------- */

    const currentPlayers = new Set();

    players.forEach(player => {

        if (!player || !player.username) {
            return;
        }

        const id =
            player.username;

        currentPlayers.add(id);

        let element =
            playerElements[id];

        if (!element) {

            element =
                document.createElement("div");

            element.className =
                "player";

            const nameElement =
                document.createElement("div");

            nameElement.className =
                "player-name";

            element.appendChild(
                nameElement
            );

            world.appendChild(element);

            playerElements[id] =
                element;

        }

        const isMe =
            id === username;

        element.className =
            "player skin-" +
            (
                player.skin ||
                "normal"
            );

        if (isMe) {

            element.classList.add("me");

        }

        const px = isMe && localPrediction.initialized ? localPrediction.x : (Number(player.x) || 0);
        const py = isMe && localPrediction.initialized ? localPrediction.y : (Number(player.y) || 0);
        renderTargets[id] = {x:px, y:py, color:player.color||"#4dabf7"};
        if (element.dataset.rx === undefined) {
            element.dataset.rx = px;
            element.dataset.ry = py;
            element.style.transform = `translate3d(${px}px,${py}px,0) translate(-50%,-50%)`;
        }

        element.style.setProperty("--player-color", player.color || "#4dabf7");
        if (player.avatar) {
            element.style.backgroundImage = `url("/avatar/${encodeURIComponent(id)}")`;
            element.style.backgroundSize = "cover";
            element.style.backgroundPosition = "center";
        } else {
            element.style.backgroundImage = "";
        }
        const radius = Number(player.radius) || 29;
        element.style.width = (radius*2) + "px";
        element.style.height = (radius*2) + "px";
        element.style.filter = (Number(player.speed_boost)||0) > 0 ? "drop-shadow(0 0 12px #339af0)" : "none";

        const nameElement =
            element.querySelector(
                ".player-name"
            );

        if (nameElement) {
            const displayName = player.name || player.username;
            const displaySize = Math.max(1, Math.round(radius));
            nameElement.innerHTML = `${escapeHtml(displayName)}<span class="player-size">Size ${displaySize}</span>`;
        }

    });


    /* -----------------------------------------------------
       REMOVE PLAYERS THAT LEFT
    ----------------------------------------------------- */

    Object.keys(playerElements)
        .forEach(id => {

            if (!currentPlayers.has(id)) {

                const element =
                    playerElements[id];

                if (element) {
                    element.remove();
                }

                delete playerElements[id];
                delete renderTargets[id];

            }

        });


    /* -----------------------------------------------------
       COINS
    ----------------------------------------------------- */

    const showCoins =
        options.coins !== "off";

    const currentCoins =
        new Set();

    coins.forEach((coin, index) => {

        const id =
            String(index) +
            "_" +
            Math.round(coin.x) +
            "_" +
            Math.round(coin.y);

        currentCoins.add(id);

        if (!showCoins) {
            return;
        }

        let element =
            coinElements[id];

        if (!element) {

            element =
                document.createElement("div");

            element.className =
                "coin";

            world.appendChild(element);

            coinElements[id] =
                element;

        }

        element.style.left =
            Number(coin.x) + "px";

        element.style.top =
            Number(coin.y) + "px";

    });


    const currentPowerups = new Set();
    (Array.isArray(data.powerups) ? data.powerups : []).forEach(pu => {
        currentPowerups.add(pu.id);
        let el=powerupElements[pu.id];
        if(!el){ el=document.createElement("div"); el.className="powerup "+(pu.type||"speed"); el.textContent=pu.type==="speed"?"⚡":"✚"; world.appendChild(el); powerupElements[pu.id]=el; }
        el.style.left=Number(pu.x)+"px"; el.style.top=Number(pu.y)+"px";
    });
    Object.keys(powerupElements).forEach(id=>{ if(!currentPowerups.has(id)){ powerupElements[id].remove(); delete powerupElements[id]; }});

    /* Remove old coin elements */

    Object.keys(coinElements)
        .forEach(id => {

            if (!currentCoins.has(id) ||
                !showCoins) {

                const element =
                    coinElements[id];

                if (element) {
                    element.remove();
                }

                delete coinElements[id];

            }

        });


    /* -----------------------------------------------------
       LEADERBOARD
    ----------------------------------------------------- */

    const sorted =
        [...players]
            .sort(
                (a, b) =>
                    (b.score || 0) -
                    (a.score || 0)
            )
            .slice(0, 10);

    leaderRows.innerHTML = "";

    sorted.forEach((player, index) => {

        const row =
            document.createElement("div");

        row.className =
            "leaderRow";

        const left =
            document.createElement("span");

        left.textContent =
            "#" +
            (index + 1) +
            " " +
            (
                player.name ||
                player.username
            );

        const right =
            document.createElement("span");

        right.textContent =
            player.score || 0;

        row.appendChild(left);
        row.appendChild(right);

        leaderRows.appendChild(row);

    });

}


/* =========================================================
   CAMERA
========================================================= */

function moveCamera(x, y) {
    const screenWidth = window.innerWidth;
    const screenHeight = window.innerHeight;
    targetCameraX = screenWidth / 2 - x;
    targetCameraY = screenHeight / 2 - y;
    const minX = screenWidth - gameWorldWidth;
    const minY = screenHeight - gameWorldHeight;
    targetCameraX = Math.min(0, Math.max(minX, targetCameraX));
    targetCameraY = Math.min(0, Math.max(minY, targetCameraY));
}


/* =========================================================
   MOVEMENT
========================================================= */

function getMovement() {

    let dx = 0;
    let dy = 0;


    if (
        keys["w"] ||
        keys["arrowup"]
    ) {

        dy -= 1;

    }

    if (
        keys["s"] ||
        keys["arrowdown"]
    ) {

        dy += 1;

    }

    if (
        keys["a"] ||
        keys["arrowleft"]
    ) {

        dx -= 1;

    }

    if (
        keys["d"] ||
        keys["arrowright"]
    ) {

        dx += 1;

    }


    dx += joystickX;
    dy += joystickY;


    const length =
        Math.sqrt(
            dx * dx +
            dy * dy
        );

    if (length > 1) {

        dx /= length;
        dy /= length;

    }

    return {
        dx: dx,
        dy: dy
    };

}


async function sendMovement() {

    if (!gameRunning || moveInFlight) {
        return;
    }

    const movement =
        getMovement();

    if (
        Math.abs(movement.dx) < 0.01 &&
        Math.abs(movement.dy) < 0.01
    ) {

        return;

    }

    try {

        moveInFlight = true;

        await fetch(
            "/move",
            {
                method: "POST",

                headers: {
                    "Content-Type":
                        "application/json",

                    "X-Session":
                        sessionToken
                },

                body: JSON.stringify({
                    dx: movement.dx,
                    dy: movement.dy
                })
            }
        );

    } catch (e) {

        console.log(e);

    } finally {

        moveInFlight = false;

    }

}


/* =========================================================
   KEYBOARD
========================================================= */

window.addEventListener(
    "keydown",
    event => {

        const key =
            event.key.toLowerCase();

        keys[key] = true;

        if (
            [
                "w",
                "a",
                "s",
                "d",
                "arrowup",
                "arrowdown",
                "arrowleft",
                "arrowright"
            ].includes(key)
        ) {

            event.preventDefault();

        }

    }
);


window.addEventListener(
    "keyup",
    event => {

        const key =
            event.key.toLowerCase();

        keys[key] = false;

    }
);


/* =========================================================
   JOYSTICK
========================================================= */

function updateJoystick(clientX, clientY) {

    const rect =
        joystick.getBoundingClientRect();

    const centerX =
        rect.left +
        rect.width / 2;

    const centerY =
        rect.top +
        rect.height / 2;

    let x =
        clientX -
        centerX;

    let y =
        clientY -
        centerY;

    const maxDistance =
        rect.width / 2 -
        35;

    const distance =
        Math.sqrt(
            x * x +
            y * y
        );

    if (distance > maxDistance) {

        x =
            x / distance *
            maxDistance;

        y =
            y / distance *
            maxDistance;

    }

    joystickX =
        x / maxDistance;

    joystickY =
        y / maxDistance;

    stick.style.left =
        "calc(50% + " +
        x +
        "px)";

    stick.style.top =
        "calc(50% + " +
        y +
        "px)";

}


function resetJoystick() {

    joystickX = 0;
    joystickY = 0;

    stick.style.left =
        "50%";

    stick.style.top =
        "50%";

}


joystick.addEventListener(
    "pointerdown",
    event => {

        joystickActive = true;

        joystick.setPointerCapture(
            event.pointerId
        );

        updateJoystick(
            event.clientX,
            event.clientY
        );

    }
);


joystick.addEventListener(
    "pointermove",
    event => {

        if (!joystickActive) {
            return;
        }

        updateJoystick(
            event.clientX,
            event.clientY
        );

    }
);


joystick.addEventListener(
    "pointerup",
    () => {

        joystickActive = false;

        resetJoystick();

    }
);


joystick.addEventListener(
    "pointercancel",
    () => {

        joystickActive = false;

        resetJoystick();

    }
);


/* =========================================================
   PROFILE
========================================================= */

async function loadProfile() {

    try {

        const response =
            await fetch(
                "/profile",
                {
                    headers: {
                        "X-Session":
                            sessionToken
                    }
                }
            );

        const data =
            await response.json();

        if (!data.success) {
            return;
        }

        document
            .getElementById("nicknameInput")
            .value =
                data.profile.name || username;

        document
            .getElementById("colorInput")
            .value =
                data.profile.color || "#4dabf7";

        document
            .getElementById("skinInput")
            .value =
                data.profile.skin || "normal";

        if (data.profile.options && typeof data.profile.options === "object") {
            options = { ...options, ...data.profile.options };
            localStorage.setItem("lan_blob_options", JSON.stringify(options));
            loadOptions();
        }

        updateColorPreview();
        updateAvatarPreview(!!data.profile.avatar);

    } catch (e) {

        console.log(e);

    }

}


function updateAvatarPreview(hasAvatar) {
    const preview = document.getElementById("avatarPreview");
    if (!preview) return;
    if (hasAvatar) {
        preview.style.backgroundImage = `url("/avatar/${encodeURIComponent(username)}?t=${Date.now()}")`;
        preview.dataset.hasAvatar = "1";
    } else {
        preview.style.backgroundImage = "";
        preview.dataset.hasAvatar = "0";
    }
}

const avatarInput = document.getElementById("avatarInput");
if (avatarInput) {
    avatarInput.addEventListener("change", () => {
        const file = avatarInput.files && avatarInput.files[0];
        if (!file) return;
        if (file.size > 750000) {
            document.getElementById("profileError").textContent = "Image is too large. Max 750 KB.";
            avatarInput.value = "";
            return;
        }
        const reader = new FileReader();
        reader.onload = () => {
            const preview = document.getElementById("avatarPreview");
            if (preview) preview.style.backgroundImage = `url("${reader.result}")`;
        };
        reader.readAsDataURL(file);
    });
}

async function uploadAvatar() {
    const input = document.getElementById("avatarInput");
    const error = document.getElementById("profileError");
    const file = input && input.files && input.files[0];
    if (!file) { error.textContent = "Choose an image first."; return; }
    if (file.size > 750000) { error.textContent = "Image is too large. Max 750 KB."; return; }
    const form = new FormData();
    form.append("avatar", file);
    try {
        const response = await fetch("/avatar", {method:"POST", headers:{"X-Session":sessionToken}, body:form});
        const data = await response.json();
        error.textContent = data.success ? "Custom ball saved!" : (data.error || "Upload failed.");
        if (data.success) { input.value = ""; updateAvatarPreview(true); if (gameRunning) setTimeout(closeProfile, 400); }
    } catch(e) { error.textContent = "Connection error."; }
}

async function deleteAvatar() {
    const error = document.getElementById("profileError");
    try {
        const response = await fetch("/avatar", {method:"DELETE", headers:{"X-Session":sessionToken}});
        const data = await response.json();
        if (data.success) { updateAvatarPreview(false); error.textContent = "Custom ball removed."; }
        else error.textContent = data.error || "Could not remove image.";
    } catch(e) { error.textContent = "Connection error."; }
}

async function saveProfile() {

    const name =
        document
            .getElementById("nicknameInput")
            .value
            .trim();

    const color =
        document
            .getElementById("colorInput")
            .value;

    const skin =
        document
            .getElementById("skinInput")
            .value;

    const error =
        document
            .getElementById("profileError");

    error.textContent = "";

    if (!name) {

        error.textContent =
            "Enter a nickname.";

        return;

    }

    try {

        const response =
            await fetch(
                "/profile",
                {
                    method: "POST",

                    headers: {
                        "Content-Type":
                            "application/json",

                        "X-Session":
                            sessionToken
                    },

                    body: JSON.stringify({
                        name: name,
                        color: color,
                        skin: skin
                    })
                }
            );

        const data =
            await response.json();

        if (!data.success) {

            error.textContent =
                data.error ||
                "Could not save profile.";

            return;

        }

        error.textContent =
            "Saved!";

        if (gameRunning) {

            setTimeout(
                closeProfile,
                400
            );

        }

    } catch (e) {

        error.textContent =
            "Connection error.";

    }

}



function updateColorPreview() {

    const color =
        document
            .getElementById("colorInput")
            .value;

    document
        .getElementById("colorPreview")
        .style.background =
            color;

}


document
    .getElementById("colorInput")
    .addEventListener(
        "input",
        updateColorPreview
    );


/* =========================================================
   OPTIONS
========================================================= */

function loadOptions() {

    try {

        const saved =
            localStorage.getItem(
                "lan_blob_options"
            );

        if (saved) {

            const parsed =
                JSON.parse(saved);

            options = {
                ...options,
                ...parsed
            };

        }

    } catch (e) {

        console.log(e);

    }

    document
        .getElementById("resolutionOption")
        .value =
            options.resolution;

    document
        .getElementById("qualityOption")
        .value =
            options.quality;

    document
        .getElementById("effectsOption")
        .value =
            options.effects;

    document
        .getElementById("coinsOption")
        .value =
            options.coins;

    document
        .getElementById("fpsOption")
        .value =
            options.fps;

    document
        .getElementById("joystickOption")
        .value =
            options.joystick;

    document
        .getElementById("uiOption")
        .value =
            options.ui;

    applyOptions();

}


function saveOptions() {

    options = {

        resolution:
            document
                .getElementById("resolutionOption")
                .value,

        quality:
            document
                .getElementById("qualityOption")
                .value,

        effects:
            document
                .getElementById("effectsOption")
                .value,

        coins:
            document
                .getElementById("coinsOption")
                .value,

        fps:
            document
                .getElementById("fpsOption")
                .value,

        joystick:
            document
                .getElementById("joystickOption")
                .value,

        ui:
            document
                .getElementById("uiOption")
                .value

    };

    localStorage.setItem(
        "lan_blob_options",
        JSON.stringify(options)
    );

    // Persist options to the account as well as this browser.
    fetch("/options", {
        method: "POST",
        headers: {
            "Content-Type": "application/json",
            "X-Session": sessionToken
        },
        body: JSON.stringify({options})
    }).catch(() => {});

    applyOptions();

}


function resetOptions() {

    options = {

        resolution: "auto",
        quality: "high",
        effects: "on",
        coins: "on",
        fps: "off",
        joystick: "medium",
        ui: "normal"

    };

    localStorage.setItem(
        "lan_blob_options",
        JSON.stringify(options)
    );

    fetch("/options", {
        method: "POST",
        headers: {
            "Content-Type": "application/json",
            "X-Session": sessionToken
        },
        body: JSON.stringify({options})
    }).catch(() => {});

    loadOptions();

}


function applyOptions() {

    /* FPS */

    if (options.fps === "on") {

        fpsCounter.classList.remove(
            "hidden"
        );

    } else {

        fpsCounter.classList.add(
            "hidden"
        );

    }


    /* Joystick */

    let size = 150;

    if (options.joystick === "small") {
        size = 110;
    }

    if (options.joystick === "large") {
        size = 190;
    }

    joystick.style.width =
        size + "px";

    joystick.style.height =
        size + "px";


    /* UI scale */

    if (options.ui === "small") {

        document.body.style.fontSize =
            "90%";

    } else if (
        options.ui === "large"
    ) {

        document.body.style.fontSize =
            "115%";

    } else {

        document.body.style.fontSize =
            "100%";

    }


    /* Effects */

    if (options.effects === "off") {

        document.body.classList.add(
            "no-effects"
        );

    } else {

        document.body.classList.remove(
            "no-effects"
        );

    }


    /* Resolution */

    if (options.resolution !== "auto") {

        const scale =
            parseInt(
                options.resolution,
                10
            ) /
            1080;

        if (
            Number.isFinite(scale) &&
            scale > 0
        ) {

            world.style.transformOrigin =
                "0 0";

        }

    }

}


/* =========================================================
   FULLSCREEN
========================================================= */

async function toggleFullscreen() {

    try {

        if (!document.fullscreenElement) {

            await document.documentElement
                .requestFullscreen();

        } else {

            await document.exitFullscreen();

        }

    } catch (e) {

        console.log(e);

    }

}


/* =========================================================
   FPS
========================================================= */

function updateFPS() {

    fps =
        lastFrameCount;

    lastFrameCount = 0;

    fpsCounter.textContent =
        "FPS: " + fps;

}


/* Count browser frames */

function frameLoop() {

    lastFrameCount++;

    requestAnimationFrame(
        frameLoop
    );

}

frameLoop();


/* =========================================================
   WINDOW RESIZE
========================================================= */

window.addEventListener(
    "resize",
    () => {

        requestState();

    }
);


/* =========================================================
   AUTO LOAD OPTIONS
========================================================= */

loadOptions();


/* =========================================================
   AUTO LOGIN TOKEN CHECK
========================================================= */

async function restoreSession() {

    const savedToken =
        localStorage.getItem(
            "lan_blob_token"
        );

    const savedUsername =
        localStorage.getItem(
            "lan_blob_username"
        );

    if (!savedToken ||
        !savedUsername) {

        return;

    }

    try {

        const response =
            await fetch(
                "/session",
                {
                    headers: {
                        "X-Session":
                            savedToken
                    }
                }
            );

        const data =
            await response.json();

        if (
            data.success &&
            data.username
        ) {

            sessionToken =
                savedToken;

            username =
                data.username;

        }

    } catch (e) {

        console.log(e);

    }

}

restoreSession();

</script>

</body>
</html>
"""


# ============================================================
# ROUTES
# ============================================================

@app.route("/")
def index():
    # IMPORTANT:
    # Do NOT use render_template_string here.
    # The HTML contains CSS/JS that can look like Jinja syntax.
    return HTML


# ============================================================
# REGISTER
# ============================================================

@app.route("/register", methods=["POST"])
def register():

    if rate_limited():
        return jsonify({"success": False, "error": "Too many requests. Try again later."}), 429

    data = request.get_json(silent=True) or {}

    username = clean_username(
        data.get("username", "")
    )

    password = data.get("password", "")

    if not username:
        return jsonify({
            "success": False,
            "error": "Invalid username."
        })

    if not isinstance(password, str):
        return jsonify({
            "success": False,
            "error": "Invalid password."
        })

    if len(password) < 8:
        return jsonify({
            "success": False,
            "error": "Password must be at least 8 characters."
        })

    if len(password) > 128:
        return jsonify({
            "success": False,
            "error": "Password is too long."
        })

    key = username.lower()

    with lock:

        if key in accounts:

            return jsonify({
                "success": False,
                "error": "Username already exists."
            })

        salt, password_hash = hash_password(password)

        accounts[key] = {
            "username": username,
            "salt": salt,
            "password_hash": password_hash,
            "iterations": PASSWORD_ITERATIONS,
            "name": username,
            "color": random.choice(COLORS),
            "skin": (
                "verty"
                if username.lower() in SECRET_NAMES
                else "normal"
            ),
            "coins": 0,
            "best_score": 0,
            "options": dict(DEFAULT_OPTIONS),
        }

        save_accounts()

    return jsonify({
        "success": True
    })


# ============================================================
# LOGIN
# ============================================================

@app.route("/login", methods=["POST"])
def login():

    if rate_limited():
        return jsonify({"success": False, "error": "Too many requests. Try again later."}), 429

    data = request.get_json(silent=True) or {}

    username = clean_username(
        data.get("username", "")
    )

    password = data.get("password", "")

    if not username:
        return jsonify({
            "success": False,
            "error": "Invalid username."
        })

    key = username.lower()

    with lock:

        account = accounts.get(key)

        if not account:

            return jsonify({
                "success": False,
                "error": "Account not found."
            })

        if not verify_password(password, account):

            return jsonify({
                "success": False,
                "error": "Wrong password."
            })

        token = secrets.token_urlsafe(48)

        sessions[token] = {
            "username": username,
            "created": time.time(),
            "last_seen": time.time(),
        }

    return jsonify({
        "success": True,
        "username": username,
        "token": token
    })


# ============================================================
# SESSION
# ============================================================

@app.route("/session")
def session_check():

    username = get_session()

    if not username:

        return jsonify({
            "success": False
        })

    return jsonify({
        "success": True,
        "username": username
    })


# ============================================================
# CUSTOM AVATAR / BALL IMAGE
# ============================================================

@app.route("/avatar/<username>")
def get_avatar(username):
    key = str(username).lower()
    with lock:
        account = accounts.get(key)
        avatar = account.get("avatar") if account else None

    if not avatar:
        return ("", 404)

    try:
        import base64
        raw = base64.b64decode(avatar.get("data", ""), validate=True)
    except Exception:
        return ("", 404)

    response = Response(raw, mimetype=avatar.get("mime", "image/webp"))
    response.headers["Cache-Control"] = "public, max-age=86400"
    return response


@app.route("/avatar", methods=["POST"])
def upload_avatar():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401

    upload = request.files.get("avatar")
    if not upload or not upload.filename:
        return jsonify({"success": False, "error": "Choose an image first."}), 400

    mime = (upload.mimetype or "").lower()
    if mime not in ALLOWED_AVATAR_TYPES:
        return jsonify({"success": False, "error": "Use PNG, JPG, WEBP or GIF."}), 400

    raw = upload.read(MAX_AVATAR_BYTES + 1)
    if len(raw) > MAX_AVATAR_BYTES:
        return jsonify({"success": False, "error": "Image is too large. Max 750 KB."}), 400

    try:
        from PIL import Image, ImageOps
        import io, base64

        image = Image.open(io.BytesIO(raw))
        if getattr(image, "n_frames", 1) > 1 and mime == "image/gif":
            # Keep animated GIFs, but still validate the first frame dimensions.
            frame = image.convert("RGBA")
            if max(frame.size) > AVATAR_MAX_DIM:
                frame.thumbnail((AVATAR_MAX_DIM, AVATAR_MAX_DIM), Image.Resampling.LANCZOS)
        else:
            image = ImageOps.exif_transpose(image).convert("RGBA")
            image.thumbnail((AVATAR_MAX_DIM, AVATAR_MAX_DIM), Image.Resampling.LANCZOS)
            out = io.BytesIO()
            image.save(out, "WEBP", quality=86, method=6)
            raw = out.getvalue()
            mime = "image/webp"

        # GIFs stay animated; static images are normalized to compact WebP.
        encoded = base64.b64encode(raw).decode("ascii")
    except Exception:
        return jsonify({"success": False, "error": "That image could not be read."}), 400

    with lock:
        account = accounts.get(username.lower())
        if not account:
            return jsonify({"success": False, "error": "Account not found."}), 404
        account["avatar"] = {"mime": mime, "data": encoded, "updated": time.time()}
        if username in players:
            players[username]["avatar_data"] = True
        save_accounts()

    return jsonify({"success": True})


@app.route("/avatar", methods=["DELETE"])
def delete_avatar():
    username = get_session()
    if not username:
        return jsonify({"success": False}), 401
    with lock:
        account = accounts.get(username.lower())
        if account:
            account.pop("avatar", None)
        if username in players:
            players[username]["avatar_data"] = False
        save_accounts()
    return jsonify({"success": True})


# ============================================================
# PROFILE GET
# ============================================================

@app.route("/profile", methods=["GET"])
def get_profile():

    username = get_session()

    if not username:

        return jsonify({
            "success": False,
            "error": "Not logged in."
        }), 401

    account = accounts.get(
        username.lower()
    )

    if not account:

        return jsonify({
            "success": False,
            "error": "Account not found."
        }), 404

    return jsonify({
        "success": True,
        "profile": {
            "username": account["username"],
            "name": account.get(
                "name",
                account["username"]
            ),
            "color": account.get(
                "color",
                "#4dabf7"
            ),
            "skin": account.get(
                "skin",
                "normal"
            ),
            "avatar": bool(account.get("avatar")),
            "coins": account.get(
                "coins",
                0
            ),
            "best_score": account.get(
                "best_score",
                0
            ),
            "options": {
                **DEFAULT_OPTIONS,
                **(account.get("options") or {}),
            },
        }
    })


# ============================================================
# PROFILE UPDATE
# ============================================================

@app.route("/profile", methods=["POST"])
def update_profile():

    username = get_session()

    if not username:

        return jsonify({
            "success": False,
            "error": "Not logged in."
        }), 401

    data = request.get_json(silent=True) or {}

    name = data.get("name", username)
    color = data.get("color", "#4dabf7")
    skin = data.get("skin", "normal")
    incoming_options = data.get("options")

    if not isinstance(name, str):
        name = username

    name = name.strip()

    if not name:
        name = username

    if len(name) > MAX_USERNAME_LENGTH:
        name = name[:MAX_USERNAME_LENGTH]

    if not isinstance(color, str):
        color = "#4dabf7"

    if not re.fullmatch(r"#[0-9a-fA-F]{6}", color):
        color = "#4dabf7"

    if skin not in SKINS:
        skin = "normal"

    key = username.lower()

    with lock:

        if key not in accounts:

            return jsonify({
                "success": False,
                "error": "Account not found."
            })

        accounts[key]["name"] = name
        accounts[key]["color"] = color
        accounts[key]["skin"] = skin
        if isinstance(incoming_options, dict):
            accounts[key]["options"] = {
                **DEFAULT_OPTIONS,
                **{k: str(v) for k, v in incoming_options.items() if k in DEFAULT_OPTIONS}
            }

        if username in players:

            players[username]["name"] = name
            players[username]["color"] = color
            players[username]["skin"] = skin
            players[username]["avatar_data"] = bool(accounts[key].get("avatar"))

        save_accounts()

    return jsonify({
        "success": True
    })


# ============================================================
# ACCOUNT OPTIONS
# ============================================================

@app.route("/options", methods=["GET", "POST"])
def account_options():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401

    key = username.lower()
    with lock:
        account = accounts.get(key)
        if not account:
            return jsonify({"success": False, "error": "Account not found."}), 404

        if request.method == "GET":
            opts = {**DEFAULT_OPTIONS, **(account.get("options") or {})}
            return jsonify({"success": True, "options": opts})

        data = request.get_json(silent=True) or {}
        incoming = data.get("options", data)
        if not isinstance(incoming, dict):
            return jsonify({"success": False, "error": "Invalid options."}), 400

        allowed = set(DEFAULT_OPTIONS)
        clean = {k: str(v) for k, v in incoming.items() if k in allowed}
        account["options"] = {**DEFAULT_OPTIONS, **clean}
        save_accounts()
        return jsonify({"success": True, "options": account["options"]})


# ============================================================
# SERVER BROWSER / MATCHMAKING
# ============================================================

@app.route("/servers")
def list_servers():
    with lock:
        public = [public_server(x) for x in servers.values() if not x["private"]]
    return jsonify({"success": True, "servers": public})

@app.route("/create_server", methods=["POST"])
def create_server_route():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401
    data = request.get_json(silent=True) or {}
    name = str(data.get("name", "Private Server")).strip()[:32] or "Private Server"
    with lock:
        code = secrets.token_urlsafe(5).upper().replace("-", "").replace("_", "")[:8]
        server = make_server(True, name, code)
        server["coins"] = [create_coin() for _ in range(COIN_COUNT)]
        refill_powerups(server)
    return jsonify({"success": True, "server": public_server(server), "code": code})

@app.route("/join_server", methods=["POST"])
def join_server_route():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401
    data = request.get_json(silent=True) or {}
    code = str(data.get("code", "")).strip().upper()
    with lock:
        found = next((x for x in servers.values() if x.get("code") == code and x["private"]), None)
    if not found:
        return jsonify({"success": False, "error": "Private server not found."}), 404
    if len(found["players"]) >= MAX_PLAYERS and username not in found["players"]:
        return jsonify({"success": False, "error": "That server is full."}), 409
    return jsonify({"success": True, "server": public_server(found), "code": code})

# ============================================================
# JOIN
# ============================================================

@app.route("/join", methods=["POST"])
def join():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401
    data = request.get_json(silent=True) or {}
    with lock:
        current = get_server_for_player(username)
        if current:
            current["players"][username]["last_seen"] = time.time()
            return jsonify({"success": True, "player": public_player(current["players"][username]), "server": public_server(current)})
        server_id = data.get("server_id")
        code = str(data.get("code", "")).strip().upper()
        server = servers.get(server_id) if server_id else None
        if code:
            server = next((x for x in servers.values() if x.get("code") == code and x["private"]), None)
        if server is None:
            server = ensure_public_server()
        if len(server["players"]) >= MAX_PLAYERS:
            server = ensure_public_server()
        account = accounts.get(username.lower())
        if not account:
            return jsonify({"success": False, "error": "Account not found."}), 404
        player = {
            "username": username, "name": account.get("name", username),
            "x": random.randint(150, WORLD_WIDTH-150), "y": random.randint(150, WORLD_HEIGHT-150),
            "score": 0, "coins": account.get("coins", 0), "best_score": account.get("best_score", 0),
            "color": account.get("color", random.choice(COLORS)), "skin": account.get("skin", "normal"), "avatar_data": bool(account.get("avatar")),
            "radius": BASE_PLAYER_RADIUS, "speed_boost_until": 0, "last_seen": time.time(), "last_move": time.time(),
        }
        server["players"][username] = player
        refill_powerups(server)
    print("🟢 JOIN:", username, "->", server["name"])
    return jsonify({"success": True, "player": public_player(player), "server": public_server(server), "server_code": server.get("code")})


# ============================================================
# LEAVE
# ============================================================

@app.route("/leave", methods=["POST"])
def leave():
    username = get_session()
    if not username:
        return jsonify({"success": False}), 401
    with lock:
        server = get_server_for_player(username)
        if not server:
            return jsonify({"success": True})
        player = server["players"].pop(username, None)
        if player:
            account = accounts.get(username.lower())
            if account:
                account["coins"] = player.get("coins", account.get("coins", 0))
                account["best_score"] = max(account.get("best_score", 0), player.get("score", 0))
                save_accounts()
        if server["private"] and not server["players"]:
            servers.pop(server["id"], None)
    return jsonify({"success": True})


# ============================================================
# MOVEMENT
# ============================================================

@app.route("/move", methods=["POST"])
def move():
    username = get_session()
    if not username:
        return jsonify({"success": False, "error": "Not logged in."}), 401
    data = request.get_json(silent=True) or {}
    try:
        dx, dy = float(data.get("dx", 0)), float(data.get("dy", 0))
    except (TypeError, ValueError):
        return jsonify({"success": False, "error": "Invalid movement."}), 400
    dx, dy = clamp(dx, -1, 1), clamp(dy, -1, 1)
    length = (dx*dx + dy*dy) ** 0.5
    if length > 1: dx, dy = dx/length, dy/length
    with lock:
        server = get_server_for_player(username)
        if not server: return jsonify({"success": False, "error": "Player not in game."}), 400
        player = server["players"][username]
        now = time.time(); previous = player.get("last_move", now)
        elapsed = clamp(now - previous, MOVE_MIN_INTERVAL, 0.20)
        speed_mult = SPEED_BOOST_MULTIPLIER if player.get("speed_boost_until", 0) > now else 1.0
        distance = PLAYER_SPEED * elapsed * 60.0 * speed_mult
        player["x"] = clamp(player["x"] + dx*distance, 40, WORLD_WIDTH-40)
        player["y"] = clamp(player["y"] + dy*distance, 40, WORLD_HEIGHT-40)
        player["last_move"] = now; player["last_seen"] = now
        collected = 0
        for coin in server["coins"]:
            ddx, ddy = player["x"]-coin["x"], player["y"]-coin["y"]
            if ddx*ddx + ddy*ddy <= (player.get("radius", BASE_PLAYER_RADIUS)+16)**2:
                coin["x"], coin["y"] = random.randint(60, WORLD_WIDTH-60), random.randint(60, WORLD_HEIGHT-60)
                player["score"] += 1; player["coins"] += 1; collected += 1
                player["radius"] = clamp(player.get("radius", BASE_PLAYER_RADIUS) + 0.45, BASE_PLAYER_RADIUS, MAX_PLAYER_RADIUS)
        # powerups
        for pu in list(server["powerups"]):
            ddx, ddy = player["x"]-pu["x"], player["y"]-pu["y"]
            if ddx*ddx + ddy*ddy <= (player.get("radius", BASE_PLAYER_RADIUS)+24)**2:
                if pu["type"] == "speed": player["speed_boost_until"] = now + POWERUP_DURATION
                else: player["radius"] = clamp(player.get("radius", BASE_PLAYER_RADIUS) + 10, BASE_PLAYER_RADIUS, MAX_PLAYER_RADIUS)
                server["powerups"].remove(pu)
                refill_powerups(server)
        # blob combat: sufficiently larger blobs eat smaller blobs
        kills = 0
        for other_name, other in list(server["players"].items()):
            if other_name == username: continue
            ddx, ddy = player["x"]-other["x"], player["y"]-other["y"]
            touch = player.get("radius", BASE_PLAYER_RADIUS) + other.get("radius", BASE_PLAYER_RADIUS)
            if ddx*ddx + ddy*ddy <= (touch*0.62)**2:
                pr, orr = player.get("radius", BASE_PLAYER_RADIUS), other.get("radius", BASE_PLAYER_RADIUS)
                if pr >= orr * MIN_KILL_RATIO:
                    player["score"] += max(5, int(orr/4)); player["radius"] = clamp(pr + orr*0.22, BASE_PLAYER_RADIUS, MAX_PLAYER_RADIUS); kills += 1
                    other["x"], other["y"] = random.randint(150, WORLD_WIDTH-150), random.randint(150, WORLD_HEIGHT-150)
                    other["radius"] = BASE_PLAYER_RADIUS; other["score"] = max(0, other.get("score", 0)-3)
        player["best_score"] = max(player.get("best_score",0), player["score"])
        account = accounts.get(username.lower())
        if account:
            account["coins"] = player["coins"]; account["best_score"] = max(account.get("best_score",0), player["best_score"])
        return jsonify({"success": True, "collected": collected, "kills": kills, "x": player["x"], "y": player["y"], "score": player["score"], "coins": player["coins"], "radius": player["radius"]})


# ============================================================
# STATE
# ============================================================

@app.route("/state")
def state():
    username = get_session()
    if not username: return jsonify({"success": False, "error": "Not logged in."}), 401
    with lock:
        server = get_server_for_player(username)
        if not server: return jsonify({"success": False, "error": "Not in a server."}), 400
        now = time.time(); server["players"][username]["last_seen"] = now
        player_list = [public_player(p) for p in server["players"].values()]
        me = public_player(server["players"][username])
        return jsonify({"success": True, "world": {"width": WORLD_WIDTH, "height": WORLD_HEIGHT}, "players": player_list, "me": me, "coins": server["coins"], "powerups": server["powerups"], "server": public_server(server), "server_code": server.get("code")})


# ============================================================
# HEALTH / LOGOUT
# ============================================================

@app.route("/health")
def health():
    with lock:
        return jsonify({
            "success": True,
            "players": sum(len(x["players"]) for x in servers.values()),
            "max_players": MAX_PLAYERS,
            "servers": len(servers),
            "world": {
                "width": WORLD_WIDTH,
                "height": WORLD_HEIGHT,
            },
        })


@app.route("/logout", methods=["POST"])
def logout():
    token = request.headers.get("X-Session", "")
    if token:
        with lock:
            sessions.pop(token, None)

    return jsonify({"success": True})


# ============================================================
# CLEANUP THREAD
# ============================================================

def cleanup_players():
    while True:
        time.sleep(10)
        now = time.time()
        with lock:
            for server_id, server in list(servers.items()):
                dead = [u for u,p in server["players"].items() if now-p.get("last_seen",now) > PLAYER_TIMEOUT]
                for username in dead:
                    player = server["players"].pop(username, None)
                    if player:
                        account = accounts.get(username.lower())
                        if account:
                            account["coins"] = player.get("coins", account.get("coins",0))
                            account["best_score"] = max(account.get("best_score",0), player.get("best_score",0))
                if server["private"] and not server["players"]:
                    servers.pop(server_id, None)
            if any(True for _ in [0]):
                save_accounts()

threading.Thread(
    target=cleanup_players,
    daemon=True
).start()

def autosave():
    """Periodically persist account data without blocking the game loop."""
    while True:
        time.sleep(30)
        try:
            with lock:
                save_accounts()
        except Exception as e:
            print("⚠️ Autosave error:", e)


threading.Thread(
    target=autosave,
    daemon=True
).start()


# ============================================================
# LOCAL IP
# ============================================================

def get_local_ip():

    try:

        sock = socket.socket(
            socket.AF_INET,
            socket.SOCK_DGRAM
        )

        sock.connect(
            ("8.8.8.8", 80)
        )

        ip = sock.getsockname()[0]

        sock.close()

        return ip

    except Exception:

        return "127.0.0.1"


# ============================================================
# START
# ============================================================

if __name__ == "__main__":

    local_ip = get_local_ip()

    print()
    print("=" * 60)
    print("🟣 LAN BLOB ARENA - UPGRADED")
    print("=" * 60)
    print(
        "ACCOUNTS:",
        len(accounts)
    )
    print(
        "This phone:",
        "http://127.0.0.1:5000"
    )
    print(
        "Other devices:",
        f"http://{local_ip}:5000"
    )
    print(
        "WORLD:",
        WORLD_WIDTH,
        "x",
        WORLD_HEIGHT
    )
    print(
        "📱 Joystick | ⌨️ WASD / Arrows"
    )
    print(
        "🪙 Coins only - decorations removed"
    )
    print(
        "🌈 Color-Changing skin"
    )
    print(
        "🎨 Profile + Options"
    )
    print(
        "🚪 Leave Game"
    )
    print(
        "👥 Max players:",
        MAX_PLAYERS
    )
    print("=" * 60)
    print()

    app.run(
        host="0.0.0.0",
        port=5000,
        debug=False,
        threaded=True
    )
