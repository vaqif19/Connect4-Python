"""
CONNECT 4 ONLINE  VAQIF ISMAYILOV!
"""
from __future__ import annotations
import json
import math
import queue
import random
import socket
import sys
import threading
from array import array
from typing import Any, Dict, List, Optional, Tuple
try:
    import pygame
except ImportError:  # pragma: no cover
    print("Pygame is required. Install it with:  python -m pip install pygame")
    sys.exit(1)

# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #
BASE_W, BASE_H = 1280, 720          # virtual canvas, scaled to the real window
COLS, ROWS = 7, 6
CELL = 82
PAD = 18
BOARD_W = COLS * CELL + 2 * PAD
BOARD_H = ROWS * CELL + 2 * PAD
BOARD_X = (BASE_W - BOARD_W) // 2
BOARD_Y = 150
DISC_R = 33
HOLE_R = 37

DEFAULT_PORT = 5555
PROTOCOL_VERSION = 1
CONNECT_TIMEOUT = 6.0
SOCKET_TIMEOUT = 0.5
MAX_NAME = 14
MAX_BUFFER = 65536
START_DELAY = 1.2
RESULT_DELAY = 1.1
AI_THINK_TIME = 0.7

RESOLUTIONS = [(960, 540), (1280, 720), (1600, 900), (1920, 1080)]
FPS_OPTIONS = [30, 60, 120, 144]

# --- LIGHT PASTEL COLOR PALETTE ---
C_BG_TOP = (255, 249, 238)    # warm cream (top of background gradient)
C_BG_BOT = (196, 226, 250)    # soft sky blue (bottom of background gradient)
C_PANEL = (252, 253, 255)     # near-white panels
C_PANEL2 = (228, 239, 252)    # pale blue buttons
C_PANEL2_H = (200, 222, 250)  # button hover tone
C_TEXT = (38, 52, 84)         # dark navy text (readable on light backgrounds)
C_MUTED = (106, 122, 152)     # soft slate-blue secondary text
C_ACCENT = (36, 104, 184)     # ocean blue: titles, focus rings, highlights
C_GOLD = (255, 190, 64)       # warm gold: winning highlights, sparkles
C_SHADOW = (166, 184, 214)    # soft blue-grey drop shadow
C_RED = (255, 125, 145)       # coral pink  (Player 1)
C_RED_D = (208, 72, 100)
C_RED_L = (255, 196, 206)
C_MINT = (112, 218, 178)      # mint green  (Player 2)
C_MINT_D = (40, 150, 112)
C_MINT_L = (206, 250, 232)
C_BOARD = (150, 190, 240)     # light periwinkle board
C_BOARD_L = (108, 150, 214)   # board edge and general borders
C_HOLE_BACK = (248, 251, 255) # white-ish board holes
C_GREEN = (46, 172, 118)      # success / "on" green
C_WHITE = (255, 255, 255)
C_TRACK = (208, 220, 240)      # slider track
C_TOGGLE_OFF = (190, 202, 224)  # switch in the OFF position

PLAYER_COLORS = {1: (C_RED, C_RED_D, C_RED_L), 2: (C_MINT, C_MINT_D, C_MINT_L)}
PLAYER_NAMES = {1: "Coral", 2: "Mint"}

# --- STYLE SWITCH -----------------------------------------------------------
# The main menu keeps the original "soft" look. Settings, guide, lobby, waiting
# room and game screens use the "sticker" look: lavender/peach background with a
# faint grid, thick ink outlines, hard offset shadows and a different font.
_ALT = False
_BASE_KEYS = ("C_BG_TOP", "C_BG_BOT", "C_PANEL", "C_PANEL2", "C_PANEL2_H", "C_TEXT", "C_MUTED", "C_ACCENT",
              "C_SHADOW", "C_BOARD", "C_BOARD_L", "C_HOLE_BACK", "C_TRACK", "C_TOGGLE_OFF")
_BASE_PAL = {k: globals()[k] for k in _BASE_KEYS}
_ALT_PAL = {
    "C_BG_TOP": (255, 240, 230),      # peach
    "C_BG_BOT": (226, 220, 252),      # lavender
    "C_PANEL": (255, 255, 255),
    "C_PANEL2": (255, 238, 216),      # warm peach buttons
    "C_PANEL2_H": (255, 216, 172),
    "C_TEXT": (44, 36, 92),           # deep indigo ink (text + outlines)
    "C_MUTED": (110, 100, 156),
    "C_ACCENT": (120, 72, 222),       # violet titles / focus
    "C_SHADOW": (184, 170, 240),      # hard offset shadow
    "C_BOARD": (176, 164, 244),       # lavender board
    "C_BOARD_L": (44, 36, 92),        # outlines
    "C_HOLE_BACK": (255, 252, 248),
    "C_TRACK": (226, 218, 250),
    "C_TOGGLE_OFF": (206, 198, 232),
}


def set_alt_style(on: bool) -> None:
    """Switches the active palette (module-level colors) and widget style."""
    global _ALT
    _ALT = on
    globals().update(_ALT_PAL if on else _BASE_PAL)


Board = List[List[int]]

# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #


def clamp(v: float, lo: float, hi: float) -> float:
    return lo if v < lo else hi if v > hi else v


def lerp_color(a: Tuple[int, int, int], b: Tuple[int, int, int], t: float) -> Tuple[int, int, int]:
    t = clamp(t, 0.0, 1.0)
    return (int(a[0] + (b[0] - a[0]) * t), int(a[1] + (b[1] - a[1]) * t), int(a[2] + (b[2] - a[2]) * t))


_FONTS: Dict[Tuple[int, bool, bool], pygame.font.Font] = {}
_TEXT_CACHE: Dict[Tuple[str, int, Tuple[int, int, int], bool, bool], pygame.Surface] = {}

FONT_CANDIDATES = ["dejavusans", "liberationsans", "notosans", "freesans", "ubuntu", "arial", "calibri", "tahoma", "verdana", "trebuchetms",
                   "roboto", "opensans", "helveticaneue", "helvetica", "arialunicodems", "sfnsdisplay", "sfnstext", "lucidagrande", "menlo"]
_FONT_PATHS: Optional[Tuple[Optional[str], Optional[str]]] = None   # (regular, bold); None = no usable system font


def _font_usable(path: Optional[str]) -> bool:
    """True when the font file can render basic Latin letters correctly."""
    if not path:
        return False
    try:
        font = pygame.font.Font(path, 20)
        for char in "Aa":
            surf = font.render(char, True, (255, 255, 255))
            if surf.get_width() <= 0:
                return False
        return True
    except Exception:
        return False


ALT_FONT_CANDIDATES = ["poppins", "montserrat", "nunito", "quicksand", "comfortaa", "ubuntu", "notosans",
                       "liberationsans", "freesans", "arial"]
_FONT_PATHS_ALT: Optional[Tuple[Optional[str], Optional[str]]] = None


def _resolve_fonts() -> Tuple[Optional[str], Optional[str]]:
    """Returns (regular, bold) font paths for the active style."""
    global _FONT_PATHS_ALT
    if not _ALT:
        return _resolve_base_fonts()
    if _FONT_PATHS_ALT is None:
        found = None
        for name in ALT_FONT_CANDIDATES:
            try:
                regular = pygame.font.match_font(name)
            except Exception:
                regular = None
            if not _font_usable(regular):
                continue
            try:
                bold = pygame.font.match_font(name, bold=True)
            except Exception:
                bold = None
            found = (regular, bold if _font_usable(bold) else regular)
            break
        _FONT_PATHS_ALT = found if found else _resolve_base_fonts()
    return _FONT_PATHS_ALT


def _resolve_base_fonts() -> Tuple[Optional[str], Optional[str]]:
    """Finds a usable system font; scans every installed font if needed."""
    global _FONT_PATHS
    if _FONT_PATHS is not None:
        return _FONT_PATHS
    names: List[str] = list(FONT_CANDIDATES)
    try:
        names += [n for n in pygame.font.get_fonts() if n not in names]
    except Exception:
        pass
    for name in names:
        try:
            regular = pygame.font.match_font(name)
        except Exception:
            regular = None
        if not _font_usable(regular):
            continue
        try:
            bold = pygame.font.match_font(name, bold=True)
        except Exception:
            bold = None
        _FONT_PATHS = (regular, bold if _font_usable(bold) else regular)
        return _FONT_PATHS
    _FONT_PATHS = (None, None)
    return _FONT_PATHS


def prep_text(text: str) -> str:
    """Hook for text preprocessing (English text needs none)."""
    return text


def get_font(size: int, bold: bool = False) -> pygame.font.Font:
    key = (size, bold, _ALT)
    f = _FONTS.get(key)
    if f is None:
        regular, bold_path = _resolve_fonts()
        try:
            if regular:
                f = pygame.font.Font(bold_path if bold else regular, size)
                if bold and bold_path == regular:
                    f.set_bold(True)   # no real bold file: synthesize it
            else:
                f = pygame.font.Font(None, int(size * 1.2))
        except Exception:
            f = pygame.font.Font(None, int(size * 1.2))
        _FONTS[key] = f
    return f


def render_text(text: str, size: int, color: Tuple[int, int, int], bold: bool = False) -> pygame.Surface:
    key = (text, size, color, bold, _ALT)
    s = _TEXT_CACHE.get(key)
    if s is None:
        if len(_TEXT_CACHE) > 500:
            _TEXT_CACHE.clear()
        s = get_font(size, bold).render(prep_text(text), True, color)
        _TEXT_CACHE[key] = s
    return s


def draw_text(surf: pygame.Surface, text: str, size: int, color: Tuple[int, int, int],
              pos: Tuple[int, int], anchor: str = "center", bold: bool = False,
              max_w: Optional[int] = None) -> pygame.Rect:
    """Draws text; if max_w is given the font shrinks until the text fits inside it."""
    if max_w is not None:
        while size > 11 and get_font(size, bold).size(prep_text(text))[0] > max_w:
            size -= 1
    img = render_text(text, size, color, bold)
    rect = img.get_rect()
    setattr(rect, anchor, (int(pos[0]), int(pos[1])))
    surf.blit(img, rect)
    return rect


def wrap_text(text: str, size: int, width: int, bold: bool = False) -> List[str]:
    font = get_font(size, bold)
    lines: List[str] = []
    for para in text.split("\n"):
        cur = ""
        for word in para.split():
            trial = (cur + " " + word).strip()
            if font.size(prep_text(trial))[0] <= width:
                cur = trial
            else:
                if cur:
                    lines.append(cur)
                cur = word
        lines.append(cur)
    return lines


def draw_panel(surf: pygame.Surface, rect: pygame.Rect, fill=None, border=None, radius: int = 14) -> None:
    fill = C_PANEL if fill is None else fill
    border = C_BOARD_L if border is None else border
    if _ALT:   # sticker look: hard offset shadow + thick ink outline
        rad = max(6, radius - 4)
        pygame.draw.rect(surf, C_SHADOW, rect.move(6, 6), border_radius=rad)
        pygame.draw.rect(surf, fill, rect, border_radius=rad)
        pygame.draw.rect(surf, border, rect, width=3, border_radius=rad)
        return
    # soft drop shadow gives the panels depth
    pygame.draw.rect(surf, C_SHADOW, rect.move(0, 6), border_radius=radius)
    pygame.draw.rect(surf, fill, rect, border_radius=radius)
    pygame.draw.rect(surf, border, rect, width=2, border_radius=radius)


def draw_title(surf: pygame.Surface, text: str, size: int, pos: Tuple[int, int], max_w: Optional[int] = None) -> None:
    """Screen title; the sticker style adds an offset shadow."""
    if _ALT:
        draw_text(surf, text, size, C_SHADOW, (pos[0] + 3, pos[1] + 4), bold=True, max_w=max_w)
    draw_text(surf, text, size, C_ACCENT, pos, bold=True, max_w=max_w)


def draw_disc(surf: pygame.Surface, cx: int, cy: int, r: int, player: int) -> None:
    base, dark, light = PLAYER_COLORS[player]
    if _ALT:   # flat sticker disc: ink outline, inner ring, small shine
        pygame.draw.circle(surf, C_TEXT, (cx, cy), r)
        pygame.draw.circle(surf, base, (cx, cy), r - 4)
        pygame.draw.circle(surf, dark, (cx, cy), max(2, int(r * 0.56)), 3)
        pygame.draw.circle(surf, light, (cx - int(r * 0.34), cy - int(r * 0.34)), max(2, int(r * 0.17)))
        return
    pygame.draw.circle(surf, dark, (cx, cy), r)
    pygame.draw.circle(surf, base, (cx, cy), r - 3)
    pygame.draw.circle(surf, lerp_color(base, dark, 0.35), (cx, cy), max(2, int(r * 0.66)), 3)
    pygame.draw.circle(surf, light, (cx - int(r * 0.3), cy - int(r * 0.33)), max(2, int(r * 0.14)))


def cell_center(row: int, col: int) -> Tuple[int, int]:
    return BOARD_X + PAD + col * CELL + CELL // 2, BOARD_Y + PAD + row * CELL + CELL // 2


# --------------------------------------------------------------------------- #
# Game rules (shared by local, AI, host and client modes)
# --------------------------------------------------------------------------- #


def new_board() -> Board:
    return [[0] * COLS for _ in range(ROWS)]


def column_available(board: Board, col: int) -> bool:
    return 0 <= col < COLS and board[0][col] == 0


def lowest_empty_row(board: Board, col: int) -> int:
    if not 0 <= col < COLS:
        return -1
    for r in range(ROWS - 1, -1, -1):
        if board[r][col] == 0:
            return r
    return -1


def check_direction(board: Board, dr: int, dc: int) -> Tuple[int, List[Tuple[int, int]]]:
    for r in range(ROWS):
        for c in range(COLS):
            p = board[r][c]
            if not p:
                continue
            er, ec = r + 3 * dr, c + 3 * dc
            if not (0 <= er < ROWS and 0 <= ec < COLS):
                continue
            if all(board[r + i * dr][c + i * dc] == p for i in range(1, 4)):
                return p, [(r + i * dr, c + i * dc) for i in range(4)]
    return 0, []


def check_horizontal(board: Board):
    return check_direction(board, 0, 1)


def check_vertical(board: Board):
    return check_direction(board, 1, 0)


def check_diagonal_down(board: Board):
    return check_direction(board, 1, 1)


def check_diagonal_up(board: Board):
    return check_direction(board, 1, -1)


def find_winner(board: Board) -> Tuple[int, List[Tuple[int, int]]]:
    for fn in (check_horizontal, check_vertical, check_diagonal_down, check_diagonal_up):
        p, cells = fn(board)
        if p:
            return p, cells
    return 0, []


def board_full(board: Board) -> bool:
    return all(board[0][c] != 0 for c in range(COLS))


def is_draw(board: Board) -> bool:
    return board_full(board) and find_winner(board)[0] == 0


class Game:
    """Authoritative game state. Row 0 is the top row."""

    def __init__(self) -> None:
        self.board: Board = new_board()
        self.current = 1
        self.winner = 0
        self.win_cells: List[Tuple[int, int]] = []
        self.draw = False
        self.moves = 0
        self.last: Optional[Tuple[int, int]] = None

    def reset(self) -> None:
        self.board = new_board()
        self.current = 1
        self.winner = 0
        self.win_cells = []
        self.draw = False
        self.moves = 0
        self.last = None

    @property
    def over(self) -> bool:
        return self.winner != 0 or self.draw

    def switch_turn(self) -> None:
        self.current = 3 - self.current

    def validate(self, player: Any, col: Any) -> Optional[str]:
        if self.over:
            return "The game is already over."
        if player != self.current:
            return "It's not your turn."
        if not isinstance(col, int) or isinstance(col, bool) or not 0 <= col < COLS:
            return "Invalid column."
        if not column_available(self.board, col):
            return "That column is full."
        return None

    def drop(self, player: int, col: int) -> int:
        row = lowest_empty_row(self.board, col)
        self.board[row][col] = player
        self.moves += 1
        self.last = (row, col)
        w, cells = find_winner(self.board)
        if w:
            self.winner, self.win_cells = w, cells
        elif is_draw(self.board):
            self.draw = True
        else:
            self.switch_turn()
        return row

    def to_dict(self) -> Dict[str, Any]:
        return {"board": self.board, "current": self.current, "winner": self.winner,
                "win_cells": [list(c) for c in self.win_cells], "draw": self.draw,
                "moves": self.moves, "last": list(self.last) if self.last else None}

    def load(self, d: Dict[str, Any]) -> None:
        board = [[int(x) for x in row] for row in d["board"]]
        if len(board) != ROWS or any(len(r) != COLS for r in board) or any(x not in (0, 1, 2) for r in board for x in r):
            raise ValueError("bad board")
        self.board = board
        self.current = 1 if int(d["current"]) == 1 else 2
        self.winner = int(d["winner"])
        self.win_cells = [(int(a), int(b)) for a, b in d["win_cells"]]
        self.draw = bool(d["draw"])
        self.moves = int(d["moves"])
        last = d.get("last")
        self.last = (int(last[0]), int(last[1])) if last else None


# --------------------------------------------------------------------------- #
# AI opponent (heuristic, fast)
# --------------------------------------------------------------------------- #


def would_win(board: Board, col: int, player: int) -> bool:
    r = lowest_empty_row(board, col)
    if r < 0:
        return False
    board[r][col] = player
    won = find_winner(board)[0] == player
    board[r][col] = 0
    return won


def _window_score(w: List[int], me: int, opp: int) -> int:
    m, o, e = w.count(me), w.count(opp), w.count(0)
    if m == 4:
        return 1000
    if m == 3 and e == 1:
        return 8
    if m == 2 and e == 2:
        return 3
    if o == 3 and e == 1:
        return -9
    return 0


def evaluate_board(board: Board, me: int, opp: int) -> int:
    score = 0
    mid = COLS // 2
    for r in range(ROWS):
        if board[r][mid] == me:
            score += 4
        elif board[r][mid] == opp:
            score -= 4
    for dr, dc in ((0, 1), (1, 0), (1, 1), (1, -1)):
        for r in range(ROWS):
            for c in range(COLS):
                er, ec = r + 3 * dr, c + 3 * dc
                if 0 <= er < ROWS and 0 <= ec < COLS:
                    score += _window_score([board[r + i * dr][c + i * dc] for i in range(4)], me, opp)
    return score


def ai_choose_move(board_in: Board, me: int) -> int:
    board = [row[:] for row in board_in]
    opp = 3 - me
    valid = [c for c in range(COLS) if column_available(board, c)]
    if not valid:
        return -1
    for c in valid:                       # 1. win now
        if would_win(board, c, me):
            return c
    for c in valid:                       # 2. block the human's win
        if would_win(board, c, opp):
            return c
    best_col, best_score = valid[0], -1e18
    for c in valid:                       # 3. heuristic with 2-ply look-ahead
        r = lowest_empty_row(board, c)
        board[r][c] = me
        score = float(evaluate_board(board, me, opp))
        if r > 0 and would_win(board, c, opp):
            score -= 10000                 # avoid handing the opponent a win
        reply_best = None
        for oc in range(COLS):
            orow = lowest_empty_row(board, oc)
            if orow < 0:
                continue
            board[orow][oc] = opp
            s = evaluate_board(board, opp, me)
            board[orow][oc] = 0
            reply_best = s if reply_best is None else max(reply_best, s)
        if reply_best is not None:
            score -= 0.5 * reply_best
        board[r][c] = 0
        score += random.random() * 0.5
        if score > best_score:
            best_col, best_score = c, score
    return best_col


# --------------------------------------------------------------------------- #
# Networking (TCP, newline-delimited JSON, background threads + event queue)
# --------------------------------------------------------------------------- #


def get_local_ip() -> str:
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))  # no packet is sent for UDP connect
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return "127.0.0.1"


def describe_os_error(exc: OSError) -> str:
    if exc.errno in (98, 48, 10048):
        return "that port is already in use"
    if exc.errno in (13, 10013):
        return "permission denied (choose a port above 1024)"
    return exc.strerror or str(exc)


class Network:
    """Owns the sockets. Network threads only push tuples into `events`."""

    def __init__(self) -> None:
        self.events: "queue.Queue[tuple]" = queue.Queue()
        self.stop = threading.Event()
        self.lock = threading.Lock()
        self.send_lock = threading.Lock()
        self.conn: Optional[socket.socket] = None
        self.listener: Optional[socket.socket] = None
        self.threads: List[threading.Thread] = []

    @property
    def connected(self) -> bool:
        with self.lock:
            return self.conn is not None

    def start_host(self, port: int) -> None:
        self._spawn(self._host_loop, (port,))

    def start_connect(self, host: str, port: int) -> None:
        self._spawn(self._connect_loop, (host, port))

    def _spawn(self, fn, args) -> None:
        t = threading.Thread(target=fn, args=args, daemon=True)
        self.threads.append(t)
        t.start()

    def _host_loop(self, port: int) -> None:
        srv = None
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            if sys.platform != "win32":
                srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            srv.bind(("0.0.0.0", port))
            srv.listen(2)
            srv.settimeout(SOCKET_TIMEOUT)
        except OSError as exc:
            if srv:
                srv.close()
            self.events.put(("error", f"Could not start the server on port {port}: {describe_os_error(exc)}."))
            return
        self.listener = srv
        self.events.put(("listening", port))
        while not self.stop.is_set():
            try:
                conn, addr = srv.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            with self.lock:
                busy = self.conn is not None
            if busy:
                try:
                    conn.sendall("{\"type\":\"reject\",\"message\":\"This game already has two players.\"}\n".encode("utf-8"))
                except OSError:
                    pass
                conn.close()
                continue
            self._attach(conn)
            self.events.put(("accepted", addr[0]))
        try:
            srv.close()
        except OSError:
            pass

    def _connect_loop(self, host: str, port: int) -> None:
        try:
            sock = socket.create_connection((host, port), timeout=CONNECT_TIMEOUT)
        except socket.gaierror:
            self.events.put(("error", f"Could not find a computer named '{host}'. Check the address."))
        except socket.timeout:
            self.events.put(("error", "Connection timed out. Check the IP address and port, and make sure the host's firewall / "
                                      "router allows the connection."))
        except ConnectionRefusedError:
            self.events.put(("error", "Connection refused. Make sure the host is running the game and the port is correct."))
        except OSError as exc:
            self.events.put(("error", f"Could not connect: {describe_os_error(exc)}."))
        else:
            if self.stop.is_set():
                sock.close()
                return
            self._attach(sock)
            self.events.put(("connected",))

    def _attach(self, sock: socket.socket) -> None:
        sock.settimeout(SOCKET_TIMEOUT)
        try:
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        with self.lock:
            self.conn = sock
        self._spawn(self._reader, (sock,))

    def _reader(self, sock: socket.socket) -> None:
        buf = b""
        reason = "The other player disconnected."
        while not self.stop.is_set():
            try:
                data = sock.recv(4096)
            except socket.timeout:
                continue
            except OSError as exc:
                reason = f"Connection lost: {describe_os_error(exc)}."
                break
            if not data:
                break
            buf += data
            if len(buf) > MAX_BUFFER:
                reason = "Received invalid data from the other player."
                break
            while b"\n" in buf:  # message framing: one JSON document per line
                line, buf = buf.split(b"\n", 1)
                if not line.strip():
                    continue
                try:
                    msg = json.loads(line.decode("utf-8"))
                except (ValueError, UnicodeDecodeError):
                    continue
                if isinstance(msg, dict):
                    self.events.put(("msg", msg))
        with self.lock:
            current = self.conn is sock
            if current:
                self.conn = None
        try:
            sock.close()
        except OSError:
            pass
        if current and not self.stop.is_set():
            self.events.put(("disconnected", reason))

    def send(self, msg: Dict[str, Any]) -> bool:
        with self.lock:
            sock = self.conn
        if sock is None:
            return False
        data = (json.dumps(msg) + "\n").encode("utf-8")
        try:
            with self.send_lock:
                sock.sendall(data)
            return True
        except OSError:
            return False

    def close(self) -> None:
        self.stop.set()
        with self.lock:
            sock, self.conn = self.conn, None
        if sock is not None:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                sock.close()
            except OSError:
                pass
        if self.listener is not None:
            try:
                self.listener.close()
            except OSError:
                pass
        for t in self.threads:
            if t is not threading.current_thread():
                t.join(timeout=0.3)


# --------------------------------------------------------------------------- #
# Settings and procedural audio
# --------------------------------------------------------------------------- #


class Settings:
    def __init__(self) -> None:
        self.master = 0.8
        self.music = 0.5
        self.sfx = 0.8
        self.anim = 1.0
        self.res = 1
        self.fullscreen = False
        self.fps = 60
        self.particles = True


class Audio:
    """Generates every sound with math. Fails silently if no audio device is available."""

    def __init__(self, settings: Settings) -> None:
        self.settings = settings
        self.enabled = False
        self.sounds: Dict[str, pygame.mixer.Sound] = {}
        self.music: Optional[pygame.mixer.Sound] = None
        self.rate, self.channels = 22050, 1
        try:
            if not pygame.mixer.get_init():
                pygame.mixer.init(22050, -16, 1, 512)
            info = pygame.mixer.get_init()
            if info is None or info[1] != -16:
                return
            self.rate, _, self.channels = info
            self.sounds["click"] = self._make(self._tone(760, 0.07, 0.45, harm=0.3))
            self.sounds["drop"] = self._make(self._tone(190, 0.16, 0.8, slide=-90, harm=0.5))
            self.sounds["error"] = self._make(self._tone(130, 0.18, 0.6, harm=0.9))
            self.sounds["win"] = self._make(sum((self._tone(f, 0.16, 0.5, harm=0.3)
                                                 for f in (523, 659, 784, 1047)), []))
            self.sounds["lose"] = self._make(sum((self._tone(f, 0.2, 0.5, harm=0.3)
                                                  for f in (392, 330, 262)), []))
            self.music = self._make(self._build_music())
            self.enabled = True
            self.music.play(-1)
            self.apply_volumes()
        except Exception:
            self.enabled = False
            self.sounds = {}
            self.music = None

    def _tone(self, freq: float, dur: float, vol: float = 0.5, slide: float = 0.0, harm: float = 0.0) -> List[float]:
        n = max(1, int(self.rate * dur))
        out: List[float] = []
        ph = 0.0
        attack = self.rate * 0.004
        for i in range(n):
            t = i / n
            ph += 2 * math.pi * (freq + slide * t) / self.rate
            env = (1 - t) ** 2 * min(1.0, i / attack)
            out.append((math.sin(ph) + harm * math.sin(2 * ph)) * env * vol)
        return out

    def _build_music(self) -> List[float]:
        notes = [220, 262, 330, 262, 175, 220, 262, 220, 262, 330, 392, 330, 196, 247, 294, 247]
        out: List[float] = []
        n = int(self.rate * 0.5)
        for f in notes:
            for i in range(n):
                t = i / n
                env = math.sin(math.pi * t) ** 1.5
                ph = 2 * math.pi * f * i / self.rate
                out.append((math.sin(ph) * 0.6 + math.sin(ph * 0.5) * 0.4) * env * 0.5)
        return out

    def _make(self, samples: List[float]) -> pygame.mixer.Sound:
        data = array("h")
        for s in samples:
            v = int(clamp(s, -1.0, 1.0) * 32767)
            for _ in range(self.channels):
                data.append(v)
        return pygame.mixer.Sound(buffer=data.tobytes())

    def apply_volumes(self) -> None:
        if self.enabled and self.music is not None:
            self.music.set_volume(self.settings.master * self.settings.music * 0.5)

    def play(self, name: str) -> None:
        if not self.enabled:
            return
        s = self.sounds.get(name)
        if s is not None:
            try:
                s.set_volume(self.settings.master * self.settings.sfx)
                s.play()
            except pygame.error:
                pass


# --------------------------------------------------------------------------- #
# UI widgets
# --------------------------------------------------------------------------- #


class Button:
    def __init__(self, rect: Tuple[int, int, int, int], text: str, accent=C_ACCENT, size: int = 26) -> None:
        self.rect = pygame.Rect(rect)
        self.text = text
        self.accent = accent
        self.size = size
        self.enabled = True
        self.hover = 0.0
        self.dy = 0   # vertical text offset

    def update(self, mouse: Tuple[float, float], dt: float) -> None:
        target = 1.0 if (self.enabled and self.rect.collidepoint(mouse)) else 0.0
        self.hover += (target - self.hover) * min(1.0, dt * 14)

    def hit(self, pos: Tuple[float, float]) -> bool:
        return self.enabled and self.rect.collidepoint(pos)

    def draw(self, surf: pygame.Surface) -> None:
        h = self.hover
        if _ALT:   # sticker button: presses into its hard shadow on hover
            fill = lerp_color(C_PANEL2, C_PANEL2_H, h)
            if self.accent == C_GREEN:
                fill = lerp_color((214, 248, 232), (176, 238, 208), h)
            elif self.accent == C_RED:
                fill = lerp_color((255, 224, 228), (255, 196, 206), h)
            elif self.accent == C_ACCENT:
                fill = lerp_color((228, 216, 252), (204, 186, 250), h)
            if not self.enabled:
                fill = (238, 234, 244)
            d = int(3 * h)
            body = self.rect.move(d, d)
            pygame.draw.rect(surf, C_SHADOW, self.rect.move(5, 5), border_radius=10)
            pygame.draw.rect(surf, fill, body, border_radius=10)
            pygame.draw.rect(surf, C_TEXT if self.enabled else (176, 170, 200), body, width=3, border_radius=10)
            draw_text(surf, self.text, self.size, C_TEXT if self.enabled else C_MUTED, (body.centerx, body.centery + self.dy), bold=True,
                      max_w=body.w - 20)
            return
        r = self.rect.inflate(int(8 * h), int(8 * h))  # subtle grow-on-hover effect
        # soft button shadow
        pygame.draw.rect(surf, C_SHADOW, r.move(0, 4), border_radius=10)
        base = lerp_color(C_PANEL2, C_PANEL2_H, h) if self.enabled else (234, 238, 246)
        pygame.draw.rect(surf, base, r, border_radius=10)
        border = lerp_color(C_BOARD_L, self.accent, h) if self.enabled else (206, 212, 226)
        pygame.draw.rect(surf, border, r, width=2, border_radius=10)
        draw_text(surf, self.text, self.size, C_TEXT if self.enabled else C_MUTED, r.center, bold=True,
                  max_w=r.w - 20)


class TextInput:
    def __init__(self, rect: Tuple[int, int, int, int], text: str = "", max_len: int = 32,
                 allowed: Optional[str] = None, placeholder: str = "") -> None:
        self.rect = pygame.Rect(rect)
        self.text = text
        self.max_len = max_len
        self.allowed = allowed
        self.placeholder = placeholder
        self.active = False

    def handle_key(self, e: pygame.event.Event) -> None:
        if not self.active:
            return
        if e.key == pygame.K_BACKSPACE:
            self.text = self.text[:-1]
        elif e.unicode and e.unicode.isprintable() and len(self.text) < self.max_len:
            if self.allowed is None or e.unicode in self.allowed:
                self.text += e.unicode

    def draw(self, surf: pygame.Surface, label: str, t: float) -> None:
        draw_text(surf, label, 20, C_MUTED, (self.rect.x, self.rect.y - 6), anchor="bottomleft", max_w=self.rect.w)
        if _ALT and self.active:
            pygame.draw.rect(surf, C_SHADOW, self.rect.move(4, 4), border_radius=8)
        pygame.draw.rect(surf, C_WHITE, self.rect, border_radius=8)  # white input field
        pygame.draw.rect(surf, C_ACCENT if self.active else C_BOARD_L, self.rect, width=3 if _ALT else 2, border_radius=8)
        img = render_text(self.text or self.placeholder, 24, C_TEXT if self.text else (160, 172, 195))
        clip = surf.get_clip()
        surf.set_clip(self.rect.inflate(-16, -4))
        x = self.rect.x + 12
        if img.get_width() > self.rect.w - 28:
            x = self.rect.right - 14 - img.get_width()
        surf.blit(img, (x, self.rect.centery - img.get_height() // 2))
        if self.active and int(t * 2) % 2 == 0:
            cx = min(x + (render_text(self.text, 24, C_TEXT).get_width() if self.text else 0), self.rect.right - 10)
            pygame.draw.line(surf, C_ACCENT, (cx + 2, self.rect.y + 10), (cx + 2, self.rect.bottom - 10), 2)
        surf.set_clip(clip)


class FallingDisc:
    def __init__(self, row: int, col: int, player: int, gravity: float, bounce: bool) -> None:
        self.row, self.col, self.player = row, col, player
        self.x, self.target = cell_center(row, col)
        self.y = float(BOARD_Y - 44)
        self.vy = 0.0
        self.g = gravity
        self.bounce = bounce
        self.bounced = False
        self.hit = False
        self.hit_handled = False
        self.done = False

    def update(self, dt: float) -> None:
        self.vy += self.g * dt
        self.y += self.vy * dt
        if self.y >= self.target:
            self.y = float(self.target)
            self.hit = True
            if self.bounce and not self.bounced and self.vy > 350:
                self.vy = -self.vy * 0.28
                self.bounced = True
            else:
                self.done = True


# --------------------------------------------------------------------------- #
# Application
# --------------------------------------------------------------------------- #

HOWTO = [
    ("h", "The Goal"),
    ("p", "Connect four of your discs in a straight line - sideways, up and down, or diagonally - before your rival does. "
          "You take turns sliding a disc into any of the 7 columns, and it drops to the lowest free slot. If every slot "
          "fills up and nobody has four in a row, the round ends in a tie. Coral (Player 1) always moves first."),
    ("h", "Playing the Game"),
    ("p", "Hover over a column and click to drop your disc. Prefer the keyboard? Press 1-7, or steer with the Left/Right "
          "arrows and confirm with Enter. Esc pauses the game and F11 switches full screen on or off."),
    ("h", "Hosting a Room"),
    ("p", "Open the Create Room tab, pick a port (5555 by default) and press Open Room. Your address appears in the room "
          "lobby - send it to your friend. The host controls Coral, the guest controls Mint, and the host's game "
          "double-checks every move."),
    ("h", "Joining a Room"),
    ("p", "Open the Join Room tab, enter the host's address and port, then press Enter Room. On the same Wi-Fi or local "
          "network, use the host's local IP (for example 192.168.1.20). To test on a single computer, open two windows "
          "and connect one of them to 127.0.0.1."),
    ("h", "Playing Across the Internet"),
    ("p", "Rooms work out of the box on a shared local network. For internet play, the host's router has to forward the "
          "chosen TCP port to the host's computer, and the guest must connect to the host's public IP (or both players "
          "can join the same VPN, such as Tailscale or ZeroTier). Many home and mobile connections block incoming "
          "traffic or share one public address (CGNAT), and your firewall might need to let Python through - so "
          "internet play can't be guaranteed on every network."),
]

# Settings screen layout: mixer panel on the left, tile grid on the right
SOUND_PANEL = pygame.Rect(90, 110, 470, 480)
FADERS = [("Master", "master"), ("Music", "music"), ("Effects", "sfx")]
FADER_TOP, FADER_BOT = 215, 495
SETTING_TILES = {
    "res": pygame.Rect(600, 110, 285, 150), "fps": pygame.Rect(905, 110, 285, 150),
    "fullscreen": pygame.Rect(600, 280, 285, 150), "particles": pygame.Rect(905, 280, 285, 150),
    "anim": pygame.Rect(600, 450, 590, 140),
}
TILE_NAMES = {"res": "Window Size", "fps": "Frame Rate", "fullscreen": "Full Screen",
              "particles": "Sparkles", "anim": "Motion Level"}
TILE_TINTS = {"res": (255, 238, 216), "fps": (214, 248, 232), "fullscreen": (255, 224, 228),
              "particles": (228, 216, 252), "anim": (255, 247, 205)}
ANIM_X0, ANIM_W = 640, 400

# Self-playing demo board on the main menu
DEMO_CELL, DEMO_PAD, DEMO_R = 56, 12, 24
DEMO_W, DEMO_H = COLS * DEMO_CELL + 2 * DEMO_PAD, ROWS * DEMO_CELL + 2 * DEMO_PAD
DEMO_X, DEMO_Y = 130, 215
DEMO_DROP_T = 0.42


class App:
    def __init__(self) -> None:
        pygame.mixer.pre_init(22050, -16, 1, 512)
        pygame.init()
        pygame.display.set_caption("CONNECT 4 ONLINE")
        self.settings = Settings()
        self.window: pygame.Surface = pygame.display.set_mode(RESOLUTIONS[self.settings.res], pygame.RESIZABLE)
        self.canvas = pygame.Surface((BASE_W, BASE_H)).convert()
        self.scale_buf: Optional[pygame.Surface] = None
        self.view = (1.0, 0, 0)
        self.clock = pygame.time.Clock()
        self.audio = Audio(self.settings)
        self.running = True
        self.t = 0.0
        self.mouse: Tuple[float, float] = (0, 0)

        self.bg = self._make_background()
        self.bg_alt = self._make_background(True)
        self.bg_particles = [[random.uniform(0, BASE_W), random.uniform(0, BASE_H), random.uniform(2, 6),
                              random.uniform(8, 30), random.uniform(0, 6.28),
                              random.choice([C_RED, C_MINT, C_BOARD_L])] for _ in range(55)]
        self.fx: List[List[Any]] = []
        self.board_surf = self._make_board_surface()
        self.board_surf_alt = self._make_board_surface(True)
        self.ghosts = {p: self._make_ghost(p) for p in (1, 2)}
        set_alt_style(True)
        self.ghosts_alt = {p: self._make_ghost(p) for p in (1, 2)}
        set_alt_style(False)
        self.demo_board_surf = self._make_demo_board()
        self.demo_game = Game()
        self.demo_drop: Optional[List[Any]] = None   # [row, col, player, elapsed]
        self.demo_wait = 0.8
        self.col_hl = pygame.Surface((CELL, BOARD_H), pygame.SRCALPHA)
        pygame.draw.rect(self.col_hl, (255, 255, 255, 90), self.col_hl.get_rect(), border_radius=12)  # soft column highlight
        self.dim = pygame.Surface((BASE_W, BASE_H), pygame.SRCALPHA)
        self.dim.fill((232, 240, 252, 205))
        self.dim_light = pygame.Surface((BASE_W, BASE_H), pygame.SRCALPHA)
        self.dim_light.fill((232, 240, 252, 150))

        self.state = "menu"
        self.game = Game()
        self.mode = "local"
        self.my_player: Optional[int] = None
        self.names = ["Player 1", "Player 2"]
        self.net: Optional[Network] = None
        self.anim: Optional[FallingDisc] = None
        self.pending = False
        self.paused = False
        self.end_t = 0.0
        self.ai_timer = 0.0
        self.sel_col: Optional[int] = None
        self.my_name = "Player"
        self.result_hidden = False
        self._howto_cache: Optional[Tuple[int, List[Tuple[str, str]]]] = None
        self.rematch_me = False
        self.rematch_opp = False
        self.error: Optional[Tuple[str, str, str]] = None
        self.toast_msg: Optional[Tuple[str, float]] = None
        self.drag: Optional[str] = None
        self.lobby_mode = "join"
        self.local_ip = "127.0.0.1"
        self.port = DEFAULT_PORT
        self.target_ip = ""
        self.wait_status = ""
        self.opp_name: Optional[str] = None
        self.start_at: Optional[float] = None

        cx = BASE_W // 2
        self.in_name = TextInput((254, 312, 290, 46), "Player", MAX_NAME, placeholder="Player name")
        self.in_ip = TextInput((254, 422, 472, 46), "127.0.0.1", 45,
                               allowed="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:_",
                               placeholder="e.g. 192.168.1.20")
        self.in_port = TextInput((564, 312, 162, 46), str(DEFAULT_PORT), 5, allowed="0123456789")
        self.err_btn = Button((cx - 100, 430, 200, 50), "OK")
        self.game_btns = {
            "pause": Button((40, 330, 250, 46), "Pause Game", size=22),
            "again": Button((cx - 130, 400, 260, 46), "Rematch", C_GREEN, 22),
            "rmenu": Button((cx - 130, 454, 260, 46), "Quit to Menu", C_RED, 22),
            "view": Button((cx - 130, 508, 260, 46), "Inspect Board", C_ACCENT, 22),
            "showres": Button((40, 388, 250, 40), "Show Match Result", C_ACCENT, 18),
        }
        self.pause_btns = {
            "resume": Button((cx - 170, 292, 340, 54), "Keep Playing"),
            "restart": Button((cx - 170, 362, 340, 54), "New Round"),
            "pmenu": Button((cx - 170, 432, 340, 54), "Quit to Menu", C_RED),
        }
        self.buttons: Dict[str, Button] = {}
        self.go("menu")

    # ---- pre-rendered surfaces ------------------------------------------- #
    def _make_background(self, alt: bool = False) -> pygame.Surface:
        pal = _ALT_PAL if alt else _BASE_PAL
        top, bot = pal["C_BG_TOP"], pal["C_BG_BOT"]
        s = pygame.Surface((BASE_W, BASE_H)).convert()
        for y in range(BASE_H):
            pygame.draw.line(s, lerp_color(top, bot, y / BASE_H), (0, y), (BASE_W, y))
        if alt:   # faint notebook-style grid
            grid = pygame.Surface((BASE_W, BASE_H), pygame.SRCALPHA)
            for x in range(0, BASE_W, 48):
                pygame.draw.line(grid, (150, 130, 220, 30), (x, 0), (x, BASE_H))
            for y in range(0, BASE_H, 48):
                pygame.draw.line(grid, (150, 130, 220, 30), (0, y), (BASE_W, y))
            s.blit(grid, (0, 0))
        return s

    def _make_board_surface(self, alt: bool = False) -> pygame.Surface:
        s = pygame.Surface((BOARD_W, BOARD_H), pygame.SRCALPHA)
        if alt:   # lavender board with thick ink outline
            ink = _ALT_PAL["C_TEXT"]
            pygame.draw.rect(s, _ALT_PAL["C_BOARD"], (0, 0, BOARD_W, BOARD_H), border_radius=14)
            pygame.draw.rect(s, ink, (0, 0, BOARD_W, BOARD_H), width=4, border_radius=14)
            for r in range(ROWS):
                for c in range(COLS):
                    cx, cy = PAD + c * CELL + CELL // 2, PAD + r * CELL + CELL // 2
                    pygame.draw.circle(s, (0, 0, 0, 0), (cx, cy), HOLE_R)
                    pygame.draw.circle(s, ink + (255,), (cx, cy), HOLE_R + 1, 3)
            return s
        # soft board shadow
        pygame.draw.rect(s, (110, 140, 190, 110), (0, 6, BOARD_W, BOARD_H), border_radius=20)
        pygame.draw.rect(s, C_BOARD, (0, 0, BOARD_W, BOARD_H), border_radius=20)
        pygame.draw.rect(s, C_BOARD_L, (0, 0, BOARD_W, BOARD_H), width=2, border_radius=20)
        for r in range(ROWS):
            for c in range(COLS):
                cx, cy = PAD + c * CELL + CELL // 2, PAD + r * CELL + CELL // 2
                pygame.draw.circle(s, (0, 0, 0, 0), (cx, cy), HOLE_R)
                pygame.draw.circle(s, (96, 138, 204, 255), (cx, cy), HOLE_R + 1, 2)
        return s

    def _make_ghost(self, player: int) -> pygame.Surface:
        s = pygame.Surface((DISC_R * 2 + 4, DISC_R * 2 + 4), pygame.SRCALPHA)
        draw_disc(s, DISC_R + 2, DISC_R + 2, DISC_R, player)
        s.set_alpha(150)
        return s

    # ---- display ---------------------------------------------------------- #
    def apply_display(self) -> None:
        if self.settings.fullscreen:
            self.window = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
        else:
            self.window = pygame.display.set_mode(RESOLUTIONS[self.settings.res], pygame.RESIZABLE)
        self.scale_buf = None

    def compute_view(self) -> None:
        ww, wh = self.window.get_size()
        sc = min(ww / BASE_W, wh / BASE_H)
        vw, vh = max(1, int(BASE_W * sc)), max(1, int(BASE_H * sc))
        self.view = (sc, (ww - vw) // 2, (wh - vh) // 2)

    def to_virtual(self, pos: Tuple[int, int]) -> Tuple[float, float]:
        sc, ox, oy = self.view
        return (pos[0] - ox) / sc, (pos[1] - oy) / sc

    def present(self) -> None:
        sc, ox, oy = self.view
        self.window.fill((0, 0, 0))
        vw, vh = max(1, int(BASE_W * sc)), max(1, int(BASE_H * sc))
        if (vw, vh) == (BASE_W, BASE_H):
            self.window.blit(self.canvas, (ox, oy))
        else:
            try:
                if self.scale_buf is None or self.scale_buf.get_size() != (vw, vh):
                    self.scale_buf = pygame.Surface((vw, vh)).convert()
                pygame.transform.smoothscale(self.canvas, (vw, vh), self.scale_buf)
                self.window.blit(self.scale_buf, (ox, oy))
            except (ValueError, pygame.error):
                self.window.blit(pygame.transform.scale(self.canvas, (vw, vh)), (ox, oy))
        pygame.display.flip()

    # ---- state / navigation ---------------------------------------------- #
    def go(self, state: str) -> None:
        self.state = state
        if state == "lobby":
            pygame.key.set_repeat(400, 35)
        else:
            pygame.key.set_repeat()
        cx = BASE_W // 2
        if state != "game":
            self.paused = False
        if state == "menu":
            gx, gy, tw, th, gap = 600, 215, 268, 120, 14      # 2 x 2 game-mode tiles
            sw, sh = 174, 92                                    # row of 3 small buttons below
            sy = gy + 2 * th + 2 * gap
            self.buttons = {
                "play_online": Button((gx, gy, tw, th), "Play Online", C_ACCENT, 30),
                "join": Button((gx + tw + gap, gy, tw, th), "Join Game", C_ACCENT, 30),
                "local": Button((gx, gy + th + gap, tw, th), "Local 2 Players", C_GREEN, 30),
                "ai": Button((gx + tw + gap, gy + th + gap, tw, th), "Vs Computer", C_RED, 30),
                "settings": Button((gx, sy, sw, sh), "Settings", C_ACCENT, 22),
                "howto": Button((gx + sw + gap, sy, sw, sh), "How to Play", C_ACCENT, 22),
                "exit": Button((gx + 2 * (sw + gap), sy, sw, sh), "Exit", C_RED, 22),
            }
        elif state == "settings":
            self.buttons = {"back": Button((cx - 120, 630, 240, 50), "Return")}
        elif state == "howto":
            self.buttons = {"back": Button((cx - 120, 655, 240, 48), "Return")}
        elif state == "lobby":
            self.local_ip = get_local_ip()
            self.buttons = {
                "tab_host": Button((230, 118, 400, 96), "Create Room", size=30),
                "tab_join": Button((650, 118, 400, 96), "Join Room", size=30),
                "go": Button((500, 555, 550, 60), "Open Room" if self.lobby_mode == "host" else "Enter Room", C_GREEN, 28),
                "back": Button((230, 555, 250, 60), "Return", size=24),
            }
            self.in_name.active = True
            self.in_ip.active = self.in_port.active = False
        elif state == "waiting":
            self.buttons = {"cancel": Button((cx - 100, 600, 200, 50), "Cancel", C_RED)}

    def send_net(self, msg: Dict[str, Any]) -> bool:
        """Send a message to the opponent; safely does nothing when there is no connection."""
        net = self.net
        return net.send(msg) if net is not None else False

    def close_net(self, say_bye: bool = True) -> None:
        if self.net is not None:
            if say_bye:
                self.send_net({"type": "bye"})
            self.net.close()
            self.net = None

    def leave_to_menu(self) -> None:
        self.close_net()
        self.go("menu")

    def show_error(self, title: str, msg: str, next_state: str) -> None:
        self.error = (title, msg, next_state)
        self.audio.play("error")

    def toast(self, text: str) -> None:
        self.toast_msg = (text, self.t + 2.4)

    # ---- game setup ------------------------------------------------------- #
    def reset_visuals(self) -> None:
        self.anim = None
        self.fx.clear()
        self.pending = False
        self.paused = False
        self.rematch_me = self.rematch_opp = False
        self.ai_timer = 0.0
        self.end_t = 1e18
        self.sel_col = None
        self.result_hidden = False

    def begin_game(self) -> None:
        self.game.reset()
        self.reset_visuals()
        self.go("game")

    def start_local(self) -> None:
        self.mode, self.my_player = "local", None
        self.names = ["Player 1", "Player 2"]
        self.begin_game()

    def start_ai(self) -> None:
        self.mode, self.my_player = "ai", 1
        self.names = ["You", "Computer"]
        self.begin_game()

    def restart_match(self) -> None:
        self.game.reset()
        self.reset_visuals()

    # ---- lobby ------------------------------------------------------------ #
    def lobby_submit(self) -> None:
        name = self.in_name.text.strip()[:MAX_NAME] or "Player"
        try:
            port = int(self.in_port.text)
            if not 1 <= port <= 65535:
                raise ValueError
        except ValueError:
            self.show_error("Invalid port", "The port must be a number between 1 and 65535 (default 5555).", "lobby")
            return
        self.port = port
        self.my_name = name
        if self.lobby_mode == "host":
            self.mode, self.my_player = "host", 1
            self.names = [name, "Opponent"]
            self.net = Network()
            self.net.start_host(port)
            self.opp_name = None
            self.start_at = None
            self.wait_status = "Opening the room ..."
            self.go("waiting")
        else:
            ip = self.in_ip.text.strip()
            if not ip or " " in ip or len(ip) > 253:
                self.show_error("Invalid address", "Enter the host's IP address, for example 192.168.1.20.", "lobby")
                return
            self.target_ip = ip
            self.mode, self.my_player = "client", 2
            self.names = ["Host", name]
            self.net = Network()
            self.net.start_connect(ip, port)
            self.wait_status = f"Connecting to {ip}:{port} ..."
            self.go("waiting")

    # ---- moves ------------------------------------------------------------ #
    def human_can_move(self) -> bool:
        g = self.game
        if self.paused or g.over or self.anim is not None or self.pending or self.state != "game":
            return False
        if self.mode == "local":
            return True
        if self.mode == "ai":
            return g.current == 1
        return g.current == self.my_player and self.net is not None and self.net.connected

    def human_move(self, col: int) -> None:
        if not self.human_can_move():
            return
        if not column_available(self.game.board, col):
            self.audio.play("error")
            self.toast("No space left in that column")
            return
        if self.mode == "client":
            self.pending = True
            if not self.send_net({"type": "move", "col": col}):
                self.pending = False
        else:
            if self.apply_move(self.game.current, col) is None and self.mode == "host":
                self.broadcast_state()

    def apply_move(self, player: int, col: Any) -> Optional[str]:
        err = self.game.validate(player, col)
        if err:
            return err
        row = self.game.drop(player, col)
        self.start_anim(row, col, player)
        return None

    def start_anim(self, row: int, col: int, player: int) -> None:
        if self.anim is not None:
            self.anim = None
        a = self.settings.anim
        if a < 0.05:
            self.audio.play("drop")
            self.on_landed()
            return
        self.anim = FallingDisc(row, col, player, 2600 + 1400 * a, a > 0.4)

    def on_landed(self) -> None:
        self.anim = None
        g = self.game
        if g.over:
            self.end_t = self.t
            if g.draw:
                self.audio.play("lose")
            else:
                mine = self.my_player is None or self.my_player == g.winner or (self.mode == "ai" and g.winner == 1)
                self.audio.play("win" if mine else "lose")
                if self.settings.anim >= 0.05:
                    for r, c in g.win_cells:
                        x, y = cell_center(r, c)
                        self.burst(x, y, PLAYER_COLORS[g.winner][0], 10)
                        self.burst(x, y, C_GOLD, 4)

    def burst(self, x: float, y: float, color, n: int) -> None:
        n = int(n * self.settings.anim)
        for _ in range(n):
            if len(self.fx) > 240:
                break
            ang = random.uniform(0, math.tau)
            sp = random.uniform(80, 260)
            life = random.uniform(0.4, 0.9)
            self.fx.append([x, y, math.cos(ang) * sp, math.sin(ang) * sp - 60, life, life, color, random.randint(2, 5)])

    def result_visible(self) -> bool:
        return self.game.over and self.anim is None and self.t - self.end_t > RESULT_DELAY

    # ---- online messages --------------------------------------------------- #
    def broadcast_state(self, restart: bool = False) -> None:
        if self.net:
            self.send_net({"type": "state", "state": self.game.to_dict(), "restart": restart})

    def apply_state(self, st: Dict[str, Any], restart: bool) -> None:
        new = Game()
        try:
            new.load(st)
        except (KeyError, TypeError, ValueError):
            self.toast("Received an invalid game state")
            return
        old_moves = self.game.moves
        self.game = new
        self.pending = False
        if restart or new.moves == 0:
            self.reset_visuals()
            return
        if new.moves > old_moves and new.last:
            row, col = new.last
            self.start_anim(row, col, new.board[row][col])

    def try_rematch(self) -> None:
        if self.mode == "host" and self.rematch_me and self.rematch_opp:
            self.restart_match()
            self.broadcast_state(restart=True)

    def host_start_match(self) -> None:
        if not (self.net and self.net.connected and self.opp_name):
            return
        self.names = [self.my_name, self.opp_name]
        self.game.reset()
        self.reset_visuals()
        self.send_net({"type": "start", "names": self.names, "state": self.game.to_dict()})
        self.go("game")

    def process_network(self) -> None:
        while self.net is not None:
            try:
                ev = self.net.events.get_nowait()
            except queue.Empty:
                return
            kind = ev[0]
            if kind == "error":
                self.close_net(False)
                self.show_error("Network error", ev[1], "lobby")
            elif kind == "listening":
                self.wait_status = f"Listening on port {ev[1]}"
            elif kind == "accepted":
                self.wait_status = f"{ev[1]} is trying to connect ..."
            elif kind == "connected":
                self.send_net({"type": "hello", "name": self.my_name, "version": PROTOCOL_VERSION})
                self.wait_status = "Connected. Waiting for the host ..."
            elif kind == "disconnected":
                self.on_disconnect(ev[1])
            elif kind == "msg":
                self.on_message(ev[1])

    def on_disconnect(self, reason: str) -> None:
        if self.state == "waiting" and self.mode == "host":
            self.opp_name = None
            self.start_at = None
            self.wait_status = "Opponent left. Waiting for a new opponent ..."
            return
        self.close_net(False)
        self.show_error("Disconnected", reason, "menu" if self.state == "game" else "lobby")

    def on_message(self, msg: Dict[str, Any]) -> None:
        mtype = msg.get("type")
        if mtype == "bye":
            self.on_disconnect("Your opponent left the game.")
            return
        if self.mode == "host":
            self.host_message(mtype, msg)
        elif self.mode == "client":
            self.client_message(mtype, msg)

    def host_message(self, mtype: Any, msg: Dict[str, Any]) -> None:
        if mtype == "hello":
            if msg.get("version") != PROTOCOL_VERSION:
                self.send_net({"type": "error", "message": "Version mismatch."})
                return
            self.opp_name = str(msg.get("name", "Opponent"))[:MAX_NAME] or "Opponent"
            self.send_net({"type": "welcome", "name": self.my_name, "player": 2})
            self.wait_status = "Opponent joined!"
        elif mtype == "ready":
            if self.state == "waiting" and self.opp_name:
                self.start_at = self.t + START_DELAY
                self.wait_status = "Both players are ready - starting ..."
        elif mtype == "move":
            if self.state != "game":
                self.send_net({"type": "error", "message": "The game hasn't started yet."})
                return
            if self.anim is not None:  # let the previous disc land; client retries are not needed because of turn order
                pass
            err = self.apply_move(2, msg.get("col"))
            if err:
                self.send_net({"type": "error", "message": err})
            else:
                self.broadcast_state()
        elif mtype == "rematch":
            self.rematch_opp = True
            self.try_rematch()

    def client_message(self, mtype: Any, msg: Dict[str, Any]) -> None:
        if mtype == "welcome":
            self.names[0] = str(msg.get("name", "Host"))[:MAX_NAME] or "Host"
            self.wait_status = f"Connected to {self.names[0]}. Waiting for the game to start ..."
            self.send_net({"type": "ready"})
        elif mtype == "start":
            try:
                self.names = [str(n)[:MAX_NAME] for n in msg["names"]][:2]
                self.game.load(msg["state"])
            except (KeyError, TypeError, ValueError):
                self.close_net()
                self.show_error("Protocol error", "The host sent invalid data.", "lobby")
                return
            self.reset_visuals()
            self.go("game")
        elif mtype == "state" and self.state == "game":
            self.apply_state(msg.get("state", {}), bool(msg.get("restart")))
        elif mtype == "error":
            self.pending = False
            self.audio.play("error")
            self.toast(str(msg.get("message", "Move rejected"))[:60])
        elif mtype == "reject":
            self.close_net(False)
            self.show_error("Connection refused", str(msg.get("message", "The host did not accept the connection.")), "lobby")
        elif mtype == "rematch":
            self.rematch_opp = True

    # ---- events ----------------------------------------------------------- #
    def active_buttons(self) -> Dict[str, Button]:
        if self.error:
            return {"ok": self.err_btn}
        if self.state == "game":
            if self.paused:
                return self.pause_btns
            if self.result_visible():
                if not self.result_hidden:
                    return {"again": self.game_btns["again"], "rmenu": self.game_btns["rmenu"],
                            "view": self.game_btns["view"]}
                return {"pause": self.game_btns["pause"], "showres": self.game_btns["showres"]}
            return {"pause": self.game_btns["pause"]}
        return self.buttons

    def button_hit(self, e: pygame.event.Event, pos: Optional[Tuple[float, float]]) -> Optional[str]:
        if pos is not None and e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
            for key, b in self.active_buttons().items():
                if b.hit(pos):
                    self.audio.play("click")
                    return key
        return None

    def handle_event(self, e: pygame.event.Event) -> None:
        if e.type == pygame.QUIT:
            self.running = False
            return
        if e.type == pygame.KEYDOWN and e.key == pygame.K_F11:
            self.settings.fullscreen = not self.settings.fullscreen
            self.apply_display()
            return
        pos = None
        if e.type in (pygame.MOUSEMOTION, pygame.MOUSEBUTTONDOWN, pygame.MOUSEBUTTONUP):
            pos = self.to_virtual(e.pos)
        key = self.button_hit(e, pos)
        if self.error:
            if key == "ok" or (e.type == pygame.KEYDOWN and e.key in (pygame.K_RETURN, pygame.K_ESCAPE, pygame.K_SPACE)):
                self.on_button("ok")
            return
        if key:
            self.on_button(key)
            return
        if self.state == "settings":
            self.ev_settings(e, pos)
        elif self.state == "lobby":
            self.ev_lobby(e, pos)
        elif self.state == "game":
            self.ev_game(e, pos)
        elif e.type == pygame.KEYDOWN and e.key == pygame.K_ESCAPE:
            if self.state == "waiting":
                self.on_button("cancel")
            elif self.state in ("howto",):
                self.go("menu")

    def ev_lobby(self, e: pygame.event.Event, pos) -> None:
        inputs = [self.in_name, self.in_port] + ([self.in_ip] if self.lobby_mode == "join" else [])
        if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and pos:
            for i in inputs:
                i.active = i.rect.collidepoint(pos)
        elif e.type == pygame.KEYDOWN:
            if e.key == pygame.K_ESCAPE:
                self.go("menu")
            elif e.key == pygame.K_TAB:
                idx = next((n for n, i in enumerate(inputs) if i.active), -1)
                for i in inputs:
                    i.active = False
                inputs[(idx + 1) % len(inputs)].active = True
            elif e.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                self.lobby_submit()
            else:
                for i in inputs:
                    i.handle_key(e)

    def column_at(self, pos) -> Optional[int]:
        x, y = pos
        if y < 60 or y > BOARD_Y + BOARD_H:
            return None
        cx = x - (BOARD_X + PAD)
        if 0 <= cx < COLS * CELL:
            return int(cx // CELL)
        return None

    def ev_game(self, e: pygame.event.Event, pos) -> None:
        if e.type == pygame.KEYDOWN:
            if e.key == pygame.K_ESCAPE:
                if self.result_visible() and not self.result_hidden:
                    self.result_hidden = True
                else:
                    self.toggle_pause()
            elif self.paused:
                return
            elif pygame.K_1 <= e.key <= pygame.K_7:
                self.human_move(e.key - pygame.K_1)
            elif e.key == pygame.K_LEFT:
                self.sel_col = max(0, (3 if self.sel_col is None else self.sel_col) - 1)
            elif e.key == pygame.K_RIGHT:
                self.sel_col = min(COLS - 1, (3 if self.sel_col is None else self.sel_col) + 1)
            elif e.key in (pygame.K_RETURN, pygame.K_SPACE, pygame.K_DOWN) and self.sel_col is not None:
                self.human_move(self.sel_col)
        elif e.type == pygame.MOUSEMOTION and not self.paused:
            self.sel_col = self.column_at(pos)
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and not self.paused:
            col = self.column_at(pos)
            if col is not None:
                self.human_move(col)

    def toggle_pause(self) -> None:
        self.paused = not self.paused
        if self.paused:
            offline = self.mode in ("local", "ai")
            b = self.pause_btns["restart"]
            b.enabled = offline
            b.text = "New Round" if offline else "New Round (offline only)"

    def fader_cx(self, i: int) -> int:
        return SOUND_PANEL.x + int(SOUND_PANEL.w * (2 * i + 1) / 6)

    def fader_rect(self, i: int) -> pygame.Rect:
        return pygame.Rect(self.fader_cx(i) - 34, FADER_TOP - 24, 68, FADER_BOT - FADER_TOP + 48)

    def anim_hit_rect(self) -> pygame.Rect:
        r = SETTING_TILES["anim"]
        return pygame.Rect(ANIM_X0 - 20, r.y + 60, ANIM_W + 40, 60)

    def choice_btns(self, key: str) -> Tuple[pygame.Rect, pygame.Rect]:
        r = SETTING_TILES[key]
        return pygame.Rect(r.x + 16, r.y + 82, 44, 44), pygame.Rect(r.right - 60, r.y + 82, 44, 44)

    def toggle_geo(self, key: str) -> pygame.Rect:
        r = SETTING_TILES[key]
        return pygame.Rect(r.centerx - 55, r.y + 70, 110, 40)

    def set_slider_at(self, key: str, pos) -> None:
        if key == "anim":
            v = (pos[0] - ANIM_X0) / ANIM_W
        else:
            v = (FADER_BOT - pos[1]) / (FADER_BOT - FADER_TOP)
        setattr(self.settings, key, round(clamp(v, 0.0, 1.0), 3))
        self.audio.apply_volumes()

    def ev_settings(self, e: pygame.event.Event, pos) -> None:
        s = self.settings
        if e.type == pygame.KEYDOWN and e.key == pygame.K_ESCAPE:
            self.go("menu")
        elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1 and pos:
            for i, (_, key) in enumerate(FADERS):
                if self.fader_rect(i).collidepoint(pos):
                    self.drag = key
                    self.set_slider_at(key, pos)
                    return
            if self.anim_hit_rect().collidepoint(pos):
                self.drag = "anim"
                self.set_slider_at("anim", pos)
                return
            for key in ("res", "fps"):
                left, right = self.choice_btns(key)
                for d, rect in ((-1, left), (1, right)):
                    if rect.collidepoint(pos):
                        self.audio.play("click")
                        if key == "res":
                            s.res = (s.res + d) % len(RESOLUTIONS)
                            if not s.fullscreen:
                                self.apply_display()
                        else:
                            idx = FPS_OPTIONS.index(s.fps) if s.fps in FPS_OPTIONS else 1
                            s.fps = FPS_OPTIONS[(idx + d) % len(FPS_OPTIONS)]
            for key in ("fullscreen", "particles"):
                if SETTING_TILES[key].collidepoint(pos):    # the whole tile is a switch
                    self.audio.play("click")
                    setattr(s, key, not getattr(s, key))
                    if key == "fullscreen":
                        self.apply_display()
        elif e.type == pygame.MOUSEMOTION and self.drag and pos:
            self.set_slider_at(self.drag, pos)
        elif e.type == pygame.MOUSEBUTTONUP:
            self.drag = None

    def on_button(self, key: str) -> None:
        if key == "ok":
            nxt = self.error[2] if self.error else "menu"
            self.error = None
            self.go(nxt)
        elif key == "play_online":
            self.go("lobby")
        elif key == "host":
            self.lobby_mode = "host"
            self.go("lobby")
        elif key == "join":
            self.lobby_mode = "join"
            self.go("lobby")
        elif key == "local":
            self.start_local()
        elif key == "ai":
            self.start_ai()
        elif key == "settings":
            self.go("settings")
        elif key == "howto":
            self.go("howto")
        elif key == "exit":
            self.running = False
        elif key == "back":
            self.go("menu")
        elif key in ("tab_host", "tab_join"):
            self.lobby_mode = "host" if key == "tab_host" else "join"
            self.go("lobby")
        elif key == "go":
            self.lobby_submit()
        elif key == "cancel":
            self.close_net()
            self.go("lobby")
        elif key == "pause":
            self.toggle_pause()
        elif key == "resume":
            self.paused = False
        elif key == "restart":
            if self.mode in ("local", "ai"):
                self.restart_match()
        elif key == "view":
            self.result_hidden = True
        elif key == "showres":
            self.result_hidden = False
        elif key in ("pmenu", "rmenu"):
            self.leave_to_menu()
        elif key == "again":
            if self.mode in ("local", "ai"):
                self.restart_match()
            elif not self.rematch_me:
                self.rematch_me = True
                if self.net:
                    self.send_net({"type": "rematch"})
                self.try_rematch()

    # ---- update ------------------------------------------------------------ #
    def update(self, dt: float) -> None:
        self.t += dt
        for b in self.active_buttons().values():
            b.update(self.mouse, dt)
        if self.settings.particles:
            for p in self.bg_particles:
                p[1] -= p[3] * dt
                if p[1] < -10:
                    p[0], p[1] = random.uniform(0, BASE_W), BASE_H + 10
        if self.fx:
            for p in self.fx:
                p[0] += p[2] * dt
                p[1] += p[3] * dt
                p[3] += 520 * dt
                p[4] -= dt
            self.fx = [p for p in self.fx if p[4] > 0]
        if self.state == "waiting" and self.start_at is not None and self.t >= self.start_at:
            self.start_at = None
            self.host_start_match()
        if self.state == "game":
            self.update_game(dt)
        elif self.state == "menu":
            self.update_demo(dt)

    def update_game(self, dt: float) -> None:
        a = self.anim
        if a is not None:
            a.update(dt)
            if a.hit and not a.hit_handled:
                a.hit_handled = True
                self.audio.play("drop")
                self.burst(a.x, a.target + 20, PLAYER_COLORS[a.player][0], 8)
            if a.done:
                self.on_landed()
        if self.mode == "ai" and not self.paused and not self.game.over and self.game.current == 2 and self.anim is None:
            self.ai_timer += dt
            if self.ai_timer > AI_THINK_TIME:
                self.ai_timer = 0.0
                col = ai_choose_move(self.game.board, 2)
                if col >= 0:
                    self.apply_move(2, col)
        else:
            self.ai_timer = 0.0

    # ---- drawing ------------------------------------------------------------ #
    def draw_background(self) -> None:
        s = self.canvas
        s.blit(self.bg_alt if _ALT else self.bg, (0, 0))
        if self.settings.particles:
            for x, y, r, _, ph, col in self.bg_particles:
                px = x + math.sin(self.t * 0.5 + ph) * 22
                bgc = lerp_color(C_BG_TOP, C_BG_BOT, y / BASE_H)
                pygame.draw.circle(s, lerp_color(bgc, col, 0.45), (int(px), int(y)), int(r))

    def draw(self) -> None:
        set_alt_style(self.state != "menu")
        self.draw_background()
        fn = {"menu": self.draw_menu, "settings": self.draw_settings, "howto": self.draw_howto,
              "lobby": self.draw_lobby, "waiting": self.draw_waiting, "game": self.draw_game}[self.state]
        fn()
        if self.error:
            self.draw_error()
        if self.toast_msg:
            text, until = self.toast_msg
            if self.t < until:
                img = render_text(text, 22, C_TEXT, True)
                r = img.get_rect(center=(BASE_W // 2, 700)).inflate(40, 16)
                pygame.draw.rect(self.canvas, C_PANEL, r, border_radius=14)
                pygame.draw.rect(self.canvas, C_ACCENT, r, width=2, border_radius=14)
                self.canvas.blit(img, img.get_rect(center=r.center))
            else:
                self.toast_msg = None

    def draw_buttons(self) -> None:
        for b in self.active_buttons().values():
            b.draw(self.canvas)

    def _make_demo_board(self) -> pygame.Surface:
        s = pygame.Surface((DEMO_W, DEMO_H), pygame.SRCALPHA)
        pygame.draw.rect(s, C_BOARD, (0, 0, DEMO_W, DEMO_H), border_radius=18)
        pygame.draw.rect(s, C_BOARD_L, (0, 0, DEMO_W, DEMO_H), width=3, border_radius=18)
        for r in range(ROWS):
            for c in range(COLS):
                cx, cy = DEMO_PAD + c * DEMO_CELL + DEMO_CELL // 2, DEMO_PAD + r * DEMO_CELL + DEMO_CELL // 2
                pygame.draw.circle(s, (0, 0, 0, 0), (cx, cy), DEMO_R + 2)
                pygame.draw.circle(s, (96, 138, 204, 255), (cx, cy), DEMO_R + 3, 2)
        return s

    def demo_center(self, row: int, col: int) -> Tuple[int, int]:
        return (DEMO_X + DEMO_PAD + col * DEMO_CELL + DEMO_CELL // 2,
                DEMO_Y + DEMO_PAD + row * DEMO_CELL + DEMO_CELL // 2)

    def update_demo(self, dt: float) -> None:
        """The computer plays against itself on the menu board, forever."""
        if self.demo_drop is not None:
            self.demo_drop[3] += dt
            if self.demo_drop[3] >= DEMO_DROP_T:
                self.demo_drop = None
            return
        self.demo_wait -= dt
        if self.demo_wait > 0:
            return
        g = self.demo_game
        if g.over:
            self.demo_game = Game()
            self.demo_wait = 0.6
            return
        if g.moves == 0:
            col = random.randrange(COLS)
        else:
            col = ai_choose_move(g.board, g.current)
        if col < 0:
            self.demo_game = Game()
            return
        player = g.current
        row = g.drop(player, col)
        self.demo_drop = [row, col, player, 0.0]
        self.demo_wait = 2.6 if g.over else 0.45

    def draw_demo(self) -> None:
        s, g, dr = self.canvas, self.demo_game, self.demo_drop
        pygame.draw.rect(s, C_SHADOW, (DEMO_X, DEMO_Y + 8, DEMO_W, DEMO_H), border_radius=18)
        pygame.draw.rect(s, C_HOLE_BACK, (DEMO_X, DEMO_Y, DEMO_W, DEMO_H), border_radius=18)
        for r in range(ROWS):
            for c in range(COLS):
                p = g.board[r][c]
                if p and not (dr and dr[0] == r and dr[1] == c):
                    x, y = self.demo_center(r, c)
                    draw_disc(s, x, y, DEMO_R, p)
        if dr:
            row, col, player, t = dr
            x, ty = self.demo_center(row, col)
            y0 = DEMO_Y - 24
            f = min(1.0, t / DEMO_DROP_T)
            draw_disc(s, x, int(y0 + (ty - y0) * f * f), DEMO_R, player)
        s.blit(self.demo_board_surf, (DEMO_X, DEMO_Y))
        if g.winner and dr is None:
            pulse = 0.5 + 0.5 * math.sin(self.t * 8)
            for r, c in g.win_cells:
                x, y = self.demo_center(r, c)
                pygame.draw.circle(s, lerp_color(C_GOLD, C_WHITE, pulse), (x, y), DEMO_R + 5, 4)

    def draw_menu(self) -> None:
        s = self.canvas
        draw_text(s, "CONNECT 4 ONLINE", 80, (170, 200, 238), (BASE_W // 2 + 4, 98), bold=True)
        draw_text(s, "CONNECT 4 ONLINE", 80, C_ACCENT, (BASE_W // 2, 94), bold=True)
        draw_text(s, "Drop. Connect. Win.", 26, C_MUTED, (BASE_W // 2, 152), bold=True)
        self.draw_demo()
        self.draw_buttons()
        draw_text(s, "Python + Pygame", 16, C_MUTED, (BASE_W - 16, BASE_H - 12), anchor="bottomright")

    def draw_settings(self) -> None:
        s, st = self.canvas, self.settings
        draw_title(s, "Control Panel", 54, (BASE_W // 2, 62))

        # --- left: sound mixer with vertical faders ---
        draw_panel(s, SOUND_PANEL)
        draw_text(s, "SOUND MIXER", 20, C_MUTED, (SOUND_PANEL.centerx, SOUND_PANEL.y + 30), bold=True)
        span = FADER_BOT - FADER_TOP
        for i, (label, key) in enumerate(FADERS):
            cx, v = self.fader_cx(i), getattr(st, key)
            track = pygame.Rect(cx - 6, FADER_TOP, 12, span)
            pygame.draw.rect(s, C_TRACK, track, border_radius=6)
            fh = int(span * v)
            if fh > 0:
                pygame.draw.rect(s, C_ACCENT, (cx - 6, FADER_BOT - fh, 12, fh), border_radius=6)
            pygame.draw.rect(s, C_TEXT, track, width=2, border_radius=6)
            for k in range(5):
                ty = FADER_TOP + span * k // 4
                pygame.draw.line(s, C_MUTED, (cx + 18, ty), (cx + 30, ty), 2)
            knob = pygame.Rect(cx - 20, FADER_BOT - fh - 12, 40, 24)
            pygame.draw.rect(s, C_SHADOW, knob.move(3, 3), border_radius=8)
            pygame.draw.rect(s, C_WHITE, knob, border_radius=8)
            pygame.draw.rect(s, C_TEXT, knob, width=3, border_radius=8)
            draw_text(s, f"{int(v * 100)}%", 24, C_ACCENT, (cx, FADER_TOP - 34), bold=True)
            draw_text(s, label, 22, C_TEXT, (cx, FADER_BOT + 34), bold=True, max_w=130)

        # --- right: tile grid ---
        for key, rect in SETTING_TILES.items():
            draw_panel(s, rect, fill=TILE_TINTS[key])
            draw_text(s, TILE_NAMES[key], 22, C_TEXT, (rect.x + 20, rect.y + 26), anchor="midleft", bold=True,
                      max_w=rect.w - 40)
        for key in ("res", "fps"):
            rect = SETTING_TILES[key]
            txt = f"{RESOLUTIONS[st.res][0]} x {RESOLUTIONS[st.res][1]}" if key == "res" else f"{st.fps} FPS"
            for r_, sym in zip(self.choice_btns(key), ("<", ">")):
                hov = r_.collidepoint(self.mouse)
                pygame.draw.rect(s, C_SHADOW, r_.move(3, 3), border_radius=10)
                pygame.draw.rect(s, C_PANEL2_H if hov else C_WHITE, r_, border_radius=10)
                pygame.draw.rect(s, C_TEXT, r_, width=3, border_radius=10)
                draw_text(s, sym, 26, C_TEXT, r_.center, bold=True)
            draw_text(s, txt, 26, C_TEXT, (rect.centerx, rect.y + 104), bold=True, max_w=rect.w - 128)
        for key in ("fullscreen", "particles"):
            rect, on, geo = SETTING_TILES[key], getattr(st, key), self.toggle_geo(key)
            pygame.draw.rect(s, C_GREEN if on else C_TOGGLE_OFF, geo, border_radius=20)
            pygame.draw.rect(s, C_TEXT, geo, width=3, border_radius=20)
            kx = geo.right - 20 if on else geo.x + 20
            pygame.draw.circle(s, C_WHITE, (kx, geo.centery), 14)
            pygame.draw.circle(s, C_TEXT, (kx, geo.centery), 14, 3)
            draw_text(s, "ENABLED" if on else "DISABLED", 20, C_TEXT, (rect.centerx, rect.y + 126), bold=True)
        # motion slider (horizontal) in the wide tile
        rect, v = SETTING_TILES["anim"], st.anim
        track = pygame.Rect(ANIM_X0, rect.y + 80, ANIM_W, 12)
        pygame.draw.rect(s, C_TRACK, track, border_radius=6)
        if v > 0:
            pygame.draw.rect(s, C_ACCENT, (ANIM_X0, track.y, int(ANIM_W * v), 12), border_radius=6)
        pygame.draw.rect(s, C_TEXT, track, width=2, border_radius=6)
        kx = ANIM_X0 + int(ANIM_W * v)
        pygame.draw.circle(s, C_WHITE, (kx, track.centery), 14)
        pygame.draw.circle(s, C_TEXT, (kx, track.centery), 14, 3)
        draw_text(s, f"{int(v * 100)}%", 28, C_ACCENT, (ANIM_X0 + ANIM_W + 30, track.centery), anchor="midleft", bold=True)
        draw_text(s, "Still", 18, C_MUTED, (ANIM_X0, track.bottom + 26), anchor="midleft")
        draw_text(s, "Lively", 18, C_MUTED, (ANIM_X0 + ANIM_W, track.bottom + 26), anchor="midright")

        if st.fullscreen:
            draw_text(s, "Window size can only be changed in windowed mode.", 16, C_MUTED, (BASE_W // 2, 610), max_w=760)
        elif not self.audio.enabled:
            draw_text(s, "No audio device was found.", 16, C_MUTED, (BASE_W // 2, 610), max_w=760)
        self.draw_buttons()

    def howto_layout(self) -> Tuple[int, List[Tuple[str, str]]]:
        """Wraps the help text once and picks the largest font size that fits inside the panel."""
        if self._howto_cache is None:
            size, rows = 19, []
            for size in (19, 18, 17, 16, 15, 14):
                rows, total = [], 0
                for kind, text in HOWTO:
                    if kind == "h":
                        rows.append(("h", text))
                        total += 6 + (size + 5) + 6
                    else:
                        for line in wrap_text(text, size, 980):
                            rows.append(("p", line))
                            total += size + 4
                if total <= 520:
                    break
            self._howto_cache = (size, rows)
        return self._howto_cache

    def draw_howto(self) -> None:
        s = self.canvas
        draw_title(s, "Game Guide", 50, (BASE_W // 2, 50))
        draw_panel(s, pygame.Rect(120, 90, 1040, 554))
        size, rows = self.howto_layout()
        y = 106
        for kind, text in rows:
            if kind == "h":
                y += 6
                draw_text(s, text, size + 5, C_ACCENT, (150, y), anchor="topleft", bold=True, max_w=980)
                y += size + 5 + 6
            else:
                draw_text(s, text, size, C_TEXT, (150, y), anchor="topleft")
                y += size + 4
        self.draw_buttons()

    def draw_lobby(self) -> None:
        s = self.canvas
        host = self.lobby_mode == "host"
        draw_title(s, "Multiplayer Lobby", 50, (BASE_W // 2, 62))
        cards = (("tab_host", "host", "You host - your friend joins you"),
                 ("tab_join", "join", "Enter a host's address to hop in"))
        for k, mode, _ in cards:
            b = self.buttons[k]
            b.accent = C_ACCENT if self.lobby_mode == mode else C_BOARD_L
            b.size, b.dy = 30, -12
        # body: details form on the left, tips on the right
        left, right = pygame.Rect(230, 240, 520, 280), pygame.Rect(770, 240, 280, 280)
        draw_panel(s, left)
        draw_panel(s, right, fill=(236, 228, 254))
        draw_text(s, "YOUR DETAILS", 18, C_MUTED, (left.x + 24, left.y + 24), anchor="midleft", bold=True)
        draw_text(s, "GOOD TO KNOW", 18, C_MUTED, (right.x + 22, right.y + 24), anchor="midleft", bold=True)
        self.in_name.draw(s, "Player name", self.t)
        self.in_port.draw(s, "Port number", self.t)
        if host:
            r = self.in_ip.rect
            draw_text(s, "Your address on this network", 20, C_MUTED, (r.x, r.y - 6), anchor="bottomleft", max_w=r.w)
            draw_text(s, self.local_ip, 34, C_ACCENT, (r.centerx, r.centery), bold=True, max_w=r.w)
        else:
            self.in_ip.draw(s, "Room address (host IP)", self.t)
        tips = ["Send your address and port number to the player joining you." if host
                else "Get the address and port from the host - they're shown in the room lobby.",
                "Playing across the internet needs port forwarding (see Game Guide)."]
        y = right.y + 56
        for tip in tips:
            for line in wrap_text(tip, 16, right.w - 44):
                draw_text(s, line, 16, C_TEXT, (right.x + 22, y), anchor="topleft")
                y += 21
            y += 12
        self.draw_buttons()
        # captions and the "selected" badge go on top of the mode cards
        for k, mode, caption in cards:
            b = self.buttons[k]
            draw_text(s, caption, 17, C_MUTED, (b.rect.centerx, b.rect.centery + 22 + int(3 * b.hover)),
                      max_w=b.rect.w - 30)
            if self.lobby_mode == mode:
                pill = pygame.Rect(b.rect.x + 12, b.rect.y + 12, 82, 22)
                pygame.draw.rect(s, C_ACCENT, pill, border_radius=11)
                draw_text(s, "SELECTED", 12, C_WHITE, pill.center, bold=True)

    def draw_spinner(self, cx: int, cy: int) -> None:
        for i in range(8):
            a = self.t * 3 - i * math.pi / 4
            col = lerp_color(C_BG_BOT, C_ACCENT if i % 2 == 0 else C_RED, 1 - i / 9)
            pygame.draw.circle(self.canvas, col, (int(cx + math.cos(a) * 24), int(cy + math.sin(a) * 24)), 7 - i // 2)

    def draw_waiting(self) -> None:
        s = self.canvas
        host = self.mode == "host"
        draw_title(s, "Room Lobby" if host else "Entering Room", 52, (BASE_W // 2, 62))
        draw_panel(s, pygame.Rect(290, 110, 700, 470))
        if host:
            draw_text(s, "Give this address to your opponent", 24, C_MUTED, (BASE_W // 2, 160), max_w=640)
            draw_text(s, f"{self.local_ip}:{self.port}", 58, C_ACCENT, (BASE_W // 2, 222), bold=True, max_w=640)
            note = ("Same network: use the address above. Over the internet: the host's router must forward this TCP "
                    "port, and the guest must know the host's public IP address.")
            for i, line in enumerate(wrap_text(note, 18, 620)[:3]):
                draw_text(s, line, 18, C_MUTED, (BASE_W // 2, 276 + i * 22), max_w=640)
            draw_text(s, self.wait_status, 24, C_TEXT, (BASE_W // 2, 360), max_w=640)
            if self.opp_name:
                draw_text(s, f"{self.opp_name} has joined the room!", 30, C_GREEN, (BASE_W // 2, 410), bold=True, max_w=640)
            else:
                draw_text(s, "Nobody has joined yet ...", 26, C_MUTED, (BASE_W // 2, 410), max_w=640)
        else:
            draw_text(s, f"{self.target_ip}:{self.port}", 46, C_ACCENT, (BASE_W // 2, 200), bold=True, max_w=640)
            for i, line in enumerate(wrap_text(self.wait_status, 26, 620)[:4]):
                draw_text(s, line, 26, C_TEXT, (BASE_W // 2, 300 + i * 32), max_w=640)
        self.draw_spinner(BASE_W // 2, 500)
        self.draw_buttons()

    def status_text(self) -> Tuple[str, Tuple[int, int, int]]:
        g = self.game
        if g.over:
            if g.draw:
                return "Nobody wins - it's a tie!", C_TEXT
            col = PLAYER_COLORS[g.winner][1]
            if self.mode in ("host", "client") and g.winner == self.my_player:
                return "You won the round!", col
            if self.mode == "ai":
                return ("You won the round!" if g.winner == 1 else "The computer wins!"), col
            return f"Champion: {self.names[g.winner - 1]}", col
        col = PLAYER_COLORS[g.current][1]
        if self.mode == "local":
            return f"{self.names[g.current - 1]}'s move", col
        if self.mode == "ai":
            return ("Your move" if g.current == 1 else "Computer is planning ..."), col
        if g.current == self.my_player:
            return "Your move - choose a column", col
        return f"{self.names[g.current - 1]} is choosing ...", col

    def draw_player_card(self, p: int, rect: pygame.Rect) -> None:
        s, g = self.canvas, self.game
        active = (g.current == p and not g.over)
        border = C_BOARD_L
        if active:
            border = lerp_color(PLAYER_COLORS[p][0], PLAYER_COLORS[p][1], 0.5 + 0.5 * math.sin(self.t * 5))
        if g.winner == p:
            border = C_GOLD
        draw_panel(s, rect, border=border)
        pygame.draw.rect(s, border, rect, width=3 if (active or g.winner == p) else 2, border_radius=10 if _ALT else 14)
        draw_disc(s, rect.x + 46, rect.y + 58, 28, p)
        you = (self.my_player == p) or (self.mode == "ai" and p == 1)
        text_w = rect.w - 88 - 14
        draw_text(s, self.names[p - 1], 26, C_TEXT, (rect.x + 86, rect.y + 44), anchor="midleft", bold=True, max_w=text_w)
        draw_text(s, f"{PLAYER_NAMES[p]}{' - you' if you else ''}", 20, C_MUTED, (rect.x + 86, rect.y + 76),
                  anchor="midleft", max_w=text_w)
        if g.winner == p:
            draw_text(s, "CHAMPION", 24, C_ACCENT, (rect.centerx, rect.y + 122), bold=True, max_w=rect.w - 24)
        elif active:
            draw_text(s, "On the move", 20, PLAYER_COLORS[p][1], (rect.centerx, rect.y + 122), max_w=rect.w - 24)

    def draw_result_modal(self) -> None:
        s, g = self.canvas, self.game
        s.blit(self.dim_light, (0, 0))
        rect = pygame.Rect(BASE_W // 2 - 240, 150, 480, 420)
        draw_panel(s, rect, border=C_ACCENT)
        cx = rect.centerx
        inner = rect.w - 40
        draw_text(s, "MATCH OVER", 20, C_MUTED, (cx, rect.y + 32), max_w=inner)
        if g.draw:
            draw_text(s, "TIE GAME", 50, C_TEXT, (cx, rect.y + 96), bold=True, max_w=inner)
            draw_text(s, "Every slot is filled and nobody connected four.", 20, C_MUTED, (cx, rect.y + 170), max_w=inner)
        else:
            w = g.winner
            if self.mode == "local":
                head, hcol = f"{self.names[w - 1]} TAKES IT!", PLAYER_COLORS[w][1]
            else:
                me = self.my_player if self.my_player is not None else 1
                head, hcol = ("YOU WON!", C_GREEN) if w == me else ("YOU LOST", C_RED_D)
            draw_text(s, head, 50, hcol, (cx, rect.y + 96), bold=True, max_w=inner)
            draw_disc(s, cx, rect.y + 166, 24, w)
            draw_text(s, f"Champion: {self.names[w - 1]} ({PLAYER_NAMES[w]})", 22, C_TEXT, (cx, rect.y + 214), max_w=inner)
            draw_text(s, "Four in a row!", 18, C_MUTED, (cx, rect.y + 242), max_w=inner)
        again = self.game_btns["again"]
        if self.mode in ("host", "client"):
            if self.rematch_me:
                again.text, again.enabled = "Waiting for opponent ...", False
            elif self.rematch_opp:
                again.text, again.enabled = "Accept Rematch", True
            else:
                again.text, again.enabled = "Rematch", True
        else:
            again.text, again.enabled = "Rematch", True

    def draw_game(self) -> None:
        s, g = self.canvas, self.game
        text, col = self.status_text()
        draw_text(s, text, 36, col, (BASE_W // 2, 28), bold=True, max_w=640)
        label = {"local": "Same screen, 2 players", "ai": "You vs Computer",
                 "host": "Online - room host", "client": "Online - guest player"}[self.mode]
        draw_text(s, f"{label}   |   Discs played: {g.moves}", 20, C_MUTED, (BASE_W // 2, 60), max_w=640)
        if self.mode in ("host", "client"):
            ok = self.net is not None and self.net.connected
            pygame.draw.circle(s, C_GREEN if ok else C_RED, (1050, 30), 8)
            draw_text(s, "Link active" if ok else "Link lost", 20, C_TEXT, (1066, 30), anchor="midleft", max_w=170)
        self.draw_player_card(1, pygame.Rect(40, 150, 250, 160))
        self.draw_player_card(2, pygame.Rect(990, 150, 250, 160))
        # board
        rad, off = (14, 8) if _ALT else (20, 0)
        pygame.draw.rect(s, C_SHADOW, (BOARD_X + off, BOARD_Y + 10, BOARD_W, BOARD_H), border_radius=rad)
        pygame.draw.rect(s, C_HOLE_BACK, (BOARD_X, BOARD_Y, BOARD_W, BOARD_H), border_radius=rad)
        a = self.anim
        for r in range(ROWS):
            for c in range(COLS):
                p = g.board[r][c]
                if p and not (a and a.row == r and a.col == c):
                    x, y = cell_center(r, c)
                    draw_disc(s, x, y, DISC_R, p)
        if a:
            draw_disc(s, a.x, int(a.y), DISC_R, a.player)
        s.blit(self.board_surf_alt if _ALT else self.board_surf, (BOARD_X, BOARD_Y))
        # hover highlight + preview
        if self.sel_col is not None and self.human_can_move() and column_available(g.board, self.sel_col):
            c = self.sel_col
            s.blit(self.col_hl, (BOARD_X + PAD + c * CELL, BOARD_Y))
            pl = g.current if self.mode != "ai" else 1
            s.blit((self.ghosts_alt if _ALT else self.ghosts)[pl], (cell_center(0, c)[0] - DISC_R - 2, BOARD_Y - 44 - DISC_R - 2))
            lr = lowest_empty_row(g.board, c)
            x, y = cell_center(lr, c)
            pygame.draw.circle(s, PLAYER_COLORS[pl][0], (x, y), HOLE_R - 3, 3)
        # winning sequence
        if g.winner and self.anim is None and g.win_cells:
            pulse = 0.5 + 0.5 * math.sin(self.t * 7)
            pts = [cell_center(r, c) for r, c in g.win_cells]
            pygame.draw.line(s, lerp_color(C_GOLD, C_WHITE, pulse), pts[0], pts[-1], 8)
            for x, y in pts:
                draw_disc(s, x, y, DISC_R + int(2 * pulse), g.winner)
                pygame.draw.circle(s, lerp_color(C_GOLD, C_WHITE, pulse), (x, y), HOLE_R - 1, 4)
        for x, y, _, _, life, maxlife, color, size in self.fx:
            pygame.draw.circle(s, lerp_color(C_BG_BOT, color, life / maxlife), (int(x), int(y)), size)
        # result modal: centered on the screen
        if self.result_visible() and not self.result_hidden:
            self.draw_result_modal()
        self.draw_buttons()
        if self.paused:
            s.blit(self.dim, (0, 0))
            draw_panel(s, pygame.Rect(BASE_W // 2 - 230, 190, 460, 320))
            draw_title(s, "Game Paused", 46, (BASE_W // 2, 232), max_w=400)
            if self.mode in ("host", "client"):
                draw_text(s, "Online matches keep running while you pause.", 16, C_MUTED, (BASE_W // 2, 272), max_w=420)
            self.draw_buttons()

    def draw_error(self) -> None:
        s = self.canvas
        if self.error is None:
            return
        title, msg, _ = self.error
        s.blit(self.dim, (0, 0))
        draw_panel(s, pygame.Rect(BASE_W // 2 - 310, 200, 620, 300), border=C_RED)
        draw_text(s, title, 38, C_RED_D, (BASE_W // 2, 245), bold=True, max_w=560)
        for i, line in enumerate(wrap_text(msg, 22, 540)[:4]):
            draw_text(s, line, 22, C_TEXT, (BASE_W // 2, 306 + i * 28), max_w=560)
        self.err_btn.draw(s)

    # ---- main loop ---------------------------------------------------------- #
    def run(self) -> None:
        try:
            while self.running:
                dt = min(self.clock.tick(self.settings.fps) / 1000.0, 0.05)
                self.compute_view()
                self.mouse = self.to_virtual(pygame.mouse.get_pos())
                for e in pygame.event.get():
                    self.handle_event(e)
                self.process_network()
                self.update(dt)
                self.draw()
                self.present()
        finally:
            self.close_net()
            pygame.quit()


def main() -> None:
    App().run()


if __name__ == "__main__":
    main()