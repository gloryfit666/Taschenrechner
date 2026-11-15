#!/usr/bin/env python3
"""
Farbiger Konsolen-Taschenrechner (TUI) in Python ohne externe Abhängigkeiten.
Unterstützt sowohl die Steuerung über Pfeiltasten auf dem visuellen Tastenfeld
als auch die direkte Tastatureingabe von Zahlen, Operatoren und Funktionen.
"""

from __future__ import annotations

import ast
import math
import operator
import os
import re
import select
import sys
import termios
import tty
from typing import Callable

# ─── ANSI-Farben & Styling ───────────────────────────────────────────────────

RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"

# Vordergrundfarben (Bright / 256-Color kompatibel)
FG_WHITE = "\033[97m"
FG_CYAN = "\033[96m"
FG_YELLOW = "\033[93m"
FG_GREEN = "\033[92m"
FG_RED = "\033[91m"
FG_MAGENTA = "\033[95m"
FG_BLUE = "\033[94m"
FG_GRAY = "\033[90m"
FG_BLACK = "\033[30m"

# Hintergrundfarben für Tasten & Fokus
BG_DARK = "\033[48;5;235m"
BG_DISPLAY = "\033[48;5;234m"
BG_NUM = "\033[48;5;237m"
BG_OP = "\033[48;5;58m"
BG_FUNC = "\033[48;5;24m"
BG_DANGER = "\033[48;5;52m"
BG_EQUAL = "\033[48;5;28m"
BG_FOCUS = "\033[48;5;214m"  # Kräftiges Orange/Gelb für ausgewählte Taste


# ─── Sicherer Mathematischer Parser & Evaluator ──────────────────────────────

SAFE_FUNCTIONS: dict[str, Callable[..., float]] = {
    "sqrt": math.sqrt,
    "sin": lambda x: math.sin(math.radians(x)),
    "cos": lambda x: math.cos(math.radians(x)),
    "tan": lambda x: math.tan(math.radians(x)),
    "asin": lambda x: math.degrees(math.asin(x)),
    "acos": lambda x: math.degrees(math.acos(x)),
    "atan": lambda x: math.degrees(math.atan(x)),
    "log": math.log10,
    "ln": math.log,
    "abs": abs,
    "fact": lambda x: float(math.factorial(int(x))),
}

SAFE_CONSTANTS: dict[str, float] = {
    "pi": math.pi,
    "e": math.e,
}

BINARY_OPS: dict[type[ast.operator], Callable[[float, float], float]] = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.FloorDiv: operator.floordiv,
    ast.Mod: operator.mod,
    ast.Pow: operator.pow,
}

UNARY_OPS: dict[type[ast.unaryop], Callable[[float], float]] = {
    ast.UAdd: operator.pos,
    ast.USub: operator.neg,
}


def preprocess_expression(expr: str, ans: float = 0.0) -> str:
    """Bereitet einen mathematischen Ausdruck für den AST-Parser vor."""
    s = expr.strip()
    if not s:
        return "0"

    # Deutsche Kommas und spezielle Symbole normalisieren
    s = s.replace(",", ".")
    s = s.replace("×", "*").replace("÷", "/").replace("−", "-")
    s = s.replace("π", "pi").replace("√(", "sqrt(").replace("√", "sqrt")
    s = s.replace("^", "**")
    s = re.sub(r"\bANS\b", repr(ans), s, flags=re.IGNORECASE)

    # Prozent-Operator: z.B. 50% -> (50/100)
    s = re.sub(r"(\d+(?:\.\d+)?)%", r"(\1/100)", s)

    # Implizite Multiplikation ergänzen: z.B. 2(3) -> 2*(3), 2pi -> 2*pi, )2 -> )*2
    s = re.sub(r"(\d)\s*\(", r"\1*(", s)
    s = re.sub(r"\)\s*(\d)", r")*\1", s)
    s = re.sub(r"\)\s*\(", r")*(", s)
    s = re.sub(r"(\d)\s*(pi|e|sqrt|sin|cos|tan|log|ln|fact|abs)\b", r"\1*\2", s)
    s = re.sub(r"\)\s*(pi|e|sqrt|sin|cos|tan|log|ln|fact|abs)\b", r")*\1", s)
    s = re.sub(r"\b(pi|e)\s*(\d|\(|pi|e|sqrt|sin|cos|tan|log|ln|fact|abs)", r"\1*\2", s)

    # Offene Klammern am Ende automatisch schließen
    open_parens = s.count("(") - s.count(")")
    if open_parens > 0:
        s += ")" * open_parens

    return s


def _eval_node(node: ast.AST) -> float:
    if isinstance(node, ast.Expression):
        return _eval_node(node.body)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
        return float(node.value)
    if isinstance(node, ast.Name):
        name = node.id.lower()
        if name in SAFE_CONSTANTS:
            return SAFE_CONSTANTS[name]
        raise ValueError(f"Unbekannte Konstante: {node.id}")
    if isinstance(node, ast.BinOp):
        op_type = type(node.op)
        if op_type not in BINARY_OPS:
            raise ValueError("Nicht unterstützter Operator")
        left = _eval_node(node.left)
        right = _eval_node(node.right)
        if op_type is ast.Pow and abs(right) > 1000:
            raise OverflowError("Exponent zu groß")
        return float(BINARY_OPS[op_type](left, right))
    if isinstance(node, ast.UnaryOp):
        op_type = type(node.unaryop if hasattr(node, "unaryop") else node.op)
        if op_type not in UNARY_OPS:
            raise ValueError("Nicht unterstützter unärer Operator")
        return float(UNARY_OPS[op_type](_eval_node(node.operand)))
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        func_name = node.func.id.lower()
        if func_name not in SAFE_FUNCTIONS:
            raise ValueError(f"Unbekannte Funktion: {func_name}")
        if len(node.args) != 1:
            raise ValueError(f"{func_name}() erwartet genau 1 Argument")
        arg_val = _eval_node(node.args[0])
        return float(SAFE_FUNCTIONS[func_name](arg_val))
    raise ValueError("Ungültiger Ausdruck")


def evaluate_expression(expr: str, ans: float = 0.0) -> float:
    """Wertet einen mathematischen Ausdruck sicher aus."""
    prepared = preprocess_expression(expr, ans)
    tree = ast.parse(prepared, mode="eval")
    result = _eval_node(tree)
    if math.isnan(result) or math.isinf(result):
        raise OverflowError("Ergebnis außerhalb des gültigen Bereichs")
    return result


def format_number(val: float) -> str:
    """Formatiert eine Zahl sauber für die Anzeige."""
    if abs(val) < 1e-12:
        val = 0.0
    if val == int(val) and abs(val) < 1e15:
        return str(int(val))
    formatted = f"{val:.10g}"
    return formatted


# ─── Tastenfeld-Definition ───────────────────────────────────────────────────

# Jede Taste: (Anzeigename, Einfügewert/Aktion, Kategorie)
# Kategorien: "func", "danger", "num", "op", "equal"
KEYPAD: list[list[tuple[str, str, str]]] = [
    [
        ("sin", "sin(", "func"),
        ("cos", "cos(", "func"),
        ("tan", "tan(", "func"),
        ("√", "√(", "func"),
        ("AC", "CLEAR", "danger"),
    ],
    [
        ("ln", "ln(", "func"),
        ("log", "log(", "func"),
        ("x^y", "^", "func"),
        ("(", "(", "func"),
        (")", ")", "func"),
    ],
    [
        ("π", "π", "func"),
        ("7", "7", "num"),
        ("8", "8", "num"),
        ("9", "9", "num"),
        ("÷", "÷", "op"),
    ],
    [
        ("e", "e", "func"),
        ("4", "4", "num"),
        ("5", "5", "num"),
        ("6", "6", "num"),
        ("×", "×", "op"),
    ],
    [
        ("%", "%", "func"),
        ("1", "1", "num"),
        ("2", "2", "num"),
        ("3", "3", "num"),
        ("−", "−", "op"),
    ],
    [
        ("ANS", "ANS", "func"),
        ("0", "0", "num"),
        (".", ".", "num"),
        ("DEL", "BACKSPACE", "danger"),
        ("+", "+", "op"),
    ],
    [
        ("±", "NEGATE", "func"),
        ("x!", "fact(", "func"),
        ("abs", "abs(", "func"),
        ("=", "EVAL", "equal"),
        ("Ende", "QUIT", "danger"),
    ],
]


# ─── Konsolen-Taschenrechner TUI ─────────────────────────────────────────────

class ConsoleCalculator:
    def __init__(self) -> None:
        self.expression: str = ""
        self.ans: float = 0.0
        self.status_message: str = "Bereit – Pfeiltasten/Leertaste oder direkt tippen!"
        self.error_state: bool = False
        self.history: list[tuple[str, str]] = []
        self.row: int = 2
        self.col: int = 1
        self.nav_mode: bool = True  # True wenn zuletzt per Pfeiltasten navigiert wurde

    def trigger_action(self, action: str) -> bool:
        """Führt eine Tastenaktion aus. Gibt False zurück, wenn beendet werden soll."""
        self.error_state = False
        self.status_message = ""

        if action == "QUIT":
            return False
        elif action == "CLEAR":
            self.expression = ""
            self.status_message = "Anzeige gelöscht"
        elif action == "BACKSPACE":
            # Ganze Funktionsnamen am Ende auf einmal löschen, falls vorhanden
            for token in ("sin(", "cos(", "tan(", "log(", "fact(", "abs(", "ANS", "ln(", "√("):
                if self.expression.endswith(token):
                    self.expression = self.expression[: -len(token)]
                    break
            else:
                self.expression = self.expression[:-1]
        elif action == "NEGATE":
            if self.expression.startswith("-"):
                self.expression = self.expression[1:]
            elif self.expression:
                self.expression = f"-({self.expression})"
            else:
                self.expression = "-"
        elif action == "EVAL":
            if not self.expression.strip():
                return True
            try:
                res = evaluate_expression(self.expression, self.ans)
                formatted = format_number(res)
                self.history.append((self.expression, formatted))
                if len(self.history) > 5:
                    self.history.pop(0)
                self.ans = res
                self.expression = formatted
                self.status_message = "Ergebnis berechnet (in ANS gespeichert)"
            except ZeroDivisionError:
                self.error_state = True
                self.status_message = "Fehler: Division durch Null!"
            except OverflowError:
                self.error_state = True
                self.status_message = "Fehler: Zahlenbereich überschritten!"
            except Exception:
                self.error_state = True
                self.status_message = "Fehler: Ungültiger mathematischer Ausdruck!"
        else:
            # Wenn direkt nach einem Ergebnis ein binärer Operator getippt wird, normal anhängen
            self.expression += action

        return True

    def get_live_preview(self) -> str:
        """Berechnet eine Live-Vorschau des aktuellen Ausdrucks."""
        if not self.expression.strip():
            return "0"
        try:
            res = evaluate_expression(self.expression, self.ans)
            return format_number(res)
        except ZeroDivisionError:
            return "Division durch 0"
        except Exception:
            return "..."

    def select_button_by_action(self, action: str) -> None:
        """Bewegt den Fokus auf die Taste, die der getippten Aktion entspricht."""
        for r_idx, row in enumerate(KEYPAD):
            for c_idx, (_, act, _) in enumerate(row):
                if act == action:
                    self.row = r_idx
                    self.col = c_idx
                    return

    def style_button(self, label: str, category: str, focused: bool) -> str:
        """Formatiert eine einzelne Taste farbig."""
        width = 7
        text = label.center(width)
        if focused:
            return f"{BG_FOCUS}{FG_BLACK}{BOLD}▸{label.center(width - 2)}◂{RESET}"

        if category == "num":
            return f"{BG_NUM}{FG_WHITE}{BOLD}{text}{RESET}"
        elif category == "op":
            return f"{BG_OP}{FG_YELLOW}{BOLD}{text}{RESET}"
        elif category == "func":
            return f"{BG_FUNC}{FG_CYAN}{text}{RESET}"
        elif category == "danger":
            return f"{BG_DANGER}{FG_RED}{BOLD}{text}{RESET}"
        elif category == "equal":
            return f"{BG_EQUAL}{FG_GREEN}{BOLD}{text}{RESET}"
        return text

    def render(self) -> str:
        """Erstellt den kompletten Konsolen-Frame als String."""
        box_w = 43  # Innenbreite des Rahmens
        lines: list[str] = []

        # Cursor nach oben links setzen & Bildschirm ab Cursor löschen
        lines.append("\033[H\033[J")

        # ── Kopfzeile ──
        lines.append(f"  {FG_CYAN}{BOLD}╭{'─' * box_w}╮{RESET}")
        title = "◆ FARB-TASCHENRECHNER PRO ◆"
        lines.append(
            f"  {FG_CYAN}{BOLD}│{RESET}{BG_DARK}{FG_YELLOW}{BOLD}{title.center(box_w)}{RESET}{FG_CYAN}{BOLD}│{RESET}"
        )
        lines.append(f"  {FG_CYAN}{BOLD}├{'─' * box_w}┤{RESET}")

        # ── Verlauf (letzte 3 Berechnungen) ──
        lines.append(
            f"  {FG_CYAN}{BOLD}│{RESET} {FG_GRAY}{'Verlauf:'.ljust(box_w - 2)} {FG_CYAN}{BOLD}│{RESET}"
        )
        recent = self.history[-3:]
        for i in range(3):
            if i < len(recent):
                expr_str, res_str = recent[i]
                entry = f"{expr_str} = {res_str}"
                if len(entry) > box_w - 4:
                    entry = "…" + entry[-(box_w - 5) :]
                padded = entry.rjust(box_w - 2)
                lines.append(
                    f"  {FG_CYAN}{BOLD}│{RESET} {FG_MAGENTA}{padded}{RESET} {FG_CYAN}{BOLD}│{RESET}"
                )
            else:
                lines.append(
                    f"  {FG_CYAN}{BOLD}│{RESET} {FG_GRAY}{'·'.rjust(box_w - 2)}{RESET} {FG_CYAN}{BOLD}│{RESET}"
                )

        lines.append(f"  {FG_CYAN}{BOLD}├{'─' * box_w}┤{RESET}")

        # ── Haupt-Display (Ausdruck & Live-Vorschau) ──
        disp_expr = self.expression if self.expression else "0"
        if len(disp_expr) > box_w - 4:
            disp_expr = "…" + disp_expr[-(box_w - 5) :]

        preview = self.get_live_preview()
        if len(preview) > box_w - 8:
            preview = preview[: box_w - 8]

        lines.append(
            f"  {FG_CYAN}{BOLD}│{RESET}{BG_DISPLAY} {FG_WHITE}{BOLD}{disp_expr.rjust(box_w - 2)}{RESET}{BG_DISPLAY} {RESET}{FG_CYAN}{BOLD}│{RESET}"
        )

        preview_color = FG_RED if self.error_state else FG_GREEN
        preview_line = f"= {preview}"
        lines.append(
            f"  {FG_CYAN}{BOLD}│{RESET}{BG_DISPLAY} {preview_color}{BOLD}{preview_line.rjust(box_w - 2)}{RESET}{BG_DISPLAY} {RESET}{FG_CYAN}{BOLD}│{RESET}"
        )
        lines.append(f"  {FG_CYAN}{BOLD}├{'─' * box_w}┤{RESET}")

        # ── Tastenfeld ──
        for r_idx, row in enumerate(KEYPAD):
            rendered_btns = []
            for c_idx, (label, _, cat) in enumerate(row):
                is_focused = (r_idx == self.row) and (c_idx == self.col)
                rendered_btns.append(self.style_button(label, cat, is_focused))
            row_str = " ".join(rendered_btns)
            lines.append(f"  {FG_CYAN}{BOLD}│{RESET}  {row_str}  {FG_CYAN}{BOLD}│{RESET}")
            if r_idx < len(KEYPAD) - 1:
                lines.append(f"  {FG_CYAN}{BOLD}│{' ' * box_w}│{RESET}")

        lines.append(f"  {FG_CYAN}{BOLD}├{'─' * box_w}┤{RESET}")

        # ── Statusleiste ──
        status_color = FG_RED if self.error_state else FG_YELLOW
        msg = self.status_message or f"ANS = {format_number(self.ans)}"
        if len(msg) > box_w - 2:
            msg = msg[: box_w - 3] + "…"
        lines.append(
            f"  {FG_CYAN}{BOLD}│{RESET} {status_color}{msg.ljust(box_w - 2)}{RESET} {FG_CYAN}{BOLD}│{RESET}"
        )
        lines.append(f"  {FG_CYAN}{BOLD}╰{'─' * box_w}╯{RESET}")

        # ── Kurzanleitung ──
        lines.append(
            f"  {DIM}Steuerung: {RESET}{FG_CYAN}↑↓←→{RESET}{DIM} Auswahl │ "
            f"{RESET}{FG_GREEN}Enter{RESET}{DIM} Rechnen/Klick │ "
            f"{RESET}{FG_YELLOW}0-9 + - * /{RESET}{DIM} Direkt-Tippen │ "
            f"{RESET}{FG_RED}c{RESET}{DIM} Clear │ {RESET}{FG_RED}q{RESET}{DIM} Ende{RESET}"
        )

        return "\n".join(lines) + "\n"

    def read_key(self) -> str:
        """Liest einen einzelnen Tastendruck inklusive Escape-Sequenzen (Pfeiltasten)."""
        fd = sys.stdin.fileno()
        old_settings = termios.tcgetattr(fd)
        try:
            tty.setraw(fd, when=termios.TCSANOW)
            b1 = os.read(fd, 1)
            if not b1:
                return "\x04"  # EOF

            if b1 == b"\x1b":
                # Direkt auf dem ungepufferten File-Descriptor prüfen, ob weitere Bytes
                # einer Escape-Sequenz anliegen (sys.stdin.read würde alle Bytes puffern!).
                if not select.select([fd], [], [], 0.05)[0]:
                    return "ESC"

                b2 = os.read(fd, 1)
                if b2 in (b"[", b"O"):
                    seq = b""
                    while select.select([fd], [], [], 0.02)[0]:
                        ch = os.read(fd, 1)
                        seq += ch
                        if ch.isalpha() or ch == b"~":
                            break
                    if seq.endswith(b"A"):
                        return "UP"
                    elif seq.endswith(b"B"):
                        return "DOWN"
                    elif seq.endswith(b"C"):
                        return "RIGHT"
                    elif seq.endswith(b"D"):
                        return "LEFT"
                    elif seq == b"3~":
                        return "DELETE"
                    elif b2 == b"O" and seq == b"M":
                        return "\r"
                    return "IGNORE"
                return "ESC"

            # Mehrfach-Byte UTF-8 Zeichen vollständig einlesen
            first_byte = b1[0]
            if first_byte >= 0x80:
                if (first_byte & 0xE0) == 0xC0:
                    extra = 1
                elif (first_byte & 0xF0) == 0xE0:
                    extra = 2
                elif (first_byte & 0xF8) == 0xF0:
                    extra = 3
                else:
                    extra = 0
                for _ in range(extra):
                    if select.select([fd], [], [], 0.02)[0]:
                        b1 += os.read(fd, 1)

            return b1.decode("utf-8", errors="ignore")
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

    def handle_keypress(self, key: str) -> bool:
        """Verarbeitet einen Tastendruck. Gibt False zurück, wenn beendet werden soll."""
        rows = len(KEYPAD)
        cols = len(KEYPAD[0])

        # Navigation
        if key == "UP":
            self.row = (self.row - 1) % rows
            self.nav_mode = True
            return True
        elif key == "DOWN":
            self.row = (self.row + 1) % rows
            self.nav_mode = True
            return True
        elif key == "LEFT":
            self.col = (self.col - 1) % cols
            self.nav_mode = True
            return True
        elif key == "RIGHT":
            self.col = (self.col + 1) % cols
            self.nav_mode = True
            return True

        # Leertaste betätigt immer die aktuell ausgewählte Taste auf dem Tastenfeld
        if key == " ":
            _, action, _ = KEYPAD[self.row][self.col]
            return self.trigger_action(action)

        # Enter: Bei Pfeiltasten-Navigation wird die ausgewählte Taste gedrückt,
        # bei direkter Tastatureingabe wird sofort das Ergebnis berechnet (=).
        if key in ("\r", "\n"):
            if self.nav_mode:
                _, action, _ = KEYPAD[self.row][self.col]
                return self.trigger_action(action)
            self.select_button_by_action("EVAL")
            return self.trigger_action("EVAL")

        # Gleichheitszeichen berechnet sofort das Ergebnis
        if key == "=":
            self.nav_mode = False
            self.select_button_by_action("EVAL")
            return self.trigger_action("EVAL")

        # Beenden mit q oder Ctrl+C / Ctrl+D
        if key in ("q", "Q", "\x03", "\x04"):
            return False

        # Löschen mit Escape, c, C oder Entf
        if key in ("ESC", "c", "C", "DELETE"):
            self.nav_mode = False
            self.select_button_by_action("CLEAR")
            return self.trigger_action("CLEAR")

        # Backspace
        if key in ("\x7f", "\x08"):
            self.nav_mode = False
            self.select_button_by_action("BACKSPACE")
            return self.trigger_action("BACKSPACE")

        # Direkte Zahleneingabe & Operatoren
        direct_map = {
            "0": "0",
            "1": "1",
            "2": "2",
            "3": "3",
            "4": "4",
            "5": "5",
            "6": "6",
            "7": "7",
            "8": "8",
            "9": "9",
            ".": ".",
            ",": ".",
            "+": "+",
            "-": "−",
            "*": "×",
            "/": "÷",
            "^": "^",
            "%": "%",
            "(": "(",
            ")": ")",
            "p": "π",
            "e": "e",
            "s": "sin(",
            "o": "cos(",
            "t": "tan(",
            "r": "√(",
            "l": "log(",
            "n": "ln(",
            "a": "ANS",
            "!": "fact(",
        }
        if key in direct_map:
            self.nav_mode = False
            action = direct_map[key]
            self.select_button_by_action(action)
            return self.trigger_action(action)

        return True

    def run(self) -> None:
        """Startet die interaktive Hauptschleife."""
        if not sys.stdin.isatty():
            self.run_fallback_repl()
            return

        # Alternativen Bildschirm-Puffer aktivieren & Cursor verstecken
        sys.stdout.write("\033[?1049h\033[?25l")
        sys.stdout.flush()
        try:
            running = True
            while running:
                sys.stdout.write(self.render())
                sys.stdout.flush()
                key = self.read_key()
                running = self.handle_keypress(key)
        finally:
            # Cursor wieder anzeigen & Bildschirm-Puffer wiederherstellen
            sys.stdout.write("\033[?25h\033[?1049l")
            sys.stdout.flush()

    def run_fallback_repl(self) -> None:
        """Fallback-Modus falls stdin kein interaktives Terminal (TTY) ist."""
        print(f"{FG_CYAN}{BOLD}⚡ FARB-TASCHENRECHNER (REPL-Modus) ⚡{RESET}")
        print(f"{DIM}Gib einen Ausdruck ein (oder 'q' zum Beenden):{RESET}")
        for line in sys.stdin:
            cmd = line.strip()
            if cmd.lower() in ("q", "quit", "exit"):
                break
            if not cmd:
                continue
            try:
                res = evaluate_expression(cmd, self.ans)
                self.ans = res
                print(f"{FG_GREEN}{BOLD}= {format_number(res)}{RESET}")
            except Exception as exc:
                print(f"{FG_RED}Fehler: {exc}{RESET}")


def main() -> None:
    # Unterstützt auch direkte Auswertung über Kommandozeilenargumente:
    # python3 taschenrechner.py "2 + 3 * 4"
    if len(sys.argv) > 1:
        expr = " ".join(sys.argv[1:])
        try:
            res = evaluate_expression(expr)
            print(f"{FG_CYAN}{expr}{RESET} = {FG_GREEN}{BOLD}{format_number(res)}{RESET}")
        except Exception as exc:
            print(f"{FG_RED}Fehler: {exc}{RESET}", file=sys.stderr)
            sys.exit(1)
        return

    calc = ConsoleCalculator()
    calc.run()


if __name__ == "__main__":
    main()
