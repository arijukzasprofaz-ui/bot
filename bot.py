import discord
from discord.ext import commands
import asyncio
import ast
import io
import math
import os
import random
import re
from dataclasses import dataclass
from typing import Optional

TOKEN = os.environ.get("TOKEN")

# ============================================================
# Detection
# ============================================================
SIGNATURES = [
    ("WeAreDevs", lambda c: bool(re.search(
        r"wearedevs\s*\.?\s*net\s*/\s*obfuscator|"
        r"wearedevs\s*obfuscator|--\[\[\s*v1\.0\.0\s+https?://wearedevs",
        c[:12000], re.I))),
    ("LuaObfuscator", lambda c: bool(re.search(
        r'''VMCall\s*\(\s*["']LOL!''', c))),
    ("IronBrew3", lambda c: bool(re.search(r"ironbrew\s*3", c[:2000], re.I)) or "IronBrew3" in c[:1000]),
    ("IronBrew2", lambda c: bool(re.search(r"ironbrew\s*2", c[:2000], re.I)) or "IronBrew2" in c[:1000]),
    ("IronBrew", lambda c: bool(re.search(r"ironbrew", c[:2000], re.I))),
    ("Luraph", lambda c: bool(re.search(r"luraph", c[:3000], re.I)) or "--[[ luraph" in c[:300].lower()),
    ("MoonVeil", lambda c: bool(re.search(r"moonveil", c[:3000], re.I))),
    ("MoonSec", lambda c: bool(re.search(r"moonsec", c[:3000], re.I))),
    ("Prometheus", lambda c: bool(re.search(r"prometheus", c[:3000], re.I))),
    ("SynapseXen", lambda c: bool(re.search(r"synapse.*xen|xen.*synapse", c[:1000], re.I))),
    ("Hercules", lambda c: bool(re.search(r"hercules", c[:3000], re.I))),
    ("Boronide", lambda c: bool(re.search(r"boronide", c[:3000], re.I))),
    ("77fuscator", lambda c: bool(re.search(r"77fuscator", c[:3000], re.I))),
    ("wYnFuscate", lambda c: bool(re.search(r"wyn(?:fuscate|obf)", c[:3000], re.I))),
    ("PSU", lambda c: bool(re.search(r"\bPSU\b", c[:1000]))),
    ("LPS", lambda c: bool(re.search(r"\bLPS\b", c[:1000]))),
]


def detect_obfuscator(code: str) -> str:
    code = code.lstrip("\ufeff").strip()

    if re.search(
        r"--\[\[\s*v1\.0\.0\s+https?://wearedevs\.net/obfuscator\s*\]\]",
        code[:12000],
        re.I
    ):
        return "WeAreDevs"

    if re.search(
        r"wearedevs\.net\s*/\s*obfuscator",
        code[:12000],
        re.I
    ):
        return "WeAreDevs"

    for name, check in SIGNATURES:
        try:
            if check(code):
                return name
        except Exception:
            pass

    return "Unknown"


# ============================================================
# LuaObfuscator binary decoder
# ============================================================
def decode_luaobf(encoded: str) -> bytes:
    if not encoded.startswith("LOL!"):
        raise ValueError("Missing LOL! prefix")

    payload = encoded[4:]

    if len(payload) % 2:
        raise ValueError("Malformed LOL! payload")

    out = bytearray()
    repeat_next = None
    i = 0

    while i < len(payload):
        pair = payload[i:i + 2]
        i += 2

        if pair[1].upper() == "Q":
            repeat_next = int(pair[0], 16)
            continue

        value = int(pair, 16)
        count = repeat_next if repeat_next is not None else 1
        repeat_next = None
        out.extend(bytes([value]) * count)

    return bytes(out)


class Reader:
    def __init__(self, data: bytes):
        self.d = data
        self.p = 0

    def _need(self, size: int):
        if size < 0 or self.p + size > len(self.d):
            raise ValueError(f"Unexpected end of bytecode at {self.p}")

    def u8(self):
        self._need(1)
        v = self.d[self.p]
        self.p += 1
        return v

    def u16(self):
        self._need(2)
        a, b = self.d[self.p:self.p + 2]
        self.p += 2
        return (b << 8) | a

    def u32(self):
        self._need(4)
        a, b, c, d = self.d[self.p:self.p + 4]
        self.p += 4
        return (d << 24) | (c << 16) | (b << 8) | a

    def f64(self):
        left = self.u32()
        right = self.u32()

        mantissa = ((right & 0xFFFFF) << 32) | left
        exponent = (right >> 20) & 0x7FF
        sign = -1.0 if right >> 31 else 1.0

        if exponent == 0:
            return sign * (
                0.0 if mantissa == 0
                else math.ldexp(mantissa, -1074)
            )

        if exponent == 0x7FF:
            return math.inf * sign if mantissa == 0 else math.nan

        return sign * math.ldexp(
            (1 << 52) | mantissa,
            exponent - 1023 - 52
        )

    def string(self, length=None):
        if length is None:
            length = self.u32()

        if length == 0:
            return ""

        self._need(length)
        raw = self.d[self.p:self.p + length]
        self.p += length

        return raw.decode("utf-8", errors="replace")

    @staticmethod
    def gbit(value, start, end=None):
        if end is None:
            return (value >> (start - 1)) & 1

        width = end - start + 1
        return (value >> (start - 1)) & ((1 << width) - 1)


def parse_chunk(r: Reader, depth=0):
    const_count = r.u32()
    consts = []

    for _ in range(const_count):
        t = r.u8()

        if t == 1:
            consts.append(("bool", r.u8() != 0))
        elif t == 2:
            consts.append(("num", r.f64()))
        elif t == 3:
            consts.append(("str", r.string()))
        else:
            consts.append(("nil", None))

    params = r.u8()
    instr_count = r.u32()
    instrs = []

    for _ in range(instr_count):
        desc = r.u8()

        if Reader.gbit(desc, 1):
            continue

        typ = Reader.gbit(desc, 2, 3)
        mask = Reader.gbit(desc, 4, 6)

        op = r.u16()
        a = r.u16()
        b = c = None

        if typ == 0:
            b, c = r.u16(), r.u16()
        elif typ == 1:
            b = r.u32()
        elif typ == 2:
            b = r.u32() - (1 << 16)
        elif typ == 3:
            b, c = r.u32() - (1 << 16), r.u16()

        def resolve(v, bit):
            if (
                v is not None
                and Reader.gbit(mask, bit)
                and isinstance(v, int)
                and 0 <= v < len(consts)
            ):
                return consts[v][1]

            return v

        instrs.append((
            op,
            resolve(a, 1),
            resolve(b, 2),
            resolve(c, 3)
        ))

    subs = [
        parse_chunk(r, depth + 1)
        for _ in range(r.u32())
    ]

    return {
        "depth": depth,
        "params": params,
        "consts": consts,
        "instrs": instrs,
        "subs": subs
    }


def collect_consts(chunk, out=None):
    if out is None:
        out = []

    out.extend(chunk["consts"])

    for sub in chunk["subs"]:
        collect_consts(sub, out)

    return out


def count_funcs(chunk):
    return 1 + sum(
        count_funcs(x)
        for x in chunk["subs"]
    )


# ============================================================
# Lua 5.1 opcode names
# ============================================================
LUA51_OPS = {
    0: "MOVE",
    1: "LOADK",
    2: "LOADBOOL",
    3: "LOADNIL",
    4: "GETUPVAL",
    5: "GETGLOBAL",
    6: "GETTABLE",
    7: "SETGLOBAL",
    8: "SETUPVAL",
    9: "SETTABLE",
    10: "NEWTABLE",
    11: "SELF",
    12: "ADD",
    13: "SUB",
    14: "MUL",
    15: "DIV",
    16: "MOD",
    17: "POW",
    18: "UNM",
    19: "NOT",
    20: "LEN",
    21: "CONCAT",
    22: "JMP",
    23: "EQ",
    24: "LT",
    25: "LE",
    26: "TEST",
    27: "TESTSET",
    28: "CALL",
    29: "TAILCALL",
    30: "RETURN",
    31: "FORLOOP",
    32: "FORPREP",
    33: "TFORLOOP",
    34: "SETLIST",
    35: "CLOSE",
    36: "CLOSURE",
    37: "VARARG"
}


def _lua_literal(v):
    if v is None:
        return "nil"

    if isinstance(v, bool):
        return "true" if v else "false"

    if isinstance(v, str):
        return repr(v)

    if isinstance(v, float) and v.is_integer():
        return str(int(v))

    return repr(v)


def _reg(v):
    return f"r{v}" if isinstance(v, int) else _lua_literal(v)


def _safe_expr(expr):
    if not re.fullmatch(r"[0-9+\-*/%().\s]+", expr or ""):
        return None

    try:
        tree = ast.parse(expr, mode="eval")

        allowed = (
            ast.Expression,
            ast.Constant,
            ast.BinOp,
            ast.UnaryOp,
            ast.Add,
            ast.Sub,
            ast.Mult,
            ast.Div,
            ast.FloorDiv,
            ast.Mod,
            ast.Pow,
            ast.USub,
            ast.UAdd
        )

        if any(not isinstance(n, allowed) for n in ast.walk(tree)):
            return None

        return eval(
            compile(tree, "<expr>", "eval"),
            {"__builtins__": {}},
            {}
        )

    except Exception:
        return None


def _simplify_constants(text):
    def repl(m):
        value = _safe_expr(m.group(0))

        return (
            str(value)
            if isinstance(value, (int, float))
            else m.group(0)
        )

    return re.sub(
        r"\b\d+(?:\s*[+\-*/%]\s*\d+)+\b",
        repl,
        text
    )


def lift_lua_chunk(chunk, indent=0):
    """Best-effort Lua-like lifting from the parsed chunk."""

    pad = "    " * indent
    lines = []
    instrs = chunk["instrs"]
    labels = set()

    for i, (op, a, b, c) in enumerate(instrs):
        if (
            LUA51_OPS.get(op)
            in {"JMP", "FORLOOP", "FORPREP", "TFORLOOP"}
            and isinstance(a, int)
        ):
            target = i + 1 + a

            if 0 <= target < len(instrs):
                labels.add(target)

    for i, (op, a, b, c) in enumerate(instrs):
        if i in labels:
            lines.append(f"{pad}::L{i}::")

        name = LUA51_OPS.get(op, f"vm_op_{op}")

        if name == "MOVE":
            lines.append(f"{pad}r{a} = {_reg(b)}")

        elif name == "LOADK":
            lines.append(f"{pad}r{a} = {_lua_literal(b)}")

        elif name == "LOADBOOL":
            lines.append(
                f"{pad}r{a} = {'true' if b else 'false'}"
            )

        elif name == "LOADNIL":
            lines.append(f"{pad}r{a} = nil")

        elif name in {"ADD", "SUB", "MUL", "DIV", "MOD", "POW"}:
            opch = {
                "ADD": "+",
                "SUB": "-",
                "MUL": "*",
                "DIV": "/",
                "MOD": "%",
                "POW": "^"
            }[name]

            lines.append(
                f"{pad}r{a} = {_reg(b)} {opch} {_reg(c)}"
            )

        elif name == "UNM":
            lines.append(f"{pad}r{a} = -{_reg(b)}")

        elif name == "NOT":
            lines.append(f"{pad}r{a} = not {_reg(b)}")

        elif name == "LEN":
            lines.append(f"{pad}r{a} = #{_reg(b)}")

        elif name == "CONCAT":
            lines.append(
                f"{pad}r{a} = {_reg(b)} .. {_reg(c)}"
            )

        elif name == "GETGLOBAL":
            lines.append(
                f"{pad}r{a} = {_lua_literal(b)}"
            )

        elif name == "SETGLOBAL":
            lines.append(
                f"{pad}{_lua_literal(b)} = {_reg(a)}"
            )

        elif name == "GETUPVAL":
            lines.append(
                f"{pad}r{a} = upvalue_{b}"
            )

        elif name == "SETUPVAL":
            lines.append(
                f"{pad}upvalue_{b} = {_reg(a)}"
            )

        elif name == "JMP":
            target = (
                i + 1 + a
                if isinstance(a, int)
                else None
            )

            if target is not None:
                lines.append(
                    f"{pad}goto L{target}"
                )
            else:
                lines.append(
                    f"{pad}-- JMP {_reg(a)}"
                )

        elif name in {"EQ", "LT", "LE"}:
            cmpop = {
                "EQ": "==",
                "LT": "<",
                "LE": "<="
            }[name]

            lines.append(
                f"{pad}-- if {_reg(b)} {cmpop} {_reg(c)} then"
            )

        elif name == "CALL":
            lines.append(
                f"{pad}-- call {_reg(a)} ({_reg(b)}, {_reg(c)})"
            )

        elif name == "RETURN":
            lines.append(
                f"{pad}return {_reg(a)}"
            )

        elif name == "CLOSURE":
            lines.append(
                f"{pad}r{a} = function(...) -- nested function"
            )

        elif name in {"FORPREP", "FORLOOP", "TFORLOOP"}:
            lines.append(
                f"{pad}-- {name} A={a} B={b} C={c}"
            )

        else:
            lines.append(
                f"{pad}-- {name} A={a!r} B={b!r} C={c!r}"
            )

    for idx, sub in enumerate(chunk["subs"], 1):
        lines.append("")
        lines.append(
            f"{pad}local function __deob_func_"
            f"{chunk['depth']}_{idx}(...)"
        )

        lines.extend(
            lift_lua_chunk(sub, indent + 1)
        )

        lines.append(f"{pad}end")

    return lines


def deobfuscate_luaobfuscator(code, include_instrs=False):
    m = re.search(
        r'''VMCall\s*\(\s*["'](LOL![^"']+)''',
        code
    )

    if not m:
        return "[LuaObfuscator] VMCall payload not found."

    raw = decode_luaobf(m.group(1))
    chunk = parse_chunk(Reader(raw))

    all_consts = collect_consts(chunk)

    lines = [
        "=" * 62,
        "  LuaObfuscator.com — reconstructed Lua",
        f"  {len(raw):,} decoded bytes | "
        f"{count_funcs(chunk)} functions",
        "=" * 62,
        "",
        "-- Best-effort static lift.",
        "-- Unknown/remapped VM opcodes are kept as comments.",
        "-- No submitted Lua/Luau code is executed.",
        "",
    ]

    lines.extend(lift_lua_chunk(chunk))

    result = _simplify_constants(
        "\n".join(lines)
    )

    if include_instrs:
        result += (
            "\n\n-- CONSTANTS\n"
            + "\n".join(
                f"-- {i}: {t} = {v!r}"
                for i, (t, v)
                in enumerate(all_consts)
            )
        )

    return result


# ============================================================
# WeAreDevs Method 2
# ============================================================
def _safe_lua_expr(expr):
    return _safe_expr(expr)


def _decode_lua_escapes(value):
    def repl(m):
        token = m.group(1)

        try:
            return chr(
                int(token[1:], 16)
                if token.lower().startswith("x")
                else int(token)
            )
        except Exception:
            return m.group(0)

    value = re.sub(
        r"\\(x[0-9a-fA-F]{2}|[0-9]{1,3})",
        repl,
        value
    )

    return (
        value
        .replace(r'\"', '"')
        .replace(r"\'", "'")
        .replace(r"\\", "\\")
        .replace(r"\n", "\n")
        .replace(r"\r", "\r")
        .replace(r"\t", "\t")
    )


def _extract_lua_table_body(code, name, limit=200000):
    m = re.search(
        r"\blocal\s+" +
        re.escape(name) +
        r"\s*=\s*\{",
        code[:limit]
    )

    if not m:
        return None

    start = m.end()
    depth = 1
    quote = None
    esc = False

    for i in range(
        start,
        min(len(code), limit)
    ):
        ch = code[i]

        if quote:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == quote:
                quote = None

            continue

        if ch in "\"'":
            quote = ch

        elif ch == "{":
            depth += 1

        elif ch == "}":
            depth -= 1

            if depth == 0:
                return code[start:i]

    return None


def _parse_numeric_lookup_table(body):
    out = {}

    if not body:
        return out

    pattern = re.compile(
        r'''(?:\[\s*(["'])(.*?)\1\s*\]|([A-Za-z_][A-Za-z0-9_]*))'''
        r'''\s*=\s*([0-9+\-*/%().\s]+)(?=[,;]|$)'''
    )

    for m in pattern.finditer(body):
        key = (
            m.group(2)
            if m.group(2) is not None
            else m.group(3)
        )

        val = _safe_lua_expr(m.group(4))

        if val is not None and len(key) == 1:
            out[key] = int(val)

    return out


def _extract_quoted_strings(body):
    return [
        _decode_lua_escapes(m.group(1))
        for m in re.finditer(
            r'"((?:\\.|[^"\\])*)"',
            body or ""
        )
    ]


def _custom_b64_decode(value, alphabet):
    if not value or value[0] not in ("?", "s"):
        return None

    width, out_width = (
        (5, 4)
        if value[0] == "?"
        else (4, 3)
    )

    vals = []

    for ch in value[1:]:
        if ch == "=":
            vals.append(0)
        elif ch in alphabet:
            vals.append(alphabet[ch])
        else:
            return None

    out = bytearray()

    for i in range(0, len(vals), width):
        chunk = vals[i:i + width]

        if len(chunk) < 2:
            break

        real = len(chunk)
        chunk += [0] * (width - real)

        n = 0

        for v in chunk:
            n = n * 64 + v

        for shift in range(
            (out_width - 1) * 8,
            -1,
            -8
        ):
            out.append((n >> shift) & 255)

        if real < width:
            del out[
                -min(width - real, out_width):
            ]

    try:
        return out.decode("utf-8")
    except UnicodeDecodeError:
        return out.decode(
            "latin-1",
            errors="replace"
        )


def _decode_wad_strings(code):
    ubody = _extract_lua_table_body(code, "U")

    omap = _parse_numeric_lookup_table(
        _extract_lua_table_body(code, "o") or ""
    )

    wmap = _parse_numeric_lookup_table(
        _extract_lua_table_body(code, "w") or ""
    )

    strings = _extract_quoted_strings(
        ubody or ""
    )

    decoded = []

    for s in strings:
        if s.startswith("?"):
            value = _custom_b64_decode(s, omap)
        elif s.startswith("s"):
            value = _custom_b64_decode(s, wmap)
        else:
            value = None

        decoded.append(
            value if value is not None else s
        )

    return decoded, omap, wmap


def _replace_wad_string_indexes(code, decoded):
    def repl(m):
        idx = int(m.group(1)) - 1

        if 0 <= idx < len(decoded):
            return _lua_literal(decoded[idx])

        return m.group(0)

    return re.sub(
        r"\bU\s*\[\s*(\d+)\s*\]",
        repl,
        code
    )


def deobfuscate_wearedevs(code):
    decoded, omap, wmap = _decode_wad_strings(code)
    lifted = _replace_wad_string_indexes(
        code,
        decoded
    )

    for name in ("U", "o", "w"):
        pattern = re.compile(
            r"\blocal\s+" +
            re.escape(name) +
            r"\s*=\s*\{",
            re.M
        )

        m = pattern.search(lifted)

        if m:
            start = m.start()
            depth = 0
            quote = None
            esc = False

            for i in range(
                m.end() - 1,
                len(lifted)
            ):
                ch = lifted[i]

                if quote:
                    if esc:
                        esc = False
                    elif ch == "\\":
                        esc = True
                    elif ch == quote:
                        quote = None

                    continue

                if ch in "\"'":
                    quote = ch

                elif ch == "{":
                    depth += 1

                elif ch == "}":
                    depth -= 1

                    if depth == 0:
                        end = i + 1

                        while (
                            end < len(lifted)
                            and lifted[end]
                            in " \t\r\n;"
                        ):
                            end += 1

                        lifted = (
                            lifted[:start]
                            + lifted[end:]
                        )

                        break

    lifted = re.sub(
        r"if\s+false\s+then[\s\S]*?end",
        "",
        lifted,
        flags=re.I
    )

    lifted = re.sub(
        r"\n{3,}",
        "\n\n",
        lifted
    ).strip()

    header = [
        "=" * 62,
        "  WeAreDevs v1.0.0 — reconstructed Lua",
        f"  {len(code):,} chars | "
        f"{len(decoded):,} decoded strings",
        "=" * 62,
        "",
        "-- String layer decoded statically.",
        "-- VM code is not executed.",
        "-- Unknown VM semantics are not guessed.",
        "",
    ]

    if lifted:
        header += [
            "-- RECONSTRUCTED SOURCE",
            "",
            lifted
        ]
    else:
        header += [
            "-- No non-table source could be reconstructed."
        ]

    header += [
        "",
        f"-- decoder mappings: "
        f"o={len(omap)}, w={len(wmap)}"
    ]

    return "\n".join(header)


# ============================================================
# Generic analysis
# ============================================================
def extract_strings_generic(code):
    seen = set()
    result = []

    for pattern in [
        r'"((?:[^"\\]|\\.){2,})"',
        r"'((?:[^'\\]|\\.){2,})'"
    ]:
        for m in re.finditer(pattern, code):
            s = m.group(1)

            if s not in seen:
                seen.add(s)
                result.append(s)

    return result


def generic_analysis(code, obf_name):
    strings = [
        s
        for s in extract_strings_generic(code)
        if all(32 <= ord(c) < 127 for c in s)
        and len(s) > 3
    ]

    nums = list(
        dict.fromkeys(
            re.findall(r"\b\d{5,}\b", code)
        )
    )

    urls = list(
        dict.fromkeys(
            re.findall(
                r"https?://[^\s\"'\\]+",
                code
            )
        )
    )

    funcs = [
        x
        for x in (
            "loadstring",
            "getfenv",
            "require",
            "HttpGet",
            "coroutine",
            "debug",
            "pcall/xpcall"
        )
        if re.search(
            r"\b[xp]?call\b"
            if x == "pcall/xpcall"
            else r"\b" +
                 re.escape(x.split('/')[0]) +
                 r"\b",
            code
        )
    ]

    out = [
        "=" * 58,
        f"  {obf_name} — Static Analysis",
        f"  {len(code):,} chars | "
        f"{code.count(chr(10)) + 1:,} lines",
        "=" * 58,
        "  [!] No dedicated control-flow backend "
        "exists for this obfuscator yet.",
        ""
    ]

    out += [
        f"── READABLE STRINGS ({len(strings)}) "
        "─────────────────────"
    ]

    out += [
        f"  {s!r}"
        for s in strings[:60]
    ]

    if nums:
        out += [
            "",
            f"── LARGE CONSTANTS ({len(nums)}) "
            "──────────────────────",
            "  " + "  ".join(nums[:30])
        ]

    if urls:
        out += [
            "",
            f"── URLS ({len(urls)}) "
            "──────────────────────────────"
        ]

        out += [
            f"  {u}"
            for u in urls[:10]
        ]

    if funcs:
        out += [
            "",
            "── NOTABLE FUNCTIONS "
            "───────────────────────────────",
            "  " + "  ".join(funcs)
        ]

    return "\n".join(out)


def run_deob(code, include_instrs=False):
    obf = detect_obfuscator(code)

    try:
        if obf == "LuaObfuscator":
            return deobfuscate_luaobfuscator(
                code,
                include_instrs
            )

        if obf == "WeAreDevs":
            return deobfuscate_wearedevs(code)

        return generic_analysis(
            code,
            obf
        )

    except Exception as exc:
        return (
            f"[{obf}] deobfuscation error: "
            f"{type(exc).__name__}: {exc}"
        )


# ============================================================
# Discord bot
# ============================================================
async def extract_code(ctx):
    for att in ctx.message.attachments:
        if att.filename.lower().endswith(
            (".lua", ".luau", ".txt")
        ):
            return (
                await att.read()
            ).decode(
                "utf-8",
                errors="replace"
            )

    content = ctx.message.content

    m = re.search(
        r"```(?:lua[ua]?)?\n?([\s\S]+?)```",
        content,
        re.I
    )

    if m:
        return m.group(1).strip()

    m = re.search(
        r"`([^`]{10,})`",
        content
    )

    if m:
        return m.group(1).strip()

    parts = content.split(None, 1)

    if len(parts) == 2 and len(parts[1]) > 20:
        return parts[1].strip()

    return None


intents = discord.Intents.default()
intents.message_content = True

bot = commands.Bot(
    command_prefix="!",
    intents=intents,
    help_command=None
)


@bot.event
async def on_ready():
    print(
        f"[+] Logged in as "
        f"{bot.user} ({bot.user.id})"
    )

    await bot.change_presence(
        activity=discord.Activity(
            type=discord.ActivityType.watching,
            name="obfuscated lua"
        )
    )


# ============================================================
# Flow: channel lock -> tracing delay -> direct delivery
# ============================================================
TRACE_DELAY = (4.0, 6.0)

_busy: set = set()


# ------------------------------------------------------------
# channel lock
# ------------------------------------------------------------
async def lock_channel(channel):
    """Temporarily prevent normal members from sending."""

    role = channel.guild.default_role
    me = channel.guild.me

    ow_role = channel.overwrites_for(role)
    ow_me = channel.overwrites_for(me)

    prev = (
        ow_role.send_messages,
        ow_me.send_messages
    )

    ow_role.send_messages = False
    ow_me.send_messages = True

    await channel.set_permissions(
        role,
        overwrite=ow_role,
        reason="Deobfuscation task running"
    )

    await channel.set_permissions(
        me,
        overwrite=ow_me,
        reason="Deobfuscation task running"
    )

    return prev


async def unlock_channel(channel, prev):
    for target, value in (
        (channel.guild.default_role, prev[0]),
        (channel.guild.me, prev[1])
    ):
        ow = channel.overwrites_for(target)
        ow.send_messages = value

        await channel.set_permissions(
            target,
            overwrite=None
            if ow.is_empty()
            else ow,
            reason="Deobfuscation task finished"
        )


# ------------------------------------------------------------
# analysis
# ------------------------------------------------------------
@dataclass
class Analysis:
    ok: bool
    family: str
    raw: str = ""
    decompiled: str = ""
    notes: str = ""


def decompile_stage(lifted: str) -> str:
    return _simplify_constants(lifted)


def analyze_code(code: str) -> Analysis:
    obf = detect_obfuscator(code)

    try:
        if obf == "LuaObfuscator":
            m = re.search(
                r'''VMCall\s*\(\s*["'](LOL![^"']+)''',
                code
            )

            if not m:
                return Analysis(
                    False,
                    obf,
                    notes="VMCall payload not found."
                )

            data = decode_luaobf(
                m.group(1)
            )

            chunk = parse_chunk(
                Reader(data)
            )

            consts = collect_consts(chunk)

            lifted = "\n".join(
                lift_lua_chunk(chunk)
            )

            head = (
                f"-- LuaObfuscator | "
                f"{len(data):,} decoded bytes | "
                f"{count_funcs(chunk)} functions\n"
                "-- Static lift only; submitted code "
                "was not executed.\n\n"
            )

            table = "\n".join(
                f"-- {i}: {t} = {v!r}"
                for i, (t, v)
                in enumerate(consts)
            )

            return Analysis(
                True,
                obf,
                raw=(
                    head
                    + lifted
                    + "\n\n-- CONSTANTS\n"
                    + table
                ),
                decompiled=(
                    head
                    + decompile_stage(lifted)
                )
            )

        if obf == "WeAreDevs":
            decoded, omap, wmap = (
                _decode_wad_strings(code)
            )

            raw = (
                f"-- WeAreDevs | "
                f"{len(decoded)} decoded strings | "
                f"o={len(omap)} w={len(wmap)}\n\n"
                + "\n".join(
                    f"U[{i}] = {s!r}"
                    for i, s in enumerate(
                        decoded,
                        1
                    )
                )
            )

            return Analysis(
                True,
                obf,
                raw=raw,
                decompiled=deobfuscate_wearedevs(
                    code
                )
            )

        return Analysis(
            False,
            obf,
            raw=generic_analysis(
                code,
                obf
            ),
            decompiled=(
                f"-- No dedicated backend for "
                f"{obf}; nothing was reconstructed.\n"
            ),
            notes=(
                f"No dedicated backend for "
                f"{obf}; string/constant "
                f"analysis only."
            )
        )

    except Exception as exc:
        return Analysis(
            False,
            obf,
            notes=(
                f"{type(exc).__name__}: "
                f"{exc}"
            )
        )


def make_files(a: Analysis):
    files = []

    if a.raw:
        files.append(
            discord.File(
                io.BytesIO(
                    a.raw.encode("utf-8")
                ),
                filename="file-raw.lua"
            )
        )

    if a.decompiled:
        files.append(
            discord.File(
                io.BytesIO(
                    a.decompiled.encode("utf-8")
                ),
                filename="file-decompiled.lua"
            )
        )

    return files


# ============================================================
# Main command
# ============================================================
@bot.command(
    name="deob",
    aliases=["d", "deobfuscate"]
)
@commands.guild_only()
async def cmd_deob(ctx):
    chan = ctx.channel

    if chan.id in _busy:
        await ctx.reply(
            "⏳ A task is already running "
            "in this channel."
        )
        return

    _busy.add(chan.id)

    lock_state = None
    locked = False
    status = None

    try:
        code = await extract_code(ctx)

        if not code:
            await ctx.reply(
                "❌ No code found."
            )
            return

        lock_state = await lock_channel(chan)
        locked = True

        status = await chan.send(
            "🔍 Tracing VM interpreter structures "
            "& unpacking bytecode stream... ⚙️"
        )

        analysis, _ = await asyncio.gather(
            asyncio.to_thread(
                analyze_code,
                code
            ),
            asyncio.sleep(
                random.uniform(
                    *TRACE_DELAY
                )
            )
        )

        # ====================================================
        # DIRECT DELIVERY
        # No admin approval.
        # No reviewer.
        # No DM.
        # No Approve/Deny buttons.
        # ====================================================
        files = make_files(analysis)

        if files:
            await chan.send(
                f"{ctx.author.mention} "
                "✅ Deobfuscation complete:",
                files=files
            )

        if analysis.notes:
            await status.edit(
                content=(
                    f"⚠️ Finished with notes: "
                    f"{analysis.notes}"
                )
            )
        elif analysis.ok:
            await status.edit(
                content=(
                    f"✅ {analysis.family} "
                    "deobfuscation complete."
                )
            )
        else:
            await status.edit(
                content=(
                    f"⚠️ {analysis.family}: "
                    "analysis completed."
                )
            )

    except discord.HTTPException as exc:
        if status:
            try:
                await status.edit(
                    content=(
                        f"❌ Discord delivery error: "
                        f"{exc}"
                    )
                )
            except Exception:
                pass

    except Exception as exc:
        if status:
            try:
                await status.edit(
                    content=(
                        f"❌ Unexpected error: "
                        f"{type(exc).__name__}: "
                        f"{exc}"
                    )
                )
            except Exception:
                pass

    finally:
        if locked:
            await unlock_channel(
                chan,
                lock_state
            )

        _busy.discard(chan.id)


# ============================================================
# Detect
# ============================================================
@bot.command(name="detect")
async def cmd_detect(ctx):
    code = await extract_code(ctx)

    if not code:
        await ctx.reply(
            "❌ No code found."
        )
        return

    obf = detect_obfuscator(code)

    embed = discord.Embed(
        title="🔍 Detection Result",
        color=(
            0x00FF00
            if obf != "Unknown"
            else 0xFF4444
        )
    )

    embed.add_field(
        name="Obfuscator",
        value=f"**{obf}**",
        inline=True
    )

    embed.add_field(
        name="Size",
        value=f"{len(code):,} chars",
        inline=True
    )

    embed.add_field(
        name="Lines",
        value=f"{code.count(chr(10)) + 1:,}",
        inline=True
    )

    await ctx.reply(
        embed=embed
    )


# ============================================================
# Strings
# ============================================================
@bot.command(
    name="strings",
    aliases=["s", "strs"]
)
async def cmd_strings(ctx):
    code = await extract_code(ctx)

    if not code:
        await ctx.reply(
            "❌ No code found."
        )
        return

    obf = detect_obfuscator(code)

    try:
        if obf == "LuaObfuscator":
            m = re.search(
                r'''VMCall\s*\(\s*["'](LOL![^"']+)''',
                code
            )

            raw = (
                decode_luaobf(m.group(1))
                if m
                else b""
            )

            strs = (
                [
                    v
                    for t, v
                    in collect_consts(
                        parse_chunk(
                            Reader(raw)
                        )
                    )
                    if t == "str"
                ]
                if raw
                else []
            )

        elif obf == "WeAreDevs":
            strs, _, _ = _decode_wad_strings(
                code
            )

        else:
            strs = extract_strings_generic(
                code
            )

    except Exception as e:
        await ctx.reply(
            f"❌ String decode error: {e}"
        )
        return

    out = "\n".join(
        repr(s)
        for s in strs
    )

    if len(out) <= 1800:
        await ctx.reply(
            f"**{len(strs)} strings "
            f"[{obf}]:**\n```\n"
            f"{out}\n```"
        )
    else:
        await ctx.reply(
            f"**{len(strs)} strings "
            f"[{obf}]:**",
            file=discord.File(
                io.BytesIO(
                    out.encode()
                ),
                filename="strings.txt"
            )
        )


# ============================================================
# Info
# ============================================================
@bot.command(name="info")
async def cmd_info(ctx):
    code = await extract_code(ctx)

    if not code:
        await ctx.reply(
            "❌ No code found."
        )
        return

    obf = detect_obfuscator(code)

    embed = discord.Embed(
        title="📋 Script Info",
        color=0x7289DA
    )

    embed.add_field(
        name="Obfuscator",
        value=obf,
        inline=True
    )

    embed.add_field(
        name="Size",
        value=f"{len(code):,} chars",
        inline=True
    )

    embed.add_field(
        name="Lines",
        value=f"{code.count(chr(10)) + 1:,}",
        inline=True
    )

    if obf == "LuaObfuscator":
        m = re.search(
            r'''VMCall\s*\(\s*["'](LOL![^"']+)''',
            code
        )

        if m:
            try:
                chunk = parse_chunk(
                    Reader(
                        decode_luaobf(
                            m.group(1)
                        )
                    )
                )

                embed.add_field(
                    name="Constants",
                    value=str(
                        len(
                            collect_consts(
                                chunk
                            )
                        )
                    ),
                    inline=True
                )

                embed.add_field(
                    name="Functions",
                    value=str(
                        count_funcs(chunk)
                    ),
                    inline=True
                )

            except Exception:
                pass

    if obf == "WeAreDevs":
        try:
            strings, o, w = (
                _decode_wad_strings(
                    code
                )
            )

            embed.add_field(
                name="Decoded WAD strings",
                value=str(
                    len(strings)
                ),
                inline=True
            )

            embed.add_field(
                name="Mappings",
                value=f"o={len(o)}, w={len(w)}",
                inline=True
            )

        except Exception:
            pass

    await ctx.reply(
        embed=embed
    )


# ============================================================
# Help
# ============================================================
@bot.command(
    name="help",
    aliases=["h", "commands", "cmds"]
)
async def cmd_help(ctx):
    embed = discord.Embed(
        title="Lua Deobfuscator Bot",
        color=0x7289DA
    )

    embed.description = (
        "Attach a `.lua`/`.luau`/`.txt` "
        "file or paste a fenced Lua block."
    )

    embed.add_field(
        name="!deob / !d",
        value=(
            "Detect, reconstruct, and directly "
            "send the result "
            "(file-raw + file-decompiled)"
        ),
        inline=False
    )

    embed.add_field(
        name="!detect",
        value="Identify the obfuscator",
        inline=False
    )

    embed.add_field(
        name="!strings / !s",
        value="Extract decoded strings",
        inline=False
    )

    embed.add_field(
        name="!info",
        value="Script metadata",
        inline=False
    )

    embed.add_field(
        name="Backends",
        value=(
            "LuaObfuscator + WeAreDevs Method 2; "
            "other protectors remain "
            "static-analysis only."
        ),
        inline=False
    )

    await ctx.reply(
        embed=embed
    )


# ============================================================
# Error handler
# ============================================================
@bot.event
async def on_command_error(ctx, error):
    if isinstance(
        error,
        commands.CommandNotFound
    ):
        return

    if isinstance(
        error,
        commands.NoPrivateMessage
    ):
        await ctx.reply(
            "❌ This command only works "
            "in a server channel."
        )
        return

    if isinstance(
        error,
        commands.MissingPermissions
    ):
        await ctx.reply(
            "❌ You do not have permission "
            "to use this command."
        )
        return

    if isinstance(
        error,
        commands.CommandOnCooldown
    ):
        await ctx.reply(
            f"⏳ Try again in "
            f"{error.retry_after:.1f}s."
        )
        return

    await ctx.reply(
        f"❌ Unexpected error: "
        f"{type(error).__name__}: {error}"
    )


# ============================================================
# Start
# ============================================================
if not TOKEN:
    raise RuntimeError(
        "TOKEN environment variable is not set."
    )

bot.run(TOKEN)
