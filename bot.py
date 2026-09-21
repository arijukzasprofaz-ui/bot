import discord
from discord.ext import commands
import asyncio
import ast
import io
import math
import os
import re
from typing import Optional
 
TOKEN = os.environ.get("TOKEN")
 
# ─── DETECTION ────────────────────────────────────────────────
 
SIGNATURES = [
    # WeAreDevs v1.0.0 has an explicit banner. Keep this ahead of the
    # generic VM detector so WAD code can never be routed to LuaObfuscator.
    ("WeAreDevs",     lambda c: bool(re.search(
        r'wearedevs\s*\.?\s*net\s*/\s*obfuscator|'
        r'wearedevs\s*obfuscator|--\[\[\s*v1\.0\.0\s+https?://wearedevs',
        c[:12000], re.I
    ))),
    ("LuaObfuscator", lambda c: bool(re.search(r'VMCall\s*\(\s*["\']LOL!', c))),
    ("IronBrew3",     lambda c: bool(re.search(r'ironbrew\s*3', c[:2000], re.I)) or "IronBrew3" in c[:1000]),
    ("IronBrew2",     lambda c: bool(re.search(r'ironbrew\s*2', c[:2000], re.I)) or "IronBrew2" in c[:1000]),
    ("IronBrew",      lambda c: bool(re.search(r'ironbrew', c[:2000], re.I))),
    ("Luraph",        lambda c: bool(re.search(r'luraph', c[:3000], re.I)) or "--[[ luraph" in c[:300].lower()),
    ("MoonVeil",      lambda c: bool(re.search(r'moonveil', c[:3000], re.I))),
    ("MoonSec",       lambda c: bool(re.search(r'moonsec', c[:3000], re.I))),
    ("Prometheus",    lambda c: bool(re.search(r'prometheus', c[:3000], re.I))),
    ("SynapseXen",    lambda c: bool(re.search(r'synapse.*xen|xen.*synapse', c[:1000], re.I))),
    ("Hercules",      lambda c: bool(re.search(r'hercules', c[:3000], re.I))),
    ("Boronide",      lambda c: bool(re.search(r'boronide', c[:3000], re.I))),
    ("77fuscator",    lambda c: bool(re.search(r'77fuscator', c[:3000], re.I))),
    ("wYnFuscate",    lambda c: bool(re.search(r'wyn(?:fuscate|obf)', c[:3000], re.I))),
    ("PSU",           lambda c: bool(re.search(r'\bPSU\b', c[:1000]))),
    ("LPS",           lambda c: bool(re.search(r'\bLPS\b', c[:1000]))),
]

def detect_obfuscator(code: str) -> str:
    # Normalize a UTF-8 BOM and a few common paste wrappers first.
    code = code.lstrip("\ufeff").strip()
    # Hard-stop on the explicit WAD banner. This prevents any accidental
    # VMCall/Prometheus keyword elsewhere in the payload from winning.
    if re.search(
        r'--\[\[\s*v1\.0\.0\s+https?://wearedevs\.net/obfuscator\s*\]\]',
        code[:12000], re.I
    ) or re.search(r'wearedevs\.net\s*/\s*obfuscator', code[:12000], re.I):
        return "WeAreDevs"

    for name, check in SIGNATURES:
        try:
            if check(code):
                return name
        except Exception:
            pass
    return "Unknown"
 
# ─── LUAOBFUSCATOR BYTECODE DECODER ──────────────────────────
# Custom RLE-hex: each "pair" is 2 chars.
# If second char == 'Q', first char is repeat count (hex digit) for the NEXT byte.
# Otherwise the pair is a 2-digit hex byte.
 
def decode_luaobf(encoded: str) -> bytes:
    if not encoded.startswith("LOL!"):
        raise ValueError("Missing LOL! prefix")
    payload = encoded[4:]
    out = bytearray()
    repeat_next = None
    i = 0
    if len(payload) % 2:
        raise ValueError("Malformed LOL! payload: odd number of hex characters")

    while i < len(payload):
        pair = payload[i:i+2]
        i += 2
        if pair[1] == 'Q':
            # FIX: was int(pair[0]) — breaks on hex digits A-F
            repeat_next = int(pair[0], 16)
        else:
            bv = int(pair, 16)
            count = repeat_next if repeat_next is not None else 1
            repeat_next = None
            out.extend(bytes([bv]) * count)
    return bytes(out)
 
# ─── BINARY READER ────────────────────────────────────────────
 
class Reader:
    def __init__(self, data: bytes):
        self.d = data
        self.p = 0

    def _need(self, size: int) -> None:
        if size < 0 or self.p + size > len(self.d):
            raise ValueError(
                f"Unexpected end of bytecode at offset {self.p} "
                f"(needed {size} bytes, {len(self.d) - self.p} remaining)"
            )

    def u8(self) -> int:
        self._need(1)
        value = self.d[self.p]
        self.p += 1
        return value

    def u16(self) -> int:
        self._need(2)
        a, b = self.d[self.p:self.p + 2]
        self.p += 2
        return (b << 8) | a

    def u32(self) -> int:
        self._need(4)
        a, b, c, d = self.d[self.p:self.p + 4]
        self.p += 4
        return (d << 24) | (c << 16) | (b << 8) | a

    def f64(self) -> float:
        # Lua-style little-endian IEEE-754 double.
        left = self.u32()
        right = self.u32()
        mantissa = ((right & 0xFFFFF) << 32) | left
        exponent = (right >> 20) & 0x7FF
        sign = -1.0 if (right >> 31) else 1.0

        if exponent == 0:
            if mantissa == 0:
                return -0.0 if sign < 0 else 0.0
            return sign * math.ldexp(mantissa, -1074)

        if exponent == 0x7FF:
            return math.inf * sign if mantissa == 0 else math.nan

        return sign * math.ldexp((1 << 52) | mantissa, exponent - 1023 - 52)

    def string(self, length: Optional[int] = None) -> str:
        if length is None:
            length = self.u32()

        if length == 0:
            return ""

        self._need(length)
        raw = self.d[self.p:self.p + length]
        self.p += length
        return raw.decode("utf-8", errors="replace")

    @staticmethod
    def gbit(value: int, start: int, end: Optional[int] = None) -> int:
        if start < 1:
            raise ValueError("Bit positions are 1-based")

        if end is not None:
            if end < start:
                raise ValueError("end must be >= start")
            width = end - start + 1
            return (value >> (start - 1)) & ((1 << width) - 1)

        return (value >> (start - 1)) & 1

# ─── LUAOBFUSCATOR CHUNK PARSER ───────────────────────────────
 
def parse_chunk(r: Reader, depth: int = 0) -> dict:
    const_count = r.u32()
    consts = []
    for _ in range(const_count):
        t = r.u8()
        if   t == 1: consts.append(('bool', r.u8() != 0))
        elif t == 2: consts.append(('num',  r.f64()))
        elif t == 3: consts.append(('str',  r.string()))
        else:        consts.append(('nil',  None))
 
    r.u8()  # param count
    instr_count = r.u32()
    instrs = []
    for _ in range(instr_count):
        desc = r.u8()
        if Reader.gbit(desc, 1, 1) == 1:
            continue
        typ  = Reader.gbit(desc, 2, 3)
        mask = Reader.gbit(desc, 4, 6)
        op   = r.u16()
        a    = r.u16()
        b = c = None
        if   typ == 0: b = r.u16(); c = r.u16()
        elif typ == 1: b = r.u32()
        elif typ == 2: b = r.u32() - (1 << 16)
        elif typ == 3: b = r.u32() - (1 << 16); c = r.u16()
 
        def resolve(v, bit, _m=mask, _c=consts):
            if v is None:
                return v
            if Reader.gbit(_m, bit, bit) == 1 and isinstance(v, int) and 0 <= v < len(_c):
                return _c[v][1]
            return v
 
        instrs.append((op, resolve(a,1), resolve(b,2), resolve(c,3)))
 
    subs = [parse_chunk(r, depth+1) for _ in range(r.u32())]
    return {'depth': depth, 'consts': consts, 'instrs': instrs, 'subs': subs}
 
def collect_consts(chunk: dict, out: list = None) -> list:
    if out is None: out = []
    out.extend(chunk['consts'])
    for s in chunk['subs']:
        collect_consts(s, out)
    return out
 
def count_funcs(chunk: dict) -> int:
    return 1 + sum(count_funcs(s) for s in chunk['subs'])
 
def format_luaobf(chunk: dict, include_instrs: bool = False) -> str:
    lines = []
    all_c   = collect_consts(chunk)
    strings = [(i, v) for i, (t, v) in enumerate(all_c) if t == 'str']
    numbers = [(i, v) for i, (t, v) in enumerate(all_c) if t == 'num']
 
    lines.append("=" * 58)
    lines.append("  LuaObfuscator.com — Deobfuscated")
    lines.append(f"  {len(all_c)} consts  |  {count_funcs(chunk)} functions")
    lines.append("=" * 58)
 
    lines.append(f"\n── STRINGS ({len(strings)}) ─────────────────────────────")
    for i, v in strings:
        lines.append(f"  [{i:03d}]  {repr(v)}")
 
    lines.append(f"\n── NUMBERS ({len(numbers)}) ─────────────────────────────")
    for i, v in numbers:
        lines.append(f"  [{i:03d}]  {v}")
 
    if include_instrs:
        lines.append("\n── INSTRUCTIONS (main chunk) ────────────────────────")
        for idx, (op, a, b, c) in enumerate(chunk['instrs']):
            lines.append(f"  [{idx:04d}]  OP={op:<4} A={str(a):<22} B={str(b):<22} C={str(c)}")
        for fi, sub in enumerate(chunk['subs']):
            lines.append(f"\n── FUNCTION {fi} ({'  '*sub['depth']}) ─────────────────────────")
            for idx, (op, a, b, c) in enumerate(sub['instrs']):
                lines.append(f"  [{idx:04d}]  OP={op:<4} A={str(a):<22} B={str(b):<22} C={str(c)}")
 
    return "\n".join(lines)
 
# ─── WEAREDEVS ANALYSIS ───────────────────────────────────────
 
def extract_strings_generic(code: str) -> list:
    seen = set()
    results = []
    for pattern in [r'"((?:[^"\\]|\\.){2,})"', r"'((?:[^'\\]|\\.){2,})'"]:
        for m in re.finditer(pattern, code):
            s = m.group(1)
            if s not in seen:
                seen.add(s); results.append(s)
    for m in re.finditer(r'\[=*\[([\s\S]+?)\]=*\]', code):
        s = m.group(1)
        if s not in seen and len(s) > 2:
            seen.add(s); results.append(s[:1000])
    return results
 

# ─── WEAREDEVS v1.0.0 STATIC DECODER (METHOD 2) ─────────────
# This reverses the string-table layer without executing the submitted
# Roblox/Luau program. WAD v1.0.0 uses two small numeric lookup tables and
# custom base64-like alphabets; the VM itself is intentionally left inert.

def _safe_lua_expr(expr: str) -> int | None:
    """Evaluate only integer arithmetic used by WAD's generated constants."""
    expr = expr.strip()
    if not expr or len(expr) > 100:
        return None
    if not re.fullmatch(r'[0-9+\-*/%().\s]+', expr):
        return None
    try:
        tree = ast.parse(expr, mode="eval")
        allowed = (ast.Expression, ast.Constant, ast.BinOp, ast.UnaryOp,
                   ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
                   ast.Mod, ast.Pow, ast.USub, ast.UAdd)
        if any(not isinstance(n, allowed) for n in ast.walk(tree)):
            return None
        value = eval(compile(tree, "<wad-expr>", "eval"),
                     {"__builtins__": {}}, {})
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            return None
        return int(value)
    except Exception:
        return None

def _decode_lua_escapes(value: str) -> str:
    """Decode the numeric/quoted escapes emitted inside WAD string tables."""
    def repl(m):
        token = m.group(1)
        try:
            if token.lower().startswith("x"):
                return chr(int(token[1:], 16))
            return chr(int(token, 10))
        except Exception:
            return m.group(0)
    value = re.sub(r'\\(x[0-9a-fA-F]{2}|[0-9]{1,3})', repl, value)
    return value.replace(r'\"', '"').replace(r"\'", "'").replace(r"\\", "\\").replace(r"\n", "\n").replace(r"\r", "\r").replace(r"\t", "\t")

def _extract_lua_table_body(code: str, name: str, limit: int = 30000) -> str | None:
    m = re.search(r'\blocal\s+' + re.escape(name) + r'\s*=\s*\{', code[:limit])
    if not m:
        return None
    start = m.end()
    depth = 1
    quote = None
    esc = False
    for i in range(start, min(len(code), limit)):
        ch = code[i]
        if quote:
            if esc:
                esc = False
            elif ch == '\\':
                esc = True
            elif ch == quote:
                quote = None
            continue
        if ch in "\"'":
            quote = ch
        elif ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
            if depth == 0:
                return code[start:i]
    return None

def _parse_numeric_lookup_table(body: str) -> dict[str, int]:
    out = {}
    # WAD entries are key=arithmetic-expression. Stop at commas/semicolons
    # outside brackets/strings; the expression itself only contains arithmetic.
    pattern = re.compile(
        r'(?:\[\s*(["\'])(.*?)\1\s*\]|([A-Za-z_][A-Za-z0-9_]*))\s*=\s*'
        r'([0-9+\-*/%().\s]+)(?=[,;]|$)'
    )
    for m in pattern.finditer(body):
        key = m.group(2) if m.group(2) is not None else m.group(3)
        val = _safe_lua_expr(m.group(4))
        if val is not None and len(key) == 1:
            out[key] = val
    return out

def _extract_quoted_strings(body: str) -> list[str]:
    return [
        _decode_lua_escapes(m.group(1))
        for m in re.finditer(r'"((?:\\.|[^"\\])*)"', body)
    ]

def _custom_b64_decode(value: str, alphabet: dict[str, int]) -> str | None:
    """
    Decode the two WAD v1.0.0 string encodings.

    '?' strings use 5 encoded characters -> 4 bytes.
    's' strings use 4 encoded characters -> 3 bytes.
    The generated lookup values are intentionally not a normal 0..63
    alphabet, so this is arithmetic decoding rather than Python's base64.
    """
    if not value or value[:1] not in ("?", "s"):
        return None

    mode = value[0]
    raw = value[1:]
    width = 5 if mode == "?" else 4
    out_width = 4 if mode == "?" else 3

    vals = []
    for ch in raw:
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
        while len(chunk) < width:
            chunk.append(0)

        # Equivalent to the obfuscator's:
        # L = L * 64 + lookup[character]
        n = 0
        for v in chunk:
            n = n * 64 + v

        for shift in range((out_width - 1) * 8, -1, -8):
            out.append((n >> shift) & 255)

        # Padding / incomplete final groups.
        if len(raw[i:i + width]) < width:
            missing = width - len(raw[i:i + width])
            if missing:
                del out[-min(missing, out_width):]

    try:
        return out.decode("utf-8")
    except UnicodeDecodeError:
        return out.decode("latin-1", errors="replace")

def _decode_wad_strings(code: str) -> tuple[list[str], dict[str, int], dict[str, int]]:
    ubody = _extract_lua_table_body(code, "U")
    obody = _extract_lua_table_body(code, "o")
    wbody = _extract_lua_table_body(code, "w")

    strings = _extract_quoted_strings(ubody or "")
    omap = _parse_numeric_lookup_table(obody or "")
    wmap = _parse_numeric_lookup_table(wbody or "")

    decoded = []
    for item in strings:
        if item.startswith("?"):
            val = _custom_b64_decode(item, omap)
        elif item.startswith("s"):
            val = _custom_b64_decode(item, wmap)
        else:
            val = None
        decoded.append(val if val is not None else item)
    return decoded, omap, wmap

def deobfuscate_wad_method2(code: str) -> str:
    decoded, omap, wmap = _decode_wad_strings(code)
    lines = [
        "=" * 62,
        "  WeAreDevs v1.0.0 — Method 2 Static Deobfuscation",
        f"  {len(code):,} chars | {code.count(chr(10))+1:,} lines",
        "=" * 62,
        "",
        f"  String table: {len(decoded)} entries",
        f"  Decoder table o: {len(omap)} mappings",
        f"  Decoder table w: {len(wmap)} mappings",
        "",
        "── DECODED STRING TABLE ─────────────────────────────────",
    ]
    for i, value in enumerate(decoded, 1):
        clean = value.replace("\x00", "\\0")
        lines.append(f"  [{i:03d}] {clean!r}")
    lines += [
        "",
        "── VM STATUS ────────────────────────────────────────────",
        "  The WAD VM was not executed.",
        "  The string/encoding layer was decoded statically.",
        "  Remaining VM/control-flow reconstruction requires a separate",
        "  Luau-aware lifting pass.",
    ]
    return "\n".join(lines)

def analyze_wad(code: str) -> str:
    lines = []
    lines.append("=" * 58)
    lines.append("  WeAreDevs Obfuscator — Analysis")
    lines.append(f"  {len(code):,} chars | {code.count(chr(10))+1:,} lines")
    lines.append("=" * 58)
 
    table_m = re.search(r'local\s+\w+\s*=\s*\{([^}]{20,})\}', code[:8000])
    if table_m:
        raw_entries = re.findall(r'"((?:[^"\\]|\\.)*)"', table_m.group(1))
        lines.append(f"\n── ENCODED STRING TABLE ({len(raw_entries)} entries) ──────")
        for i, e in enumerate(raw_entries[:40]):
            tag = '?-enc' if (e.startswith('?') if e else False) else 'raw  '
            lines.append(f"  [{i:03d}] [{tag}]  {repr(e[:60])}")
        if len(raw_entries) > 40:
            lines.append(f"  ... and {len(raw_entries)-40} more")
 
    all_strs = extract_strings_generic(code)
    readable = [s for s in all_strs
                if all(32 <= ord(c) < 127 for c in s)
                and len(s) > 4
                and not s.startswith('?')
                and s not in ('true', 'false', 'nil')]
    if readable:
        lines.append(f"\n── READABLE STRINGS ({len(readable)}) ──────────────────")
        for s in readable[:40]:
            lines.append(f"  {repr(s)}")
 
    urls = re.findall(r'https?://[^\s"\'\\]+', code)
    if urls:
        lines.append(f"\n── URLS ({len(set(urls))}) ──────────────────────────────")
        for u in list(set(urls))[:10]:
            lines.append(f"  {u}")
 
    return "\n".join(lines)
 
# ─── GENERIC STATIC ANALYSIS ─────────────────────────────────
 
def generic_analysis(code: str, obf_name: str) -> str:
    lines = []
    lines.append("=" * 58)
    lines.append(f"  {obf_name} — Static Analysis")
    lines.append(f"  {len(code):,} chars | {code.count(chr(10))+1:,} lines")
    lines.append("=" * 58)
    lines.append("  [!] Full decompilation not supported for this obfuscator.")
    lines.append("      Showing static analysis only.\n")
 
    all_strs = extract_strings_generic(code)
    readable = [s for s in all_strs
                if all(32 <= ord(c) < 127 for c in s)
                and len(s) > 3
                and s not in ('true', 'false', 'nil', 'and', 'or', 'not', 'end', 'do')]
    lines.append(f"── READABLE STRINGS ({len(readable)}) ─────────────────────")
    for s in readable[:60]:
        lines.append(f"  {repr(s)}")
    if len(readable) > 60:
        lines.append(f"  ... and {len(readable)-60} more")
 
    nums = list(dict.fromkeys(re.findall(r'\b\d{5,}\b', code)))
    if nums:
        lines.append(f"\n── LARGE CONSTANTS ({len(nums)}) ──────────────────────")
        lines.append("  " + "  ".join(nums[:30]))
 
    urls = re.findall(r'https?://[^\s"\'\\]+', code)
    if urls:
        lines.append(f"\n── URLS ({len(set(urls))}) ──────────────────────────────")
        for u in list(set(urls))[:10]:
            lines.append(f"  {u}")
 
    patterns = {
        "loadstring":   bool(re.search(r'\bloadstring\b', code)),
        "getfenv":      bool(re.search(r'\bgetfenv\b', code)),
        "require":      bool(re.search(r'\brequire\b', code)),
        "HttpGet":      bool(re.search(r'\bHttpGet\b', code)),
        "coroutine":    bool(re.search(r'\bcoroutine\b', code)),
        "debug":        bool(re.search(r'\bdebug\b', code)),
        "pcall/xpcall": bool(re.search(r'\b[xp]call\b', code)),
    }
    found = [k for k, v in patterns.items() if v]
    if found:
        lines.append(f"\n── NOTABLE FUNCTIONS ───────────────────────────────")
        lines.append("  " + "  ".join(found))
 
    return "\n".join(lines)
 
# ─── MAIN ROUTER ─────────────────────────────────────────────
 
def run_deob(code: str, include_instrs: bool = False) -> str:
    obf = detect_obfuscator(code)
 
    if obf == "LuaObfuscator":
        m = re.search(r'VMCall\s*\(\s*"(LOL![^"]+)"', code)
        if not m:
            return "[LuaObfuscator] VMCall payload not found in script."
        try:
            raw   = decode_luaobf(m.group(1))
            chunk = parse_chunk(Reader(raw))
            return format_luaobf(chunk, include_instrs)
        except Exception as e:
            return f"[LuaObfuscator] Parse error: {e}"
 
    elif obf == "WeAreDevs":
        try:
            return deobfuscate_wad_method2(code)
        except Exception as e:
            # Never route WAD code through the LuaObfuscator VM decoder.
            return f"[WeAreDevs] Static method 2 failed: {e}\n\n{analyze_wad(code)}"
 
    else:
        return generic_analysis(code, obf)
 
# ─── CODE EXTRACTION ─────────────────────────────────────────
# FIX: original regex was r'(?:lua[ua]?)?\n?([\s\S]+?)' — matched literally
# anything (lazy quantifier with no anchor = 1 char). Added proper backtick
# delimiters and fallback for raw pastes.
 
async def extract_code(ctx) -> str | None:
    # 1. Attachments first
    for att in ctx.message.attachments:
        if att.filename.lower().endswith(('.lua', '.luau', '.txt')):
            return (await att.read()).decode('utf-8', errors='replace')
 
    content = ctx.message.content
 
    # 2. Fenced code block  ```lua ... ``` or ``` ... ```
    m = re.search(r'```(?:lua[ua]?)?\n?([\s\S]+?)```', content, re.IGNORECASE)
    if m:
        return m.group(1).strip()
 
    # 3. Inline backtick  `...`
    m = re.search(r'`([^`]{10,})`', content)
    if m:
        return m.group(1).strip()
 
    # 4. Bare paste — strip the command prefix/name and try the rest
    # e.g. "!deob <code here>"
    parts = content.split(None, 1)
    if len(parts) == 2 and len(parts[1]) > 20:
        return parts[1].strip()
 
    return None
 
# ─── SEND HELPERS ─────────────────────────────────────────────
 
async def send_result(ctx, msg, result: str, filename: str):
    if len(result) <= 1900:
        await msg.edit(content=f"```\n{result[:1890]}\n```")
    else:
        f = discord.File(io.BytesIO(result.encode('utf-8')), filename=filename)
        await msg.delete()
        await ctx.reply("✅ Done — full output attached:", file=f)
 
# ─── BOT SETUP ────────────────────────────────────────────────

intents = discord.Intents.default()
intents.message_content = True

# Disable discord.py's built-in !help command because this bot
# provides its own custom help command below.
bot = commands.Bot(
    command_prefix="!",
    intents=intents,
    help_command=None
)

@bot.event
async def on_ready():
    print(f"[+] Logged in as {bot.user} ({bot.user.id})")
    await bot.change_presence(
        activity=discord.Activity(
            type=discord.ActivityType.watching,
            name="obfuscated lua"
        )
    )
 
# ─── COMMANDS ─────────────────────────────────────────────────
 
@bot.command(name="deob", aliases=["d", "deobfuscate"])
async def cmd_deob(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply(
            "❌ No code found.\n"
            "Attach a `.lua`/`.txt` file, paste in a \\`\\`\\`lua ... \\`\\`\\` block, "
            "or paste raw code after the command."
        )
        return
    obf = detect_obfuscator(code)
    msg = await ctx.reply(f"⏳ Detected **{obf}** — analyzing...")
    result = await asyncio.to_thread(run_deob, code, False)
    await send_result(ctx, msg, result, "deobf.txt")
 
 
@bot.command(name="deob_full", aliases=["df"])
async def cmd_deob_full(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return
    obf = detect_obfuscator(code)
    msg = await ctx.reply(f"⏳ Detected **{obf}** — full decode (includes instructions)...")
    result = await asyncio.to_thread(run_deob, code, True)
    await send_result(ctx, msg, result, "deobf_full.txt")
 
 
@bot.command(name="detect")
async def cmd_detect(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return
    obf = detect_obfuscator(code)
    color = 0x00ff00 if obf != "Unknown" else 0xff4444
    embed = discord.Embed(title="🔍 Detection Result", color=color)
    embed.add_field(name="Obfuscator", value=f"**{obf}**",         inline=True)
    embed.add_field(name="Size",       value=f"{len(code):,} chars", inline=True)
    embed.add_field(name="Lines",      value=f"{code.count(chr(10))+1:,}", inline=True)
    await ctx.reply(embed=embed)
 
 
@bot.command(name="strings", aliases=["s", "strs"])
async def cmd_strings(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return
    obf = detect_obfuscator(code)
 
    if obf == "LuaObfuscator":
        m = re.search(r'VMCall\s*\(\s*["\'](LOL![^"\']+)', code)
        if not m:
            await ctx.reply("❌ No VMCall payload found.")
            return
        try:
            raw   = decode_luaobf(m.group(1))
            chunk = parse_chunk(Reader(raw))
            strs  = [v for t, v in collect_consts(chunk) if t == 'str']
        except Exception as e:
            await ctx.reply(f"❌ Parse error: {e}")
            return
    elif obf == "WeAreDevs":
        try:
            strs, _, _ = _decode_wad_strings(code)
            strs = [s for s in strs if len(s) > 0]
        except Exception as e:
            await ctx.reply(f"❌ WeAreDevs decode error: {e}")
            return
    else:
        all_strs = extract_strings_generic(code)
        strs = [s for s in all_strs
                if all(32 <= ord(c) < 127 for c in s) and len(s) > 3]
 
    out = "\n".join(repr(s) for s in strs)
    header = f"**{len(strs)} strings [{obf}]:**\n"
    if len(out) <= 1800:
        await ctx.reply(f"{header}\n```\n{out}\n```")
    else:
        f = discord.File(io.BytesIO(out.encode('utf-8')), filename="strings.txt")
        await ctx.reply(header, file=f)
 
 
@bot.command(name="info")
async def cmd_info(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return
    obf = detect_obfuscator(code)
    embed = discord.Embed(title="📋 Script Info", color=0x7289DA)
    embed.add_field(name="Obfuscator", value=obf,                              inline=True)
    embed.add_field(name="Size",       value=f"{len(code):,} chars",           inline=True)
    embed.add_field(name="Lines",      value=f"{code.count(chr(10))+1:,}",     inline=True)
 
    all_strs = extract_strings_generic(code)
    readable = [s for s in all_strs if all(32 <= ord(c) < 127 for c in s) and len(s) > 3]
    embed.add_field(name="Readable strings", value=str(len(readable)), inline=True)
 
    urls = re.findall(r'https?://[^\s"\'\\]+', code)
    if urls:
        embed.add_field(name="URLs", value="\n".join(list(set(urls))[:5]), inline=False)
 
    if obf == "WeAreDevs":
        try:
            wad_strings, omap, wmap = _decode_wad_strings(code)
            embed.add_field(name="Decoded WAD strings", value=str(len(wad_strings)), inline=True)
            embed.add_field(name="Decoder mappings", value=f"o={len(omap)}, w={len(wmap)}", inline=True)
        except Exception:
            pass

    if obf == "LuaObfuscator":
        m = re.search(r'VMCall\s*\(\s*"(LOL![^"]+)"', code)
        if m:
            try:
                raw   = decode_luaobf(m.group(1))
                chunk = parse_chunk(Reader(raw))
                all_c = collect_consts(chunk)
                embed.add_field(name="Constants",     value=str(len(all_c)),         inline=True)
                embed.add_field(name="Functions",     value=str(count_funcs(chunk)), inline=True)
                embed.add_field(name="Decoded bytes", value=f"{len(raw):,}",         inline=True)
            except Exception:
                pass
 
    await ctx.reply(embed=embed)
 
 
@bot.command(name="help", aliases=["h", "commands", "cmds"])
async def cmd_help(ctx):
    embed = discord.Embed(
        title="Lua Deobfuscator Bot",
        color=0x7289DA,
        description=(
            "Attach a `.lua`/`.luau`/`.txt` file **or** paste code in a "
            "\\`\\`\\`lua ... \\`\\`\\` block."
        )
    )
    embed.add_field(name="!deob / !d",       value="Auto-detect & analyze",                    inline=False)
    embed.add_field(name="!deob_full / !df", value="Full mode (LuaObfuscator: + instructions)", inline=False)
    embed.add_field(name="!detect",          value="Identify the obfuscator only",              inline=False)
    embed.add_field(name="!strings / !s",    value="Extract string constants",                  inline=False)
    embed.add_field(name="!info",            value="Script metadata & stats",                   inline=False)
    embed.add_field(
        name="Supported obfuscators",
        value=(
            "✅ **LuaObfuscator** — full bytecode parse\n"
            "🔍 **WeAreDevs** — string table + static analysis\n"
            "🔍 **Luraph · IronBrew 1/2/3 · MoonSec · MoonVeil**\n"
            "🔍 **Prometheus · SynapseXen · Hercules · Boronide**\n"
            "🔍 **77fuscator · wYnFuscate · PSU · LPS**\n"
            "*(🔍 = static analysis: strings, URLs, patterns)*"
        ),
        inline=False
    )
    await ctx.reply(embed=embed)
 
 
@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    if isinstance(error, commands.MissingPermissions):
        await ctx.reply("❌ You do not have permission to use this command.")
        return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.reply(f"⏳ Try again in {error.retry_after:.1f}s.")
        return
    await ctx.reply(f"❌ Unexpected error: {type(error).__name__}: {error}")


if not TOKEN:
    raise RuntimeError("TOKEN environment variable is not set.")

bot.run(TOKEN)
