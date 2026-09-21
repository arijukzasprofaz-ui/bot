import discord
from discord.ext import commands
import asyncio
import ast
import base64
import io
import math
import os
import random
import re
import struct
from dataclasses import dataclass, field
from typing import Optional

TOKEN = os.environ.get("TOKEN")

# ============================================================
# Hard limits for Luraph analysis
# ============================================================
LURAPH_MAX_INPUT    = 2 * 1024 * 1024   # 2 MB input cap
LURAPH_BLOB_WIN     = 500_000           # blob-search window
LURAPH_DISPATCH_WIN = 300_000           # dispatch-table search window

# ============================================================
# Lua 5.1 opcode table — shared by LuaObfuscator + Luraph
# ============================================================
LUA51_OPS = {
    0:  "MOVE",      1:  "LOADK",     2:  "LOADBOOL",  3:  "LOADNIL",
    4:  "GETUPVAL",  5:  "GETGLOBAL", 6:  "GETTABLE",  7:  "SETGLOBAL",
    8:  "SETUPVAL",  9:  "SETTABLE",  10: "NEWTABLE",   11: "SELF",
    12: "ADD",       13: "SUB",       14: "MUL",         15: "DIV",
    16: "MOD",       17: "POW",       18: "UNM",         19: "NOT",
    20: "LEN",       21: "CONCAT",    22: "JMP",         23: "EQ",
    24: "LT",        25: "LE",        26: "TEST",        27: "TESTSET",
    28: "CALL",      29: "TAILCALL",  30: "RETURN",      31: "FORLOOP",
    32: "FORPREP",   33: "TFORLOOP",  34: "SETLIST",     35: "CLOSE",
    36: "CLOSURE",   37: "VARARG",
}

# ============================================================
# Luraph IR dataclasses
# ============================================================

@dataclass
class LuraphInstr:
    """One decoded VM instruction in the Luraph IR."""
    pc:          int
    raw_opcode:  int
    opcode_name: str
    a:           Optional[int] = None
    b:           object        = None
    c:           object        = None
    bx:          Optional[int] = None
    sbx:         Optional[int] = None
    const_refs:  list          = field(default_factory=list)
    target_addr: Optional[int] = None


@dataclass
class LuraphProto:
    """A Lua function prototype recovered from bytecode."""
    index:         int
    depth:         int
    param_count:   int  = 0
    is_vararg:     bool = False
    max_stack:     int  = 0
    instructions:  list = field(default_factory=list)
    constants:     list = field(default_factory=list)
    upvalue_count: int  = 0
    protos:        list = field(default_factory=list)
    source_name:   str  = ""


@dataclass
class BasicBlock:
    """A basic block in the intra-procedural control-flow graph."""
    id:           int
    start_pc:     int
    end_pc:       int
    instrs:       list = field(default_factory=list)
    successors:   list = field(default_factory=list)
    predecessors: list = field(default_factory=list)


@dataclass
class LuraphResult:
    """Aggregated output from the full Luraph staged analysis pipeline."""
    detected:          bool = False
    version_hint:      str  = "unknown"
    stages:            list = field(default_factory=list)
    bootstrap_source:  str  = ""
    data_blobs:        list = field(default_factory=list)
    all_strings:       list = field(default_factory=list)
    prototypes:        list = field(default_factory=list)
    unknown_opcodes:   set  = field(default_factory=set)
    vm_opcode_map:     dict = field(default_factory=dict)
    bytecode_size:     int  = 0
    instruction_count: int  = 0
    constant_count:    int  = 0
    string_count:      int  = 0
    proto_count:       int  = 0
    notes:             list = field(default_factory=list)
    raw_output:        str  = ""
    decompiled_output: str  = ""


# ============================================================
# Detection
# ============================================================

def _luraph_quick_check(code: str) -> bool:
    """Fast Luraph check used by SIGNATURES tuple."""
    if "luraph" in code[:5000].lower():
        return True
    s = code[:120_000]
    return (
        bool(re.search(r'\[\s*\d+\s*\]\s*=\s*function', s))
        and bool(re.search(r'loadstring\s*\(', s))
    )


SIGNATURES = [
    ("WeAreDevs",     lambda c: bool(re.search(
        r"wearedevs\s*\.?\s*net\s*/\s*obfuscator|"
        r"wearedevs\s*obfuscator|--\[\[\s*v1\.0\.0\s+https?://wearedevs",
        c[:12000], re.I))),
    ("LuaObfuscator", lambda c: bool(re.search(r'''VMCall\s*\(\s*["']LOL!''', c))),
    ("Luraph",        lambda c: _luraph_quick_check(c)),
    ("IronBrew3",     lambda c: bool(re.search(r"ironbrew\s*3", c[:2000], re.I)) or "IronBrew3" in c[:1000]),
    ("IronBrew2",     lambda c: bool(re.search(r"ironbrew\s*2", c[:2000], re.I)) or "IronBrew2" in c[:1000]),
    ("IronBrew",      lambda c: bool(re.search(r"ironbrew", c[:2000], re.I))),
    ("MoonVeil",      lambda c: bool(re.search(r"moonveil", c[:3000], re.I))),
    ("MoonSec",       lambda c: bool(re.search(r"moonsec", c[:3000], re.I))),
    ("Prometheus",    lambda c: bool(re.search(r"prometheus", c[:3000], re.I))),
    ("SynapseXen",    lambda c: bool(re.search(r"synapse.*xen|xen.*synapse", c[:1000], re.I))),
    ("Hercules",      lambda c: bool(re.search(r"hercules", c[:3000], re.I))),
    ("Boronide",      lambda c: bool(re.search(r"boronide", c[:3000], re.I))),
    ("77fuscator",    lambda c: bool(re.search(r"77fuscator", c[:3000], re.I))),
    ("wYnFuscate",    lambda c: bool(re.search(r"wyn(?:fuscate|obf)", c[:3000], re.I))),
    ("PSU",           lambda c: bool(re.search(r"\bPSU\b", c[:1000]))),
    ("LPS",           lambda c: bool(re.search(r"\bLPS\b", c[:1000]))),
]


def detect_obfuscator(code: str) -> str:
    code = code.lstrip("\ufeff").strip()
    if re.search(r"--\[\[\s*v1\.0\.0\s+https?://wearedevs\.net/obfuscator\s*\]\]", code[:12000], re.I):
        return "WeAreDevs"
    if re.search(r"wearedevs\.net\s*/\s*obfuscator", code[:12000], re.I):
        return "WeAreDevs"
    for name, check in SIGNATURES:
        try:
            if check(code):
                return name
        except Exception:
            pass
    return "Unknown"


# ============================================================
# Shared utility helpers
# ============================================================

def _lua_literal(v):
    if v is None:        return "nil"
    if isinstance(v, bool): return "true" if v else "false"
    if isinstance(v, str):  return repr(v)
    if isinstance(v, float) and v.is_integer(): return str(int(v))
    return repr(v)

def _reg(v):
    return f"r{v}" if isinstance(v, int) else _lua_literal(v)

def _safe_expr(expr):
    if not re.fullmatch(r"[0-9+\-*/%().\s]+", expr or ""):
        return None
    try:
        tree = ast.parse(expr, mode="eval")
        allowed = (
            ast.Expression, ast.Constant, ast.BinOp, ast.UnaryOp,
            ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
            ast.Mod, ast.Pow, ast.USub, ast.UAdd,
        )
        if any(not isinstance(n, allowed) for n in ast.walk(tree)):
            return None
        return eval(compile(tree, "<expr>", "eval"), {"__builtins__": {}}, {})
    except Exception:
        return None

def _simplify_constants(text):
    def repl(m):
        v = _safe_expr(m.group(0))
        return str(v) if isinstance(v, (int, float)) else m.group(0)
    return re.sub(r"\b\d+(?:\s*[+\-*/%]\s*\d+)+\b", repl, text)


# ============================================================
# ── LURAPH STAGED ANALYSIS BACKEND ───────────────────────────
# ============================================================

# ── Stage 1: detailed detection ──────────────────────────────

def _luraph_stage1_detect(code: str) -> tuple:
    """
    Returns (detected: bool, version_hint: str, features: list[str]).
    Analyses structural indicators without executing any code.
    """
    features    = []
    version_hint = "unknown"
    sample      = code[:LURAPH_DISPATCH_WIN]

    # Header comment — most reliable indicator
    hdr = re.search(r'--\[\[\s*luraph[^\]]*\]\]', code[:2000], re.I)
    if hdr:
        features.append("header_comment")
        ver = re.search(r'v?(\d+\.\d+(?:\.\d+)?)', hdr.group(), re.I)
        if ver:
            version_hint = ver.group(1)

    if "luraph" in code[:5000].lower():
        features.append("name_in_code")

    # Numeric VM dispatch table
    dispatch_nums = re.findall(r'\[\s*(\d+)\s*\]\s*=\s*function', sample)
    if len(dispatch_nums) >= 4:
        features.append(f"dispatch_table:{len(dispatch_nums)}_opcodes")
        if len(dispatch_nums) >= 20:
            features.append("full_vm_dispatch")
        if version_hint == "unknown":
            version_hint = (">=2.x" if len(dispatch_nums) >= 25 else "1.x") + " (inferred)"

    # Large base64-like blobs
    if re.findall(r'"[A-Za-z0-9+/=]{200,}"', sample):
        features.append("base64_blob")

    # Raw long-string blobs
    raw_blobs = re.findall(r'\[=*\[.{100,}?\]=*\]', sample, re.S)
    if raw_blobs:
        features.append(f"raw_blob:{len(raw_blobs)}")

    # Numeric-escape heavy strings (e.g. "\78\56\12...")
    if re.findall(r'"(?:\\[0-9]{1,3}){50,}"', sample):
        features.append("numeric_escape_blob")

    # Anti-tamper / environment checks
    env = set(re.findall(
        r'\b(getfenv|debug\.getinfo|debug\.sethook|debug\.getupvalue|newproxy)\b', sample))
    if env:
        features.append(f"env_protection:{','.join(sorted(env))}")

    # XOR / bit ops
    if re.search(r'\bbit\b[.\w]*bxor|\bbxor\b', sample):
        features.append("xor_bitops")

    # loadstring bootstrap
    if re.search(r'\bloadstring\s*\(', sample):
        features.append("loadstring_bootstrap")

    detected = bool(
        "name_in_code" in features
        or "header_comment" in features
        or ("full_vm_dispatch" in features
            and any('blob' in f for f in features))
    )
    return detected, version_hint, features


# ── Stage 2: bootstrap / wrapper extraction ───────────────────

def _luraph_stage2_bootstrap(code: str) -> str:
    """
    Return a human-readable skeleton of the Luraph bootstrap layer.
    Large encoded blobs are replaced with placeholders so the VM
    structure is visible without the noise.
    """
    skeleton = re.sub(r'"[A-Za-z0-9+/=]{200,}"', '"[ENCODED_BLOB]"',
                      code[:LURAPH_DISPATCH_WIN])
    skeleton = re.sub(r'\[=*\[.{200,}?\]=*\]', '[[LONG_RAW_STRING]]',
                      skeleton, flags=re.S)
    return skeleton[:20_000]


# ── Stage 3: VM opcode dispatch table ─────────────────────────

def _infer_opcode_from_body(body: str) -> str:
    """
    Heuristically map a VM handler body to a Lua 5.1-like opcode name.
    Unknown semantics are returned as 'UNKNOWN' rather than invented.
    """
    b = body.lower()
    checks = [
        (r'\.\.', 'CONCAT'),
        (r'=\s*-\s*(?:stk|s|reg)\[', 'UNM'),
        (r'=\s*not\s+', 'NOT'),
        (r'=\s*#(?:stk|s|reg)\[', 'LEN'),
        (r'\*\s*(?:stk|s|reg)\[', 'MUL'),
        (r'/\s*(?:stk|s|reg)\[', 'DIV'),
        (r'%\s*(?:stk|s|reg)\[', 'MOD'),
        (r'\^\s*(?:stk|s|reg)\[|math\.pow', 'POW'),
        (r'(?:stk|s|reg)\[a\]\s*=\s*(?:stk|s|reg)\[b\](?!\s*[+\-*/])', 'MOVE'),
        (r'=\s*kst?\[|=\s*const\[|=\s*k\[bx?\]', 'LOADK'),
        (r'=\s*(true|false)\b', 'LOADBOOL'),
        (r'=\s*nil\b', 'LOADNIL'),
        (r'_?env\[.*\]\s*=|_G\s*\[.*\]\s*=', 'SETGLOBAL'),
        (r'=\s*_?env\[|=\s*_G\s*\[', 'GETGLOBAL'),
        (r'(?:stk|s)\[a\]\s*=\s*(?:stk|s)\[b\]\[', 'GETTABLE'),
        (r'(?:stk|s)\[a\]\[', 'SETTABLE'),
        (r'=\s*\{\}', 'NEWTABLE'),
        (r'\bself\b', 'SELF'),
        (r'tailcall|tail.*call', 'TAILCALL'),
        (r'\bcall\b|(?:stk|s)\[a\]\s*\(', 'CALL'),
        (r'\breturn\b', 'RETURN'),
        (r'forprep|prep.*for', 'FORPREP'),
        (r'forloop|loop.*for|step|limit', 'FORLOOP'),
        (r'tforloop|generic.*for', 'TFORLOOP'),
        (r'testset', 'TESTSET'),
        (r'\btest\b', 'TEST'),
        (r'closure|function|proto\[', 'CLOSURE'),
        (r'vararg|\.\.\.', 'VARARG'),
        (r'setlist', 'SETLIST'),
        (r'close.*upval', 'CLOSE'),
        (r'pc\s*=\s*pc\s*\+|pc\s*\+=', 'JMP'),
        (r'<=', 'LE'),
        (r'<(?!=)', 'LT'),
        (r'==', 'EQ'),
        (r'upval|upv\[', 'GETUPVAL'),
        (r'\+\s*(?:stk|s|reg)\[', 'ADD'),
        (r'-\s*(?:stk|s|reg)\[', 'SUB'),
    ]
    for pattern, name in checks:
        if re.search(pattern, b):
            return name
    return 'UNKNOWN'


def _luraph_stage3_dispatch(code: str) -> dict:
    """
    Stage 3: Parse the Luraph VM opcode dispatch table.
    Returns {opcode_int: inferred_name_str}.
    Entries that cannot be semantically classified stay as 'UNKNOWN'.
    """
    opcode_map: dict = {}
    sample = code[:LURAPH_DISPATCH_WIN]

    pattern = re.compile(
        r'\[\s*(\d+)\s*\]\s*=\s*function[^)]*\)'
        r'([\s\S]{1,800}?)(?=\[\s*\d+\s*\]\s*=\s*function|\Z)',
        re.M,
    )
    for m in pattern.finditer(sample):
        op_num = int(m.group(1))
        body   = m.group(2)
        name   = _infer_opcode_from_body(body)
        opcode_map[op_num] = name

    return opcode_map


# ── Stage 4: blob extraction ──────────────────────────────────

def _luraph_stage4_blobs(code: str) -> list:
    """
    Stage 4: Locate candidate encoded data blobs in the Luraph source.
    Sorted by size (largest first); capped at 12 entries.
    """
    blobs: list = []
    area = code[:LURAPH_BLOB_WIN]

    # Long base64-style quoted strings
    for m in re.finditer(r'"([A-Za-z0-9+/=]{100,})"', area):
        blobs.append({'type': 'quoted_b64', 'raw': m.group(1),
                      'offset': m.start(), 'size': len(m.group(1))})

    # Lua raw long strings  [[ ... ]]  or  [=*[ ... ]=*]
    for m in re.finditer(r'\[=*\[([\s\S]{50,}?)\]=*\]', area):
        blobs.append({'type': 'raw_long_str', 'raw': m.group(1),
                      'offset': m.start(), 'size': len(m.group(1))})

    # Numeric-escape strings   "\78\56\12..."
    for m in re.finditer(r'"((?:\\[0-9]{1,3}){30,})"', area):
        nums_str = m.group(1)
        try:
            nums = re.findall(r'\\([0-9]{1,3})', nums_str)
            decoded_bytes = bytes(min(int(n), 255) for n in nums)
            blobs.append({'type': 'numeric_escape', 'raw': decoded_bytes,
                          'offset': m.start(), 'size': len(decoded_bytes)})
        except Exception:
            pass

    blobs.sort(key=lambda b: b.get('size', 0), reverse=True)
    return blobs[:12]


def _luraph_try_decode(blob: dict) -> dict:
    """
    Try to decode a blob with common encodings.
    Adds 'decoded' (bytes|None), 'encoding' (str), 'is_lua_bytecode' (bool).
    Never guesses: reports what it found or nothing.
    """
    result = {**blob, 'decoded': None, 'encoding': 'none', 'is_lua_bytecode': False}
    raw = blob.get('raw')

    if raw is None:
        return result

    # Already bytes (numeric_escape blobs)
    if isinstance(raw, (bytes, bytearray)):
        data = bytes(raw)
        result['decoded'] = data
        result['encoding'] = 'raw_bytes'
        if data[:4] == b'\x1bLua':
            result['is_lua_bytecode'] = True
            result['encoding'] = 'raw_lua51'
        return result

    s = str(raw)

    # Standard base64
    for label, fn in [
        ('base64',      lambda x: base64.b64decode(x + '==')),
        ('urlsafe_b64', lambda x: base64.urlsafe_b64decode(x + '==')),
    ]:
        try:
            dec = fn(s)
            if len(dec) < 4:
                continue
            result['decoded']  = dec
            result['encoding'] = label
            if dec[:4] == b'\x1bLua':
                result['is_lua_bytecode'] = True
                result['encoding'] = f'{label}+lua51'
            return result
        except Exception:
            continue

    # Latin-1 raw bytes (common for embedded string payloads)
    try:
        as_bytes = s.encode('latin-1')
        result['decoded']  = as_bytes
        result['encoding'] = 'latin1_raw'
        if as_bytes[:4] == b'\x1bLua':
            result['is_lua_bytecode'] = True
            result['encoding'] = 'latin1_lua51'
        return result
    except Exception:
        pass

    return result


def _luraph_try_xor_keys(data: bytes, code: str) -> Optional[bytes]:
    """
    Stage 4 bonus: try numeric XOR keys visible in the bootstrap.
    Returns decoded bytes if a key produces valid Lua 5.1 bytecode,
    otherwise None.  Never invents keys that are not present in the source.
    """
    # Extract small numeric table literals {N, N, N, ...} (possible XOR key)
    for m in re.finditer(r'\{(\s*\d+(?:\s*,\s*\d+){3,63})\s*\}', code[:200_000]):
        try:
            nums = [int(n.strip()) for n in m.group(1).split(',')]
            if not all(0 <= n <= 255 for n in nums):
                continue
            key   = bytes(nums)
            xored = bytes(b ^ key[i % len(key)] for i, b in enumerate(data))
            if xored[:4] == b'\x1bLua':
                return xored
        except Exception:
            continue
    return None


# ── Stage 5: string recovery ──────────────────────────────────

def _luraph_stage5_strings(code: str, decoded_blobs: list) -> list:
    """
    Stage 5: Extract readable strings from every recoverable layer.
    Only genuinely recovered strings are included; nothing is invented.
    """
    seen: set = set()
    out:  list = []

    def add(s: str):
        if s and len(s) >= 2 and s not in seen:
            seen.add(s)
            out.append(s)

    # Quoted strings in the Lua source
    for m in re.finditer(r'"((?:[^"\\]|\\.){2,})"', code[:400_000]):
        add(m.group(1))
    for m in re.finditer(r"'((?:[^'\\]|\\.){2,})'", code[:400_000]):
        add(m.group(1))

    # Printable ASCII runs from decoded binary blobs
    for blob in decoded_blobs:
        data = blob.get('decoded')
        if not isinstance(data, (bytes, bytearray)):
            continue
        for m in re.finditer(rb'[\x20-\x7e]{4,}', bytes(data)):
            try:
                add(m.group(0).decode('ascii'))
            except Exception:
                pass

    return out


# ============================================================
# ── Lua 5.1 standard bytecode parser (for embedded bytecode) ─
# ============================================================

def _read_lua51_string(r: 'Reader') -> str:
    """
    Read a Lua 5.1 TString from bytecode.
    Format: u32 size (including null terminator) + bytes.
    size == 0 means the nil string.
    """
    sz = r.u32()
    if sz == 0:
        return ""
    r._need(sz)
    raw  = r.d[r.p:r.p + sz]
    r.p += sz
    # Strip trailing null terminator
    return raw.rstrip(b'\x00').decode('utf-8', errors='replace')


def _parse_lua51_header(r: 'Reader') -> dict:
    """Validate and skip the 12-byte Lua 5.1 bytecode file header."""
    if r.d[r.p:r.p + 4] != b'\x1bLua':
        raise ValueError("Not a Lua 5.1 bytecode file (bad magic bytes)")
    r.p += 4
    return {
        'version':  r.u8(),   # 0x51
        'format':   r.u8(),   # 0x00
        'endian':   r.u8(),   # 1 = LE
        'int_sz':   r.u8(),   # usually 4
        'sizet_sz': r.u8(),   # usually 4 or 8
        'instr_sz': r.u8(),   # usually 4
        'num_sz':   r.u8(),   # usually 8
        'integral': r.u8(),   # 0
    }


def _decode_lua51_instrs(raw: list, consts: list) -> list:
    """
    Decode standard Lua 5.1 packed instruction words into LuraphInstr objects.

    Standard bit layout (32-bit word):
      bits  0-5  : opcode  (6 bits)
      bits  6-13 : A       (8 bits)
      bits 14-22 : C       (9 bits)
      bits 23-31 : B       (9 bits)
      bits 14-31 : Bx      (18 bits, unsigned)
      bits 14-31 : sBx     (18 bits, signed: value - 131071)

    B and C ≥ 256 mean "constant at index (value − 256)" in the const pool.
    """
    out: list = []
    for pc, word in enumerate(raw):
        opcode = word & 0x3F
        a      = (word >> 6)  & 0xFF
        c      = (word >> 14) & 0x1FF
        b      = (word >> 23) & 0x1FF
        bx     = (word >> 14) & 0x3FFFF
        sbx    = bx - 131071

        name       = LUA51_OPS.get(opcode, f'UNKNOWN_{opcode}')
        b_val      = b
        c_val      = c
        const_refs = []

        # LOADK / GETGLOBAL / SETGLOBAL reference constants via Bx
        if name in ('LOADK', 'GETGLOBAL', 'SETGLOBAL'):
            if 0 <= bx < len(consts):
                b_val = consts[bx][1]
                const_refs.append(('Bx', bx))
        else:
            # B ≥ 256 → constant index b-256
            if b >= 256:
                idx = b - 256
                if 0 <= idx < len(consts):
                    b_val = consts[idx][1]
                    const_refs.append(('B', idx))
            # C ≥ 256 → constant index c-256
            if c >= 256:
                idx = c - 256
                if 0 <= idx < len(consts):
                    c_val = consts[idx][1]
                    const_refs.append(('C', idx))

        # Compute jump target for branch/loop instructions
        target = None
        if name in ('JMP', 'FORLOOP', 'FORPREP', 'TFORLOOP'):
            target = pc + 1 + sbx

        out.append(LuraphInstr(
            pc=pc, raw_opcode=opcode, opcode_name=name,
            a=a, b=b_val, c=c_val, bx=bx, sbx=sbx,
            const_refs=const_refs, target_addr=target,
        ))
    return out


def _parse_lua51_chunk(r: 'Reader', hdr: dict, depth: int = 0, idx: int = 0) -> LuraphProto:
    """
    Recursively parse a Lua 5.1 function prototype from a Reader.
    Reads instructions, constants, sub-protos, and debug info.
    Debug info (source lines, locals, upvalue names) is consumed but not stored.
    """
    source    = _read_lua51_string(r)
    _line_def = r.u32()     # line_defined
    _lline    = r.u32()     # last_line_defined
    nups      = r.u8()      # upvalue count
    nparams   = r.u8()      # parameter count
    is_vararg = r.u8()      # vararg flags
    maxstack  = r.u8()      # max stack size

    # ── Instructions ──────────────────────────────────────────
    n_inst    = r.u32()
    raw_words = [r.u32() for _ in range(n_inst)]

    # ── Constants ─────────────────────────────────────────────
    n_consts  = r.u32()
    consts: list = []
    for _ in range(n_consts):
        t = r.u8()
        if t == 0:
            consts.append(('nil',  None))
        elif t == 1:
            consts.append(('bool', r.u8() != 0))
        elif t == 3:
            consts.append(('num',  r.f64()))
        elif t == 4:
            consts.append(('str',  _read_lua51_string(r)))
        else:
            consts.append(('unknown', None))

    # ── Sub-prototypes ─────────────────────────────────────────
    n_protos   = r.u32()
    sub_protos = [_parse_lua51_chunk(r, hdr, depth + 1, i) for i in range(n_protos)]

    # ── Debug info (consume, don't store) ─────────────────────
    n_lines = r.u32()
    r.p    += n_lines * 4

    n_locals = r.u32()
    for _ in range(n_locals):
        _read_lua51_string(r)
        r.p += 8          # startpc (u32) + endpc (u32)

    n_upvals = r.u32()
    for _ in range(n_upvals):
        _read_lua51_string(r)

    instrs = _decode_lua51_instrs(raw_words, consts)

    return LuraphProto(
        index=idx, depth=depth,
        param_count=nparams, is_vararg=bool(is_vararg),
        max_stack=maxstack, instructions=instrs,
        constants=consts, upvalue_count=nups,
        protos=sub_protos,
        source_name=source or f"@lua51_d{depth}_f{idx}",
    )


# ============================================================
# ── CFG builder ───────────────────────────────────────────────
# ============================================================

def _build_cfg(proto: LuraphProto) -> list:
    """
    Build a list of BasicBlock objects with successor/predecessor edges
    for the given prototype.  Does not modify the prototype itself.
    """
    instrs = proto.instructions
    if not instrs:
        return []

    COND_OPS = {'EQ', 'LT', 'LE', 'TEST', 'TESTSET'}
    JUMP_OPS = {'JMP', 'FORPREP', 'FORLOOP', 'TFORLOOP'}
    TERM_OPS = {'RETURN', 'TAILCALL'}

    # ── Identify block leaders ────────────────────────────────
    leaders: set = {0}
    for i, ins in enumerate(instrs):
        nm = ins.opcode_name
        if nm in JUMP_OPS | COND_OPS | TERM_OPS:
            if i + 1 < len(instrs):
                leaders.add(i + 1)
        # Conditionals skip one instruction when taken
        if nm in COND_OPS:
            if i + 2 < len(instrs):
                leaders.add(i + 2)
        # Explicit jump targets
        if nm in JUMP_OPS and ins.target_addr is not None:
            t = ins.target_addr
            if 0 <= t < len(instrs):
                leaders.add(t)

    sorted_leaders = sorted(leaders)
    blocks: list   = []
    for bi, leader in enumerate(sorted_leaders):
        end = (sorted_leaders[bi + 1] - 1
               if bi + 1 < len(sorted_leaders)
               else len(instrs) - 1)
        blocks.append(BasicBlock(
            id=bi, start_pc=leader, end_pc=end,
            instrs=instrs[leader: end + 1],
        ))

    # ── pc → block id map ────────────────────────────────────
    pc2b: dict = {}
    for bl in blocks:
        for p in range(bl.start_pc, bl.end_pc + 1):
            pc2b[p] = bl.id

    def edge(src: int, dst_pc: int):
        if dst_pc in pc2b:
            dst = pc2b[dst_pc]
            if dst not in blocks[src].successors:
                blocks[src].successors.append(dst)
            if src not in blocks[dst].predecessors:
                blocks[dst].predecessors.append(src)

    # ── Wire edges ────────────────────────────────────────────
    for bl in blocks:
        if not bl.instrs:
            continue
        last = bl.instrs[-1]
        nm   = last.opcode_name

        if nm in TERM_OPS:
            pass  # no successors
        elif nm == 'JMP':
            if last.target_addr is not None:
                edge(bl.id, last.target_addr)
        elif nm == 'FORPREP':
            # FORPREP jumps ahead to skip the loop body on prep
            if last.target_addr is not None:
                edge(bl.id, last.target_addr)
        elif nm in ('FORLOOP', 'TFORLOOP'):
            edge(bl.id, bl.end_pc + 1)           # fall-through (loop exits)
            if last.target_addr is not None:
                edge(bl.id, last.target_addr)    # loop-back
        elif nm in COND_OPS:
            # Condition true → skip next instr (pc+2); false → fall to pc+1
            edge(bl.id, bl.end_pc + 1)
            edge(bl.id, bl.end_pc + 2)
        else:
            edge(bl.id, bl.end_pc + 1)

    return blocks


# ============================================================
# ── Instruction lifter: LuraphInstr → readable Lua pseudocode
# ============================================================

def _lift_instr(ins: LuraphInstr) -> str:
    """
    Produce a single readable Lua-like line for one instruction.
    Unknown or environment-dependent operations are preserved as comments
    rather than invented.
    """
    nm       = ins.opcode_name
    a, b, c  = ins.a, ins.b, ins.c

    def rg(v):
        return f"r{v}" if isinstance(v, int) else _lua_literal(v)

    # ── Register moves and loads ──────────────────────────────
    if nm == 'MOVE':       return f"r{a} = {rg(b)}"
    if nm == 'LOADK':      return f"r{a} = {_lua_literal(b)}"
    if nm == 'LOADBOOL':
        val  = "true" if b else "false"
        skip = "  -- skip next" if c else ""
        return f"r{a} = {val}{skip}"
    if nm == 'LOADNIL':
        end = b if isinstance(b, int) else a
        return f"r{a}..r{end} = nil"

    # ── Upvalues / globals / tables ───────────────────────────
    if nm == 'GETUPVAL':   return f"r{a} = upval[{b}]"
    if nm == 'SETUPVAL':   return f"upval[{b}] = r{a}"
    if nm == 'GETGLOBAL':  return f"r{a} = _G[{_lua_literal(b)}]"
    if nm == 'SETGLOBAL':  return f"_G[{_lua_literal(b)}] = r{a}"
    if nm == 'GETTABLE':   return f"r{a} = r{b}[{rg(c)}]"
    if nm == 'SETTABLE':   return f"r{a}[{rg(b)}] = {rg(c)}"
    if nm == 'NEWTABLE':   return f"r{a} = {{}}  -- array_size:{b} hash_size:{c}"
    if nm == 'SELF':       return f"r{a+1} = r{b}; r{a} = r{b}[{rg(c)}]"

    # ── Arithmetic ────────────────────────────────────────────
    ARITH = {'ADD': '+', 'SUB': '-', 'MUL': '*', 'DIV': '/', 'MOD': '%', 'POW': '^'}
    if nm in ARITH:        return f"r{a} = {rg(b)} {ARITH[nm]} {rg(c)}"
    if nm == 'UNM':        return f"r{a} = -{rg(b)}"
    if nm == 'NOT':        return f"r{a} = not {rg(b)}"
    if nm == 'LEN':        return f"r{a} = #{rg(b)}"
    if nm == 'CONCAT':
        if isinstance(b, int) and isinstance(c, int):
            parts = " .. ".join(f"r{i}" for i in range(b, c + 1))
        else:
            parts = f"{rg(b)} .. {rg(c)}"
        return f"r{a} = {parts}"

    # ── Control flow ──────────────────────────────────────────
    if nm == 'JMP':
        t = ins.target_addr
        return f"goto L{t}" if t is not None else f"-- JMP sbx={ins.sbx}"

    CMP = {'EQ': '==', 'LT': '<', 'LE': '<='}
    if nm in CMP:
        neg = "" if a == 0 else "not "
        return f"if {neg}({rg(b)} {CMP[nm]} {rg(c)}) then skip_next"
    if nm == 'TEST':
        cond = "" if c else "not "
        return f"if {cond}r{a} then skip_next"
    if nm == 'TESTSET':
        cond = "" if c else "not "
        return f"if {cond}r{b} then r{a} = r{b} else skip_next"

    # ── Calls and returns ─────────────────────────────────────
    if nm == 'CALL':
        n_args = (f"r{a+1}" + (f"..r{a+b-1}" if isinstance(b, int) and b > 2 else "")
                  if isinstance(b, int) and b > 1 else "...")
        n_rets = (f"r{a}"   + (f"..r{a+c-2}" if isinstance(c, int) and c > 2 else "")
                  if isinstance(c, int) and c > 1 else "...")
        return f"{n_rets} = r{a}({n_args})"
    if nm == 'TAILCALL':
        n_args = (f"r{a+1}" + (f"..r{a+b-1}" if isinstance(b, int) and b > 2 else "")
                  if isinstance(b, int) and b > 1 else "...")
        return f"return r{a}({n_args})  -- tail call"
    if nm == 'RETURN':
        if isinstance(b, int):
            if b == 1: return "return"
            if b == 0: return "return ...  -- variable count"
            end = a + b - 2
            return f"return r{a}" + (f"..r{end}" if end > a else "")
        return f"return r{a}"

    # ── Numeric for loops ─────────────────────────────────────
    if nm == 'FORPREP':
        t = ins.target_addr
        return f"r{a} = r{a} - r{a+2}; goto L{t}"
    if nm == 'FORLOOP':
        t = ins.target_addr
        return f"r{a} += r{a+2}; if r{a} <= r{a+1} then r{a+3} = r{a}; goto L{t}"
    if nm == 'TFORLOOP':
        n    = c if isinstance(c, int) else 1
        rets = ", ".join(f"r{a+3+i}" for i in range(n))
        return (f"{rets} = r{a}(r{a+1}, r{a+2}); "
                f"if r{a+3} ~= nil then r{a+2} = r{a+3} else skip_next")

    # ── Misc ──────────────────────────────────────────────────
    if nm == 'SETLIST':
        n = c if isinstance(c, int) else 0
        return f"r{a}[{b}..{(b or 0)+n-1}] = r{a+1}..r{a+n}"
    if nm == 'CLOSE':   return f"-- close upvalues down to r{a}"
    if nm == 'CLOSURE': return f"r{a} = closure(proto[{ins.bx}])"
    if nm == 'VARARG':
        if isinstance(b, int) and b > 1:
            return f"r{a}..r{a+b-2} = ..."
        return f"r{a}... = ..."

    # ── Unknown / environment-dependent — preserved, not guessed ──
    if nm.startswith('UNKNOWN_'):
        return (f"-- [LURAPH] unknown opcode {ins.raw_opcode}"
                f"  A={a!r}  B={b!r}  C={c!r}")
    return f"-- [LURAPH] {nm}  A={a!r}  B={b!r}  C={c!r}"


def _lift_proto(proto: LuraphProto, blocks: list, indent: int = 0) -> list:
    """
    Recursively lift a prototype and all its nested functions
    to readable Lua pseudocode lines.
    """
    pad   = "    " * indent
    inner = "    " * (indent + 1)
    lines: list = []

    params = [f"r{i}" for i in range(proto.param_count)]
    if proto.is_vararg:
        params.append("...")
    fname = f"__luraph_func_{proto.depth}_{proto.index}"

    lines.append(f"{pad}local function {fname}({', '.join(params)})")
    lines.append(f"{pad}    -- source   : {proto.source_name or 'unknown'}")
    lines.append(f"{pad}    -- maxstack : {proto.max_stack}   upvalues: {proto.upvalue_count}")

    # Collect label targets for ::LN:: placement
    label_pcs: set = set()
    for bl in blocks:
        for ins in bl.instrs:
            if ins.target_addr is not None:
                label_pcs.add(ins.target_addr)

    for bl in blocks:
        if bl.start_pc in label_pcs:
            lines.append(f"{inner}::L{bl.start_pc}::")
        for ins in bl.instrs:
            lines.append(f"{inner}{_lift_instr(ins)}")

    lines.append(f"{pad}end -- {fname}")

    # Recurse into nested prototypes
    for i, sub in enumerate(proto.protos):
        sub.index = i
        sub_blocks = _build_cfg(sub)
        lines.append("")
        lines.extend(_lift_proto(sub, sub_blocks, indent))

    return lines


# ── Prototype / IR counters ───────────────────────────────────

def _count_protos(p: LuraphProto) -> int:
    return 1 + sum(_count_protos(s) for s in p.protos)

def _count_instrs(p: LuraphProto) -> int:
    return len(p.instructions) + sum(_count_instrs(s) for s in p.protos)

def _count_consts(p: LuraphProto) -> int:
    return len(p.constants) + sum(_count_consts(s) for s in p.protos)

def _collect_unknown_ops(p: LuraphProto, out: set = None) -> set:
    if out is None:
        out = set()
    for ins in p.instructions:
        if ins.opcode_name.startswith('UNKNOWN_'):
            out.add(ins.raw_opcode)
    for s in p.protos:
        _collect_unknown_ops(s, out)
    return out

def _collect_proto_strings(p: LuraphProto) -> list:
    strs = [v for t, v in p.constants if t == 'str' and v]
    for s in p.protos:
        strs.extend(_collect_proto_strings(s))
    return strs


# ============================================================
# ── Main Luraph pipeline entry point ─────────────────────────
# ============================================================

def luraph_analyze(code: str) -> LuraphResult:
    """
    Run the full staged Luraph static-analysis pipeline.
    No submitted Lua code is executed at any point.
    Unknown or environment-dependent operations are preserved as
    comments in the output, never guessed.
    """
    res = LuraphResult()

    # Hard size cap
    if len(code) > LURAPH_MAX_INPUT:
        res.notes.append(f"Input capped at {LURAPH_MAX_INPUT:,} B (was {len(code):,} B).")
        code = code[:LURAPH_MAX_INPUT]

    # ── Stage 1: Detection ───────────────────────────────────
    detected, version_hint, features = _luraph_stage1_detect(code)
    res.detected     = detected
    res.version_hint = version_hint
    feat_str = ', '.join(features) or 'none'
    res.stages.append(
        f"stage1  detect={detected}  version={version_hint}  features=[{feat_str}]"
    )
    if not detected:
        res.notes.append(
            "Not confidently identified as Luraph; proceeding with best-effort analysis."
        )

    # ── Stage 2: Bootstrap extraction ───────────────────────
    bootstrap = _luraph_stage2_bootstrap(code)
    res.bootstrap_source = bootstrap
    res.stages.append(f"stage2  bootstrap_preview={len(bootstrap)}_chars")

    # ── Stage 3: VM dispatch table ──────────────────────────
    vm_map = _luraph_stage3_dispatch(code)
    res.vm_opcode_map = vm_map
    res.stages.append(f"stage3  dispatch_entries={len(vm_map)}")

    # ── Stage 4: Blob extraction + decoding ─────────────────
    blobs        = _luraph_stage4_blobs(code)
    decoded_blobs = [_luraph_try_decode(b) for b in blobs]

    # Bonus: try XOR key decode on undecoded binary blobs
    for blob in decoded_blobs:
        data = blob.get('decoded')
        if isinstance(data, (bytes, bytearray)):
            data = bytes(data)
            if data[:4] != b'\x1bLua':
                xored = _luraph_try_xor_keys(data, code)
                if xored is not None:
                    blob['decoded']        = xored
                    blob['is_lua_bytecode'] = True
                    blob['encoding']       += '+xor_key'

    res.data_blobs = decoded_blobs
    n_dec = sum(1 for b in decoded_blobs if b.get('decoded') is not None)
    res.stages.append(f"stage4  blobs_found={len(blobs)}  decoded={n_dec}")

    # ── Stage 5: String recovery ────────────────────────────
    all_strings = _luraph_stage5_strings(code, decoded_blobs)
    res.all_strings  = all_strings
    res.string_count = len(all_strings)
    res.stages.append(f"stage5  strings={len(all_strings)}")

    # ── Stages 6-9: Bytecode / prototype parsing ─────────────
    prototypes:   list = []
    unknown_ops:  set  = set()
    total_bc_sz:  int  = 0

    for blob in decoded_blobs:
        data = blob.get('decoded')
        if not isinstance(data, (bytes, bytearray)):
            continue
        data = bytes(data)

        # ── Path A: Standard Lua 5.1 bytecode ────────────────
        if data[:4] == b'\x1bLua':
            try:
                r   = Reader(data)
                hdr = _parse_lua51_header(r)
                proto = _parse_lua51_chunk(r, hdr, depth=0, idx=len(prototypes))
                prototypes.append(proto)
                total_bc_sz += len(data)
                unknown_ops |= _collect_unknown_ops(proto)

                # Merge strings from constant pools
                for s in _collect_proto_strings(proto):
                    if s and s not in all_strings:
                        all_strings.append(s)

                res.stages.append(
                    f"stage6-9  lua51_bytecode  {len(data):,}B  "
                    f"{_count_protos(proto)}_protos  "
                    f"{_count_instrs(proto)}_instrs  "
                    f"{_count_consts(proto)}_consts  "
                    f"enc={blob.get('encoding','?')}"
                )
            except Exception as ex:
                res.notes.append(
                    f"Lua 5.1 bytecode parse failed "
                    f"({blob.get('encoding','?')}): {type(ex).__name__}: {ex}"
                )
            continue

        # ── Path B: Custom Luraph bytecode (heuristic) ───────
        # Only attempt if we have a dispatch map AND the blob looks like
        # packed 32-bit instruction words whose low 6 bits map to known ops.
        if vm_map and len(data) >= 16 and len(data) % 4 == 0:
            try:
                words = struct.unpack(f'<{len(data)//4}I', data)
                valid = sum(1 for w in words if (w & 0x3F) in vm_map)
                ratio = valid / len(words)
                if ratio >= 0.65 and len(words) >= 8:
                    instrs_custom: list = []
                    for pc, word in enumerate(words):
                        opcode = word & 0x3F
                        a      = (word >> 6)  & 0xFF
                        c      = (word >> 14) & 0x1FF
                        b      = (word >> 23) & 0x1FF
                        bx     = (word >> 14) & 0x3FFFF
                        sbx    = bx - 131071
                        nm     = vm_map.get(opcode, f'UNKNOWN_{opcode}')
                        if nm.startswith('UNKNOWN_'):
                            unknown_ops.add(opcode)
                        tgt = (pc + 1 + sbx
                               if nm in ('JMP', 'FORLOOP', 'FORPREP', 'TFORLOOP')
                               else None)
                        instrs_custom.append(LuraphInstr(
                            pc=pc, raw_opcode=opcode, opcode_name=nm,
                            a=a, b=b, c=c, bx=bx, sbx=sbx,
                            target_addr=tgt,
                        ))
                    proto = LuraphProto(
                        index=len(prototypes), depth=0,
                        param_count=0, is_vararg=True,
                        max_stack=255, instructions=instrs_custom,
                        constants=[], upvalue_count=0,
                        protos=[], source_name="@luraph_custom_vm",
                    )
                    prototypes.append(proto)
                    total_bc_sz += len(data)
                    res.stages.append(
                        f"stage6-9  custom_vm_bytecode  {len(data):,}B  "
                        f"{len(instrs_custom)}_instrs  "
                        f"opcode_match={ratio:.0%}  "
                        f"(heuristic — format not fully established)"
                    )
            except Exception as ex:
                res.notes.append(
                    f"Custom-bytecode heuristic failed: {type(ex).__name__}: {ex}"
                )

    res.prototypes        = prototypes
    res.unknown_opcodes   = unknown_ops
    res.bytecode_size     = total_bc_sz
    res.instruction_count = sum(_count_instrs(p) for p in prototypes)
    res.constant_count    = sum(_count_consts(p)  for p in prototypes)
    res.proto_count       = sum(_count_protos(p)  for p in prototypes)
    res.string_count      = len(all_strings)
    res.stages.append(
        f"summary  protos={res.proto_count}  instrs={res.instruction_count}  "
        f"consts={res.constant_count}  strings={res.string_count}  "
        f"unknown_opcodes={len(unknown_ops)}  bytecode_size={total_bc_sz:,}B"
    )

    # ── Stages 10-12: CFG + lift + constant fold ──────────────
    raw_lines: list = []
    dec_lines: list = []

    # ── Header ────────────────────────────────────────────────
    raw_lines += [
        "=" * 72,
        "  Luraph Static Analysis — Raw IR / Prototype Detail",
        f"  version hint : {version_hint}",
        f"  features     : {feat_str}",
        "=" * 72,
        "  No submitted Lua/Luau code was executed at any point.",
        "  Unknown/env-dependent operations are preserved as comments.",
        "=" * 72,
        "",
    ]
    for stage in res.stages:
        raw_lines.append(f"-- {stage}")
    raw_lines.append("")

    if prototypes:
        # ── RAW: per-prototype instruction / CFG detail ───────
        for proto in prototypes:
            blocks = _build_cfg(proto)
            raw_lines += [
                f"-- {'='*68}",
                f"-- Prototype {proto.index}",
                f"--   source   : {proto.source_name!r}",
                f"--   depth    : {proto.depth}",
                f"--   params   : {proto.param_count}   vararg: {proto.is_vararg}",
                f"--   maxstack : {proto.max_stack}   upvalues: {proto.upvalue_count}",
                f"--   instructions : {len(proto.instructions)}",
                f"--   constants    : {len(proto.constants)}",
                f"--   sub-protos   : {len(proto.protos)}",
                "--",
                "-- CONSTANTS:",
            ]
            for ci, (ct, cv) in enumerate(proto.constants):
                raw_lines.append(f"--   [{ci:4d}]  {ct:8s}  {cv!r}")

            raw_lines.append("--")
            raw_lines.append(
                f"-- INSTRUCTION IR:"
                f"  {'pc':>6}  {'raw_op':>6}  {'name':<12}  "
                f"{'A':>6}  {'B':>12}  {'C':>12}  target"
            )
            for ins in proto.instructions:
                tgt = f"→L{ins.target_addr}" if ins.target_addr is not None else ""
                raw_lines.append(
                    f"--   {ins.pc:6d}  {ins.raw_opcode:6d}  {ins.opcode_name:<12}  "
                    f"{str(ins.a):>6}  {str(ins.b)[:12]:>12}  "
                    f"{str(ins.c)[:12]:>12}  {tgt}"
                )

            raw_lines.append("--")
            raw_lines.append("-- CONTROL-FLOW GRAPH (basic blocks):")
            for bl in blocks:
                raw_lines.append(
                    f"--   block_{bl.id:3d}  "
                    f"pc[{bl.start_pc:4d}..{bl.end_pc:4d}]  "
                    f"succs={bl.successors}  preds={bl.predecessors}"
                )
            raw_lines.append("")

        # ── DECOMPILED: reconstructed Lua ─────────────────────
        dec_lines += [
            "=" * 72,
            "  Luraph — Reconstructed Lua (static lift)",
            f"  version hint : {version_hint}",
            f"  {res.proto_count} prototype(s)  "
            f"{res.instruction_count} instructions  "
            f"{res.constant_count} constants",
        ]
        if unknown_ops:
            dec_lines.append(
                f"  unknown opcodes (preserved as comments) : "
                f"{sorted(unknown_ops)}"
            )
        dec_lines += [
            "=" * 72,
            "",
            "-- Static lift only. No submitted code was executed.",
            "-- [LURAPH] tags = instructions whose semantics could not be established.",
            "",
        ]
        for proto in prototypes:
            blocks = _build_cfg(proto)
            dec_lines.extend(_lift_proto(proto, blocks, indent=0))
            dec_lines.append("")

    else:
        # ── Nothing decoded: report what we do have ───────────
        raw_lines += [
            "-- No bytecode or prototype structures were recovered from this sample.",
            "--",
            "-- Possible reasons:",
            "--   • XOR or keyed encryption where the key is not statically visible",
            "--   • A runtime-only transformation (key derived from environment)",
            "--   • An undocumented or custom Luraph fork",
            "--   • Bytecode compressed or encrypted before base64",
            "",
            "-- BOOTSTRAP / VM LAYER (readable Lua; blobs replaced with placeholders):",
            "",
        ]
        raw_lines.append(bootstrap[:12_000])
        if len(bootstrap) > 12_000:
            raw_lines.append(f"\n-- ... ({len(bootstrap) - 12_000:,} more chars truncated) ...")

        if vm_map:
            raw_lines += ["", "-- RECOVERED VM OPCODE TABLE:"]
            for op, nm in sorted(vm_map.items()):
                raw_lines.append(f"--   [{op:3d}]  {nm}")

        raw_lines += ["", f"-- {len(all_strings)} STRINGS RECOVERED (all layers):"]
        for s in all_strings[:120]:
            raw_lines.append(f"--   {s!r}")
        if len(all_strings) > 120:
            raw_lines.append(f"--   ... ({len(all_strings) - 120} more) ...")

        dec_lines += [
            "-- Luraph: insufficient static information to reconstruct source.",
            "--",
            "-- The protected bytecode payload could not be decoded statically.",
            "-- Meaningful deobfuscation would require one of:",
            "--   • A runtime XOR / encryption key derived at execution time",
            "--   • Environment-specific values (getfenv, debug.getinfo, etc.)",
            "--   • A known Luraph version specification for this exact format",
            "--",
            "-- See file-raw.lua for: recovered bootstrap code, VM opcode map, strings.",
        ]
        for note in res.notes:
            dec_lines.append(f"-- Note: {note}")

    res.raw_output        = "\n".join(raw_lines)
    res.decompiled_output = _simplify_constants("\n".join(dec_lines))
    return res


# ============================================================
# ── LuaObfuscator binary decoder (unchanged) ─────────────────
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
        self._need(1); v = self.d[self.p]; self.p += 1; return v

    def u16(self):
        self._need(2)
        a, b = self.d[self.p:self.p + 2]; self.p += 2
        return (b << 8) | a

    def u32(self):
        self._need(4)
        a, b, c, d = self.d[self.p:self.p + 4]; self.p += 4
        return (d << 24) | (c << 16) | (b << 8) | a

    def f64(self):
        left = self.u32(); right = self.u32()
        mantissa = ((right & 0xFFFFF) << 32) | left
        exponent = (right >> 20) & 0x7FF
        sign = -1.0 if right >> 31 else 1.0
        if exponent == 0:
            return sign * (0.0 if mantissa == 0 else math.ldexp(mantissa, -1074))
        if exponent == 0x7FF:
            return math.inf * sign if mantissa == 0 else math.nan
        return sign * math.ldexp((1 << 52) | mantissa, exponent - 1023 - 52)

    def string(self, length=None):
        if length is None:
            length = self.u32()
        if length == 0:
            return ""
        self._need(length)
        raw = self.d[self.p:self.p + length]; self.p += length
        return raw.decode("utf-8", errors="replace")

    @staticmethod
    def gbit(value, start, end=None):
        if end is None:
            return (value >> (start - 1)) & 1
        width = end - start + 1
        return (value >> (start - 1)) & ((1 << width) - 1)


# LuaObfuscator-format chunk parser (custom format, not Lua 5.1 standard)
def parse_chunk(r: Reader, depth=0):
    const_count = r.u32()
    consts = []
    for _ in range(const_count):
        t = r.u8()
        if t == 1:   consts.append(("bool", r.u8() != 0))
        elif t == 2: consts.append(("num",  r.f64()))
        elif t == 3: consts.append(("str",  r.string()))
        else:        consts.append(("nil",  None))

    params      = r.u8()
    instr_count = r.u32()
    instrs      = []

    for _ in range(instr_count):
        desc = r.u8()
        if Reader.gbit(desc, 1):
            continue
        typ  = Reader.gbit(desc, 2, 3)
        mask = Reader.gbit(desc, 4, 6)
        op   = r.u16()
        a    = r.u16()
        b = c = None
        if typ == 0:   b, c = r.u16(), r.u16()
        elif typ == 1: b = r.u32()
        elif typ == 2: b = r.u32() - (1 << 16)
        elif typ == 3: b, c = r.u32() - (1 << 16), r.u16()

        def resolve(v, bit):
            if (v is not None and Reader.gbit(mask, bit)
                    and isinstance(v, int) and 0 <= v < len(consts)):
                return consts[v][1]
            return v

        instrs.append((op, resolve(a, 1), resolve(b, 2), resolve(c, 3)))

    subs = [parse_chunk(r, depth + 1) for _ in range(r.u32())]
    return {"depth": depth, "params": params, "consts": consts,
            "instrs": instrs, "subs": subs}


def collect_consts(chunk, out=None):
    if out is None: out = []
    out.extend(chunk["consts"])
    for sub in chunk["subs"]: collect_consts(sub, out)
    return out


def count_funcs(chunk):
    return 1 + sum(count_funcs(x) for x in chunk["subs"])


def lift_lua_chunk(chunk, indent=0):
    """Best-effort Lua-like lifting from a LuaObfuscator parsed chunk (unchanged)."""
    pad = "    " * indent
    lines = []
    instrs = chunk["instrs"]
    labels: set = set()

    for i, (op, a, b, c) in enumerate(instrs):
        if (LUA51_OPS.get(op) in {"JMP", "FORLOOP", "FORPREP", "TFORLOOP"}
                and isinstance(a, int)):
            target = i + 1 + a
            if 0 <= target < len(instrs):
                labels.add(target)

    for i, (op, a, b, c) in enumerate(instrs):
        if i in labels:
            lines.append(f"{pad}::L{i}::")
        name = LUA51_OPS.get(op, f"vm_op_{op}")

        if name == "MOVE":        lines.append(f"{pad}r{a} = {_reg(b)}")
        elif name == "LOADK":     lines.append(f"{pad}r{a} = {_lua_literal(b)}")
        elif name == "LOADBOOL":  lines.append(f"{pad}r{a} = {'true' if b else 'false'}")
        elif name == "LOADNIL":   lines.append(f"{pad}r{a} = nil")
        elif name in {"ADD","SUB","MUL","DIV","MOD","POW"}:
            opch = {"ADD":"+","SUB":"-","MUL":"*","DIV":"/","MOD":"%","POW":"^"}[name]
            lines.append(f"{pad}r{a} = {_reg(b)} {opch} {_reg(c)}")
        elif name == "UNM":       lines.append(f"{pad}r{a} = -{_reg(b)}")
        elif name == "NOT":       lines.append(f"{pad}r{a} = not {_reg(b)}")
        elif name == "LEN":       lines.append(f"{pad}r{a} = #{_reg(b)}")
        elif name == "CONCAT":    lines.append(f"{pad}r{a} = {_reg(b)} .. {_reg(c)}")
        elif name == "GETGLOBAL": lines.append(f"{pad}r{a} = {_lua_literal(b)}")
        elif name == "SETGLOBAL": lines.append(f"{pad}{_lua_literal(b)} = {_reg(a)}")
        elif name == "GETUPVAL":  lines.append(f"{pad}r{a} = upvalue_{b}")
        elif name == "SETUPVAL":  lines.append(f"{pad}upvalue_{b} = {_reg(a)}")
        elif name == "JMP":
            target = (i + 1 + a) if isinstance(a, int) else None
            lines.append(f"{pad}goto L{target}" if target is not None else f"{pad}-- JMP {_reg(a)}")
        elif name in {"EQ","LT","LE"}:
            cmpop = {"EQ":"==","LT":"<","LE":"<="}[name]
            lines.append(f"{pad}-- if {_reg(b)} {cmpop} {_reg(c)} then")
        elif name == "CALL":
            lines.append(f"{pad}-- call {_reg(a)} ({_reg(b)}, {_reg(c)})")
        elif name == "RETURN":
            lines.append(f"{pad}return {_reg(a)}")
        elif name == "CLOSURE":
            lines.append(f"{pad}r{a} = function(...) -- nested function")
        elif name in {"FORPREP","FORLOOP","TFORLOOP"}:
            lines.append(f"{pad}-- {name} A={a} B={b} C={c}")
        else:
            lines.append(f"{pad}-- {name} A={a!r} B={b!r} C={c!r}")

    for idx, sub in enumerate(chunk["subs"], 1):
        lines.append("")
        lines.append(f"{pad}local function __deob_func_{chunk['depth']}_{idx}(...)")
        lines.extend(lift_lua_chunk(sub, indent + 1))
        lines.append(f"{pad}end")

    return lines


def deobfuscate_luaobfuscator(code, include_instrs=False):
    m = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
    if not m:
        return "[LuaObfuscator] VMCall payload not found."
    raw        = decode_luaobf(m.group(1))
    chunk      = parse_chunk(Reader(raw))
    all_consts = collect_consts(chunk)
    lines      = [
        "=" * 62, "  LuaObfuscator.com — reconstructed Lua",
        f"  {len(raw):,} decoded bytes | {count_funcs(chunk)} functions",
        "=" * 62, "",
        "-- Best-effort static lift.",
        "-- Unknown/remapped VM opcodes are kept as comments.",
        "-- No submitted Lua/Luau code is executed.", "",
    ]
    lines.extend(lift_lua_chunk(chunk))
    result = _simplify_constants("\n".join(lines))
    if include_instrs:
        result += "\n\n-- CONSTANTS\n" + "\n".join(
            f"-- {i}: {t} = {v!r}" for i, (t, v) in enumerate(all_consts))
    return result


# ============================================================
# ── WeAreDevs Method 2 (unchanged) ───────────────────────────
# ============================================================

def _safe_lua_expr(expr):
    return _safe_expr(expr)

def _decode_lua_escapes(value):
    def repl(m):
        token = m.group(1)
        try:
            return chr(int(token[1:], 16) if token.lower().startswith("x") else int(token))
        except Exception:
            return m.group(0)
    value = re.sub(r"\\(x[0-9a-fA-F]{2}|[0-9]{1,3})", repl, value)
    return (value.replace(r'\"', '"').replace(r"\'", "'").replace(r"\\", "\\")
            .replace(r"\n", "\n").replace(r"\r", "\r").replace(r"\t", "\t"))

def _extract_lua_table_body(code, name, limit=200000):
    m = re.search(r"\blocal\s+" + re.escape(name) + r"\s*=\s*\{", code[:limit])
    if not m:
        return None
    start = m.end(); depth = 1; quote = None; esc = False
    for i in range(start, min(len(code), limit)):
        ch = code[i]
        if quote:
            if esc:     esc = False
            elif ch == "\\": esc = True
            elif ch == quote: quote = None
            continue
        if ch in "\"'": quote = ch
        elif ch == "{": depth += 1
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
        r'''\s*=\s*([0-9+\-*/%().\s]+)(?=[,;]|$)''')
    for m in pattern.finditer(body):
        key = m.group(2) if m.group(2) is not None else m.group(3)
        val = _safe_lua_expr(m.group(4))
        if val is not None and len(key) == 1:
            out[key] = int(val)
    return out

def _extract_quoted_strings(body):
    return [_decode_lua_escapes(m.group(1))
            for m in re.finditer(r'"((?:\\.|[^"\\])*)"', body or "")]

def _custom_b64_decode(value, alphabet):
    if not value or value[0] not in ("?", "s"):
        return None
    width, out_width = (5, 4) if value[0] == "?" else (4, 3)
    vals = []
    for ch in value[1:]:
        if ch == "=":     vals.append(0)
        elif ch in alphabet: vals.append(alphabet[ch])
        else:             return None
    out = bytearray()
    for i in range(0, len(vals), width):
        chunk_v = vals[i:i + width]
        if len(chunk_v) < 2: break
        real = len(chunk_v)
        chunk_v += [0] * (width - real)
        n = 0
        for v in chunk_v: n = n * 64 + v
        for shift in range((out_width - 1) * 8, -1, -8):
            out.append((n >> shift) & 255)
        if real < width:
            del out[-min(width - real, out_width):]
    try:               return out.decode("utf-8")
    except UnicodeDecodeError: return out.decode("latin-1", errors="replace")

def _decode_wad_strings(code):
    ubody  = _extract_lua_table_body(code, "U")
    omap   = _parse_numeric_lookup_table(_extract_lua_table_body(code, "o") or "")
    wmap   = _parse_numeric_lookup_table(_extract_lua_table_body(code, "w") or "")
    strings = _extract_quoted_strings(ubody or "")
    decoded = []
    for s in strings:
        if   s.startswith("?"): value = _custom_b64_decode(s, omap)
        elif s.startswith("s"): value = _custom_b64_decode(s, wmap)
        else:                   value = None
        decoded.append(value if value is not None else s)
    return decoded, omap, wmap

def _replace_wad_string_indexes(code, decoded):
    def repl(m):
        idx = int(m.group(1)) - 1
        return _lua_literal(decoded[idx]) if 0 <= idx < len(decoded) else m.group(0)
    return re.sub(r"\bU\s*\[\s*(\d+)\s*\]", repl, code)

def deobfuscate_wearedevs(code):
    decoded, omap, wmap = _decode_wad_strings(code)
    lifted = _replace_wad_string_indexes(code, decoded)
    for name in ("U", "o", "w"):
        pattern = re.compile(r"\blocal\s+" + re.escape(name) + r"\s*=\s*\{", re.M)
        m = pattern.search(lifted)
        if m:
            start = m.start(); depth = 0; quote = None; esc = False
            for i in range(m.end() - 1, len(lifted)):
                ch = lifted[i]
                if quote:
                    if esc:     esc = False
                    elif ch == "\\": esc = True
                    elif ch == quote: quote = None
                    continue
                if ch in "\"'": quote = ch
                elif ch == "{": depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        end = i + 1
                        while end < len(lifted) and lifted[end] in " \t\r\n;":
                            end += 1
                        lifted = lifted[:start] + lifted[end:]
                        break
    lifted = re.sub(r"if\s+false\s+then[\s\S]*?end", "", lifted, flags=re.I)
    lifted = re.sub(r"\n{3,}", "\n\n", lifted).strip()
    header = [
        "=" * 62, "  WeAreDevs v1.0.0 — reconstructed Lua",
        f"  {len(code):,} chars | {len(decoded):,} decoded strings",
        "=" * 62, "",
        "-- String layer decoded statically.",
        "-- VM code is not executed.",
        "-- Unknown VM semantics are not guessed.", "",
    ]
    if lifted:
        header += ["-- RECONSTRUCTED SOURCE", "", lifted]
    else:
        header += ["-- No non-table source could be reconstructed."]
    header += ["", f"-- decoder mappings: o={len(omap)}, w={len(wmap)}"]
    return "\n".join(header)


# ============================================================
# Generic analysis (unchanged)
# ============================================================

def extract_strings_generic(code):
    seen = set(); result = []
    for pattern in [r'"((?:[^"\\]|\\.){2,})"', r"'((?:[^'\\]|\\.){2,})'"]:
        for m in re.finditer(pattern, code):
            s = m.group(1)
            if s not in seen:
                seen.add(s); result.append(s)
    return result

def generic_analysis(code, obf_name):
    strings = [s for s in extract_strings_generic(code)
               if all(32 <= ord(c) < 127 for c in s) and len(s) > 3]
    nums  = list(dict.fromkeys(re.findall(r"\b\d{5,}\b", code)))
    urls  = list(dict.fromkeys(re.findall(r"https?://[^\s\"'\\]+", code)))
    funcs = [x for x in ("loadstring","getfenv","require","HttpGet",
                          "coroutine","debug","pcall/xpcall")
             if re.search(r"\b[xp]?call\b" if x == "pcall/xpcall"
                          else r"\b" + re.escape(x.split('/')[0]) + r"\b", code)]
    out = [
        "=" * 58, f"  {obf_name} — Static Analysis",
        f"  {len(code):,} chars | {code.count(chr(10)) + 1:,} lines",
        "=" * 58,
        "  [!] No dedicated control-flow backend exists for this obfuscator yet.", "",
        f"── READABLE STRINGS ({len(strings)}) ─────────────────────",
    ]
    out += [f"  {s!r}" for s in strings[:60]]
    if nums:
        out += ["", f"── LARGE CONSTANTS ({len(nums)}) ──────────────────────",
                "  " + "  ".join(nums[:30])]
    if urls:
        out += ["", f"── URLS ({len(urls)}) ──────────────────────────────"]
        out += [f"  {u}" for u in urls[:10]]
    if funcs:
        out += ["", "── NOTABLE FUNCTIONS ───────────────────────────────────",
                "  " + "  ".join(funcs)]
    return "\n".join(out)


# ============================================================
# run_deob / analyze_code — updated for Luraph
# ============================================================

def run_deob(code: str, include_instrs: bool = False) -> str:
    obf = detect_obfuscator(code)
    try:
        if obf == "LuaObfuscator":
            return deobfuscate_luaobfuscator(code, include_instrs)
        if obf == "WeAreDevs":
            return deobfuscate_wearedevs(code)
        if obf == "Luraph":
            r = luraph_analyze(code)
            return r.decompiled_output or r.raw_output
        return generic_analysis(code, obf)
    except Exception as exc:
        return f"[{obf}] deobfuscation error: {type(exc).__name__}: {exc}"


@dataclass
class Analysis:
    ok:         bool
    family:     str
    raw:        str = ""
    decompiled: str = ""
    notes:      str = ""


def _decompile_stage(lifted: str) -> str:
    return _simplify_constants(lifted)


def analyze_code(code: str) -> Analysis:
    obf = detect_obfuscator(code)
    try:
        # ── LuaObfuscator ─────────────────────────────────────
        if obf == "LuaObfuscator":
            m = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
            if not m:
                return Analysis(False, obf, notes="VMCall payload not found.")
            data   = decode_luaobf(m.group(1))
            chunk  = parse_chunk(Reader(data))
            consts = collect_consts(chunk)
            lifted = "\n".join(lift_lua_chunk(chunk))
            head   = (f"-- LuaObfuscator | {len(data):,} decoded bytes | "
                      f"{count_funcs(chunk)} functions\n"
                      "-- Static lift only; submitted code was not executed.\n\n")
            table  = "\n".join(f"-- {i}: {t} = {v!r}"
                               for i, (t, v) in enumerate(consts))
            return Analysis(
                True, obf,
                raw=head + lifted + "\n\n-- CONSTANTS\n" + table,
                decompiled=head + _decompile_stage(lifted),
            )

        # ── WeAreDevs ─────────────────────────────────────────
        if obf == "WeAreDevs":
            decoded, omap, wmap = _decode_wad_strings(code)
            raw = (f"-- WeAreDevs | {len(decoded)} decoded strings | "
                   f"o={len(omap)} w={len(wmap)}\n\n"
                   + "\n".join(f"U[{i}] = {s!r}" for i, s in enumerate(decoded, 1)))
            return Analysis(True, obf, raw=raw,
                            decompiled=deobfuscate_wearedevs(code))

        # ── Luraph ────────────────────────────────────────────
        if obf == "Luraph":
            r = luraph_analyze(code)
            if r.proto_count > 0:
                note = (f"v{r.version_hint}  {r.proto_count} protos  "
                        f"{r.instruction_count} instrs  "
                        f"{r.constant_count} consts  "
                        f"{r.string_count} strings")
                if r.unknown_opcodes:
                    note += f"  unknown_opcodes={sorted(r.unknown_opcodes)}"
            else:
                note = ("; ".join(r.notes)
                        if r.notes else
                        "Bootstrap extracted; bytecode payload not decoded statically.")
            return Analysis(
                ok=r.detected and r.proto_count > 0,
                family="Luraph",
                raw=r.raw_output,
                decompiled=r.decompiled_output,
                notes=note,
            )

        # ── Generic fallback ──────────────────────────────────
        return Analysis(
            False, obf,
            raw=generic_analysis(code, obf),
            decompiled=f"-- No dedicated backend for {obf}; nothing reconstructed.\n",
            notes=f"No dedicated backend for {obf}; string/constant analysis only.",
        )

    except Exception as exc:
        return Analysis(False, obf, notes=f"{type(exc).__name__}: {exc}")


def make_files(a: Analysis):
    files = []
    if a.raw:
        files.append(discord.File(
            io.BytesIO(a.raw.encode("utf-8")), filename="file-raw.lua"))
    if a.decompiled:
        files.append(discord.File(
            io.BytesIO(a.decompiled.encode("utf-8")), filename="file-decompiled.lua"))
    return files


# ============================================================
# Discord bot infrastructure
# ============================================================

async def extract_code(ctx):
    for att in ctx.message.attachments:
        if att.filename.lower().endswith((".lua", ".luau", ".txt")):
            return (await att.read()).decode("utf-8", errors="replace")
    content = ctx.message.content
    m = re.search(r"```(?:lua[ua]?)?\n?([\s\S]+?)```", content, re.I)
    if m:
        return m.group(1).strip()
    m = re.search(r"`([^`]{10,})`", content)
    if m:
        return m.group(1).strip()
    parts = content.split(None, 1)
    if len(parts) == 2 and len(parts[1]) > 20:
        return parts[1].strip()
    return None


intents = discord.Intents.default()
intents.message_content = True

bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

TRACE_DELAY = (4.0, 6.0)
_busy: set = set()


@bot.event
async def on_ready():
    print(f"[+] Logged in as {bot.user} ({bot.user.id})")
    await bot.change_presence(activity=discord.Activity(
        type=discord.ActivityType.watching, name="obfuscated lua"))


async def lock_channel(channel):
    role  = channel.guild.default_role
    me    = channel.guild.me
    ow_r  = channel.overwrites_for(role)
    ow_me = channel.overwrites_for(me)
    prev  = (ow_r.send_messages, ow_me.send_messages)
    ow_r.send_messages  = False
    ow_me.send_messages = True
    await channel.set_permissions(role, overwrite=ow_r,  reason="Deobfuscation running")
    await channel.set_permissions(me,   overwrite=ow_me, reason="Deobfuscation running")
    return prev

async def unlock_channel(channel, prev):
    for target, value in ((channel.guild.default_role, prev[0]),
                          (channel.guild.me,            prev[1])):
        ow = channel.overwrites_for(target)
        ow.send_messages = value
        await channel.set_permissions(
            target, overwrite=None if ow.is_empty() else ow,
            reason="Deobfuscation finished")


# ============================================================
# !deob
# ============================================================

@bot.command(name="deob", aliases=["d", "deobfuscate"])
@commands.guild_only()
async def cmd_deob(ctx):
    chan = ctx.channel
    if chan.id in _busy:
        await ctx.reply("⏳ A task is already running in this channel.")
        return

    _busy.add(chan.id)
    lock_state = None
    locked     = False
    status     = None

    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No code found.")
            return

        lock_state = await lock_channel(chan)
        locked     = True
        obf_quick  = detect_obfuscator(code)

        if obf_quick == "Luraph":
            status_msg = ("🔍 Luraph detected — running staged static analysis "
                          "(bootstrap → blob decode → bytecode parse → CFG → lift)... ⚙️")
        else:
            status_msg = ("🔍 Tracing VM interpreter structures "
                          "& unpacking bytecode stream... ⚙️")

        status = await chan.send(status_msg)

        analysis, _ = await asyncio.gather(
            asyncio.to_thread(analyze_code, code),
            asyncio.sleep(random.uniform(*TRACE_DELAY)),
        )

        files = make_files(analysis)
        if files:
            await chan.send(
                f"{ctx.author.mention} ✅ Deobfuscation complete:",
                files=files)

        if analysis.notes:
            await status.edit(content=f"⚠️ Finished with notes: {analysis.notes}")
        elif analysis.ok:
            await status.edit(content=f"✅ {analysis.family} deobfuscation complete.")
        else:
            await status.edit(content=f"⚠️ {analysis.family}: analysis completed.")

    except discord.HTTPException as exc:
        if status:
            try: await status.edit(content=f"❌ Discord delivery error: {exc}")
            except Exception: pass
    except Exception as exc:
        if status:
            try: await status.edit(content=f"❌ Unexpected error: {type(exc).__name__}: {exc}")
            except Exception: pass
    finally:
        if locked:
            await unlock_channel(chan, lock_state)
        _busy.discard(chan.id)


# ============================================================
# !detect
# ============================================================

@bot.command(name="detect")
async def cmd_detect(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return

    obf   = detect_obfuscator(code)
    color = 0x00FF00 if obf != "Unknown" else 0xFF4444
    embed = discord.Embed(title="🔍 Detection Result", color=color)
    embed.add_field(name="Obfuscator", value=f"**{obf}**", inline=True)
    embed.add_field(name="Size",  value=f"{len(code):,} chars", inline=True)
    embed.add_field(name="Lines", value=f"{code.count(chr(10)) + 1:,}", inline=True)

    # For Luraph, run stage-1 detect for richer detail (cheap — no blob decode)
    if obf == "Luraph":
        try:
            _, version_hint, features = _luraph_stage1_detect(code)
            embed.add_field(name="Version Hint", value=version_hint, inline=True)
            embed.add_field(name="Luraph Features",
                            value=", ".join(features) or "none", inline=False)
        except Exception:
            pass

    await ctx.reply(embed=embed)


# ============================================================
# !strings
# ============================================================

@bot.command(name="strings", aliases=["s", "strs"])
async def cmd_strings(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return

    obf  = detect_obfuscator(code)
    strs = []

    try:
        if obf == "LuaObfuscator":
            m   = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
            raw = decode_luaobf(m.group(1)) if m else b""
            strs = ([v for t, v in collect_consts(parse_chunk(Reader(raw))) if t == "str"]
                    if raw else [])

        elif obf == "WeAreDevs":
            strs, _, _ = _decode_wad_strings(code)

        elif obf == "Luraph":
            # Run full pipeline to get strings from all layers including bytecode consts
            result = await asyncio.to_thread(luraph_analyze, code)
            strs   = result.all_strings

        else:
            strs = extract_strings_generic(code)

    except Exception as e:
        await ctx.reply(f"❌ String decode error: {e}")
        return

    out = "\n".join(repr(s) for s in strs)
    if len(out) <= 1800:
        await ctx.reply(f"**{len(strs)} strings [{obf}]:**\n```\n{out}\n```")
    else:
        await ctx.reply(
            f"**{len(strs)} strings [{obf}]:**",
            file=discord.File(io.BytesIO(out.encode()), filename="strings.txt"))


# ============================================================
# !info
# ============================================================

@bot.command(name="info")
async def cmd_info(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found.")
        return

    obf   = detect_obfuscator(code)
    embed = discord.Embed(title="📋 Script Info", color=0x7289DA)
    embed.add_field(name="Obfuscator", value=obf,                       inline=True)
    embed.add_field(name="Size",  value=f"{len(code):,} chars",         inline=True)
    embed.add_field(name="Lines", value=f"{code.count(chr(10)) + 1:,}", inline=True)

    if obf == "LuaObfuscator":
        m = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
        if m:
            try:
                chunk = parse_chunk(Reader(decode_luaobf(m.group(1))))
                embed.add_field(name="Constants", value=str(len(collect_consts(chunk))), inline=True)
                embed.add_field(name="Functions", value=str(count_funcs(chunk)), inline=True)
            except Exception:
                pass

    elif obf == "WeAreDevs":
        try:
            strings, o, w = _decode_wad_strings(code)
            embed.add_field(name="Decoded WAD strings", value=str(len(strings)), inline=True)
            embed.add_field(name="Mappings", value=f"o={len(o)}, w={len(w)}", inline=True)
        except Exception:
            pass

    elif obf == "Luraph":
        try:
            r = await asyncio.to_thread(luraph_analyze, code)
            embed.add_field(name="Version Hint",   value=r.version_hint,              inline=True)
            embed.add_field(name="Prototypes",     value=str(r.proto_count),           inline=True)
            embed.add_field(name="Instructions",   value=f"{r.instruction_count:,}",   inline=True)
            embed.add_field(name="Constants",      value=f"{r.constant_count:,}",      inline=True)
            embed.add_field(name="Strings",        value=f"{r.string_count:,}",        inline=True)
            embed.add_field(name="Bytecode Size",  value=f"{r.bytecode_size:,} B",     inline=True)
            if r.vm_opcode_map:
                embed.add_field(name="VM Opcodes Mapped",
                                value=str(len(r.vm_opcode_map)), inline=True)
            if r.unknown_opcodes:
                embed.add_field(name="Unknown Opcodes",
                                value=str(len(r.unknown_opcodes)), inline=True)
            stages_summary = f"{len(r.stages)} stages completed"
            if r.notes:
                stages_summary += f" | {'; '.join(r.notes[:2])}"
            embed.add_field(name="Analysis", value=stages_summary, inline=False)
        except Exception as ex:
            embed.add_field(name="Luraph Error", value=str(ex)[:256], inline=False)

    await ctx.reply(embed=embed)


# ============================================================
# !help
# ============================================================

@bot.command(name="help", aliases=["h", "commands", "cmds"])
async def cmd_help(ctx):
    embed = discord.Embed(title="Lua Deobfuscator Bot", color=0x7289DA)
    embed.description = (
        "Attach a `.lua` / `.luau` / `.txt` file or paste a fenced Lua block.\n"
        "All analysis is **static only** — no submitted code is ever executed.")

    embed.add_field(name="!deob / !d",
                    value=("Detect, reconstruct, and deliver two files:\n"
                           "`file-raw.lua` — detailed IR / prototype / CFG info\n"
                           "`file-decompiled.lua` — readable reconstructed Lua"),
                    inline=False)
    embed.add_field(name="!detect",
                    value="Identify the obfuscator (Luraph: also shows version hint + features)",
                    inline=False)
    embed.add_field(name="!strings / !s",
                    value="Extract all decoded strings (Luraph: from bootstrap + bytecode consts)",
                    inline=False)
    embed.add_field(name="!info",
                    value=("Script metadata\n"
                           "Luraph: version hint · prototypes · instructions · constants · "
                           "strings · bytecode size · VM opcode map size · unknown opcodes"),
                    inline=False)
    embed.add_field(
        name="Backends",
        value=(
            "**LuaObfuscator** — full LOL! decode · bytecode parse · Lua-like lift\n"
            "**WeAreDevs** — string layer decode · code reconstruction\n"
            "**Luraph** — 12-stage static pipeline:\n"
            "  detect → bootstrap extract → VM dispatch parse → blob decode "
            "(base64 / numeric-escape / XOR key search) → string recovery → "
            "Lua 5.1 bytecode parse → custom-VM heuristic decode → "
            "CFG construction → instruction lift → constant fold\n"
            "  Unknown opcodes are preserved as `-- [LURAPH]` comments, never guessed.\n"
            "**Others** — string / constant extraction only"
        ),
        inline=False)
    await ctx.reply(embed=embed)


# ============================================================
# Error handler
# ============================================================

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    if isinstance(error, commands.NoPrivateMessage):
        await ctx.reply("❌ This command only works in a server channel.")
        return
    if isinstance(error, commands.MissingPermissions):
        await ctx.reply("❌ You do not have permission to use this command.")
        return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.reply(f"⏳ Try again in {error.retry_after:.1f}s.")
        return
    await ctx.reply(f"❌ Unexpected error: {type(error).__name__}: {error}")


# ============================================================
# Start
# ============================================================

if not TOKEN:
    raise RuntimeError("TOKEN environment variable is not set.")

bot.run(TOKEN)
