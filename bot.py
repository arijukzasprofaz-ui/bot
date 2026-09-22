import ast
import asyncio
import base64
import io
import math
import os
import random
import re
import struct
from dataclasses import dataclass, field
from typing import Optional

import discord
from discord.ext import commands

# ============================================================
# Configuration
# ============================================================

TOKEN = os.getenv("TOKEN")

MAX_INPUT_BYTES = 2 * 1024 * 1024
MAX_OUTPUT_CHARS = 7_500_000
MAX_DISCORD_FILE_BYTES = 2 * 1024 * 1024
MAX_PROTO_DEPTH = 64
MAX_PROTOS = 10_000
MAX_INSTRUCTIONS = 500_000
MAX_CONSTANTS = 200_000
MAX_STRINGS = 20_000
MAX_STRING_LENGTH = 200_000

LURAPH_BLOB_WINDOW = 500_000
LURAPH_DISPATCH_WINDOW = 300_000
LURAPH_XOR_SCAN_WINDOW = 200_000

ANALYSIS_CONCURRENCY = 2
TRACE_DELAY = (1.5, 3.0)

analysis_semaphore = asyncio.Semaphore(ANALYSIS_CONCURRENCY)
_busy_channels: set[int] = set()

# ============================================================
# Lua 5.1 opcodes
# ============================================================

LUA51_OPS = {
    0: "MOVE", 1: "LOADK", 2: "LOADBOOL", 3: "LOADNIL",
    4: "GETUPVAL", 5: "GETGLOBAL", 6: "GETTABLE", 7: "SETGLOBAL",
    8: "SETUPVAL", 9: "SETTABLE", 10: "NEWTABLE", 11: "SELF",
    12: "ADD", 13: "SUB", 14: "MUL", 15: "DIV", 16: "MOD",
    17: "POW", 18: "UNM", 19: "NOT", 20: "LEN", 21: "CONCAT",
    22: "JMP", 23: "EQ", 24: "LT", 25: "LE", 26: "TEST", 27: "TESTSET",
    28: "CALL", 29: "TAILCALL", 30: "RETURN", 31: "FORLOOP", 32: "FORPREP",
    33: "TFORLOOP", 34: "SETLIST", 35: "CLOSE", 36: "CLOSURE", 37: "VARARG",
}

ARITHMETIC_OPS = {"ADD": "+", "SUB": "-", "MUL": "*", "DIV": "/", "MOD": "%", "POW": "^"}
JUMP_OPS = {"JMP", "FORPREP", "FORLOOP"}
COND_OPS = {"EQ", "LT", "LE", "TEST", "TESTSET", "TFORLOOP"}
TERM_OPS = {"RETURN", "TAILCALL"}

# ============================================================
# Data structures
# ============================================================

@dataclass
class LuraphInstr:
    pc: int
    raw_opcode: int
    opcode_name: str
    a: Optional[int] = None
    b: object = None
    c: object = None
    bx: Optional[int] = None
    sbx: Optional[int] = None
    const_refs: list = field(default_factory=list)
    target_addr: Optional[int] = None


@dataclass
class LuraphProto:
    index: int
    depth: int
    param_count: int = 0
    is_vararg: bool = False
    max_stack: int = 0
    instructions: list = field(default_factory=list)
    constants: list = field(default_factory=list)
    upvalue_count: int = 0
    protos: list = field(default_factory=list)
    source_name: str = ""


@dataclass
class BasicBlock:
    id: int
    start_pc: int
    end_pc: int
    instrs: list = field(default_factory=list)
    successors: list = field(default_factory=list)
    predecessors: list = field(default_factory=list)


@dataclass
class LuraphResult:
    detected: bool = False
    version_hint: str = "unknown"
    stages: list = field(default_factory=list)
    bootstrap_source: str = ""
    data_blobs: list = field(default_factory=list)
    all_strings: list = field(default_factory=list)
    prototypes: list = field(default_factory=list)
    unknown_opcodes: set = field(default_factory=set)
    vm_opcode_map: dict = field(default_factory=dict)
    bytecode_size: int = 0
    instruction_count: int = 0
    constant_count: int = 0
    string_count: int = 0
    proto_count: int = 0
    notes: list = field(default_factory=list)
    raw_output: str = ""
    decompiled_output: str = ""


@dataclass
class Analysis:
    ok: bool
    family: str
    raw: str = ""
    decompiled: str = ""
    notes: str = ""

# ============================================================
# General helpers
# ============================================================

def _lua_literal(value):
    if value is None:
        return "nil"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return repr(value)
    if isinstance(value, float) and value.is_integer():
        return str(int(value))
    return repr(value)


def _reg(value):
    return f"r{value}" if isinstance(value, int) else _lua_literal(value)


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
        if any(not isinstance(node, allowed) for node in ast.walk(tree)):
            return None
        return eval(compile(tree, "<expr>", "eval"), {"__builtins__": {}}, {})
    except Exception:
        return None


def _simplify_constants(text: str) -> str:
    def replace(match):
        value = _safe_expr(match.group(0))
        return str(value) if isinstance(value, (int, float)) else match.group(0)
    return re.sub(r"\b\d+(?:\s*[+\-*/%]\s*\d+)+\b", replace, text)


def _clip_text(text: str, limit: int = MAX_OUTPUT_CHARS) -> str:
    if len(text) <= limit:
        return text
    return text[:limit] + f"\n\n-- [truncated at {limit:,} characters]"


def _unique_append(out: list, seen: set, value: str, max_items=MAX_STRINGS):
    if len(out) >= max_items or not value or not isinstance(value, str):
        return
    if len(value) > MAX_STRING_LENGTH:
        value = value[:MAX_STRING_LENGTH] + "..."
    if value not in seen:
        seen.add(value)
        out.append(value)

# ============================================================
# Obfuscator detection
# ============================================================

def _luraph_quick_check(code: str) -> bool:
    head = code[:5_000].lower()
    if "luraph" in head:
        return True
    sample = code[:120_000]
    return bool(re.search(r"\[\s*\d+\s*\]\s*=\s*function", sample)) and bool(
        re.search(r"\bloadstring\s*\(", sample)
    )


SIGNATURES = [
    ("WeAreDevs", lambda c: bool(re.search(
        r"wearedevs\s*\.\s*net\s*/\s*obfuscator|"
        r"wearedevs\s*obfuscator|--\[\[\s*v1\.0\.0\s+https?://wearedevs",
        c[:12_000], re.I))),
    ("LuaObfuscator", lambda c: bool(re.search(r'''VMCall\s*\(\s*["']LOL!''', c))),
    ("Luraph", _luraph_quick_check),
    ("IronBrew3", lambda c: bool(re.search(r"ironbrew\s*3", c[:2_000], re.I))),
    ("IronBrew2", lambda c: bool(re.search(r"ironbrew\s*2", c[:2_000], re.I))),
    ("IronBrew", lambda c: bool(re.search(r"ironbrew", c[:2_000], re.I))),
    ("MoonVeil", lambda c: bool(re.search(r"moonveil", c[:3_000], re.I))),
    ("MoonSec", lambda c: bool(re.search(r"moonsec", c[:3_000], re.I))),
    ("Prometheus", lambda c: bool(re.search(r"prometheus", c[:3_000], re.I))),
    ("SynapseXen", lambda c: bool(re.search(r"synapse.*xen|xen.*synapse", c[:1_000], re.I))),
    ("Hercules", lambda c: bool(re.search(r"hercules", c[:3_000], re.I))),
    ("Boronide", lambda c: bool(re.search(r"boronide", c[:3_000], re.I))),
    ("77fuscator", lambda c: bool(re.search(r"77fuscator", c[:3_000], re.I))),
    ("wYnFuscate", lambda c: bool(re.search(r"wyn(?:fuscate|obf)", c[:3_000], re.I))),
    ("PSU", lambda c: bool(re.search(r"\bPSU\b", c[:1_000]))),
    ("LPS", lambda c: bool(re.search(r"\bLPS\b", c[:1_000]))),
]


def detect_obfuscator(code: str) -> str:
    code = code.lstrip("\ufeff").strip()
    if re.search(
        r"--\[\[\s*v1\.0\.0\s+https?://wearedevs\.net/obfuscator\s*\]\]",
        code[:12_000], re.I,
    ):
        return "WeAreDevs"
    if re.search(r"wearedevs\.net\s*/\s*obfuscator", code[:12_000], re.I):
        return "WeAreDevs"
    for name, check in SIGNATURES:
        try:
            if check(code):
                return name
        except Exception:
            continue
    return "Unknown"

# ============================================================
# Reader / Lua 5.1 parser
# ============================================================

class Reader:
    def __init__(self, data: bytes, endian: str = "<"):
        self.d = data
        self.p = 0
        self.endian = endian

    def _need(self, size: int):
        if size < 0 or self.p + size > len(self.d):
            raise ValueError(f"Unexpected end of bytecode at offset {self.p}")

    def u8(self):
        self._need(1)
        value = self.d[self.p]
        self.p += 1
        return value

    def u16(self):
        self._need(2)
        value = struct.unpack_from(self.endian + "H", self.d, self.p)[0]
        self.p += 2
        return value

    def u32(self):
        self._need(4)
        value = struct.unpack_from(self.endian + "I", self.d, self.p)[0]
        self.p += 4
        return value

    def f64(self):
        self._need(8)
        value = struct.unpack_from(self.endian + "d", self.d, self.p)[0]
        self.p += 8
        return value

    def string(self, length=None):
        if length is None:
            length = self.u32()
        if length == 0:
            return ""
        if length > MAX_STRING_LENGTH + 1:
            raise ValueError(f"Lua string too large: {length:,} bytes")
        self._need(length)
        raw = self.d[self.p:self.p + length]
        self.p += length
        return raw.rstrip(b"\x00").decode("utf-8", errors="replace")

    @staticmethod
    def gbit(value, start, end=None):
        if end is None:
            return (value >> (start - 1)) & 1
        width = end - start + 1
        return (value >> (start - 1)) & ((1 << width) - 1)


def _parse_lua51_header(reader: Reader) -> dict:
    reader._need(12)
    if reader.d[reader.p:reader.p + 4] != b"\x1bLua":
        raise ValueError("Not a Lua bytecode file: bad magic")
    reader.p += 4

    hdr = {
        "version": reader.u8(),
        "format": reader.u8(),
        "endian": reader.u8(),
        "int_sz": reader.u8(),
        "sizet_sz": reader.u8(),
        "instr_sz": reader.u8(),
        "num_sz": reader.u8(),
        "integral": reader.u8(),
    }

    if hdr["version"] != 0x51:
        raise ValueError(f"Unsupported Lua bytecode version: 0x{hdr['version']:02x}")
    if hdr["format"] != 0:
        raise ValueError(f"Unsupported Lua bytecode format: {hdr['format']}")
    if hdr["endian"] != 1:
        raise ValueError("Only little-endian Lua 5.1 bytecode is supported")
    if hdr["int_sz"] != 4 or hdr["sizet_sz"] not in (4, 8):
        raise ValueError("Unsupported Lua integer/size_t layout")
    if hdr["instr_sz"] != 4:
        raise ValueError("Unsupported Lua instruction size")
    if hdr["num_sz"] != 8:
        raise ValueError("Unsupported Lua number size")
    if hdr["integral"] != 0:
        raise ValueError("Integral Lua number format is not supported")
    return hdr


def _read_lua51_string(reader: Reader) -> str:
    return reader.string()


def _validate_count(label: str, value: int, maximum: int):
    if value < 0 or value > maximum:
        raise ValueError(f"Unreasonable {label}: {value:,}")


def _decode_lua51_instrs(raw: list[int], consts: list) -> list[LuraphInstr]:
    out = []
    for pc, word in enumerate(raw):
        opcode = word & 0x3F
        a = (word >> 6) & 0xFF
        c = (word >> 14) & 0x1FF
        b = (word >> 23) & 0x1FF
        bx = (word >> 14) & 0x3FFFF
        sbx = bx - 131071

        name = LUA51_OPS.get(opcode, f"UNKNOWN_{opcode}")
        b_val = b
        c_val = c
        const_refs = []

        if name in {"LOADK", "GETGLOBAL", "SETGLOBAL"}:
            if bx < len(consts):
                b_val = consts[bx][1]
                const_refs.append(("Bx", bx))
        else:
            if b >= 256:
                idx = b - 256
                if idx < len(consts):
                    b_val = consts[idx][1]
                    const_refs.append(("B", idx))
            if c >= 256:
                idx = c - 256
                if idx < len(consts):
                    c_val = consts[idx][1]
                    const_refs.append(("C", idx))

        target = pc + 1 + sbx if name in {"JMP", "FORPREP", "FORLOOP"} else None
        out.append(LuraphInstr(
            pc=pc,
            raw_opcode=opcode,
            opcode_name=name,
            a=a,
            b=b_val,
            c=c_val,
            bx=bx,
            sbx=sbx,
            const_refs=const_refs,
            target_addr=target,
        ))
    return out


def _parse_lua51_chunk(reader: Reader, depth: int = 0, idx: int = 0) -> LuraphProto:
    if depth > MAX_PROTO_DEPTH:
        raise ValueError("Prototype nesting depth exceeded")

    source = _read_lua51_string(reader)
    reader.u32()  # line_defined
    reader.u32()  # last_line_defined
    nups = reader.u8()
    nparams = reader.u8()
    is_vararg = reader.u8()
    maxstack = reader.u8()

    n_inst = reader.u32()
    _validate_count("instructions", n_inst, MAX_INSTRUCTIONS)
    raw_words = [reader.u32() for _ in range(n_inst)]

    n_consts = reader.u32()
    _validate_count("constants", n_consts, MAX_CONSTANTS)
    consts = []
    for _ in range(n_consts):
        tag = reader.u8()
        if tag == 0:
            consts.append(("nil", None))
        elif tag == 1:
            consts.append(("bool", reader.u8() != 0))
        elif tag == 3:
            consts.append(("num", reader.f64()))
        elif tag == 4:
            consts.append(("str", _read_lua51_string(reader)))
        else:
            raise ValueError(f"Unsupported Lua constant tag: {tag}")

    n_protos = reader.u32()
    _validate_count("sub-prototypes", n_protos, MAX_PROTOS)
    sub_protos = [
        _parse_lua51_chunk(reader, depth + 1, i)
        for i in range(n_protos)
    ]

    n_lines = reader.u32()
    _validate_count("line-info entries", n_lines, MAX_INSTRUCTIONS * 2)
    reader._need(n_lines * 4)
    reader.p += n_lines * 4

    n_locals = reader.u32()
    _validate_count("local-info entries", n_locals, MAX_CONSTANTS)
    for _ in range(n_locals):
        _read_lua51_string(reader)
        reader._need(8)
        reader.p += 8

    n_upvals = reader.u32()
    _validate_count("upvalue-info entries", n_upvals, MAX_CONSTANTS)
    for _ in range(n_upvals):
        _read_lua51_string(reader)

    return LuraphProto(
        index=idx,
        depth=depth,
        param_count=nparams,
        is_vararg=bool(is_vararg),
        max_stack=maxstack,
        instructions=_decode_lua51_instrs(raw_words, consts),
        constants=consts,
        upvalue_count=nups,
        protos=sub_protos,
        source_name=source or f"@lua51_d{depth}_f{idx}",
    )

# ============================================================
# CFG + Lua 5.1 lifting
# ============================================================

def _build_cfg(proto: LuraphProto) -> list[BasicBlock]:
    instrs = proto.instructions
    if not instrs:
        return []

    leaders = {0}
    for i, ins in enumerate(instrs):
        nm = ins.opcode_name
        if nm in JUMP_OPS | TERM_OPS:
            if i + 1 < len(instrs):
                leaders.add(i + 1)
        if nm in JUMP_OPS and ins.target_addr is not None:
            if 0 <= ins.target_addr < len(instrs):
                leaders.add(ins.target_addr)
        if nm in {"EQ", "LT", "LE", "TEST", "TESTSET", "TFORLOOP"}:
            if i + 1 < len(instrs):
                leaders.add(i + 1)
            if i + 2 < len(instrs):
                leaders.add(i + 2)

    sorted_leaders = sorted(leaders)
    blocks = []
    for i, leader in enumerate(sorted_leaders):
        end = sorted_leaders[i + 1] - 1 if i + 1 < len(sorted_leaders) else len(instrs) - 1
        blocks.append(BasicBlock(
            id=i, start_pc=leader, end_pc=end, instrs=instrs[leader:end + 1]
        ))

    pc_to_block = {}
    for block in blocks:
        for pc in range(block.start_pc, block.end_pc + 1):
            pc_to_block[pc] = block.id

    def add_edge(src: int, dst_pc: int):
        if dst_pc not in pc_to_block:
            return
        dst = pc_to_block[dst_pc]
        if dst not in blocks[src].successors:
            blocks[src].successors.append(dst)
        if src not in blocks[dst].predecessors:
            blocks[dst].predecessors.append(src)

    for block in blocks:
        last = block.instrs[-1]
        nm = last.opcode_name
        next_pc = block.end_pc + 1
        if nm in TERM_OPS:
            continue
        if nm == "JMP":
            if last.target_addr is not None:
                add_edge(block.id, last.target_addr)
            continue
        if nm in {"FORPREP", "FORLOOP"}:
            if next_pc < len(instrs):
                add_edge(block.id, next_pc)
            if last.target_addr is not None:
                add_edge(block.id, last.target_addr)
            continue
        if nm in {"EQ", "LT", "LE", "TEST", "TESTSET", "TFORLOOP"}:
            if next_pc < len(instrs):
                add_edge(block.id, next_pc)
            if next_pc + 1 < len(instrs):
                add_edge(block.id, next_pc + 1)
            continue
        if next_pc < len(instrs):
            add_edge(block.id, next_pc)

    return blocks


def _lift_call(ins: LuraphInstr) -> str:
    a = ins.a or 0
    b = ins.b if isinstance(ins.b, int) else None
    c = ins.c if isinstance(ins.c, int) else None

    if b == 0:
        args = "..."
    elif b == 1:
        args = ""
    else:
        args = ", ".join(f"r{i}" for i in range(a + 1, a + b))

    if c == 0:
        returns = f"r{a}, ..."
    elif c == 1:
        returns = None
    elif c is not None:
        values = ", ".join(f"r{i}" for i in range(a, a + c - 1))
        returns = values
    else:
        returns = None

    call = f"r{a}({args})"
    return f"{returns} = {call}" if returns else call


def _lift_instr(ins: LuraphInstr) -> str:
    nm = ins.opcode_name
    a, b, c = ins.a, ins.b, ins.c

    def rg(value):
        return f"r{value}" if isinstance(value, int) else _lua_literal(value)

    if nm == "MOVE":
        return f"r{a} = {rg(b)}"
    if nm == "LOADK":
        return f"r{a} = {_lua_literal(b)}"
    if nm == "LOADBOOL":
        return f"r{a} = {'true' if b else 'false'}" + ("  -- skip next" if c else "")
    if nm == "LOADNIL":
        end = b if isinstance(b, int) else a
        return f"r{a}..r{end} = nil"
    if nm == "GETUPVAL":
        return f"r{a} = upval[{b}]"
    if nm == "SETUPVAL":
        return f"upval[{b}] = r{a}"
    if nm == "GETGLOBAL":
        return f"r{a} = _G[{_lua_literal(b)}]"
    if nm == "SETGLOBAL":
        return f"_G[{_lua_literal(b)}] = r{a}"
    if nm == "GETTABLE":
        return f"r{a} = r{b}[{rg(c)}]"
    if nm == "SETTABLE":
        return f"r{a}[{rg(b)}] = {rg(c)}"
    if nm == "NEWTABLE":
        return f"r{a} = {{}}  -- array_size:{b} hash_size:{c}"
    if nm == "SELF":
        return f"r{a + 1} = r{b}; r{a} = r{b}[{rg(c)}]"
    if nm in ARITHMETIC_OPS:
        return f"r{a} = {rg(b)} {ARITHMETIC_OPS[nm]} {rg(c)}"
    if nm == "UNM":
        return f"r{a} = -{rg(b)}"
    if nm == "NOT":
        return f"r{a} = not {rg(b)}"
    if nm == "LEN":
        return f"r{a} = #{rg(b)}"
    if nm == "CONCAT":
        if isinstance(b, int) and isinstance(c, int):
            parts = " .. ".join(f"r{i}" for i in range(b, c + 1))
            return f"r{a} = {parts}"
        return f"r{a} = {rg(b)} .. {rg(c)}"
    if nm == "JMP":
        return f"goto L{ins.target_addr}" if ins.target_addr is not None else f"-- JMP sbx={ins.sbx}"
    if nm in {"EQ", "LT", "LE"}:
        cmpop = {"EQ": "==", "LT": "<", "LE": "<="}[nm]
        neg = "" if a == 0 else "not "
        return f"if {neg}({rg(b)} {cmpop} {rg(c)}) then skip_next"
    if nm == "TEST":
        return f"if {'not ' if not c else ''}r{a} then skip_next"
    if nm == "TESTSET":
        return f"if {'not ' if not c else ''}r{b} then r{a} = r{b} else skip_next"
    if nm == "CALL":
        return _lift_call(ins)
    if nm == "TAILCALL":
        b_int = b if isinstance(b, int) else 0
        args = "..." if b_int == 0 else ", ".join(f"r{i}" for i in range(a + 1, a + b_int)) if b_int > 1 else ""
        return f"return r{a}({args})  -- tail call"
    if nm == "RETURN":
        if b == 1:
            return "return"
        if b == 0:
            return f"return r{a}, ..."
        end = a + b - 2
        return f"return r{a}" + (f"..r{end}" if end > a else "")
    if nm == "FORPREP":
        return f"r{a} = r{a} - r{a + 2}; goto L{ins.target_addr}"
    if nm == "FORLOOP":
        return f"r{a} += r{a + 2}; if r{a} <= r{a + 1} then r{a + 3} = r{a}; goto L{ins.target_addr}"
    if nm == "TFORLOOP":
        count = c if isinstance(c, int) else 1
        returns = ", ".join(f"r{a + 3 + i}" for i in range(count))
        return f"{returns} = r{a}(r{a + 1}, r{a + 2}); if r{a + 3} == nil then skip_next"
    if nm == "SETLIST":
        return f"-- SETLIST A={a} B={b} C={c}"
    if nm == "CLOSE":
        return f"-- close upvalues down to r{a}"
    if nm == "CLOSURE":
        return f"r{a} = closure(proto[{ins.bx}])"
    if nm == "VARARG":
        if b == 0:
            return f"r{a}... = ..."
        if isinstance(b, int) and b > 1:
            return f"r{a}..r{a + b - 2} = ..."
        return f"r{a} = ..."
    return f"-- [LUA] {nm} A={a!r} B={b!r} C={c!r}"


def _lift_proto(proto: LuraphProto, indent=0) -> list[str]:
    blocks = _build_cfg(proto)
    pad = "    " * indent
    inner = "    " * (indent + 1)
    lines = []
    params = [f"r{i}" for i in range(proto.param_count)]
    if proto.is_vararg:
        params.append("...")
    fname = f"__lua_func_{proto.depth}_{proto.index}"
    lines.append(f"{pad}local function {fname}({', '.join(params)})")
    lines.append(f"{inner}-- source: {proto.source_name or 'unknown'}")
    lines.append(f"{inner}-- maxstack: {proto.max_stack}; upvalues: {proto.upvalue_count}")

    label_pcs = {
        ins.target_addr
        for block in blocks
        for ins in block.instrs
        if ins.target_addr is not None
    }
    for block in blocks:
        if block.start_pc in label_pcs:
            lines.append(f"{inner}::L{block.start_pc}::")
        for ins in block.instrs:
            lines.append(f"{inner}{_lift_instr(ins)}")

    lines.append(f"{pad}end -- {fname}")
    for sub in proto.protos:
        lines.append("")
        lines.extend(_lift_proto(sub, indent))
    return lines


def _count_protos(proto: LuraphProto) -> int:
    return 1 + sum(_count_protos(p) for p in proto.protos)


def _count_instrs(proto: LuraphProto) -> int:
    return len(proto.instructions) + sum(_count_instrs(p) for p in proto.protos)


def _count_consts(proto: LuraphProto) -> int:
    return len(proto.constants) + sum(_count_consts(p) for p in proto.protos)


def _collect_unknown_ops(proto: LuraphProto, out=None) -> set:
    if out is None:
        out = set()
    for ins in proto.instructions:
        if ins.opcode_name.startswith("UNKNOWN_"):
            out.add(ins.raw_opcode)
    for sub in proto.protos:
        _collect_unknown_ops(sub, out)
    return out


def _collect_proto_strings(proto: LuraphProto) -> list[str]:
    out = [value for typ, value in proto.constants if typ == "str" and value]
    for sub in proto.protos:
        out.extend(_collect_proto_strings(sub))
    return out

# ============================================================
# LuaObfuscator backend
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


def parse_chunk(reader: Reader, depth=0, total_state=None):
    if total_state is None:
        total_state = {"functions": 0, "instructions": 0}
    if depth > MAX_PROTO_DEPTH:
        raise ValueError("LuaObfuscator function nesting exceeded")
    total_state["functions"] += 1
    if total_state["functions"] > MAX_PROTOS:
        raise ValueError("Too many LuaObfuscator functions")

    const_count = reader.u32()
    _validate_count("LuaObfuscator constants", const_count, MAX_CONSTANTS)
    consts = []
    for _ in range(const_count):
        tag = reader.u8()
        if tag == 1:
            consts.append(("bool", reader.u8() != 0))
        elif tag == 2:
            consts.append(("num", reader.f64()))
        elif tag == 3:
            consts.append(("str", reader.string()))
        else:
            consts.append(("nil", None))

    params = reader.u8()
    instr_count = reader.u32()
    _validate_count("LuaObfuscator instructions", instr_count, MAX_INSTRUCTIONS)
    total_state["instructions"] += instr_count
    if total_state["instructions"] > MAX_INSTRUCTIONS:
        raise ValueError("Too many LuaObfuscator instructions")

    instrs = []
    for _ in range(instr_count):
        desc = reader.u8()
        if Reader.gbit(desc, 1):
            continue
        typ = Reader.gbit(desc, 2, 3)
        mask = Reader.gbit(desc, 4, 6)
        op = reader.u16()
        a = reader.u16()
        b = c = None
        if typ == 0:
            b, c = reader.u16(), reader.u16()
        elif typ == 1:
            b = reader.u32()
        elif typ == 2:
            b = reader.u32() - (1 << 16)
        elif typ == 3:
            b, c = reader.u32() - (1 << 16), reader.u16()

        def resolve(value, bit):
            if (
                value is not None and Reader.gbit(mask, bit)
                and isinstance(value, int) and 0 <= value < len(consts)
            ):
                return consts[value][1]
            return value

        instrs.append((op, resolve(a, 1), resolve(b, 2), resolve(c, 3)))

    sub_count = reader.u32()
    _validate_count("LuaObfuscator sub-functions", sub_count, MAX_PROTOS)
    subs = [parse_chunk(reader, depth + 1, total_state) for _ in range(sub_count)]
    return {
        "depth": depth,
        "params": params,
        "consts": consts,
        "instrs": instrs,
        "subs": subs,
    }


def collect_consts(chunk, out=None):
    if out is None:
        out = []
    out.extend(chunk["consts"])
    for sub in chunk["subs"]:
        collect_consts(sub, out)
    return out


def count_funcs(chunk):
    return 1 + sum(count_funcs(x) for x in chunk["subs"])


def lift_lua_chunk(chunk, indent=0):
    pad = "    " * indent
    lines = []
    instrs = chunk["instrs"]

    for i, (op, a, b, c) in enumerate(instrs):
        name = LUA51_OPS.get(op, f"vm_op_{op}")
        if name == "MOVE":
            lines.append(f"{pad}r{a} = {_reg(b)}")
        elif name == "LOADK":
            lines.append(f"{pad}r{a} = {_lua_literal(b)}")
        elif name == "LOADBOOL":
            lines.append(f"{pad}r{a} = {'true' if b else 'false'}")
        elif name == "LOADNIL":
            lines.append(f"{pad}r{a} = nil")
        elif name in ARITHMETIC_OPS:
            lines.append(f"{pad}r{a} = {_reg(b)} {ARITHMETIC_OPS[name]} {_reg(c)}")
        elif name == "UNM":
            lines.append(f"{pad}r{a} = -{_reg(b)}")
        elif name == "NOT":
            lines.append(f"{pad}r{a} = not {_reg(b)}")
        elif name == "LEN":
            lines.append(f"{pad}r{a} = #{_reg(b)}")
        elif name == "CONCAT":
            lines.append(f"{pad}r{a} = {_reg(b)} .. {_reg(c)}")
        elif name == "GETGLOBAL":
            lines.append(f"{pad}r{a} = _G[{_lua_literal(b)}]")
        elif name == "SETGLOBAL":
            lines.append(f"{pad}_G[{_lua_literal(b)}] = {_reg(a)}")
        elif name == "GETUPVAL":
            lines.append(f"{pad}r{a} = upvalue_{b}")
        elif name == "SETUPVAL":
            lines.append(f"{pad}upvalue_{b} = {_reg(a)}")
        elif name == "GETTABLE":
            lines.append(f"{pad}r{a} = {_reg(b)}[{_reg(c)}]")
        elif name == "SETTABLE":
            lines.append(f"{pad}{_reg(a)}[{_reg(b)}] = {_reg(c)}")
        elif name == "JMP":
            target = i + 1 + a if isinstance(a, int) else None
            lines.append(f"{pad}goto L{target}" if target is not None else f"{pad}-- JMP {a!r}")
        elif name in {"EQ", "LT", "LE"}:
            cmp = {"EQ": "==", "LT": "<", "LE": "<="}[name]
            lines.append(f"{pad}-- if {_reg(b)} {cmp} {_reg(c)} then skip next")
        elif name == "CALL":
            lines.append(f"{pad}-- CALL A={a} B={b} C={c}")
        elif name == "RETURN":
            lines.append(f"{pad}return {_reg(a)}")
        elif name == "CLOSURE":
            lines.append(f"{pad}r{a} = function(...) -- nested function")
        else:
            lines.append(f"{pad}-- {name} A={a!r} B={b!r} C={c!r}")

    for idx, sub in enumerate(chunk["subs"], 1):
        lines.append("")
        lines.append(f"{pad}local function __deob_func_{chunk['depth']}_{idx}(...)")
        lines.extend(lift_lua_chunk(sub, indent + 1))
        lines.append(f"{pad}end")
    return lines


def deobfuscate_luaobfuscator(code: str, include_instrs=False) -> str:
    match = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
    if not match:
        return "[LuaObfuscator] VMCall payload not found."
    raw = decode_luaobf(match.group(1))
    chunk = parse_chunk(Reader(raw))
    consts = collect_consts(chunk)
    lines = [
        "=" * 62,
        "  LuaObfuscator.com — reconstructed Lua",
        f"  {len(raw):,} decoded bytes | {count_funcs(chunk)} functions",
        "=" * 62,
        "",
        "-- Best-effort static lift.",
        "-- Unknown/remapped VM operations are retained as comments.",
        "-- No submitted Lua/Luau code is executed.",
        "",
    ]
    lines.extend(lift_lua_chunk(chunk))
    result = _simplify_constants("\n".join(lines))
    if include_instrs:
        result += "\n\n-- CONSTANTS\n" + "\n".join(
            f"-- {i}: {typ} = {value!r}" for i, (typ, value) in enumerate(consts)
        )
    return _clip_text(result)

# ============================================================
# WeAreDevs static backend
# ============================================================

def _decode_lua_escapes(value: str) -> str:
    def replace(match):
        token = match.group(1)
        try:
            if token.lower().startswith("x"):
                return chr(int(token[1:], 16))
            return chr(int(token))
        except Exception:
            return match.group(0)

    value = re.sub(r"\\(x[0-9a-fA-F]{2}|[0-9]{1,3})", replace, value)
    return (
        value.replace(r'\"', '"')
        .replace(r"\'", "'")
        .replace(r"\\", "\\")
        .replace(r"\n", "\n")
        .replace(r"\r", "\r")
        .replace(r"\t", "\t")
    )


def _extract_lua_table_body(code: str, name: str, limit=400_000):
    match = re.search(r"\b(?:local\s+)?" + re.escape(name) + r"\s*=\s*\{", code[:limit])
    if not match:
        return None
    start = match.end()
    depth = 1
    quote = None
    escape = False
    for i in range(start, min(len(code), limit)):
        ch = code[i]
        if quote:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
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
    result = {}
    if not body:
        return result
    pattern = re.compile(
        r'''(?:\[\s*(["'])(.*?)\1\s*\]|([A-Za-z_][A-Za-z0-9_]*))\s*=\s*([0-9+\-*/%().\s]+)(?=[,;]|$)'''
    )
    for match in pattern.finditer(body):
        key = match.group(2) if match.group(2) is not None else match.group(3)
        value = _safe_expr(match.group(4))
        if value is not None and len(key) == 1 and isinstance(value, (int, float)):
            result[key] = int(value)
    return result


def _extract_quoted_strings(body):
    return [
        _decode_lua_escapes(m.group(1))
        for m in re.finditer(r'"((?:\\.|[^"\\]){0,200000})"', body or "")
    ]


def _custom_b64_decode(value: str, alphabet: dict) -> Optional[str]:
    if not value or value[0] not in ("?", "s") or not alphabet:
        return None
    width, out_width = (5, 4) if value[0] == "?" else (4, 3)
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
        number = 0
        for value in chunk:
            number = number * 64 + value
        for shift in range((out_width - 1) * 8, -1, -8):
            out.append((number >> shift) & 0xFF)
        if real < width:
            del out[-min(width - real, out_width):]
    try:
        return out.decode("utf-8")
    except UnicodeDecodeError:
        return out.decode("latin-1", errors="replace")


def _decode_wad_strings(code: str):
    ubody = _extract_lua_table_body(code, "U")
    omap = _parse_numeric_lookup_table(_extract_lua_table_body(code, "o") or "")
    wmap = _parse_numeric_lookup_table(_extract_lua_table_body(code, "w") or "")
    strings = _extract_quoted_strings(ubody or "")
    decoded = []
    for value in strings:
        decoded_value = (
            _custom_b64_decode(value, omap) if value.startswith("?")
            else _custom_b64_decode(value, wmap) if value.startswith("s")
            else None
        )
        decoded.append(decoded_value if decoded_value is not None else value)
    return decoded, omap, wmap


def _replace_wad_string_indexes(code: str, decoded):
    def replace(match):
        index = int(match.group(1)) - 1
        if 0 <= index < len(decoded):
            return _lua_literal(decoded[index])
        return match.group(0)
    return re.sub(r"\bU\s*\[\s*(\d+)\s*\]", replace, code)


def _extract_balanced_call_args(code: str, func_name: str, limit=20):
    results = []
    pattern = re.compile(r"\b" + re.escape(func_name) + r"\s*\(")
    for match in pattern.finditer(code):
        i = match.end()
        depth = 1
        quote = None
        escape = False
        start = i
        while i < len(code):
            ch = code[i]
            if quote:
                if escape:
                    escape = False
                elif ch == "\\":
                    escape = True
                elif ch == quote:
                    quote = None
            else:
                if ch in "\"'":
                    quote = ch
                elif ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        fragment = code[start:i].strip()
                        if len(fragment) <= MAX_STRING_LENGTH:
                            results.append(fragment)
                        break
            i += 1
        if len(results) >= limit:
            break
    return results


def _fold_simple_lua_constants(code: str, rounds=4):
    for _ in range(rounds):
        old = code
        code = re.sub(
            r"(?<![A-Za-z_])\d+(?:\s*[+\-*/%]\s*\d+)+(?![A-Za-z_])",
            lambda m: str(_safe_expr(m.group(0))) if _safe_expr(m.group(0)) is not None else m.group(0),
            code,
        )
        if code == old:
            break
    return code


def _recover_wad_layers(code: str, max_rounds=8):
    current = code
    recovered = []
    stats = []
    seen = {current}

    for round_no in range(max_rounds):
        decoded, omap, wmap = _decode_wad_strings(current)
        changed = False
        if decoded:
            replaced = _replace_wad_string_indexes(current, decoded)
            if replaced != current:
                current = replaced
                changed = True
                stats.append((round_no + 1, len(decoded), len(omap), len(wmap)))
                for value in decoded:
                    if isinstance(value, str) and len(value) >= 2 and value not in recovered:
                        recovered.append(value)

        current = _fold_simple_lua_constants(current)
        for payload in _extract_balanced_call_args(current, "loadstring"):
            if payload and payload not in recovered:
                recovered.append(payload)
                if re.search(r"\blocal\s+U\s*=\s*\{", payload) and payload not in seen:
                    seen.add(payload)
                    nested, _, _ = _decode_wad_strings(payload)
                    nested_code = _replace_wad_string_indexes(payload, nested)
                    if nested_code != payload:
                        current += "\n\n-- [WAD nested static payload]\n" + nested_code
                        changed = True

        if current in seen and not changed:
            break
        seen.add(current)

    return current, recovered, stats


def _strip_named_lua_table(code: str, name: str):
    match = re.search(r"\b(?:local\s+)?" + re.escape(name) + r"\s*=\s*\{", code, re.M)
    if not match:
        return code
    start = match.start()
    depth = 0
    quote = None
    escape = False
    for i in range(match.end() - 1, len(code)):
        ch = code[i]
        if quote:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
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
                while end < len(code) and code[end] in " \t\r\n;":
                    end += 1
                return code[:start] + code[end:]
    return code


def deobfuscate_wearedevs(code: str) -> str:
    lifted, recovered, stats = _recover_wad_layers(code)
    for name in ("U", "o", "w"):
        lifted = _strip_named_lua_table(lifted, name)
    lifted = re.sub(r"if\s+false\s+then[\s\S]*?end", "", lifted, flags=re.I)
    lifted = re.sub(r"\n{3,}", "\n\n", lifted).strip()

    unique = list(dict.fromkeys(recovered))
    header = [
        "=" * 62,
        "  WeAreDevs — recursive static reconstruction",
        f"  {len(code):,} chars | {len(unique):,} recovered strings/payloads",
        "=" * 62,
        "",
        "-- String/table layers decoded statically.",
        "-- Literal embedded payloads are extracted but NOT executed.",
        "-- VM/runtime semantics are not guessed.",
        "",
    ]
    if stats:
        header.append(
            "-- decode rounds: " + ", ".join(
                f"#{r} ({n} strings, o={o}, w={w})" for r, n, o, w in stats
            )
        )
        header.append("")
    header += ["-- RECONSTRUCTED SOURCE", "", lifted or "-- No non-table source could be reconstructed."]
    if unique:
        header += ["", "-- RECOVERED LITERAL PAYLOADS / STRINGS"]
        for i, value in enumerate(unique[:200], 1):
            clipped = value[:12_000]
            suffix = "\n-- [payload truncated]" if len(value) > 12_000 else ""
            header.extend([f"\n-- PAYLOAD {i}", clipped + suffix])
    header += ["", "-- Safety: submitted Lua/Luau was never executed."]
    return _clip_text("\n".join(header))

# ============================================================
# Luraph static backend
# ============================================================

def _luraph_stage1_detect(code: str):
    features = []
    version_hint = "unknown"
    sample = code[:LURAPH_DISPATCH_WINDOW]

    header = re.search(r"--\[\[\s*luraph[^\]]*\]\]", code[:2_000], re.I)
    if header:
        features.append("header_comment")
        version = re.search(r"v?(\d+\.\d+(?:\.\d+)?)", header.group(), re.I)
        if version:
            version_hint = version.group(1)

    if "luraph" in code[:5_000].lower():
        features.append("name_in_code")

    dispatch = re.findall(r"\[\s*(\d+)\s*\]\s*=\s*function", sample)
    if len(dispatch) >= 4:
        features.append(f"dispatch_table:{len(dispatch)}_opcodes")
        if len(dispatch) >= 20:
            features.append("full_vm_dispatch")
        if version_hint == "unknown":
            version_hint = (">=2.x" if len(dispatch) >= 25 else "1.x") + " (inferred)"

    if re.findall(r'"[A-Za-z0-9+/=]{200,}"', sample):
        features.append("base64_blob")
    if re.search(r"\[(=*)\[.{100,}?\]\1\]", sample, re.S):
        features.append("raw_blob")
    if re.findall(r'"(?:\\[0-9]{1,3}){50,}"', sample):
        features.append("numeric_escape_blob")

    env = sorted(set(re.findall(
        r"\b(getfenv|debug\.getinfo|debug\.sethook|debug\.getupvalue|newproxy)\b",
        sample,
    )))
    if env:
        features.append("env_protection:" + ",".join(env))
    if re.search(r"\bbit\b[.\w]*bxor|\bbxor\b", sample):
        features.append("xor_bitops")
    if re.search(r"\bloadstring\s*\(", sample):
        features.append("loadstring_bootstrap")

    detected = bool(
        "name_in_code" in features
        or "header_comment" in features
        or ("full_vm_dispatch" in features and any("blob" in f for f in features))
    )
    return detected, version_hint, features


def _luraph_stage2_bootstrap(code: str) -> str:
    skeleton = re.sub(r'"[A-Za-z0-9+/=]{200,}"', '"[ENCODED_BLOB]"', code[:LURAPH_DISPATCH_WINDOW])
    skeleton = re.sub(r"\[(=*)\[.{200,}?\]\1\]", "[[LONG_RAW_STRING]]", skeleton, flags=re.S)
    return skeleton[:20_000]


def _infer_opcode_from_body(body: str) -> str:
    text = body.lower()
    checks = [
        (r"\.", "UNKNOWN"),
        (r"\.\.", "CONCAT"),
        (r"=\s*-\s*(?:stk|s|reg)\[", "UNM"),
        (r"=\s*not\s+", "NOT"),
        (r"=\s*#(?:stk|s|reg)\[", "LEN"),
        (r"\*\s*(?:stk|s|reg)\[", "MUL"),
        (r"/\s*(?:stk|s|reg)\[", "DIV"),
        (r"%\s*(?:stk|s|reg)\[", "MOD"),
        (r"\^\s*(?:stk|s|reg)\[|math\.pow", "POW"),
        (r"\breturn\b", "RETURN"),
        (r"tailcall|tail.*call", "TAILCALL"),
        (r"\bcall\b|(?:stk|s|reg)\[a\]\s*\(", "CALL"),
        (r"forprep|prep.*for", "FORPREP"),
        (r"forloop|loop.*for", "FORLOOP"),
        (r"tforloop|generic.*for", "TFORLOOP"),
        (r"closure|proto\[", "CLOSURE"),
        (r"vararg", "VARARG"),
        (r"setlist", "SETLIST"),
        (r"close.*upval", "CLOSE"),
        (r"_?env\[.*\]\s*=|_G\s*\[.*\]\s*=", "SETGLOBAL"),
        (r"=\s*_?env\[|=\s*_G\s*\[", "GETGLOBAL"),
        (r"=\s*\{\}", "NEWTABLE"),
        (r"(?:stk|s)\[a\]\s*=\s*(?:stk|s)\[b\]\[", "GETTABLE"),
        (r"(?:stk|s)\[a\]\[", "SETTABLE"),
        (r"=\s*kst?\[|=\s*const\[|=\s*k\[bx?\]", "LOADK"),
        (r"=\s*(true|false)\b", "LOADBOOL"),
        (r"=\s*nil\b", "LOADNIL"),
        (r"pc\s*=\s*pc\s*\+|pc\s*\+=", "JMP"),
        (r"testset", "TESTSET"),
        (r"\btest\b", "TEST"),
        (r"<=", "LE"),
        (r"<(?!=)", "LT"),
        (r"==", "EQ"),
        (r"upval|upv\[", "GETUPVAL"),
        (r"\+\s*(?:stk|s|reg)\[", "ADD"),
        (r"-\s*(?:stk|s|reg)\[", "SUB"),
        (r"(?:stk|s|reg)\[a\]\s*=\s*(?:stk|s|reg)\[b\](?!\s*[+\-*/])", "MOVE"),
    ]
    for pattern, name in checks:
        if name != "UNKNOWN" and re.search(pattern, text):
            return name
    return "UNKNOWN"


def _luraph_stage3_dispatch(code: str) -> dict:
    opcode_map = {}
    sample = code[:LURAPH_DISPATCH_WINDOW]
    pattern = re.compile(
        r"\[\s*(\d+)\s*\]\s*=\s*function[^)]*\)"
        r"([\s\S]{1,1200}?)(?=\[\s*\d+\s*\]\s*=\s*function|\Z)",
        re.M,
    )
    for match in pattern.finditer(sample):
        opcode = int(match.group(1))
        name = _infer_opcode_from_body(match.group(2))
        opcode_map[opcode] = name
    return opcode_map


def _luraph_stage4_blobs(code: str) -> list:
    blobs = []
    area = code[:LURAPH_BLOB_WINDOW]

    for match in re.finditer(r'"([A-Za-z0-9+/=]{100,})"', area):
        blobs.append({
            "type": "quoted_b64",
            "raw": match.group(1),
            "offset": match.start(),
            "size": len(match.group(1)),
        })

    for match in re.finditer(r"\[(=*)\[([\s\S]{50,}?)\]\1\]", area):
        raw = match.group(2)
        blobs.append({
            "type": "raw_long_str",
            "raw": raw,
            "offset": match.start(),
            "size": len(raw),
        })

    for match in re.finditer(r'"((?:\\[0-9]{1,3}){30,})"', area):
        values = re.findall(r"\\([0-9]{1,3})", match.group(1))
        try:
            decoded = bytes(min(int(x), 255) for x in values)
        except Exception:
            continue
        blobs.append({
            "type": "numeric_escape",
            "raw": decoded,
            "offset": match.start(),
            "size": len(decoded),
        })

    blobs.sort(key=lambda item: item.get("size", 0), reverse=True)
    return blobs[:12]


def _luraph_try_decode(blob: dict) -> dict:
    result = {
        **blob,
        "decoded": None,
        "encoding": "none",
        "is_lua_bytecode": False,
    }
    raw = blob.get("raw")
    if raw is None:
        return result

    if isinstance(raw, (bytes, bytearray)):
        data = bytes(raw)
        result["decoded"] = data
        result["encoding"] = "raw_bytes"
        if data[:4] == b"\x1bLua":
            result["is_lua_bytecode"] = True
            result["encoding"] = "raw_lua51"
        return result

    text = str(raw)
    for label, fn in (
        ("base64", lambda value: base64.b64decode(value, validate=False)),
        ("urlsafe_b64", lambda value: base64.urlsafe_b64decode(value + "==")),
    ):
        try:
            padded = text + "=" * ((4 - len(text) % 4) % 4)
            decoded = fn(padded)
            if len(decoded) < 4:
                continue
            result["decoded"] = decoded
            result["encoding"] = label
            if decoded[:4] == b"\x1bLua":
                result["is_lua_bytecode"] = True
                result["encoding"] = label + "+lua51"
            return result
        except Exception:
            continue

    # Do not label an arbitrary Unicode source string as "decoded".
    return result


def _luraph_try_xor_keys(data: bytes, code: str) -> Optional[bytes]:
    for match in re.finditer(r"\{(\s*\d+(?:\s*,\s*\d+){3,63})\s*\}", code[:LURAPH_XOR_SCAN_WINDOW]):
        try:
            nums = [int(item.strip()) for item in match.group(1).split(",")]
            if not all(0 <= value <= 255 for value in nums):
                continue
            key = bytes(nums)
            decoded = bytes(value ^ key[i % len(key)] for i, value in enumerate(data))
            if decoded[:4] == b"\x1bLua":
                return decoded
        except Exception:
            continue
    return None


def _luraph_stage5_strings(code: str, decoded_blobs: list) -> list[str]:
    out = []
    seen = set()

    for match in re.finditer(r'"((?:[^"\\]|\\.){2,200000})"', code[:400_000]):
        _unique_append(out, seen, match.group(1))
    for match in re.finditer(r"'((?:[^'\\]|\\.){2,200000})'", code[:400_000]):
        _unique_append(out, seen, match.group(1))

    for blob in decoded_blobs:
        data = blob.get("decoded")
        if not isinstance(data, (bytes, bytearray)):
            continue
        for match in re.finditer(rb"[\x20-\x7e]{4,}", bytes(data)):
            try:
                _unique_append(out, seen, match.group(0).decode("ascii"))
            except Exception:
                pass
    return out


def luraph_analyze(code: str) -> LuraphResult:
    result = LuraphResult()
    if len(code.encode("utf-8", errors="ignore")) > MAX_INPUT_BYTES:
        encoded = code.encode("utf-8", errors="ignore")[:MAX_INPUT_BYTES]
        code = encoded.decode("utf-8", errors="ignore")
        result.notes.append("Input was truncated to the configured Luraph size limit.")

    detected, version_hint, features = _luraph_stage1_detect(code)
    result.detected = detected
    result.version_hint = version_hint
    feature_text = ", ".join(features) or "none"
    result.stages.append(
        f"stage1 detect={detected} version={version_hint} features=[{feature_text}]"
    )

    bootstrap = _luraph_stage2_bootstrap(code)
    result.bootstrap_source = bootstrap
    result.stages.append(f"stage2 bootstrap_preview={len(bootstrap)} chars")

    vm_map = _luraph_stage3_dispatch(code)
    result.vm_opcode_map = vm_map
    result.stages.append(
        f"stage3 heuristic_dispatch_entries={len(vm_map)}"
    )
    if vm_map:
        result.notes.append("Luraph VM opcode names are heuristic classifications, not verified semantics.")

    blobs = _luraph_stage4_blobs(code)
    decoded_blobs = [_luraph_try_decode(blob) for blob in blobs]
    for blob in decoded_blobs:
        data = blob.get("decoded")
        if isinstance(data, (bytes, bytearray)) and data[:4] != b"\x1bLua":
            xored = _luraph_try_xor_keys(bytes(data), code)
            if xored is not None:
                blob["decoded"] = xored
                blob["is_lua_bytecode"] = True
                blob["encoding"] += "+xor_key"
    result.data_blobs = decoded_blobs
    result.stages.append(
        f"stage4 blobs_found={len(blobs)} decoded={sum(1 for b in decoded_blobs if b.get('decoded') is not None)}"
    )

    result.all_strings = _luraph_stage5_strings(code, decoded_blobs)
    result.string_count = len(result.all_strings)
    result.stages.append(f"stage5 strings={result.string_count}")

    prototypes = []
    unknown_ops = set()
    total_bc_size = 0

    for blob in decoded_blobs:
        data = blob.get("decoded")
        if not isinstance(data, (bytes, bytearray)):
            continue
        data = bytes(data)

        if data[:4] == b"\x1bLua":
            try:
                reader = Reader(data)
                _parse_lua51_header(reader)
                proto = _parse_lua51_chunk(reader, depth=0, idx=len(prototypes))
                prototypes.append(proto)
                total_bc_size += len(data)
                unknown_ops |= _collect_unknown_ops(proto)
                for string in _collect_proto_strings(proto):
                    if string not in result.all_strings:
                        result.all_strings.append(string)
                result.stages.append(
                    f"stage6 lua51_bytecode {len(data):,}B "
                    f"{_count_protos(proto)} protos {_count_instrs(proto)} instrs "
                    f"{_count_consts(proto)} consts"
                )
            except Exception as exc:
                result.notes.append(
                    f"Lua 5.1 bytecode parse failed ({blob.get('encoding', '?')}): "
                    f"{type(exc).__name__}: {exc}"
                )
            continue

        if vm_map and len(data) >= 16 and len(data) % 4 == 0:
            try:
                words = struct.unpack(f"<{len(data) // 4}I", data)
                valid = sum(1 for word in words if (word & 0x3F) in vm_map)
                ratio = valid / len(words)
                if ratio >= 0.65 and len(words) >= 8:
                    instructions = []
                    for pc, word in enumerate(words):
                        opcode = word & 0x3F
                        a = (word >> 6) & 0xFF
                        c = (word >> 14) & 0x1FF
                        b = (word >> 23) & 0x1FF
                        bx = (word >> 14) & 0x3FFFF
                        sbx = bx - 131071
                        name = vm_map.get(opcode, f"UNKNOWN_{opcode}")
                        if name.startswith("UNKNOWN_"):
                            unknown_ops.add(opcode)
                        target = pc + 1 + sbx if name in {"JMP", "FORPREP", "FORLOOP"} else None
                        instructions.append(LuraphInstr(
                            pc=pc, raw_opcode=opcode, opcode_name=name,
                            a=a, b=b, c=c, bx=bx, sbx=sbx, target_addr=target,
                        ))
                    proto = LuraphProto(
                        index=len(prototypes), depth=0,
                        param_count=0, is_vararg=True, max_stack=255,
                        instructions=instructions,
                        source_name="@luraph_custom_vm",
                    )
                    prototypes.append(proto)
                    total_bc_size += len(data)
                    result.stages.append(
                        f"stage6 custom_vm_bytecode {len(data):,}B "
                        f"{len(instructions)} instrs opcode_match={ratio:.0%} (heuristic)"
                    )
            except Exception as exc:
                result.notes.append(
                    f"Custom-bytecode heuristic failed: {type(exc).__name__}: {exc}"
                )

    result.prototypes = prototypes
    result.unknown_opcodes = unknown_ops
    result.bytecode_size = total_bc_size
    result.proto_count = sum(_count_protos(proto) for proto in prototypes)
    result.instruction_count = sum(_count_instrs(proto) for proto in prototypes)
    result.constant_count = sum(_count_consts(proto) for proto in prototypes)
    result.string_count = len(result.all_strings)
    result.stages.append(
        f"summary protos={result.proto_count} instrs={result.instruction_count} "
        f"consts={result.constant_count} strings={result.string_count} "
        f"unknown_opcodes={len(unknown_ops)} bytecode_size={total_bc_size:,}B"
    )

    raw_lines = [
        "=" * 72,
        "  Luraph Static Analysis — Raw IR / Prototype Detail",
        f"  version hint : {version_hint}",
        f"  features     : {feature_text}",
        "=" * 72,
        "  No submitted Lua/Luau code was executed.",
        "  Luraph opcode classifications are heuristic unless verified by bytecode format.",
        "=" * 72,
        "",
    ]
    raw_lines.extend(f"-- {stage}" for stage in result.stages)
    raw_lines.append("")

    dec_lines = [
        "=" * 72,
        "  Luraph — Reconstructed Lua (static lift)",
        f"  {result.proto_count} prototype(s)  {result.instruction_count} instructions  {result.constant_count} constants",
        "=" * 72,
        "",
        "-- Static lift only. No submitted code was executed.",
        "-- VM opcode mappings marked heuristic are not guaranteed to be exact.",
        "",
    ]

    if prototypes:
        for proto in prototypes:
            blocks = _build_cfg(proto)
            raw_lines += [
                f"-- {'=' * 68}",
                f"-- Prototype {proto.index}",
                f"-- source       : {proto.source_name!r}",
                f"-- depth        : {proto.depth}",
                f"-- parameters   : {proto.param_count}   vararg: {proto.is_vararg}",
                f"-- maxstack     : {proto.max_stack}   upvalues: {proto.upvalue_count}",
                f"-- instructions : {len(proto.instructions)}",
                f"-- constants    : {len(proto.constants)}",
                "--",
                "-- CONSTANTS:",
            ]
            for index, (typ, value) in enumerate(proto.constants):
                raw_lines.append(f"--   [{index:4d}] {typ:8s} {value!r}")
            raw_lines += ["--", "-- INSTRUCTION IR:"]
            for ins in proto.instructions:
                target = f"→L{ins.target_addr}" if ins.target_addr is not None else ""
                raw_lines.append(
                    f"--   {ins.pc:6d} raw={ins.raw_opcode:3d} {ins.opcode_name:<12} "
                    f"A={ins.a!r:<4} B={str(ins.b)[:20]!r:<22} C={str(ins.c)[:20]!r:<22} {target}"
                )
            raw_lines.append("-- CONTROL-FLOW GRAPH:")
            for block in blocks:
                raw_lines.append(
                    f"--   block_{block.id:3d} pc[{block.start_pc:4d}..{block.end_pc:4d}] "
                    f"succs={block.successors} preds={block.predecessors}"
                )
            raw_lines.append("")

        for proto in prototypes:
            dec_lines.extend(_lift_proto(proto))
            dec_lines.append("")
    else:
        raw_lines += [
            "-- No standard or heuristic bytecode payload was recovered.",
            "--",
            "-- BOOTSTRAP / VM PREVIEW:",
            "",
            result.bootstrap_source[:12_000],
            "",
            "-- RECOVERED VM OPCODE TABLE (heuristic):",
        ]
        for opcode, name in sorted(vm_map.items()):
            raw_lines.append(f"--   [{opcode:3d}] {name}")
        raw_lines += ["", f"-- {len(result.all_strings)} strings recovered:"]
        raw_lines.extend(f"--   {value!r}" for value in result.all_strings[:120])
        dec_lines += [
            "-- Luraph: insufficient static information to reconstruct source.",
            "-- The protected payload could not be decoded with the static methods available here.",
        ]

    for note in result.notes:
        raw_lines.append(f"-- NOTE: {note}")
        dec_lines.append(f"-- NOTE: {note}")

    result.raw_output = _clip_text("\n".join(raw_lines))
    result.decompiled_output = _clip_text(_simplify_constants("\n".join(dec_lines)))
    return result

# ============================================================
# Generic backend and analysis dispatch
# ============================================================

def extract_strings_generic(code: str) -> list[str]:
    seen = set()
    result = []
    for pattern in (
        r'"((?:[^"\\]|\\.){2,200000})"',
        r"'((?:[^'\\]|\\.){2,200000})'",
    ):
        for match in re.finditer(pattern, code):
            value = match.group(1)
            if value not in seen:
                seen.add(value)
                result.append(value)
    return result


def generic_analysis(code: str, obf_name: str) -> str:
    strings = [
        value for value in extract_strings_generic(code)
        if all(32 <= ord(char) < 127 for char in value) and len(value) > 3
    ]
    numbers = list(dict.fromkeys(re.findall(r"\b\d{5,}\b", code)))
    urls = list(dict.fromkeys(re.findall(r"https?://[^\s\"'\\]+", code)))
    notable = [
        name for name in ("loadstring", "getfenv", "require", "HttpGet", "coroutine", "debug")
        if re.search(r"\b" + re.escape(name) + r"\b", code)
    ]
    out = [
        "=" * 58,
        f"  {obf_name} — Static Analysis",
        f"  {len(code):,} chars | {code.count(chr(10)) + 1:,} lines",
        "=" * 58,
        "  [!] No dedicated decompilation backend exists for this family.",
        "",
        f"── READABLE STRINGS ({len(strings)}) ─────────────────────",
    ]
    out.extend(f"  {value!r}" for value in strings[:60])
    if numbers:
        out += ["", f"── LARGE CONSTANTS ({len(numbers)}) ──────────────────────", "  " + "  ".join(numbers[:30])]
    if urls:
        out += ["", f"── URLS ({len(urls)}) ──────────────────────────────"]
        out.extend(f"  {url}" for url in urls[:10])
    if notable:
        out += ["", "── NOTABLE FUNCTIONS ───────────────────────────────────", "  " + "  ".join(notable)]
    return _clip_text("\n".join(out))


def analyze_code(code: str) -> Analysis:
    obf = detect_obfuscator(code)
    try:
        if obf == "LuaObfuscator":
            match = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
            if not match:
                return Analysis(False, obf, notes="VMCall payload not found.")
            data = decode_luaobf(match.group(1))
            chunk = parse_chunk(Reader(data))
            consts = collect_consts(chunk)
            lifted = "\n".join(lift_lua_chunk(chunk))
            header = (
                f"-- LuaObfuscator | {len(data):,} decoded bytes | {count_funcs(chunk)} functions\n"
                "-- Static lift only; submitted code was not executed.\n\n"
            )
            raw = header + lifted + "\n\n-- CONSTANTS\n" + "\n".join(
                f"-- {i}: {typ} = {value!r}" for i, (typ, value) in enumerate(consts)
            )
            return Analysis(True, obf, raw=_clip_text(raw), decompiled=_clip_text(header + _simplify_constants(lifted)))

        if obf == "WeAreDevs":
            decoded, omap, wmap = _decode_wad_strings(code)
            raw = (
                f"-- WeAreDevs | {len(decoded)} decoded strings | o={len(omap)} w={len(wmap)}\n\n"
                + "\n".join(f"U[{i}] = {value!r}" for i, value in enumerate(decoded, 1))
            )
            return Analysis(True, obf, raw=_clip_text(raw), decompiled=deobfuscate_wearedevs(code))

        if obf == "Luraph":
            result = luraph_analyze(code)
            ok = result.detected and result.proto_count > 0
            if result.proto_count:
                notes = (
                    f"v{result.version_hint}; {result.proto_count} protos; "
                    f"{result.instruction_count} instrs; {result.constant_count} consts; "
                    f"{result.string_count} strings"
                )
            else:
                notes = "; ".join(result.notes) or "Bootstrap extracted; bytecode not decoded statically."
            return Analysis(ok, obf, raw=result.raw_output, decompiled=result.decompiled_output, notes=notes)

        return Analysis(
            False,
            obf,
            raw=generic_analysis(code, obf),
            decompiled=f"-- No dedicated backend for {obf}; static string/constant analysis only.\n",
            notes=f"No dedicated backend for {obf}; static analysis only.",
        )
    except Exception as exc:
        return Analysis(False, obf, notes=f"{type(exc).__name__}: {exc}")


def run_deob(code: str, include_instrs=False) -> str:
    return analyze_code(code).decompiled or generic_analysis(code, detect_obfuscator(code))

# ============================================================
# Discord helpers
# ============================================================

async def extract_code(ctx) -> Optional[str]:
    for attachment in ctx.message.attachments:
        name = attachment.filename.lower()
        if not name.endswith((".lua", ".luau", ".txt")):
            continue
        if attachment.size > MAX_DISCORD_FILE_BYTES:
            raise ValueError(f"Attachment is too large. Maximum: {MAX_DISCORD_FILE_BYTES:,} bytes.")
        data = await attachment.read()
        if len(data) > MAX_DISCORD_FILE_BYTES:
            raise ValueError("Attachment exceeded the configured size limit.")
        return data.decode("utf-8", errors="replace")

    content = ctx.message.content
    match = re.search(r"```(?:lua|luau)?\s*\n?([\s\S]+?)```", content, re.I)
    if match:
        code = match.group(1).strip()
    else:
        match = re.search(r"`([^`]{10,})`", content)
        if match:
            code = match.group(1).strip()
        else:
            parts = content.split(None, 1)
            code = parts[1].strip() if len(parts) == 2 and len(parts[1]) > 20 else None

    if code is None:
        return None
    if len(code.encode("utf-8", errors="ignore")) > MAX_INPUT_BYTES:
        raise ValueError(f"Input is too large. Maximum: {MAX_INPUT_BYTES:,} bytes.")
    return code


intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)


async def lock_channel(channel):
    role = channel.guild.default_role
    me = channel.guild.me
    if me is None:
        raise RuntimeError("Bot member object is unavailable.")
    ow_role = channel.overwrites_for(role)
    ow_me = channel.overwrites_for(me)
    previous = (ow_role.send_messages, ow_me.send_messages)
    ow_role.send_messages = False
    ow_me.send_messages = True
    await channel.set_permissions(role, overwrite=ow_role, reason="Static analysis running")
    await channel.set_permissions(me, overwrite=ow_me, reason="Static analysis running")
    return previous


async def unlock_channel(channel, previous):
    role = channel.guild.default_role
    me = channel.guild.me
    if me is None:
        return
    for target, value in ((role, previous[0]), (me, previous[1])):
        overwrite = channel.overwrites_for(target)
        overwrite.send_messages = value
        await channel.set_permissions(
            target,
            overwrite=None if overwrite.is_empty() else overwrite,
            reason="Static analysis finished",
        )

# ============================================================
# Events
# ============================================================

@bot.event
async def on_ready():
    print(f"[+] Logged in as {bot.user} ({bot.user.id})")
    await bot.change_presence(
        activity=discord.Activity(
            type=discord.ActivityType.watching,
            name="static Lua analysis",
        )
    )

# ============================================================
# Commands
# ============================================================

@bot.command(name="deob", aliases=["d", "deobfuscate"])
@commands.guild_only()
@commands.cooldown(1, 8, commands.BucketType.user)
async def cmd_deob(ctx):
    channel = ctx.channel
    if channel.id in _busy_channels:
        await ctx.reply("⏳ A task is already running in this channel.")
        return

    _busy_channels.add(channel.id)
    locked = False
    lock_state = None
    status = None

    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No Lua/Luau code or supported attachment was found.")
            return

        obf = detect_obfuscator(code)
        if obf == "Luraph":
            status_text = "🔍 Luraph detected — running static analysis (detection → blob recovery → bytecode analysis → CFG → lift)..."
        else:
            status_text = f"🔍 {obf} detected — running static analysis..."

        lock_state = await lock_channel(channel)
        locked = True
        status = await channel.send(status_text)

        async with analysis_semaphore:
            analysis_task = asyncio.to_thread(analyze_code, code)
            analysis, _ = await asyncio.gather(
                analysis_task,
                asyncio.sleep(random.uniform(*TRACE_DELAY)),
            )

        files = []
        if analysis.raw:
            files.append(discord.File(io.BytesIO(analysis.raw.encode("utf-8")), filename="file-raw.lua"))
        if analysis.decompiled:
            files.append(discord.File(io.BytesIO(analysis.decompiled.encode("utf-8")), filename="file-decompiled.lua"))

        if files:
            await channel.send(
                f"{ctx.author.mention} ✅ Analysis complete for **{analysis.family}**.",
                files=files,
            )
        else:
            await channel.send("⚠️ No output file could be generated.")

        if analysis.notes:
            await status.edit(content=f"⚠️ Finished with notes: {analysis.notes[:1_800]}")
        elif analysis.ok:
            await status.edit(content=f"✅ {analysis.family} analysis complete.")
        else:
            await status.edit(content=f"⚠️ {analysis.family}: static analysis completed.")

    except ValueError as exc:
        if status:
            await status.edit(content=f"❌ {exc}")
        else:
            await ctx.reply(f"❌ {exc}")
    except discord.HTTPException as exc:
        if status:
            try:
                await status.edit(content=f"❌ Discord error: {exc}")
            except Exception:
                pass
        else:
            try:
                await ctx.reply(f"❌ Discord error: {exc}")
            except Exception:
                pass
    except Exception as exc:
        message = f"❌ Unexpected error: {type(exc).__name__}: {exc}"
        if status:
            try:
                await status.edit(content=message[:2_000])
            except Exception:
                pass
        else:
            await ctx.reply(message[:2_000])
    finally:
        if locked:
            try:
                await unlock_channel(channel, lock_state)
            except Exception as exc:
                print(f"[!] Could not restore channel permissions: {exc}")
        _busy_channels.discard(channel.id)


@bot.command(name="detect")
@commands.cooldown(1, 4, commands.BucketType.user)
async def cmd_detect(ctx):
    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No code found.")
            return
    except ValueError as exc:
        await ctx.reply(f"❌ {exc}")
        return

    obf = detect_obfuscator(code)
    embed = discord.Embed(title="🔍 Detection Result", color=0x5865F2)
    embed.add_field(name="Obfuscator", value=f"**{obf}**", inline=True)
    embed.add_field(name="Size", value=f"{len(code):,} chars", inline=True)
    embed.add_field(name="Lines", value=f"{code.count(chr(10)) + 1:,}", inline=True)

    if obf == "Luraph":
        _, version_hint, features = _luraph_stage1_detect(code)
        embed.add_field(name="Version Hint", value=version_hint, inline=True)
        embed.add_field(name="Features", value=", ".join(features) or "none", inline=False)
    await ctx.reply(embed=embed)


@bot.command(name="strings", aliases=["s", "strs"])
@commands.cooldown(1, 4, commands.BucketType.user)
async def cmd_strings(ctx):
    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No code found.")
            return
    except ValueError as exc:
        await ctx.reply(f"❌ {exc}")
        return

    obf = detect_obfuscator(code)
    try:
        if obf == "LuaObfuscator":
            match = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
            if not match:
                strings = []
            else:
                chunk = parse_chunk(Reader(decode_luaobf(match.group(1))))
                strings = [value for typ, value in collect_consts(chunk) if typ == "str"]
        elif obf == "WeAreDevs":
            strings, _, _ = _decode_wad_strings(code)
        elif obf == "Luraph":
            async with analysis_semaphore:
                result = await asyncio.to_thread(luraph_analyze, code)
            strings = result.all_strings
        else:
            strings = extract_strings_generic(code)
    except Exception as exc:
        await ctx.reply(f"❌ String extraction error: {type(exc).__name__}: {exc}")
        return

    strings = list(dict.fromkeys(strings))
    body = "\n".join(repr(value) for value in strings)
    if len(body) <= 1_800:
        await ctx.reply(f"**{len(strings)} strings [{obf}]**\n```\n{body or '(none)'}\n```")
    else:
        await ctx.reply(
            f"**{len(strings)} strings [{obf}]**",
            file=discord.File(io.BytesIO(body.encode("utf-8")), filename="strings.txt"),
        )


@bot.command(name="info")
@commands.cooldown(1, 4, commands.BucketType.user)
async def cmd_info(ctx):
    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No code found.")
            return
    except ValueError as exc:
        await ctx.reply(f"❌ {exc}")
        return

    obf = detect_obfuscator(code)
    embed = discord.Embed(title="📋 Script Info", color=0x5865F2)
    embed.add_field(name="Obfuscator", value=obf, inline=True)
    embed.add_field(name="Size", value=f"{len(code):,} chars", inline=True)
    embed.add_field(name="Lines", value=f"{code.count(chr(10)) + 1:,}", inline=True)

    try:
        if obf == "LuaObfuscator":
            match = re.search(r'''VMCall\s*\(\s*["'](LOL![^"']+)''', code)
            if match:
                chunk = parse_chunk(Reader(decode_luaobf(match.group(1))))
                embed.add_field(name="Constants", value=str(len(collect_consts(chunk))), inline=True)
                embed.add_field(name="Functions", value=str(count_funcs(chunk)), inline=True)
        elif obf == "WeAreDevs":
            strings, omap, wmap = _decode_wad_strings(code)
            embed.add_field(name="Decoded WAD strings", value=str(len(strings)), inline=True)
            embed.add_field(name="Mappings", value=f"o={len(omap)}, w={len(wmap)}", inline=True)
        elif obf == "Luraph":
            async with analysis_semaphore:
                result = await asyncio.to_thread(luraph_analyze, code)
            embed.add_field(name="Version Hint", value=result.version_hint, inline=True)
            embed.add_field(name="Prototypes", value=str(result.proto_count), inline=True)
            embed.add_field(name="Instructions", value=f"{result.instruction_count:,}", inline=True)
            embed.add_field(name="Constants", value=f"{result.constant_count:,}", inline=True)
            embed.add_field(name="Strings", value=f"{result.string_count:,}", inline=True)
            embed.add_field(name="Bytecode", value=f"{result.bytecode_size:,} B", inline=True)
            embed.add_field(name="VM Opcodes", value=str(len(result.vm_opcode_map)), inline=True)
            embed.add_field(name="Unknown Opcodes", value=str(len(result.unknown_opcodes)), inline=True)
            if result.notes:
                embed.add_field(name="Notes", value="; ".join(result.notes[:2])[:900], inline=False)
    except Exception as exc:
        embed.add_field(name="Analysis Error", value=f"{type(exc).__name__}: {exc}"[:1_000], inline=False)

    await ctx.reply(embed=embed)


@bot.command(name="help", aliases=["h", "commands", "cmds"])
async def cmd_help(ctx):
    embed = discord.Embed(title="Lua Static Analysis Bot", color=0x5865F2)
    embed.description = (
        "Attach a `.lua`, `.luau`, or `.txt` file, or paste a Lua code block.\n"
        "Analysis is static only; submitted code is never executed."
    )
    embed.add_field(
        name="!deob / !d",
        value="Run the appropriate static-analysis backend and return raw + reconstructed output.",
        inline=False,
    )
    embed.add_field(
        name="!detect",
        value="Detect the obfuscator family and show Luraph structural features when available.",
        inline=False,
    )
    embed.add_field(
        name="!strings / !s",
        value="Extract readable strings from the source and supported decoded layers.",
        inline=False,
    )
    embed.add_field(
        name="!info",
        value="Show script size, line count, and backend-specific statistics.",
        inline=False,
    )
    embed.add_field(
        name="Backends",
        value=(
            "**LuaObfuscator:** LOL! decode + custom chunk parse + Lua-like lift\n"
            "**WeAreDevs:** static table/string reconstruction\n"
            "**Luraph:** staged detection + blob recovery + Lua 5.1/custom-Vm heuristics + CFG\n"
            "**Other families:** generic string/constant analysis"
        ),
        inline=False,
    )
    await ctx.reply(embed=embed)

# ============================================================
# Error handling
# ============================================================

@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandNotFound):
        return
    if isinstance(error, commands.NoPrivateMessage):
        await ctx.reply("❌ This command only works in a server channel.")
        return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.reply(f"⏳ Try again in {error.retry_after:.1f}s.")
        return
    if isinstance(error, commands.MissingPermissions):
        await ctx.reply("❌ You do not have permission to use this command.")
        return
    if isinstance(error, commands.MissingRequiredArgument):
        await ctx.reply("❌ Missing required argument.")
        return
    await ctx.reply(f"❌ Unexpected error: {type(error).__name__}: {error}")

# ============================================================
# Start
# ============================================================

if __name__ == "__main__":
    if not TOKEN:
        raise RuntimeError("TOKEN environment variable is not set.")
    bot.run(TOKEN)
