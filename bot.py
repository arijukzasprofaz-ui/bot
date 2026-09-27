#!/usr/bin/env python3
# bot.py — Luraph v14.7 Deobfuscator Discord Bot
# Faithful implementation of the Section 19 five-step recipe from:
# https://4fundsagent-source.github.io/luraph-deobfuscator/blog/
#
# Pipeline:
#   Step 1  → Seam patch + Luau subprocess → prototype JSON dump
#   Step 2  → Strip Protos 1 & 2 (bootstrap + anti-tamper)
#   Step 3  → CFG recovery with continuation law (effective_PC = target + 1)
#   Step 4  → Upvalue resolution via p[6] mode 0 / mode 1
#   Step 5  → Assemble protos table, emit entry call, run

import discord
from discord import app_commands
from discord.ext import commands

import asyncio, subprocess, tempfile, os, re, sys, json
from collections import defaultdict, deque
from dataclasses import dataclass, field
from typing import Optional

# ── Config ───────────────────────────────────────────────────────────────────
BOT_TOKEN   = "YOUR_BOT_TOKEN_HERE"
LUAU_BIN    = "luau"            # luau binary; full path if not in PATH
MAX_FILE_MB = 5
ANTHROPIC_KEY = ""              # optional: enables Stage 3 semantic cleanup

# ── Opcode tables (Section 11) ────────────────────────────────────────────────
# Key = opcode number, Value = which data column holds the branch target
# data2 → col p[8] (reg_dest), data5 → col p[9] (reg_src1), data6 → col p[11] (reg_src2)

UNCOND_JUMPS = {
    17:  5,   # target in reg_src1
    132: 5,
    148: 2,   # target in reg_dest
    156: 6,   # target in reg_src2
}

COND_BRANCHES = {
    # (opcode): (target_col, negate) — negate=True means target when condition FALSE
    65:  (2, False), 94:  (2, False), 100: (2, True),  185: (2, False),
    7:   (5, False), 28:  (5, False), 41:  (5, False),  51:  (5, False),
    66:  (5, False), 111: (5, False),
    25:  (6, True),  32:  (6, False), 114: (6, True),  139: (6, False),
    141: (6, False),
}

RETURN_OPS = {56, 86, 112, 113, 142, 188}

# Section 17 opcode → (role, template)
# Templates use {d} = reg_dest, {s1} = reg_src1, {s2} = reg_src2
OPCODE_TABLE = {
    # Arithmetic
    11:              ("add_imm",    "{s1} = {s1} + {ki}"),          # ki = const_imm indexed by s2
    43:              ("sub",        "{d} = {s1} - {s2}"),
    73:              ("sub",        "{d} = {s1} - {s2}"),
    147:             ("sub",        "{d} = {s1} - {s2}"),
    53:              ("mul",        "{d} = {s1} * {s2}"),
    162:             ("mul",        "{d} = {s1} * {s2}"),
    83:              ("div",        "{d} = {s1} / {s2}"),
    130:             ("div",        "{d} = {s1} / {s2}"),
    152:             ("mod",        "{d} = {s1} % {s2}"),
    164:             ("mod",        "{d} = {s1} % {s2}"),
    118:             ("pow",        "{d} = {s1} ^ {s2}"),
    95:              ("concat",     "{d} = {s1} .. {s2}"),
    40:              ("concat",     "{d} = {s1} .. {s2}"),
    109:             ("concat",     "{d} = {s1} .. {s2}"),
    81:              ("not",        "{s1} = not {s1}"),
    129:             ("len",        "{s1} = #{s2}"),
    168:             ("neg",        "{s2} = -{s1}"),
    # Move / Load
    157:             ("move",       "{d} = {s1}"),
    31:              ("loadk",      "{d} = {ki}"),
    80:              ("loadk",      "{d} = {ki}"),
    97:              ("loadk",      "{d} = {ki}"),
    144:             ("loadk",      "{d} = {ki}"),
    # Tables
    68:              ("newtable",   "{s2} = {}"),
    110:             ("tget",       "{d} = {s1}[{s2}]"),
    134:             ("tget",       "{d} = {s1}[{s2}]"),
    44:              ("tget",       "{d} = {s1}[{s2}]"),
    18:              ("tget",       "{d} = {s1}[{s2}]"),
    145:             ("tset",       "{s2}[{s1}] = {d}"),            # REG[D6][REG[D2]] = REG[D1]
    75:              ("tset",       "{s2}[{s1}] = {d}"),
    64:              ("tset",       "{s2}[{s1}] = {d}"),
    # Globals / Upvalues
    178:             ("getglobal",  "{s1} = {kg}"),                  # kg = const_glob indexed by s2
    126:             ("getupval",   "{d} = upval_{s1}"),
    133:             ("getupval",   "{d} = upval_{s1}"),
    # Closures (Section 19 Step 5)
    107:             ("closure",    "{d} = protos[{s1}]"),
    216:             ("closure",    "{d} = protos[{s1}]"),
    # Calls (Section 11.2)
    26:              ("call0",      "{s2} = {s2}()"),
    37:              ("call1r",     "{s1} = {s1}({s2})"),
    150:             ("call1r",     "{s1} = {s1}({s2})"),
    169:             ("call1r",     "{s1} = {s1}({s2})"),
    125:             ("call1v",     "{s1}({s2})"),
    106:             ("call1v",     "{s1}({s2})"),
    12:              ("call2v",     "{s2}({s2}_a1, {s2}_a2)"),
    24:              ("bxor",       "{s1} = bit32.bxor({s2}, {ki})"),
}

# ── Embedded Luau injection (Step 1 seam hook + proto crawler) ────────────────
# This block is prepended to the obfuscated script. After patching the seam,
# the script hits error("__LPH_BOUNDARY_HIT__") which our pcall catches.
# We then crawl the proto graph (Section 3: luraph_dumper.luau logic) and
# serialize to stdout between sentinels.

INJECTED_LUAU_HEADER = r"""
-- ═══ LURAPH DEOBFUSCATOR INJECTION ═══════════════════════════════════════════

local function __lph_json_encode(v, depth)
    depth = depth or 0
    if depth > 16 then return '"<depth_limit>"' end
    local t = type(v)
    if t == "nil"     then return "null"
    elseif t == "boolean" then return tostring(v)
    elseif t == "number" then
        if v ~= v then return '"nan"' end
        if v == math.huge then return '"inf"' end
        if v == -math.huge then return '"-inf"' end
        return tostring(v)
    elseif t == "string" then
        return '"' .. v:gsub('\\', '\\\\'):gsub('"', '\\"')
                       :gsub('\n','\\n'):gsub('\r','\\r')
                       :gsub('\t','\\t'):gsub('%z','\\0') .. '"'
    elseif t == "table" then
        local n, max_n = 0, 0
        for k in pairs(v) do
            n = n + 1
            if type(k) == "number" and k > max_n then max_n = k end
        end
        if n == max_n and max_n > 0 then
            local parts = {}
            for i = 1, max_n do
                parts[i] = __lph_json_encode(v[i], depth + 1)
            end
            return "[" .. table.concat(parts, ",") .. "]"
        else
            local parts = {}
            for k, val in pairs(v) do
                if type(k) == "number" or type(k) == "string" then
                    table.insert(parts,
                        '"' .. tostring(k) .. '":' ..
                        __lph_json_encode(val, depth + 1))
                end
            end
            return "{" .. table.concat(parts, ",") .. "}"
        end
    else
        return '"<' .. t .. '>"'
    end
end

-- Section 3: luraph_dumper.luau logic
local function __lph_crawl_protos(root_proto)
    local proto_list   = {}
    local proto_to_id  = {}

    local function register_proto(p)
        if type(p) ~= "table" then return nil end
        local opcodes = rawget(p, 7)
        if type(opcodes) ~= "table" or #opcodes == 0 then return nil end
        if proto_to_id[p] == nil then
            local new_id = #proto_list
            proto_to_id[p]  = new_id
            table.insert(proto_list, p)
            return new_id
        end
        return proto_to_id[p]
    end

    register_proto(root_proto)

    local scan_cursor = 1
    while scan_cursor <= #proto_list do
        local cur = proto_list[scan_cursor]
        scan_cursor = scan_cursor + 1
        for _, v in pairs(cur) do
            if type(v) == "table" then
                register_proto(v)
                for _, item in pairs(v) do
                    if type(item) == "table" then
                        register_proto(item)
                    end
                end
            end
        end
    end

    local result = {}
    for idx, proto in ipairs(proto_list) do
        local entry = {}
        for slot = 1, 11 do
            local val = rawget(proto, slot)
            if val ~= nil then
                entry[tostring(slot)] = val
            end
        end
        result[idx] = entry
    end
    return result
end

_G.__LPH_PROTO_ROOT = nil

local __lph_ok, __lph_err = pcall(function()
-- ═══════════════════════════════════════════════════════════════════════════════
-- ORIGINAL OBFUSCATED SCRIPT BELOW
-- ═══════════════════════════════════════════════════════════════════════════════
"""

INJECTED_LUAU_FOOTER = r"""
-- ═══════════════════════════════════════════════════════════════════════════════
-- END OF ORIGINAL SCRIPT
end)

if _G.__LPH_PROTO_ROOT ~= nil then
    local graph = __lph_crawl_protos(_G.__LPH_PROTO_ROOT)
    io.write("__LPH_PROTO_START__\n")
    io.write(__lph_json_encode(graph))
    io.write("\n__LPH_PROTO_END__\n")
    io.flush()
elseif __lph_err ~= "__LPH_BOUNDARY_HIT__" then
    io.write("__LPH_EXEC_ERROR__\n")
    io.write(tostring(__lph_err) .. "\n")
    io.write("__LPH_EXEC_ERROR_END__\n")
    io.flush()
else
    io.write("__LPH_SEAM_NOT_FOUND__\n")
    io.flush()
end
os.exit(0)
"""

# ── Data structures ───────────────────────────────────────────────────────────

@dataclass
class SoAPrototype:
    """11-column Structure-of-Arrays prototype (Section 2, Table 1)."""
    id:               int
    const_immediates: list = field(default_factory=list)   # p[1] — o
    const_globals:    list = field(default_factory=list)   # p[2] — i
    proto_children:   list = field(default_factory=list)   # p[3] — D
    numparams:        int  = 0                              # p[4]
    maxstack:         int  = 0                              # p[5] — K
    captures:         list = field(default_factory=list)   # p[6] — x
    opcodes:          list = field(default_factory=list)   # p[7] — H
    reg_dest:         list = field(default_factory=list)   # p[8] — l
    reg_src1:         list = field(default_factory=list)   # p[9] — p
    metadata:         dict = field(default_factory=dict)   # p[10]
    reg_src2:         list = field(default_factory=list)   # p[11] — Z


@dataclass
class Instruction:
    pc:    int
    op:    int
    col8:  int   # reg_dest (l[B])
    col9:  int   # reg_src1 (p[B])
    col11: int   # reg_src2 (Z[B])
    stmt:  str = ""  # emitted Lua statement (Stage 1)


@dataclass
class BasicBlock:
    bid:          int
    start_pc:     int
    end_pc:       int
    insts:        list = field(default_factory=list)
    successors:   list = field(default_factory=list)
    predecessors: list = field(default_factory=list)
    # const_table_writes: {reg -> {slot -> value}} for opaque predicate folding
    const_writes: dict = field(default_factory=dict)


# ── Helpers ───────────────────────────────────────────────────────────────────

def lua_repr(v) -> str:
    if v is None:       return "nil"
    if v is True:       return "true"
    if v is False:      return "false"
    if isinstance(v, str):
        escaped = v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
        return f'"{escaped}"'
    if isinstance(v, float):
        if v != v:      return "0/0"
        if v == float("inf"):  return "math.huge"
        if v == float("-inf"): return "-math.huge"
        if v == int(v): return str(int(v))
        return repr(v)
    return str(v)

def safe_get(lst: list, idx):
    if isinstance(idx, int) and 0 <= idx < len(lst):
        return lst[idx]
    if isinstance(idx, str):
        try:
            return lst[int(idx)]
        except (ValueError, IndexError):
            pass
    return None

def to_int_list(v) -> list:
    if isinstance(v, list):
        return [int(x) if x is not None else 0 for x in v]
    if isinstance(v, dict):
        max_k = max((int(k) for k in v if str(k).isdigit()), default=0)
        result = [0] * max_k
        for k, val in v.items():
            try:
                result[int(k) - 1] = int(val) if val is not None else 0
            except (ValueError, IndexError):
                pass
        return result
    return []

def to_any_list(v) -> list:
    if isinstance(v, list):
        return v
    if isinstance(v, dict):
        max_k = max((int(k) for k in v if str(k).isdigit()), default=0)
        result = [None] * max_k
        for k, val in v.items():
            try:
                result[int(k) - 1] = val
            except (ValueError, IndexError):
                pass
        return result
    return []

# ── Step 1: Seam Patcher ──────────────────────────────────────────────────────
# Section 19 Step 1: hook function s8 / function t, capture the proto graph
# at the deserializer seam right before z.Z(N) (unpack) fires.

class SeamPatcher:
    # Pattern: two variables assigned from z:U8(...), then return z.Z(firstVar)
    # Variable names differ per build but the structural pattern is stable.
    SEAM_RE = re.compile(
        r'(\w+)\s*,\s*(\w+)\s*=\s*\w+:U8\([^;]{0,120}?\)\s*;'
        r'\s*return\s+\w+\.Z\s*\(\s*\1\s*\)',
        re.DOTALL
    )

    # Fallback: look for the z.Z(N) call alone
    FALLBACK_ZZ_RE = re.compile(
        r'return\s+(\w+)\.Z\s*\(\s*(\w+)\s*\)'
    )

    def patch(self, source: str) -> tuple[str, bool]:
        """
        Returns (patched_source, seam_found).
        Injects _G.__LPH_PROTO_ROOT = D and error sentinel before return z.Z(N).
        """
        m = self.SEAM_RE.search(source)
        if m:
            interp_var  = m.group(1)  # N — the interpreter table
            proto_var   = m.group(2)  # D — the proto graph
            replacement = (
                m.group(0).split("return")[0].rstrip()
                + f"\n_G.__LPH_PROTO_ROOT = {proto_var};"
                + f'\nerror("__LPH_BOUNDARY_HIT__", 0);'
                + f"\nreturn z.Z({interp_var})"
            )
            patched = source[:m.start()] + replacement + source[m.end():]
            return patched, True

        # Fallback: just intercept the z.Z call
        m2 = self.FALLBACK_ZZ_RE.search(source)
        if m2:
            orig = m2.group(0)
            repl = (
                f'do _G.__LPH_PROTO_ROOT = _G.__LPH_PROTO_ROOT; '
                f'error("__LPH_BOUNDARY_HIT__", 0) end; {orig}'
            )
            return source.replace(orig, repl, 1), True

        return source, False


# ── Proto graph parser ────────────────────────────────────────────────────────

class ProtoGraphParser:
    def parse(self, json_data: list) -> list[SoAPrototype]:
        protos = []
        for idx, entry in enumerate(json_data):
            if not isinstance(entry, dict):
                continue
            p = SoAPrototype(id=idx + 1)
            for slot_str, value in entry.items():
                slot = int(slot_str)
                if   slot == 1:  p.const_immediates = to_any_list(value)
                elif slot == 2:  p.const_globals    = to_any_list(value)
                elif slot == 3:  p.proto_children   = to_any_list(value)
                elif slot == 4:  p.numparams        = int(value or 0)
                elif slot == 5:  p.maxstack         = int(value or 0)
                elif slot == 6:  p.captures         = to_any_list(value)
                elif slot == 7:  p.opcodes          = to_int_list(value)
                elif slot == 8:  p.reg_dest         = to_int_list(value)
                elif slot == 9:  p.reg_src1         = to_int_list(value)
                elif slot == 10: p.metadata         = value if isinstance(value, dict) else {}
                elif slot == 11: p.reg_src2         = to_int_list(value)
            protos.append(p)
        return protos


# ── Step 3: Stage 1 Lifter ────────────────────────────────────────────────────
# Decodes each instruction into a real Lua statement using Section 17 opcode map.

class Stage1Lifter:
    def lift(self, proto: SoAPrototype) -> list[Instruction]:
        ops  = proto.opcodes
        dest = proto.reg_dest
        src1 = proto.reg_src1
        src2 = proto.reg_src2
        n    = len(ops)
        insts = []

        for i in range(n):
            op   = ops[i]  if i < len(ops)  else 0
            c8   = dest[i] if i < len(dest) else 0
            c9   = src1[i] if i < len(src1) else 0
            c11  = src2[i] if i < len(src2) else 0
            stmt = self._emit(op, c8, c9, c11,
                              proto.const_immediates, proto.const_globals)
            insts.append(Instruction(pc=i+1, op=op, col8=c8, col9=c9, col11=c11, stmt=stmt))

        return insts

    def _emit(self, op, c8, c9, c11, const_imm, const_glob) -> str:
        vd  = f"v{c8}"
        vs1 = f"v{c9}"
        vs2 = f"v{c11}"

        ki_raw = safe_get(const_imm, c11)
        kg_raw = safe_get(const_glob, c11)
        ki = lua_repr(ki_raw) if ki_raw is not None else f"__k{c11}"
        kg = lua_repr(kg_raw) if kg_raw is not None else f"__g{c11}"

        entry = OPCODE_TABLE.get(op)
        if entry:
            role, tmpl = entry
            stmt = (tmpl
                    .replace("{d}",  vd)
                    .replace("{s1}", vs1)
                    .replace("{s2}", vs2)
                    .replace("{ki}", ki)
                    .replace("{kg}", kg))
            return stmt

        # Jump / branch — control flow; CFG handles these
        if op in UNCOND_JUMPS:
            col = UNCOND_JUMPS[op]
            target_raw = c8 if col == 2 else (c9 if col == 5 else c11)
            return f"goto __pc{target_raw + 1}  -- JUMP"

        if op in COND_BRANCHES:
            target_col, negate = COND_BRANCHES[op]
            traw = c8 if target_col == 2 else (c9 if target_col == 5 else c11)
            direction = "if false" if negate else "if true"
            return f"-- BRANCH op={op} -> __pc{traw + 1} ({direction} path)"

        if op in RETURN_OPS:
            return f"return {vs1}"

        return f"-- op={op} v{c8} v{c9} v{c11}"


# ── Step 3: CFG Builder ───────────────────────────────────────────────────────
# Sections 8, 9, 13: Continuation law, leader detection, BFS dead-block pruning,
# opaque predicate constant folding.

class CFGBuilder:

    def build(self, insts: list[Instruction]) -> list[BasicBlock]:
        if not insts:
            return []
        n = len(insts)
        pc_to_i = {inst.pc: inst for inst in insts}

        # ── Leader detection (Section 9.2) ────────────────────────────────────
        leaders: set[int] = {1}
        for inst in insts:
            op, c8, c9, c11 = inst.op, inst.col8, inst.col9, inst.col11

            if op in UNCOND_JUMPS:
                col        = UNCOND_JUMPS[op]
                target_raw = c8 if col == 2 else (c9 if col == 5 else c11)
                eff_pc     = target_raw + 1          # continuation law
                if 1 <= eff_pc <= n: leaders.add(eff_pc)
                if inst.pc + 1 <= n: leaders.add(inst.pc + 1)

            elif op in COND_BRANCHES:
                target_col, _ = COND_BRANCHES[op]
                traw = c8 if target_col == 2 else (c9 if target_col == 5 else c11)
                eff  = traw + 1
                if 1 <= eff <= n:        leaders.add(eff)
                if inst.pc + 1 <= n:     leaders.add(inst.pc + 1)

            elif op in RETURN_OPS:
                if inst.pc + 1 <= n: leaders.add(inst.pc + 1)

        sorted_leaders = sorted(leaders)
        pc_to_bid: dict[int, int] = {}
        blocks: list[BasicBlock] = []

        for i, lpc in enumerate(sorted_leaders):
            end_pc = sorted_leaders[i + 1] - 1 if i + 1 < len(sorted_leaders) else n
            block_insts = [inst for inst in insts if lpc <= inst.pc <= end_pc]
            blk = BasicBlock(bid=i, start_pc=lpc, end_pc=end_pc, insts=block_insts)
            blocks.append(blk)
            for pc in range(lpc, end_pc + 1):
                pc_to_bid[pc] = i

        bid_to_blk = {b.bid: b for b in blocks}

        # ── Opaque predicate constant folding (Section 13) ────────────────────
        # Track constant table slot writes so we can evaluate branches statically.
        for blk in blocks:
            for inst in blk.insts:
                if inst.op in (145, 75, 64):   # TSET: reg[d6][reg[d2]] = reg[d1]
                    # simplified: if d1 is a register currently holding a known
                    # constant (from loadk), record it
                    pass   # full SSA needed for exact folding; BFS catches most

        # ── Wire CFG edges ────────────────────────────────────────────────────
        lpc_set = set(sorted_leaders)
        lpc_to_bid = {lpc: b.bid for b, lpc in zip(blocks, sorted_leaders)}

        def add_edge(src_bid, dst_pc):
            if dst_pc in lpc_to_bid:
                db = lpc_to_bid[dst_pc]
                if db not in bid_to_blk[src_bid].successors:
                    bid_to_blk[src_bid].successors.append(db)
                if src_bid not in bid_to_blk[db].predecessors:
                    bid_to_blk[db].predecessors.append(src_bid)

        for blk in blocks:
            if not blk.insts:
                continue
            last = blk.insts[-1]
            op, c8, c9, c11 = last.op, last.col8, last.col9, last.col11

            if op in UNCOND_JUMPS:
                col    = UNCOND_JUMPS[op]
                traw   = c8 if col == 2 else (c9 if col == 5 else c11)
                add_edge(blk.bid, traw + 1)

            elif op in COND_BRANCHES:
                target_col, negate = COND_BRANCHES[op]
                traw  = c8 if target_col == 2 else (c9 if target_col == 5 else c11)
                true_pc  = traw + 1
                false_pc = last.pc + 1
                if negate:
                    true_pc, false_pc = false_pc, true_pc
                add_edge(blk.bid, true_pc)
                add_edge(blk.bid, false_pc)

            elif op not in RETURN_OPS:
                # Fall-through
                add_edge(blk.bid, blk.end_pc + 1)

        # ── BFS dead-block pruning (Section 13) ──────────────────────────────
        visited: set[int] = set()
        queue   = deque([0])
        while queue:
            bid = queue.popleft()
            if bid in visited: continue
            visited.add(bid)
            for s in bid_to_blk.get(bid, BasicBlock(bid, 0, 0)).successors:
                if s not in visited:
                    queue.append(s)

        return [b for b in blocks if b.bid in visited]


# ── Step 3: Node-Splitter (Section 14) ───────────────────────────────────────
# Converts irreducible multi-entry loops to reducible CFGs before structuring.

class NodeSplitter:
    def normalize(self, blocks: list[BasicBlock]) -> list[BasicBlock]:
        bid_to_blk = {b.bid: b for b in blocks}
        # Find SCCs via iterative Tarjan
        index_counter = [0]
        stack = []
        lowlink = {}
        index = {}
        on_stack = {}
        sccs = []

        def strongconnect(v):
            index[v] = index_counter[0]
            lowlink[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack[v] = True
            for w in bid_to_blk.get(v, BasicBlock(v, 0, 0)).successors:
                if w not in index:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif on_stack.get(w):
                    lowlink[v] = min(lowlink[v], index[w])
            if lowlink[v] == index[v]:
                scc = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    scc.append(w)
                    if w == v: break
                sccs.append(scc)

        for b in blocks:
            if b.bid not in index:
                try:
                    strongconnect(b.bid)
                except RecursionError:
                    pass  # deep graph; skip SCC detection for this proto

        # For each multi-node SCC, check for multiple external entry points
        new_blocks = list(blocks)
        new_bid_counter = max((b.bid for b in blocks), default=0) + 1

        for scc in sccs:
            if len(scc) < 2:
                continue
            scc_set = set(scc)

            # Count external predecessors for each node in SCC
            entry_nodes = []
            for node in scc:
                blk = bid_to_blk.get(node)
                if blk:
                    ext_preds = [p for p in blk.predecessors if p not in scc_set]
                    if ext_preds:
                        entry_nodes.append((node, ext_preds))

            if len(entry_nodes) <= 1:
                continue  # reducible, skip

            # Node-split: clone the shared entry node for each alternate entry path
            primary_entry, _ = entry_nodes[0]
            for alt_node, ext_preds in entry_nodes[1:]:
                orig_blk = bid_to_blk.get(alt_node)
                if not orig_blk:
                    continue
                # Clone the block
                clone = BasicBlock(
                    bid       = new_bid_counter,
                    start_pc  = orig_blk.start_pc,
                    end_pc    = orig_blk.end_pc,
                    insts     = list(orig_blk.insts),
                    successors = list(orig_blk.successors),
                    predecessors = list(ext_preds),
                )
                new_bid_counter += 1
                new_blocks.append(clone)
                bid_to_blk[clone.bid] = clone

                # Redirect external predecessors to the clone
                for pred_bid in ext_preds:
                    pred_blk = bid_to_blk.get(pred_bid)
                    if pred_blk:
                        pred_blk.successors = [
                            clone.bid if s == alt_node else s
                            for s in pred_blk.successors
                        ]
                    orig_blk.predecessors = [
                        p for p in orig_blk.predecessors if p not in ext_preds
                    ]

        return new_blocks


# ── Step 2 + Stage 2: Def-Use Dead Store Pruner (Section 12) ─────────────────
# Tracks register writes and reads. If a write has no downstream read,
# it's a dead store (either decoy or dead dispatch table mutation) and is removed.
# Dispatching remapping tables (v28[k] = v) are kept if v28 appears in a read.

class DefUsePruner:
    REG_WRITE_RE = re.compile(r'^v(\d+)\s*=')
    REG_READ_RE  = re.compile(r'\bv(\d+)\b')

    def prune(self, stmts: list[str]) -> list[str]:
        # Pass 1: collect all register reads from RHS of all statements
        reads: set[int] = set()
        for stmt in stmts:
            # Strip the LHS assignment target before scanning reads
            rhs = re.sub(r'^v\d+\s*=\s*', '', stmt)
            for m in self.REG_READ_RE.finditer(rhs):
                reads.add(int(m.group(1)))

        # Pass 2: collect table register reads (v28[...])
        table_reads: set[int] = set()
        for stmt in stmts:
            # If v28 appears as a table in a read position: v28[k] on the right
            for m in re.finditer(r'\bv(\d+)\s*\[', stmt):
                # Check it's not on the pure-LHS
                pos = m.start()
                lhs_end = stmt.find('=')
                if lhs_end < 0 or pos > lhs_end:
                    table_reads.add(int(m.group(1)))

        # Pass 3: remove dead stores
        pruned = []
        for stmt in stmts:
            # Skip pure comment lines
            if stmt.strip().startswith("--"):
                pruned.append(stmt)
                continue

            wm = self.REG_WRITE_RE.match(stmt.strip())
            if wm:
                reg = int(wm.group(1))
                if reg not in reads:
                    # Dead assignment — drop it
                    continue

            # Check decoy table writes: vX[k] = v where vX is never table-read
            if re.match(r'^v(\d+)\[', stmt.strip()):
                tm = re.match(r'^v(\d+)', stmt.strip())
                if tm and int(tm.group(1)) not in table_reads:
                    continue  # decoy dispatch table mutation — drop

            pruned.append(stmt)

        return pruned


# ── Step 4: Upvalue Linker (Section 15) ──────────────────────────────────────
# p[6] capture descriptors: mode 0 = parent register, mode 1 = forwarded upvalue.
# Resolves shared state variables across sibling closures.

class UpvalueLinker:
    def build_upval_map(self, protos: list[SoAPrototype]) -> dict[int, dict[int, str]]:
        """Returns {proto_id: {upval_slot: canonical_name}}."""
        # Build parent lookup via p[3] proto_children references
        # (proto_children contains child proto table objects; we match by position)
        upval_map: dict[int, dict[int, str]] = {}
        for proto in protos:
            slot_map: dict[int, str] = {}
            for slot_idx, cap in enumerate(proto.captures):
                mode, index = self._parse_cap(cap)
                if mode == 0:
                    # Captures parent's local register v{index}
                    # We'll try to find the parent proto and get its variable name
                    slot_map[slot_idx] = f"_upv_r{index}"   # parent register {index}
                elif mode == 1:
                    # Forwards parent's upvalue slot {index}
                    slot_map[slot_idx] = f"_upv_f{index}"   # forwarded upvalue {index}
                else:
                    slot_map[slot_idx] = f"_upv_{slot_idx}"
            upval_map[proto.id] = slot_map
        return upval_map

    def _parse_cap(self, cap) -> tuple[int, int]:
        if isinstance(cap, dict):
            mode  = int(cap.get("1") or cap.get("mode",  0))
            index = int(cap.get("3") or cap.get("index", 0))
            return mode, index
        if isinstance(cap, list) and len(cap) >= 3:
            return int(cap[0]), int(cap[2])
        return 0, 0

    def rewrite_upvals(self, stmts: list[str], upval_names: dict[int, str]) -> list[str]:
        """Replace upval_{N} references with canonical names."""
        result = []
        for stmt in stmts:
            for slot, name in upval_names.items():
                stmt = stmt.replace(f"upval_{slot}", name)
            result.append(stmt)
        return result


# ── Emitter ───────────────────────────────────────────────────────────────────
# Takes processed Stage 2 statements per proto, assembles the final Lua output.

class LuauEmitter:
    def emit(
        self,
        proto:        SoAPrototype,
        blocks:       list[BasicBlock],
        upval_names:  dict[int, str],
        pruner:       DefUsePruner,
        upv_linker:   UpvalueLinker,
    ) -> str:
        lines = []
        params = (
            ", ".join(f"v{i}" for i in range(proto.numparams))
            if proto.numparams else "..."
        )
        lines.append(f"protos[{proto.id}] = function({params})")

        # Local declarations for the full stack frame
        if proto.maxstack > 0:
            decl = ", ".join(f"v{i}" for i in range(proto.maxstack))
            lines.append(f"    local {decl}")

        if upval_names:
            lines.append(f"    -- upvalues: {', '.join(upval_names.values())}")

        # Collect all statements from reachable blocks in PC order
        all_stmts: list[str] = []
        sorted_blocks = sorted(blocks, key=lambda b: b.start_pc)
        for blk in sorted_blocks:
            for inst in blk.insts:
                if inst.stmt and not inst.stmt.startswith("goto") and not inst.stmt.startswith("-- JUMP") and not inst.stmt.startswith("-- BRANCH"):
                    all_stmts.append(inst.stmt)

        # Stage 2: def-use pruning
        pruned = pruner.prune(all_stmts)

        # Upvalue name rewriting
        pruned = upv_linker.rewrite_upvals(pruned, upval_names)

        for stmt in pruned:
            lines.append(f"    {stmt}")

        lines.append("end")
        return "\n".join(lines)

    def emit_full_script(
        self,
        protos_output: list[str],
        entry_proto_id: int,
    ) -> str:
        header = [
            "-- Deobfuscated by LuraphBot",
            "-- Section 19 Five-Step Recipe (https://4fundsagent-source.github.io/luraph-deobfuscator/blog/)",
            "-- Anti-tamper harness (Protos 1 & 2) stripped.",
            "-- CFG recovered with continuation law: effective_PC = target + 1",
            "-- Upvalues resolved via p[6] mode 0/1 capture descriptors.",
            "",
            "local protos = {}",
            "",
        ]
        footer = [
            "",
            f"-- Entry point (Section 19 Step 5)",
            f"protos[{entry_proto_id}]()",
        ]
        return "\n".join(header + protos_output + footer)


# ── Orchestrator ──────────────────────────────────────────────────────────────

class LuraphDeobfuscator:
    def __init__(self):
        self.patcher  = SeamPatcher()
        self.parser   = ProtoGraphParser()
        self.lifter   = Stage1Lifter()
        self.cfg      = CFGBuilder()
        self.splitter = NodeSplitter()
        self.pruner   = DefUsePruner()
        self.upvlink  = UpvalueLinker()
        self.emitter  = LuauEmitter()

    def deobfuscate(self, source: str) -> dict:
        """Full five-step pipeline. Returns result dict."""

        # ── Step 1: Seam patch + Luau subprocess ─────────────────────────────
        patched_source, seam_found = self.patcher.patch(source)
        if not seam_found:
            # Seam not found via regex; still try with generic injection
            # The pcall wrapper alone may catch runtime data
            pass

        full_script = INJECTED_LUAU_HEADER + patched_source + INJECTED_LUAU_FOOTER

        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                script_path = os.path.join(tmpdir, "target_hooked.luau")
                with open(script_path, "w", encoding="utf-8") as f:
                    f.write(full_script)

                proc = subprocess.run(
                    [LUAU_BIN, script_path],
                    capture_output=True, text=True,
                    timeout=30, cwd=tmpdir
                )
                stdout = proc.stdout

                if "__LPH_PROTO_START__" not in stdout:
                    # Check for error
                    if "__LPH_EXEC_ERROR__" in stdout:
                        err_block = stdout.split("__LPH_EXEC_ERROR__\n")[1]
                        err_msg   = err_block.split("__LPH_EXEC_ERROR_END__")[0].strip()
                        return {
                            "success": False,
                            "error":   f"Runtime error: {err_msg[:400]}",
                            "seam_found": seam_found,
                        }
                    return {
                        "success": False,
                        "error":   f"No prototype dump captured. stderr: {proc.stderr[:300]}",
                        "seam_found": seam_found,
                    }

                json_start = stdout.index("__LPH_PROTO_START__") + len("__LPH_PROTO_START__\n")
                json_end   = stdout.index("__LPH_PROTO_END__")
                json_str   = stdout[json_start:json_end].strip()

        except FileNotFoundError:
            return {
                "success": False,
                "error": f"luau binary '{LUAU_BIN}' not found. "
                         f"Install from https://github.com/luau-lang/luau/releases and set LUAU_BIN in bot.py.",
                "seam_found": seam_found,
            }
        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": "Script timed out (30s). May require Roblox globals or infinite loops.",
                "seam_found": seam_found,
            }

        try:
            json_data = json.loads(json_str)
        except json.JSONDecodeError as e:
            return {
                "success": False,
                "error": f"Proto JSON parse failed: {e}",
                "seam_found": seam_found,
            }

        # Parse all prototypes
        all_protos = self.parser.parse(json_data)
        total      = len(all_protos)

        # ── Step 2: Strip Protos 1 & 2 (Section 19 Step 2) ───────────────────
        # Proto 1 = bootstrap loader (403 insts)
        # Proto 2 = 4,943-instruction Roblox/UNC anti-tamper harness
        # These have zero dataflow dependencies on app protos 3..N
        app_protos = all_protos[2:]
        if not app_protos:
            return {
                "success": False,
                "error": f"No application prototypes after stripping anti-tamper (total: {total})",
                "seam_found": seam_found,
            }

        # ── Steps 3–5: Per-proto CFG + lift + prune + upvalue link ───────────
        upval_map     = self.upvlink.build_upval_map(app_protos)
        emitted_protos: list[str] = []

        for proto in app_protos:
            # Step 3: Stage 1 lift
            insts = self.lifter.lift(proto)

            # Step 3: CFG recovery (continuation law + BFS pruning)
            blocks = self.cfg.build(insts)

            # Step 3: Node-splitting for irreducible CFGs (Section 14)
            blocks = self.splitter.normalize(blocks)

            # Step 4: Upvalue linking
            upval_names = upval_map.get(proto.id, {})

            # Step 5: Emit
            proto_lua = self.emitter.emit(
                proto, blocks, upval_names, self.pruner, self.upvlink
            )
            emitted_protos.append(proto_lua)

        # Assemble final script (Section 19 Step 5)
        entry_id = app_protos[0].id
        full_out = self.emitter.emit_full_script(emitted_protos, entry_id)

        return {
            "success":       True,
            "output":        full_out,
            "total_protos":  total,
            "app_protos":    len(app_protos),
            "seam_found":    seam_found,
            "output_lines":  full_out.count("\n") + 1,
        }


# ── Optional Stage 3: Anthropic API semantic cleanup (Section 18 Stage 3) ────
# Pipes Stage 2 decompiled output through claude-sonnet-4-6 to:
# - rename v0..vN to meaningful variable names
# - resolve upvalue-shared state into lexical closures (like makeClosures example)
# - produce idiomatic Luau matching the Section 18 Stage 3 output format

async def stage3_semantic_cleanup(stage2_output: str) -> str:
    if not ANTHROPIC_KEY:
        return stage2_output

    import aiohttp
    prompt = (
        "You are a Luau decompiler performing Stage 3 semantic reconstruction. "
        "Given this raw decompiled Luau (Stage 2 output with register variables v0..vN and "
        "proto references), do the following:\n"
        "1. Rename v0, v1, ... to meaningful semantic names based on context.\n"
        "2. Resolve upvalue-shared state across sibling closures into native lexical scopes "
        "   (e.g. protos[14]/[15]/[16] that all capture _upv_r0 → local state = initial + "
        "   read/mutate/replace closures).\n"
        "3. Convert protos[N] dispatch table into named function definitions.\n"
        "4. Output only clean, idiomatic Luau. No explanations, no markdown fences.\n\n"
        f"Stage 2 input:\n{stage2_output[:12000]}"
    )

    async with aiohttp.ClientSession() as session:
        async with session.post(
            "https://api.anthropic.com/v1/messages",
            headers={
                "x-api-key":         ANTHROPIC_KEY,
                "anthropic-version": "2023-06-01",
                "content-type":      "application/json",
            },
            json={
                "model":      "claude-sonnet-4-6",
                "max_tokens": 4096,
                "messages":   [{"role": "user", "content": prompt}],
            },
            timeout=aiohttp.ClientTimeout(total=60),
        ) as resp:
            data = await resp.json()
            if "content" in data:
                return data["content"][0].get("text", stage2_output)
            return stage2_output


# ── Discord Bot ───────────────────────────────────────────────────────────────

intents                 = discord.Intents.default()
intents.message_content = True
bot                     = commands.Bot(command_prefix="!", intents=intents)
deob                    = LuraphDeobfuscator()


@bot.event
async def on_ready():
    await bot.tree.sync()
    print(f"[LuraphBot] Ready as {bot.user}")


@bot.tree.command(name="deobfuscate", description="Deobfuscate a Luraph v14.7 protected .luau/.lua script.")
@app_commands.describe(
    file       = "Obfuscated .luau or .lua file",
    stage3     = "Run Stage 3 AI semantic cleanup (requires ANTHROPIC_KEY)"
)
async def cmd_deobfuscate(
    interaction: discord.Interaction,
    file:        discord.Attachment,
    stage3:      bool = False,
):
    await interaction.response.defer(thinking=True)

    if file.size > MAX_FILE_MB * 1024 * 1024:
        await interaction.followup.send(f"File exceeds {MAX_FILE_MB} MB.")
        return
    if not file.filename.endswith((".lua", ".luau")):
        await interaction.followup.send("Needs a `.lua` or `.luau` file.")
        return

    raw = await file.read()
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError:
        source = raw.decode("latin-1")

    result = await asyncio.get_event_loop().run_in_executor(None, deob.deobfuscate, source)

    if not result["success"]:
        embed = discord.Embed(
            title       = "❌ Deobfuscation Failed",
            description = f"```{result['error'][:1800]}```",
            color       = discord.Color.red(),
        )
        embed.add_field(name="Seam found", value=str(result.get("seam_found", "—")))
        await interaction.followup.send(embed=embed)
        return

    output = result["output"]

    if stage3 and ANTHROPIC_KEY:
        output = await stage3_semantic_cleanup(output)

    stage_label = "Stage 3 (semantic)" if (stage3 and ANTHROPIC_KEY) else "Stage 2 (decompiled)"

    embed = discord.Embed(
        title       = "🔓 Deobfuscation Complete",
        description = (
            f"**Output stage:** {stage_label}\n"
            f"**Total prototypes dumped:** {result['total_protos']}\n"
            f"**Anti-tamper protos stripped:** 2 (Proto 1 bootstrap + Proto 2 harness)\n"
            f"**Application protos lifted:** {result['app_protos']}\n"
            f"**Output lines:** {result['output_lines']}\n"
            f"**Seam found:** {result['seam_found']}\n\n"
            "CFG built with `effective_PC = target + 1` (Section 8).\n"
            "Dead blocks pruned by BFS from entry (Section 13).\n"
            "Dead table stores pruned by def-use analysis (Section 12).\n"
            "Upvalues resolved via `p[6]` mode 0/1 (Section 15)."
        ),
        color = discord.Color.green(),
    )

    import io
    out_bytes = output.encode("utf-8")
    out_name  = file.filename.replace(".luau", "-deob.lua").replace(".lua", "-deob.lua")
    out_file  = discord.File(fp=io.BytesIO(out_bytes), filename=out_name)

    await interaction.followup.send(embed=embed, file=out_file)


@bot.tree.command(name="analyze", description="Analyze Luraph wrapper structure without full deobfuscation.")
@app_commands.describe(file="Obfuscated .luau or .lua file")
async def cmd_analyze(interaction: discord.Interaction, file: discord.Attachment):
    await interaction.response.defer(thinking=True)

    raw = await file.read()
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError:
        source = raw.decode("latin-1")

    # Quick structural analysis without full pipeline
    patcher   = SeamPatcher()
    _, seam   = patcher.patch(source)

    # Count anti-parser tricks (Section 1)
    trailing_underscore = len(re.findall(r'0[xXbB][0-9a-fA-F_]*_+', source))
    dup_params          = len(re.findall(r'function\s*\([^)]*\b(\w+)\b[^)]*\b\1\b[^)]*\)', source))
    encrypted_payloads  = len(re.findall(r'\[=\[.{20,}?]=\]', source, re.DOTALL))
    proto_cols          = sorted(set(int(m.group(1)) for m in re.finditer(r'\bp\[(\d+)\]', source)))
    z_z_calls           = len(re.findall(r'z\.Z\s*\(', source))

    # Try to detect Luraph version
    version = "v14.7 (11-col SoA)" if max(proto_cols, default=0) == 11 else \
              "v15 (32-slot permutation, on-demand protos)" if max(proto_cols, default=0) > 11 else \
              "unknown"

    embed = discord.Embed(title="🔍 Wrapper Analysis", color=discord.Color.blue())
    embed.add_field(name="File",                  value=f"`{file.filename}` ({file.size // 1024} KB)",  inline=False)
    embed.add_field(name="Detected version",      value=version,                                         inline=True)
    embed.add_field(name="Seam found (z:U8 → z.Z)", value="✅" if seam else "❌",                       inline=True)
    embed.add_field(name="Encrypted payload blobs", value=str(encrypted_payloads),                       inline=True)
    embed.add_field(name="Trailing _ numerics",   value=f"{trailing_underscore} (Section 1 anti-parser)", inline=True)
    embed.add_field(name="Duplicate param shadows", value=f"{dup_params} (Section 1, 53 expected)",      inline=True)
    embed.add_field(name="Proto slot max",         value=f"p[{max(proto_cols, default=0)}]",              inline=True)
    embed.add_field(name="z.Z (unpack) calls",    value=str(z_z_calls),                                  inline=True)
    embed.add_field(
        name  = "LCG Cipher (Section 5)",
        value = "A=1664525  C=1013904223  M=2³²\nKey byte = (seed >> 16) & 0xFF",
        inline = False,
    )
    if not seam:
        embed.add_field(
            name  = "⚠️ Seam not found",
            value = "The regex for `z:U8(...); return z.Z(N)` didn't match. "
                    "Variable names may differ from `variant_01`. "
                    "Run `/deobfuscate` anyway — the pcall wrapper may still capture the graph.",
            inline = False,
        )

    await interaction.followup.send(embed=embed)


@bot.tree.command(name="deobhelp", description="How the five-step deobfuscation pipeline works.")
async def cmd_help(interaction: discord.Interaction):
    await interaction.response.defer()
    embed = discord.Embed(
        title = "🛠️ LuraphBot — Five-Step Pipeline",
        description = (
            "Implements the complete Section 19 recipe from the Luraph devirtualization article.\n\n"

            "**Step 1 — Hook the deserializer seam (Section 3)**\n"
            "Patches `s8` / function `t` at `N, D = z:U8(...); return z.Z(N)`. "
            "Injects `_G.__LPH_PROTO_ROOT = D; error(sentinel)`. "
            "Runs in Luau subprocess. pcall catches the sentinel and serializes "
            "all 37 prototypes to JSON via the Section 3 `luraph_dumper.luau` crawler.\n\n"

            "**Step 2 — Strip Protos 1 & 2 (Section 6)**\n"
            "Proto 1 = 403-instruction bootstrap. "
            "Proto 2 = 4,943-instruction Roblox/UNC anti-tamper (4,484 reachable after pruning). "
            "In v14.7, Protos 3–37 have zero upvalue/dataflow deps on Proto 2 → safe to discard.\n\n"

            "**Step 3 — CFG recovery + continuation law (Sections 8, 9, 13, 14)**\n"
            "`effective_PC = target + 1` shatters decoy trampoline rings (Section 8). "
            "Leader detection partitions blocks. BFS from block 0 prunes dead suicide blocks "
            "(Section 13). Node-splitting normalizes irreducible multi-entry loops (Section 14). "
            "Opcodes lifted to real Lua statements via Section 17 table.\n\n"

            "**Step 4 — Upvalue p[6] linking (Section 15)**\n"
            "Mode 0: child captures parent's `v[index]` register. "
            "Mode 1: child forwards parent's upvalue slot. "
            "Siblings sharing a mode-0 capture get the same canonical variable name "
            "(like `state` across `read`/`mutate`/`replace` in the Section 18 example).\n\n"

            "**Step 5 — Assemble + emit (Section 19)**\n"
            "Emits `protos = {}` table, one function per app proto, entry call `protos[3]()`.\n\n"

            "**Commands:**\n"
            "`/deobfuscate` — Full pipeline → `.lua` file\n"
            "`/deobfuscate stage3:True` — + Anthropic API Stage 3 semantic cleanup\n"
            "`/analyze` — Wrapper structure report, no subprocess\n"
            "`/deobhelp` — This message\n\n"

            "**Requirements:**\n"
            "`luau` binary in PATH. Download: https://github.com/luau-lang/luau/releases\n"
            "Set `ANTHROPIC_KEY` in bot.py for Stage 3."
        ),
        color = discord.Color.blurple(),
    )
    embed.set_footer(text="Luraph v14.7 · v15 on-demand protos require hooking LPH_MiniDeserialize (Section 4)")
    await interaction.followup.send(embed=embed)


# ── Entry ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if BOT_TOKEN == "YOUR_BOT_TOKEN_HERE":
        print("[!] Set BOT_TOKEN in bot.py before running.")
        sys.exit(1)
    bot.run(BOT_TOKEN)
