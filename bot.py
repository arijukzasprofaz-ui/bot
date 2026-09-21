import discord
from discord.ext import commands
import re, math, io, os

TOKEN = os.environ.get("TOKEN")

# ─── DECODER ───────────────────────────────────────────────────

def decode_luaobf(encoded: str) -> bytes:
    if not encoded.startswith("LOL!"):
        raise ValueError("Missing LOL! prefix")
    payload = encoded[4:]
    out = bytearray()
    repeat_next = None
    i = 0
    while i + 1 < len(payload):
        pair = payload[i:i+2]; i += 2
        if pair[1] == 'Q':
            repeat_next = int(pair[0])
        else:
            bv = int(pair, 16)
            if repeat_next is not None:
                out.extend(bytes([bv]) * repeat_next)
                repeat_next = None
            else:
                out.append(bv)
    return bytes(out)


class Reader:
    def __init__(self, data: bytes):
        self.d = data; self.p = 0

    def u8(self):
        v = self.d[self.p]; self.p += 1; return v

    def u16(self):
        a, b = self.d[self.p], self.d[self.p+1]; self.p += 2
        return (b << 8) | a

    def u32(self):
        a, b, c, d = self.d[self.p:self.p+4]; self.p += 4
        return (d << 24) | (c << 16) | (b << 8) | a

    def f64(self):
        left  = self.u32()
        right = self.u32()
        mantissa = ((right & 0xFFFFF) * (2**32)) + left
        exponent = (right >> 20) & 0x7FF
        sign     = -1 if (right >> 31) else 1
        if exponent == 0:
            if mantissa == 0: return sign * 0.0
            is_normal = 0; exponent = 1
        elif exponent == 2047:
            return float('inf') * sign if mantissa == 0 else float('nan')
        else:
            is_normal = 1
        return math.ldexp(sign, exponent - 1023) * (is_normal + mantissa / (2**52))

    def string(self, length=None):
        if length is None:
            length = self.u32()
            if length == 0: return ""
        raw = self.d[self.p:self.p+length]; self.p += length
        return bytes(raw).decode('utf-8', errors='replace')

    @staticmethod
    def gbit(val, start, end=None):
        if end is not None:
            res = (val // (2 ** (start - 1))) % (2 ** ((end - start) + 1))
            return int(res)
        plc = 2 ** (start - 1)
        return 1 if (val % (plc * 2)) >= plc else 0


def parse_chunk(r: Reader, depth=0) -> dict:
    const_count = r.u32()
    consts = []
    for _ in range(const_count):
        t = r.u8()
        if   t == 1: consts.append(('bool', r.u8() != 0))
        elif t == 2: consts.append(('num',  r.f64()))
        elif t == 3: consts.append(('str',  r.string()))
        else:        consts.append(('nil',  None))

    params      = r.u8()
    instr_count = r.u32()
    instrs      = []

    for _ in range(instr_count):
        desc = r.u8()
        if r.gbit(desc, 1, 1) == 1:
            continue

        typ  = r.gbit(desc, 2, 3)
        mask = r.gbit(desc, 4, 6)
        op   = r.u16()
        a    = r.u16()
        b    = None
        c    = None

        if   typ == 0: b = r.u16(); c = r.u16()
        elif typ == 1: b = r.u32()
        elif typ == 2: b = r.u32() - (1 << 16)
        elif typ == 3: b = r.u32() - (1 << 16); c = r.u16()

        def res(v, bit):
            if v is None: return v
            if r.gbit(mask, bit, bit) == 1 and isinstance(v, int) and 0 <= v < len(consts):
                return consts[v][1]
            return v

        instrs.append((op, res(a, 1), res(b, 2), res(c, 3)))

    subs = [parse_chunk(r, depth + 1) for _ in range(r.u32())]
    return {'depth': depth, 'params': params, 'consts': consts, 'instrs': instrs, 'subs': subs}


def collect_consts(chunk, out=None):
    if out is None: out = []
    out.extend(chunk['consts'])
    for s in chunk['subs']: collect_consts(s, out)
    return out


def count_funcs(chunk):
    return 1 + sum(count_funcs(s) for s in chunk['subs'])


def format_result(chunk, include_instrs=False) -> str:
    lines = []
    all_c   = collect_consts(chunk)
    strings = [(i, v) for i, (t, v) in enumerate(all_c) if t == 'str']
    numbers = [(i, v) for i, (t, v) in enumerate(all_c) if t == 'num']

    lines.append("=" * 58)
    lines.append("  LuaObfuscator.com — Deobfuscated")
    lines.append(f"  {len(all_c)} consts  |  {count_funcs(chunk)} functions")
    lines.append("=" * 58)
    lines.append("")

    lines.append(f"── STRINGS ({len(strings)}) ─────────────────────────────")
    for i, v in strings:
        lines.append(f"  [{i:03d}]  {repr(v)}")

    lines.append("")
    lines.append(f"── NUMBERS ({len(numbers)}) ─────────────────────────────")
    for i, v in numbers:
        lines.append(f"  [{i:03d}]  {v}")

    if include_instrs:
        lines.append("")
        lines.append("── INSTRUCTIONS (main chunk) ────────────────────────")
        for idx, (op, a, b, c) in enumerate(chunk['instrs']):
            lines.append(f"  [{idx:04d}]  OP={op:<4} A={str(a):<22} B={str(b):<22} C={str(c)}")

        for fi, sub in enumerate(chunk['subs']):
            lines.append("")
            lines.append(f"── FUNCTION {fi} ({'  ' * sub['depth']}) ─────────────────────────")
            for idx, (op, a, b, c) in enumerate(sub['instrs']):
                lines.append(f"  [{idx:04d}]  OP={op:<4} A={str(a):<22} B={str(b):<22} C={str(c)}")

    return "\n".join(lines)


def run_deob(code: str, include_instrs=False) -> str:
    m = re.search(r'VMCall\("(LOL![^"]+)"', code)
    if not m:
        return "ERROR: No VMCall payload found — not a LuaObfuscator.com script."
    try:
        raw = decode_luaobf(m.group(1))
    except Exception as e:
        return f"ERROR (string decode): {e}"
    try:
        chunk = parse_chunk(Reader(raw))
    except Exception as e:
        return f"ERROR (bytecode parse): {e}\n(decoded {len(raw)} bytes)"
    return format_result(chunk, include_instrs)


# ─── BOT ───────────────────────────────────────────────────────

intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents)


@bot.event
async def on_ready():
    print(f"[+] {bot.user} ({bot.user.id})")
    await bot.change_presence(activity=discord.Activity(
        type=discord.ActivityType.watching, name="obfuscated lua"))


async def extract_code(ctx) -> str | None:
    for att in ctx.message.attachments:
        if att.filename.endswith(('.lua', '.luau', '.txt')):
            return (await att.read()).decode('utf-8', errors='replace')
    m = re.search(r'```(?:lua[ua]?)?\n?([\s\S]+?)```', ctx.message.content)
    if m:
        return m.group(1).strip()
    return None


async def send_result(ctx, msg, result: str, filename: str):
    if len(result) <= 1900:
        await msg.edit(content=f"```\n{result}\n```")
    else:
        f = discord.File(io.BytesIO(result.encode()), filename=filename)
        await msg.delete()
        await ctx.reply("✅ Done:", file=f)


@bot.command(name="deob", aliases=["d", "deobfuscate"])
async def cmd_deob(ctx):
    """Deobfuscate — strings + structure"""
    code = await extract_code(ctx)
    if not code:
        await ctx.reply(
            "❌ No code found.\n"
            "Attach `.lua`/`.txt` or paste in a ` ```lua ` block."
        ); return
    msg = await ctx.reply("⏳ Decoding...")
    result = run_deob(code, include_instrs=False)
    await send_result(ctx, msg, result, "deobf.txt")


@bot.command(name="deob_full", aliases=["df"])
async def cmd_deob_full(ctx):
    """Deobfuscate with full instruction listing"""
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found."); return
    msg = await ctx.reply("⏳ Decoding (full mode)...")
    result = run_deob(code, include_instrs=True)
    await send_result(ctx, msg, result, "deobf_full.txt")


@bot.command(name="strings", aliases=["s", "strs"])
async def cmd_strings(ctx):
    """Extract string constants only"""
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found."); return
    m = re.search(r'VMCall\("(LOL![^"]+)"', code)
    if not m:
        await ctx.reply("❌ Not a LuaObfuscator.com script."); return
    try:
        raw   = decode_luaobf(m.group(1))
        chunk = parse_chunk(Reader(raw))
        strs  = [v for t, v in collect_consts(chunk) if t == 'str']
    except Exception as e:
        await ctx.reply(f"❌ `{e}`"); return
    out = "\n".join(repr(s) for s in strs)
    if len(out) <= 1900:
        await ctx.reply(f"**{len(strs)} strings:**\n```\n{out}\n```")
    else:
        f = discord.File(io.BytesIO(out.encode()), filename="strings.txt")
        await ctx.reply(f"**{len(strs)} strings:**", file=f)


@bot.command(name="info")
async def cmd_info(ctx):
    code = await extract_code(ctx)
    if not code:
        await ctx.reply("❌ No code found."); return
    m = re.search(r'VMCall\("(LOL![^"]+)"', code)
    if not m:
        await ctx.reply("❌ Not a LuaObfuscator.com script."); return
    try:
        raw   = decode_luaobf(m.group(1))
        chunk = parse_chunk(Reader(raw))
        all_c = collect_consts(chunk)
        strs  = sum(1 for t, _ in all_c if t == 'str')
        nums  = sum(1 for t, _ in all_c if t == 'num')
        funcs = count_funcs(chunk)
    except Exception as e:
        await ctx.reply(f"❌ `{e}`"); return
    embed = discord.Embed(title="Script Info", color=0x7289DA)
    embed.add_field(name="Decoded bytes", value=f"`{len(raw)}`", inline=True)
    embed.add_field(name="Functions",     value=f"`{funcs}`",    inline=True)
    embed.add_field(name="Strings",       value=f"`{strs}`",     inline=True)
    embed.add_field(name="Numbers",       value=f"`{nums}`",     inline=True)
    await ctx.reply(embed=embed)


bot.run(TOKEN)
