# ============================================================
# flow_patch.py - paste into your existing bot script
#
# 1. Keep everything above "# Discord bot" exactly as it is.
# 2. Delete your old `send_result`, `cmd_deob` and `cmd_deob_full`.
# 3. Paste this whole file in their place (before `@bot.command(name="detect")`,
#    and after `bot = commands.Bot(...)` since the decorators need `bot`).
# 4. In `cmd_help`, replace the !deob / !deob_full lines with the one at the bottom.
#
# Bot permissions needed: Manage Channels (for the lock), Send Messages, Attach Files.
# Approval requests are DM'd to the application owner (team owner for team apps).
# The owner must allow DMs from server members, or the bot can't reach them.
# ============================================================
import random

TRACE_DELAY = (4.0, 6.0)          # cosmetic minimum display time, seconds
APPROVAL_TIMEOUT = 24 * 60 * 60   # how long the reviewer has to respond

_busy: set = set()                # channel ids with a running task


# ------------------------------------------------------------ channel lock
async def lock_channel(channel):
    """Deny @everyone from sending; keep the bot itself able to send.
    Returns previous states so unlock_channel can restore them exactly."""
    role, me = channel.guild.default_role, channel.guild.me
    ow_role, ow_me = channel.overwrites_for(role), channel.overwrites_for(me)
    prev = (ow_role.send_messages, ow_me.send_messages)
    ow_role.send_messages, ow_me.send_messages = False, True
    await channel.set_permissions(role, overwrite=ow_role, reason="Deobfuscation task running")
    await channel.set_permissions(me, overwrite=ow_me, reason="Deobfuscation task running")
    return prev


async def unlock_channel(channel, prev):
    for target, value in ((channel.guild.default_role, prev[0]), (channel.guild.me, prev[1])):
        ow = channel.overwrites_for(target)
        ow.send_messages = value
        await channel.set_permissions(target, overwrite=None if ow.is_empty() else ow,
                                      reason="Deobfuscation task finished")


# ------------------------------------------------------------ analysis (uses your backends)
@dataclass
class Analysis:
    ok: bool
    family: str
    raw: str = ""          # -> file-raw.lua
    decompiled: str = ""   # -> file-decompiled.lua
    notes: str = ""


def decompile_stage(lifted: str) -> str:
    """PLUG-IN POINT: control-flow recovery / variable naming goes here.
    Right now it only folds numeric constants, so file-decompiled is close to
    file-raw for LuaObfuscator until you add real structuring logic."""
    return _simplify_constants(lifted)


def analyze_code(code: str) -> Analysis:
    obf = detect_obfuscator(code)
    try:
        if obf == "LuaObfuscator":
            m = re.search(r"VMCall\s*\(\s*[\"'](LOL![^\"']+)", code)
            if not m:
                return Analysis(False, obf, notes="VMCall payload not found.")
            data = decode_luaobf(m.group(1))
            chunk = parse_chunk(Reader(data))
            consts = collect_consts(chunk)
            lifted = "\n".join(lift_lua_chunk(chunk))
            head = (f"-- LuaObfuscator | {len(data):,} decoded bytes | {count_funcs(chunk)} functions\n"
                    "-- Static lift only; submitted code was not executed.\n\n")
            table = "\n".join(f"-- {i}: {t} = {v!r}" for i, (t, v) in enumerate(consts))
            return Analysis(True, obf,
                            raw=head + lifted + "\n\n-- CONSTANTS\n" + table,
                            decompiled=head + decompile_stage(lifted))

        if obf == "WeAreDevs":
            decoded, omap, wmap = _decode_wad_strings(code)
            raw = (f"-- WeAreDevs | {len(decoded)} decoded strings | o={len(omap)} w={len(wmap)}\n\n"
                   + "\n".join(f"U[{i}] = {s!r}" for i, s in enumerate(decoded, 1)))
            return Analysis(True, obf, raw=raw, decompiled=deobfuscate_wearedevs(code))

        # No dedicated backend: report honestly instead of pretending.
        return Analysis(False, obf,
                        raw=generic_analysis(code, obf),
                        decompiled=f"-- No dedicated backend for {obf}; nothing was reconstructed.\n",
                        notes=f"No dedicated backend for {obf}; string/constant analysis only.")
    except Exception as exc:
        return Analysis(False, obf, notes=f"{type(exc).__name__}: {exc}")


def make_files(a: Analysis):
    files = []
    if a.raw:
        files.append(discord.File(io.BytesIO(a.raw.encode("utf-8")), filename="file-raw.lua"))
    if a.decompiled:
        files.append(discord.File(io.BytesIO(a.decompiled.encode("utf-8")), filename="file-decompiled.lua"))
    return files


# ------------------------------------------------------------ approval chain
@dataclass
class Job:
    requester: discord.Member
    channel: discord.TextChannel
    analysis: Analysis


class ApprovalView(discord.ui.View):
    def __init__(self, job: Job, reviewer_id: int):
        super().__init__(timeout=APPROVAL_TIMEOUT)
        self.job, self.reviewer_id = job, reviewer_id
        self.message = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.reviewer_id:
            await interaction.response.send_message("Not authorized.", ephemeral=True)
            return False
        return True

    async def _finish(self, interaction: discord.Interaction, verdict: str):
        for child in self.children:
            child.disabled = True
        self.stop()
        await interaction.message.edit(content=verdict, view=self)

    @discord.ui.button(label="Approve", style=discord.ButtonStyle.success)
    async def approve(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        try:
            await self.job.channel.send(
                f"{self.job.requester.mention} ✅ Your result was approved:", files=make_files(self.job.analysis))
            await self._finish(interaction, "✅ Approved and delivered.")
        except discord.HTTPException as e:
            await interaction.followup.send(f"Delivery failed: {e}")

    @discord.ui.button(label="Deny", style=discord.ButtonStyle.danger)
    async def deny(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        try:
            await self.job.channel.send(f"{self.job.requester.mention} ❌ Your result was not approved.")
        except discord.HTTPException:
            pass
        await self._finish(interaction, "❌ Denied.")

    async def on_timeout(self):
        try:
            await self.job.channel.send(f"{self.job.requester.mention} ⌛ Review timed out; nothing was delivered.")
            if self.message:
                await self.message.edit(content="⌛ Approval timed out.", view=None)
        except discord.HTTPException:
            pass


async def send_for_approval(job: Job) -> bool:
    info = await bot.application_info()
    reviewer = (info.team.owner if info.team and info.team.owner else info.owner)
    a = job.analysis
    embed = discord.Embed(title="Deobfuscation result awaiting review",
                          color=0x2ECC71 if a.ok else 0xE74C3C)
    embed.add_field(name="Requester", value=f"{job.requester} ({job.requester.id})")
    embed.add_field(name="Server / channel", value=f"{job.channel.guild.name} / #{job.channel.name}")
    embed.add_field(name="Family", value=a.family)
    embed.add_field(name="Status", value="OK" if a.ok else "FAILED / partial")
    if a.notes:
        embed.add_field(name="Notes", value=a.notes[:1000], inline=False)
    view = ApprovalView(job, reviewer.id)
    try:
        view.message = await reviewer.send(embed=embed, files=make_files(a), view=view)
        return True
    except discord.HTTPException:   # includes Forbidden (DMs closed)
        return False


# ------------------------------------------------------------ command
@bot.command(name="deob", aliases=["d", "deobfuscate"])
@commands.guild_only()
async def cmd_deob(ctx):
    chan = ctx.channel
    if chan.id in _busy:
        await ctx.reply("⏳ A task is already running in this channel.")
        return
    _busy.add(chan.id)
    lock_state, locked = None, False
    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No code found.")
            return

        lock_state = await lock_channel(chan)
        locked = True
        status = await chan.send("🔍 Tracing VM interpreter structures & unpacking bytecode stream... ⚙️")

        # Real analysis runs in a thread; the sleep is only a minimum display time.
        analysis, _ = await asyncio.gather(
            asyncio.to_thread(analyze_code, code),
            asyncio.sleep(random.uniform(*TRACE_DELAY)))

        sent = await send_for_approval(Job(ctx.author, chan, analysis))
        await status.edit(content=(
            "📨 Sent for admin review. The result will be posted here once approved."
            if sent else "❌ Review is unavailable right now; nothing was delivered."))
    finally:
        if locked:
            await unlock_channel(chan, lock_state)
        _busy.discard(chan.id)


# For cmd_help, replace the !deob / !deob_full fields with:
#   embed.add_field(name="!deob / !d", value="Detect, reconstruct, and send for admin approval (file-raw + file-decompiled)", inline=False)
