import discord
from discord.ext import commands
import aiohttp
import io

# ═══════════════════════════════════════
#  CONFIG — fill these in
# ═══════════════════════════════════════
TOKEN    = "YOUR_BOT_TOKEN_HERE"
GH_USER  = "YOUR_GITHUB_USERNAME"
GH_REPO  = "YOUR_REPO_NAME"
GH_BRANCH = "main"                     # change if your branch is 'master'
# ═══════════════════════════════════════

RAW_BASE = f"https://raw.githubusercontent.com/{GH_USER}/{GH_REPO}/{GH_BRANCH}"

FILES = [
    "optimizer.py",
    "BUILD_ME.bat",
]

intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)


@bot.event
async def on_ready():
    print(f"[K] online as {bot.user} ({bot.user.id})")


@bot.command(name="down")
async def down(ctx: commands.Context):
    """Pulls optimizer.py + BUILD_ME.bat from GitHub and drops them here."""

    # ── loading message ───────────────────────────────────
    loading = await ctx.send(
        embed=discord.Embed(
            description="⏳ fetching files from GitHub…",
            color=0x7c6aff
        )
    )

    attachments: list[discord.File] = []
    failed:      list[str]          = []

    async with aiohttp.ClientSession() as session:
        for filename in FILES:
            url = f"{RAW_BASE}/{filename}"
            try:
                async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
                    if resp.status == 200:
                        data = await resp.read()
                        attachments.append(
                            discord.File(io.BytesIO(data), filename=filename)
                        )
                    else:
                        failed.append(f"{filename} (HTTP {resp.status})")
            except Exception as e:
                failed.append(f"{filename} ({type(e).__name__})")

    # ── build response embed ──────────────────────────────
    if attachments and not failed:
        embed = discord.Embed(
            title="K|Optimizer",
            description=f"downloaded **{len(attachments)}** file(s) from `{GH_USER}/{GH_REPO}`",
            color=0x22c55e
        )
        embed.add_field(
            name="files",
            value="\n".join(f"✅ `{f.filename}`" for f in attachments),
            inline=False
        )
        embed.set_footer(text="run BUILD_ME.bat to compile → dist/KOptimizer.exe")

    elif attachments and failed:
        embed = discord.Embed(
            title="K|Optimizer — partial",
            color=0xf59e0b
        )
        embed.add_field(
            name="got",
            value="\n".join(f"✅ `{f.filename}`" for f in attachments),
            inline=False
        )
        embed.add_field(
            name="failed",
            value="\n".join(f"❌ `{name}`" for name in failed),
            inline=False
        )

    else:
        embed = discord.Embed(
            description=f"❌ couldn't fetch anything.\ncheck `GH_USER` / `GH_REPO` in bot.py\n\nfailed: " +
                        ", ".join(f"`{f}`" for f in failed),
            color=0xef4444
        )

    await loading.delete()
    await ctx.send(embed=embed, files=attachments)


bot.run(TOKEN)
