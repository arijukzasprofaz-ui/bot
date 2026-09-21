import discord
from discord.ext import commands
import asyncio
import io
import math
import os
import re
from typing import Optional
 
TOKEN = os.environ.get("TOKEN")
 
# ─── DETECTION ────────────────────────────────────────────────
 
SIGNATURES = [
    # Most specific first to avoid cross-matching
    ("LuaObfuscator", lambda c: bool(re.search(r'VMCall\s*\(\s*"LOL!', c))),
    ("IronBrew3",     lambda c: bool(re.search(r'ironbrew\s*3', c[:2000], re.I)) or "IronBrew3" in c[:1000]),
    ("IronBrew2",     lambda c: bool(re.search(r'ironbrew\s*2', c[:2000], re.I)) or "IronBrew2" in c[:1000]),
    ("IronBrew",      lambda c: bool(re.search(r'ironbrew', c[:2000], re.I))),
    ("WeAreDevs",     lambda c: "wearedevs.net/obfuscator" in c or bool(re.search(r'\bo\s*=\s*\{["\?]', c[:500]))),
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
