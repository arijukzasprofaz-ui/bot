# ============================================================
# WeAreDevs Trace-Based Deobfuscator
# Mirrors Prometheus-WeAre-Devs-Dumper approach, adapted for
# async Discord bot context. Requires Lua 5.1 on host or in
# ./lua_bin/lua5.1.exe (Windows) / lua5.1 on PATH (Linux).
# ============================================================

import shutil

_WAD_COMPOUND_OPS = ("+=", "-=", "*=", "/=", "%=", "..=")

def _wad_table_end(src: str, ob: int) -> int:
    depth, quote, i = 0, None, ob
    while i < len(src):
        c = src[i]
        if quote:
            if c == '\\': i += 2; continue
            if c == quote: quote = None
        elif c in ('"', "'"): quote = c
        elif c == '{': depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0: return i + 1
        i += 1
    return -1

def _wad_normalize(src: str) -> str:
    """Expand Luau compound assignment:  a += b  →  a = a + b"""
    replacements, i = [], 0
    while i < len(src):
        op = next((o for o in _WAD_COMPOUND_OPS if src.startswith(o, i)), None)
        if not op: i += 1; continue
        # walk left
        li = i - 1
        while li >= 0 and src[li].isspace(): li -= 1
        lend = li + 1
        while li >= 0 and (src[li].isalnum() or src[li] in '_.][ '): li -= 1
        lhs = src[li+1:lend].strip()
        # walk right
        ri = i + len(op)
        while ri < len(src) and src[ri].isspace(): ri += 1
        rend, pd, bd, brd, qq = ri, 0, 0, 0, None
        while rend < len(src):
            ch = src[rend]
            if qq:
                if ch == '\\': rend += 2; continue
                if ch == qq: qq = None
            elif ch in ('"', "'"): qq = ch
            elif ch == '(': pd += 1
            elif ch == ')':
                if pd == 0: break
                pd -= 1
            elif ch == '{': bd += 1
            elif ch == '}':
                if bd == 0: break
                bd -= 1
            elif ch == '[': brd += 1
            elif ch == ']':
                if brd == 0 and pd == 0 and bd == 0: break
                brd -= 1
            elif pd == 0 and bd == 0 and brd == 0 and ch in (',', ';', '\n', '\r'):
                break
            rend += 1
        rhs = src[i+len(op):rend].strip()
        if lhs and rhs:
            replacements.append((li+1, rend, f"{lhs} = {lhs} {op[:-1]} {rhs}"))
        i = rend
    for start, end, rep in reversed(replacements):
        src = src[:start] + rep + src[end:]
    return src

_WAD_ESC_LUA = r"""
local function _esc(s)
    local p={'"'}
    for i=1,#s do
        local b=string.byte(s,i)
        if b==92 then p[#p+1]="\\\\"
        elseif b==34 then p[#p+1]="\\\""
        elseif b==10 then p[#p+1]="\\n"
        elseif b==13 then p[#p+1]="\\r"
        elseif b==9  then p[#p+1]="\\t"
        elseif b>=32 and b<=126 then p[#p+1]=string.char(b)
        else p[#p+1]=string.format("\\%03d",b) end
    end
    p[#p+1]='"'
    return table.concat(p)
end
"""

def _wad_get_lua_exe() -> str:
    if os.name == 'nt':
        local_bin = os.path.join('lua_bin', 'lua5.1.exe')
        if os.path.isfile(local_bin): return local_bin
        for c in ('lua5.1.exe', 'lua51.exe', 'lua.exe'):
            if shutil.which(c): return c
    else:
        for c in ('lua5.1', 'lua51', 'lua'):
            if shutil.which(c): return c
    return 'lua5.1'  # falls through to subprocess error message

def _wad_extract_static_constants(src: str, var_name: str, lua_exe: str) -> str:
    """Run the string table through Lua 5.1 to resolve encoded constants."""
    m = re.search(rf'\blocal\s+{re.escape(var_name)}\s*=\s*\{{', src)
    if not m: return ""
    ob = src.find('{', m.start())
    te = _wad_table_end(src, ob)
    if te == -1: return ""
    tbl = src[ob:te]
    lua_src = _WAD_ESC_LUA + f"""
local t={tbl}
local out="local Constants = {{"
for i,v in ipairs(t) do
    out=out.." ["..i.."] = ".._esc(v)..","
end
print(out.." }}")
"""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lua', delete=False, encoding='utf-8') as f:
        f.write(lua_src); tmp = f.name
    try:
        r = subprocess.run([lua_exe, tmp], capture_output=True, timeout=15)
        return r.stdout.decode('utf-8', 'replace').strip() if r.returncode == 0 else ""
    except Exception:
        return ""
    finally:
        if os.path.exists(tmp): os.remove(tmp)

# Lua mock environment — injected at top of script before execution
_WAD_MOCK_ENV = r"""
local _rt=type; local _rc=table.concat; local _ru=unpack; local _rtn=tonumber
local _WAITS=0

local function _esc(s)
    local p={'"'}
    for i=1,#s do
        local b=string.byte(s,i)
        if b==92 then p[#p+1]="\\\\"
        elseif b==34 then p[#p+1]="\\\""
        elseif b==10 then p[#p+1]="\\n"
        elseif b==13 then p[#p+1]="\\r"
        elseif b==9  then p[#p+1]="\\t"
        elseif b>=32 and b<=126 then p[#p+1]=string.char(b)
        else p[#p+1]=string.format("\\%03d",b) end
    end
    p[#p+1]='"'; return table.concat(p)
end

local function _rts(v,d)
    d=d or 0; if d>2 then return tostring(v) end
    local t=_rt(v)
    if t=="string" then return _esc(v)
    elseif t=="number" then
        if v==math.floor(v) and v>=-2147483648 and v<=2147483647 then return tostring(math.floor(v)) end
        return tostring(v)
    elseif t=="boolean" or v==nil then return tostring(v)
    elseif t=="table" then
        local mt=getmetatable(v); if mt and mt.__wad then return tostring(v) end
        local p,ks={},{}
        for k in pairs(v) do ks[#ks+1]=k end
        table.sort(ks,function(a,b) return tostring(a)<tostring(b) end)
        for _,k in ipairs(ks) do
            local ks2=_rt(k)=="string" and ('["'..k..'"]') or tostring(k)
            p[#p+1]=ks2.." = ".._rts(v[k],d+1)
        end
        return "{"..table.concat(p,", ").."}"
    end
    return tostring(v)
end

local function _dummy(name)
    local d={}
    setmetatable(d,{
        __wad=true,
        __index=function(_,k)
            io.write("ACCESSED --> "..name.."."..k.."\n")
            if k=="HttpGet" or k=="HttpGetAsync" then
                return function(_,url) io.write("URL --> "..tostring(url).."\n") return _dummy("HttpResult") end
            end
            return _dummy(name.."."..k)
        end,
        __newindex=function(_,k,v) io.write("PROP_SET --> "..name.."."..k.." = ".._rts(v).."\n") end,
        __call=function(_,...)
            local args={...}; local ss={}
            for _,v in ipairs(args) do ss[#ss+1]=_rts(v) end
            local vn=name:gsub("%.",  "_").."_"..math.random(100,999)
            io.write("CALL_RESULT --> local "..vn.." = "..name.."("..table.concat(ss,", ")..")\n")
            if name=="task.wait" or name=="wait" then
                _WAITS=_WAITS+1; if _WAITS>10 then error("max waits") end
            end
            for _,v in ipairs(args) do
                if _rt(v)=="function" then
                    io.write("--- CLOSURE "..name.." ---\n")
                    pcall(v,_dummy("a1"),_dummy("a2"),_dummy("a3"),_dummy("a4"))
                    io.write("--- END CLOSURE ---\n")
                end
            end
            if name=="readfile" or name=="loadfile" then return "" end
            if name=="isfile" or name=="isfolder" then return false end
            if name=="listfiles" then return {} end
            if name=="writefile" or name=="makefolder" or name=="delfile" then return nil end
            return _dummy(vn)
        end,
        __tostring=function() return name end,
        __concat=function(a,b) return tostring(a)..tostring(b) end,
        __add=function(a,b) return _dummy("("..tostring(a).."+"..tostring(b)..")") end,
        __sub=function(a,b) return _dummy("("..tostring(a).."-"..tostring(b)..")") end,
        __mul=function(a,b) return _dummy("("..tostring(a).."*"..tostring(b)..")") end,
        __div=function(a,b) return _dummy("("..tostring(a).."/"..tostring(b)..")") end,
        __mod=function(a,b) return _dummy("("..tostring(a).."%"..tostring(b)..")") end,
        __pow=function(a,b) return _dummy("("..tostring(a).."^"..tostring(b)..")") end,
        __unm=function(a) return _dummy("-"..tostring(a)) end,
        __lt=function() return false end, __le=function() return false end,
        __eq=function() return false end, __len=function() return 2 end,
    })
    return d
end

local MockEnv={}
local _safe={
    string=string,
    table={insert=table.insert,remove=table.remove,sort=table.sort,maxn=table.maxn,
        concat=function(t,s,i,j)
            local r=_rc(t,s,i,j)
            local url=r:match("https?://[%w%.%-%/%?%_%=%&%:]+")
            if url then io.write("URL_CONCAT --> "..url.."\n") end
            return r
        end},
    math=math, select=select,
    unpack=function(t,i,j)
        if _rt(t)=="table" and #t>0 then
            local ok,res=pcall(_rc,t,",")
            if ok then
                local url=res:match("https?://[%w%.%-%/%?%_%=%&%:]+")
                if url then io.write("URL_UNPACK --> "..url.."\n") end
                io.write("UNPACK_TABLE --> "..res:sub(1,200).."\n")
            end
        end
        return _ru(t,i,j)
    end,
    tonumber=function(v,b)
        local mt=getmetatable(v); if mt and mt.__wad then return 1 end
        return _rtn(v,b)
    end,
    tostring=tostring,
    type=function(v) local mt=getmetatable(v); if mt and mt.__wad then return "userdata" end return _rt(v) end,
    typeof=function(v) local mt=getmetatable(v); if mt and mt.__wad then return "Instance" end return _rt(v) end,
    pcall=pcall, xpcall=xpcall, getfenv=getfenv,
    setmetatable=setmetatable, getmetatable=getmetatable,
    error=error, assert=assert, next=next,
    print=function(...) local p={} for _,v in ipairs({...}) do p[#p+1]=tostring(v) end
        io.write("TRACE_PRINT --> "..table.concat(p,"\t").."\n") end,
    rawset=rawset, rawget=rawget, os=os, io=io, debug=debug, _VERSION=_VERSION,
    loadstring=function(s)
        io.write("LOADSTRING --> size="..#s.."\n")
        io.write("LOADSTRING_START\n"..s.."\nLOADSTRING_END\n")
        return function() end
    end,
    pairs=function(t)
        local mt=getmetatable(t)
        if mt and mt.__wad then local i=0 return function() i=i+1 if i<=1 then return i,_dummy(tostring(t).."_v"..i) end end end
        return pairs(t)
    end,
    ipairs=function(t)
        local mt=getmetatable(t)
        if mt and mt.__wad then local i=0 return function() i=i+1 if i<=1 then return i,_dummy(tostring(t).."_v"..i) end end end
        return ipairs(t)
    end,
}
_safe._G=MockEnv; _safe.shared=MockEnv
setmetatable(MockEnv,{
    __index=function(_,k)
        if _safe[k] then return _safe[k] end
        if k=="game" then io.write("ACCESSED --> game\n") return _dummy("game") end
        if k=="getgenv" or k=="getrenv" or k=="getreg" then return function() return MockEnv end end
        io.write("ACCESSED --> "..tostring(k).."\n")
        return _dummy(k)
    end,
    __newindex=function(_,k,v)
        io.write("SET_GLOBAL --> "..tostring(k).." = ".._rts(v).."\n")
        rawset(MockEnv,k,v)
    end,
})
"""

async def wad_deobfuscate(code: str) -> str:
    """
    Trace-based WeAreDevs deobfuscation.
    Injects MockEnv, executes in Lua 5.1 subprocess,
    captures and returns structured report string.
    """
    lua_exe = _wad_get_lua_exe()
    code = _wad_normalize(code)

    # Locate string table  →  local XYZ={"...",...}
    m = re.search(r'local ([a-zA-Z0-9_]+)\s*=\s*\{"', code)
    if not m:
        return "❌ WeAreDevs string table not found — may not be WeAreDevs or format changed."
    var_name = m.group(1)

    # Attempt static constant extraction first (fallback if Lua compile fails)
    static_consts = _wad_extract_static_constants(code, var_name, lua_exe)

    # Injection point: last `return(function` before the getfenv call
    idx_gf = code.rfind('(getfenv')
    if idx_gf == -1: idx_gf = len(code)
    idx_ret = max(
        code.rfind('return(function', 0, idx_gf),
        code.rfind('return (function', 0, idx_gf),
    )
    if idx_ret == -1:
        return "❌ Bootstrap injection point not found."

    # Inline constant dumper — injected just before the VM bootstrap
    dumper = f"""
io.write("CONSTANTS_START\\n")
if {var_name} then
    local ks={{}}; for k in pairs({var_name}) do ks[#ks+1]=k end; table.sort(ks)
    local out="local Constants = {{"
    for _,k in ipairs(ks) do
        local v={var_name}[k]
        if type(v)=="string" then
            out=out.." ["..k.."] = \\""..v:gsub("\\\\","\\\\\\\\"):gsub('"','\\\\"').."\\","
        end
    end
    io.write(out.." }}\\n")
end
io.write("CONSTANTS_END\\n")
"""

    patched = _WAD_MOCK_ENV + code[:idx_ret] + dumper + code[idx_ret:]
    patched = re.sub(r'getfenv\s+and\s+getfenv\(\)\s*or\s*_ENV', 'MockEnv', patched)
    patched = patched.replace('getfenv and getfenv()or _ENV', 'MockEnv')

    with tempfile.NamedTemporaryFile(mode='w', suffix='.lua', delete=False, encoding='utf-8') as f:
        f.write(patched); tmp = f.name

    try:
        proc = await asyncio.create_subprocess_exec(
            lua_exe, tmp, '1',
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        try:
            stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=25)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.communicate()
            return "❌ Deobfuscation timed out (25 s)."
    finally:
        if os.path.exists(tmp): os.remove(tmp)

    out_text = stdout.decode('utf-8', 'replace')
    err_text  = stderr.decode('utf-8', 'replace').strip()

    PREFIXES = (
        "ACCESSED", "CALL_RESULT", "URL", "SET_GLOBAL",
        "UNPACK_TABLE", "TRACE_PRINT", "PROP_SET",
        "LOADSTRING", "CLOSURE",
    )
    consts_lines, trace_lines, in_consts = [], [], False
    for line in out_text.splitlines():
        s = line.strip()
        if s == "CONSTANTS_START":  in_consts = True;  continue
        if s == "CONSTANTS_END":    in_consts = False; continue
        if in_consts:               consts_lines.append(s)
        elif any(s.startswith(p) for p in PREFIXES): trace_lines.append(s)

    # Fall back to static extraction if Lua couldn't compile the whole blob
    if not consts_lines and static_consts:
        consts_lines = [static_consts]

    report = ["=== WeAreDevs Deobfuscation Report ===", ""]
    if consts_lines:
        report += ["--- Recovered Constants ---"] + consts_lines + [""]
    if trace_lines:
        report += ["--- Execution Trace ---"] + trace_lines[:500] + [""]  # cap trace at 500 lines
    if err_text and "control structure too long" not in err_text:
        report += ["--- Stderr ---", err_text[:1000]]
    if not consts_lines and not trace_lines:
        report.append("⚠ No output recovered — script may use unsupported patterns or Lua 5.1 is not installed.")

    return "\n".join(report)
