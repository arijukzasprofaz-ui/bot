import asyncio
import glob
import io
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from collections import OrderedDict
from typing import Optional

import discord
from discord.ext import commands

# ============================================================
# Configuration
# ============================================================

TOKEN = os.getenv("TOKEN")

MAX_INPUT_BYTES    = 2 * 1024 * 1024
MAX_DISCORD_FILE_BYTES = 2 * 1024 * 1024
ANALYSIS_CONCURRENCY   = 2
TRACE_DELAY            = (1.5, 3.0)

analysis_semaphore  = asyncio.Semaphore(ANALYSIS_CONCURRENCY)
_busy_channels: set[int] = set()

# ============================================================
# deobfuscator.py — Lua executable / syntax helpers
# ============================================================

COMPOUND_ASSIGNMENT_OPERATORS = ("+=", "-=", "*=", "/=", "%=", "..=")
LUA_CONTROL_STRUCTURE_TOO_LONG = "control structure too long"


def get_lua_executable():
    if os.name == "nt":
        return os.path.join("lua_bin", "lua5.1.exe")
    env_path = os.environ.get("LUA51_EXECUTABLE")
    if env_path:
        return env_path
    for candidate in ("lua5.1", "lua51", "lua"):
        path = shutil.which(candidate)
        if path:
            return path
    return "lua5.1"


def _find_table_literal_end(content, open_brace_index):
    depth = 0
    quote = None
    idx   = open_brace_index
    while idx < len(content):
        char = content[idx]
        if quote:
            if char == "\\":
                idx += 2
                continue
            if char == quote:
                quote = None
            idx += 1
            continue
        if char in ("'", '"'):
            quote = char
        elif char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return idx + 1
        idx += 1
    return -1


def extract_static_constants(content, var_name):
    table_match = re.search(rf'\blocal\s+{re.escape(var_name)}\s*=\s*\{{', content)
    if not table_match:
        return ""
    open_brace_index = content.find("{", table_match.start())
    table_end = _find_table_literal_end(content, open_brace_index)
    if table_end == -1:
        return ""

    lua_code = r'''
local function escape_lua_string(s)
    local parts = {'"'}
    for i = 1, #s do
        local byte = string.byte(s, i)
        if byte == 92 then
            table.insert(parts, "\\\\")
        elseif byte == 34 then
            table.insert(parts, "\\\"")
        elseif byte == 10 then
            table.insert(parts, "\\n")
        elseif byte == 13 then
            table.insert(parts, "\\r")
        elseif byte == 9 then
            table.insert(parts, "\\t")
        elseif byte >= 32 and byte <= 126 then
            table.insert(parts, string.char(byte))
        else
            table.insert(parts, string.format("\\%03d", byte))
        end
    end
    table.insert(parts, '"')
    return table.concat(parts)
end

local constants = __STATIC_TABLE__
local out = "local Constants = {"
for i, v in ipairs(constants) do
    out = out .. " [" .. i .. "] = " .. escape_lua_string(v) .. ","
end
out = out .. " }"
print(out)
'''.replace("__STATIC_TABLE__", content[open_brace_index:table_end])

    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".lua", delete=False) as fh:
        temp_path = fh.name
        fh.write(lua_code)
    try:
        proc = subprocess.run(
            [get_lua_executable(), temp_path],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20,
        )
        if proc.returncode == 0:
            return proc.stdout.decode("utf-8", errors="replace").strip()
    finally:
        if os.path.exists(temp_path):
            os.remove(temp_path)
    return ""


def _configure_text_streams():
    for stream_name in ("stdout", "stderr"):
        stream = getattr(sys, stream_name, None)
        if stream is None or not hasattr(stream, "reconfigure"):
            continue
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass


def _find_compound_lhs_start(content, operator_index):
    idx = operator_index - 1
    while idx >= 0 and content[idx].isspace():
        idx -= 1
    while idx >= 0 and content[idx] == "]":
        bracket_depth = 1
        idx -= 1
        while idx >= 0 and bracket_depth > 0:
            if content[idx] == "]":   bracket_depth += 1
            elif content[idx] == "[": bracket_depth -= 1
            idx -= 1
    while idx >= 0 and (content[idx].isalnum() or content[idx] == "_"):
        idx -= 1
    while idx >= 0 and content[idx] == ".":
        idx -= 1
        while idx >= 0 and content[idx] == "]":
            bracket_depth = 1
            idx -= 1
            while idx >= 0 and bracket_depth > 0:
                if content[idx] == "]":   bracket_depth += 1
                elif content[idx] == "[": bracket_depth -= 1
                idx -= 1
        while idx >= 0 and (content[idx].isalnum() or content[idx] == "_"):
            idx -= 1
    return idx + 1


def _find_compound_rhs_end(content, rhs_start):
    idx = rhs_start
    length = len(content)
    bracket_depth = paren_depth = brace_depth = 0
    quote = None
    while idx < length and content[idx].isspace():
        idx += 1
    while idx < length:
        char = content[idx]
        if quote:
            if char == "\\":
                idx += 2
                continue
            if char == quote:
                quote = None
            idx += 1
            continue
        if char in ("'", '"'):
            quote = char
            idx += 1
            continue
        if char == "[":   bracket_depth += 1
        elif char == "]": bracket_depth = max(0, bracket_depth - 1)
        elif char == "(": paren_depth += 1
        elif char == ")":
            if paren_depth == 0 and bracket_depth == 0 and brace_depth == 0:
                break
            paren_depth = max(0, paren_depth - 1)
        elif char == "{": brace_depth += 1
        elif char == "}":
            if brace_depth == 0 and bracket_depth == 0 and paren_depth == 0:
                break
            brace_depth = max(0, brace_depth - 1)
        elif bracket_depth == 0 and paren_depth == 0 and brace_depth == 0:
            if char in ";\n\r,":
                break
            if char.isspace():
                break
        idx += 1
    return idx


def normalize_luau_syntax(content):
    replacements = []
    idx = 0
    while idx < len(content):
        matched_operator = None
        for operator in COMPOUND_ASSIGNMENT_OPERATORS:
            if content.startswith(operator, idx):
                matched_operator = operator
                break
        if not matched_operator:
            idx += 1
            continue
        lhs_start = _find_compound_lhs_start(content, idx)
        rhs_start = idx + len(matched_operator)
        rhs_end   = _find_compound_rhs_end(content, rhs_start)
        lhs = content[lhs_start:idx].strip()
        rhs = content[rhs_start:rhs_end].strip()
        if lhs and rhs:
            replacements.append((lhs_start, rhs_end, f"{lhs} = {lhs} {matched_operator[:-1]} {rhs}"))
        idx = rhs_end
    if not replacements:
        return content
    rewritten = content
    for start, end, replacement in reversed(replacements):
        rewritten = rewritten[:start] + replacement + rewritten[end:]
    return rewritten


_configure_text_streams()


def deobfuscate_file(filepath):
    print(f"Processing {filepath}...")
    if ".deobf." in filepath or ".report." in filepath:
        return
    try:
        with open(filepath, "r", encoding="utf-8", errors="replace") as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return

    content = normalize_luau_syntax(content)

    match = re.search(r'local ([a-zA-Z0-9_]+)=\{"', content)
    if not match:
        print(f"Could not identify string table variable in {filepath}.")
        return
    var_name = match.group(1)
    static_constants = extract_static_constants(content, var_name)

    mock_env_code = r"""
local real_type = type
local real_tonumber = tonumber
local real_unpack = unpack
local real_concat = table.concat
local real_tostring = tostring
local real_print = print

local _WAIT_COUNT = 0
local _LOOP_COUNTER = 0
local _MAX_LOOPS = 150
local _LOOP_BODIES = {}

local function _check_loop()
    _LOOP_COUNTER = _LOOP_COUNTER + 1
    if _LOOP_COUNTER > _MAX_LOOPS then
        return false
    end
    return true
end

local function type(v)
    local mt = getmetatable(v)
    if mt and mt.__is_mock_dummy then
        return "userdata"
    end
    return real_type(v)
end

local function typeof(v)
    local mt = getmetatable(v)
    if mt and mt.__is_mock_dummy then
        return "Instance"
    end
    return type(v)
end

local function tonumber(v, base)
    if type(v) == "userdata" or (type(v) == "table" and getmetatable(v) and getmetatable(v).__is_mock_dummy) then
        return 1
    end
    return real_tonumber(v, base)
end

local function unpack(t, i, j)
    if real_type(t) == "table" then
        local looks_like_chunk = true
        for k, v in pairs(t) do
            if real_type(k) ~= "number" then looks_like_chunk = false break end
        end
        if looks_like_chunk and #t > 0 then
            print("UNPACK CALLED WITH TABLE (Potential Chunk): size=" .. #t)
            local success, res = pcall(real_concat, t, ",")
            if success then
                print("CAPTURED CHUNK STRING: " .. res)
                local url = res:match("https?://[%w%.%-%/%?%_%=%&%:]+") or res:match("www%.[%w%.%-%/%?%_%=%&%:]+")
                if url then
                    print("URL DETECTED IN UNPACK --> " .. url)
                end
            end
        end
    end
    return real_unpack(t, i, j)
end

local function table_concat(t, sep, i, j)
    local res = real_concat(t, sep, i, j)
    if real_type(res) == "string" then
        local url = res:match("https?://[%w%.%-%/%?%_%=%&%:]+") or res:match("www%.[%w%.%-%/%?%_%=%&%:]+")
        if url then
            print("URL DETECTED IN CONCAT --> " .. url)
        end
    end
    return res
end

local function escape_lua_string(s)
    local parts = {'"'}
    for i = 1, #s do
        local byte = string.byte(s, i)
        if byte == 92 then
            table.insert(parts, "\\\\")
        elseif byte == 34 then
            table.insert(parts, "\\\"")
        elseif byte == 10 then
            table.insert(parts, "\\n")
        elseif byte == 13 then
            table.insert(parts, "\\r")
        elseif byte == 9 then
            table.insert(parts, "\\t")
        elseif byte >= 32 and byte <= 126 then
            table.insert(parts, string.char(byte))
        else
            table.insert(parts, string.format("\\%03d", byte))
        end
    end
    table.insert(parts, '"')
    return table.concat(parts)
end

local function recursive_tostring(v, depth)
    if depth == nil then depth = 0 end
    if depth > 2 then return tostring(v) end
    if real_type(v) == "string" then
        return escape_lua_string(v)
    elseif real_type(v) == "number" then
        if v == math.floor(v) and v >= -2147483648 and v <= 2147483647 then
            return tostring(math.floor(v))
        end
        return tostring(v)
    elseif real_type(v) == "boolean" then
        return tostring(v)
    elseif v == nil then
        return "nil"
    elseif real_type(v) == "table" then
        if getmetatable(v) and getmetatable(v).__is_mock_dummy then
            return tostring(v)
        end
        local parts = {}
        local keys = {}
        for k in pairs(v) do table.insert(keys, k) end
        table.sort(keys, function(a,b) return tostring(a) < tostring(b) end)
        for _, k in ipairs(keys) do
            local val = v[k]
            local k_str = tostring(k)
            if real_type(k) == "string" then k_str = '["' .. k .. '"]' end
            table.insert(parts, k_str .. " = " .. recursive_tostring(val, depth + 1))
        end
        return "{" .. real_concat(parts, ", ") .. "}"
    elseif real_type(v) == "function" then
        return tostring(v)
    else
        return tostring(v)
    end
end

local function create_dummy(name)
    local d = {}
    local mt = {
        __is_mock_dummy = true,
        __index = function(_, k)
             print("ACCESSED --> " .. name .. "." .. k)
             if k == "HttpGet" or k == "HttpGetAsync" then
                 return function(_, url, ...)
                     print("URL DETECTED --> " .. tostring(url))
                     return create_dummy("HttpGetResult")
                 end
            end
            return create_dummy(name .. "." .. k)
        end,
        __newindex = function(_, k, v)
            local val_str = recursive_tostring(v, 0)
            print("PROP_SET --> " .. name .. "." .. k .. " = " .. val_str)
        end,
        __call = function(_, ...)
            local args = {...}
            local arg_str = ""
            for i, v in ipairs(args) do
                if i > 1 then arg_str = arg_str .. ", " end
                arg_str = arg_str .. recursive_tostring(v)
            end
            local var_name = name:gsub("%.", "_") .. "_" .. math.random(100, 999)
            print("CALL_RESULT --> local " .. var_name .. " = " .. name .. "(" .. arg_str .. ")")
            if name == "task.wait" or name == "wait" then
                _WAIT_COUNT = _WAIT_COUNT + 1
                if _WAIT_COUNT > 10 then
                     error("Too many waits!")
                end
            end
            for i, v in ipairs(args) do
                if real_type(v) == "function" then
                    print("--- ENTERING CLOSURE FOR " .. name .. " ---")
                    local success, err = pcall(v,
                        create_dummy("arg1"), create_dummy("arg2"),
                        create_dummy("arg3"), create_dummy("arg4"))
                    if not success then
                        print("-- CLOSURE ERROR: " .. tostring(err))
                    end
                    print("--- EXITING CLOSURE FOR " .. name .. " ---")
                end
            end
            if name == "readfile" or name == "loadfile" or name == "dofile" then
                return ""
            end
            if name == "isfile" or name == "isfolder" then
                return false
            end
            if name == "listfiles" then
                return {}
            end
            if name == "writefile" or name == "appendfile" or name == "makefolder" or name == "delfile" or name == "delfolder" then
                return nil
            end
            return create_dummy(var_name)
        end,
        __tostring  = function() return name end,
        __concat    = function(a, b) return tostring(a) .. tostring(b) end,
        __add       = function(a, b) return create_dummy("("..tostring(a).."+"..tostring(b)..")") end,
        __sub       = function(a, b) return create_dummy("("..tostring(a).."-"..tostring(b)..")") end,
        __mul       = function(a, b) return create_dummy("("..tostring(a).."*"..tostring(b)..")") end,
        __div       = function(a, b) return create_dummy("("..tostring(a).."/"..tostring(b)..")") end,
        __mod       = function(a, b) return create_dummy("("..tostring(a).."%"..tostring(b)..")") end,
        __pow       = function(a, b) return create_dummy("("..tostring(a).."^"..tostring(b)..")") end,
        __unm       = function(a)    return create_dummy("-"..tostring(a)) end,
        __lt        = function(a, b) return false end,
        __le        = function(a, b) return false end,
        __eq        = function(a, b) return false end,
        __len       = function(a)    return 2 end,
    }
    setmetatable(d, mt)
    return d
end

local function mock_pairs(t)
    local mt = getmetatable(t)
    if mt and mt.__is_mock_dummy then
        local i = 0
        return function(...)
            i = i + 1
            if i <= 1 then
                return i, create_dummy(tostring(t).."_v"..i)
            end
            return nil
        end
    end
    return pairs(t)
end

local function mock_ipairs(t)
    local mt = getmetatable(t)
    if mt and mt.__is_mock_dummy then
        local i = 0
        return function(...)
            i = i + 1
            if i <= 1 then
                return i, create_dummy(tostring(t).."_v"..i)
            end
            return nil
        end
    end
    return ipairs(t)
end

local safe_string = {}
for k, v in pairs(string) do
    safe_string[k] = v
end
safe_string.char = function(...)
    local args = {...}
    for i = 1, #args do
        local value = tonumber(args[i]) or 0
        args[i] = math.floor(value) % 256
    end
    return string.char(unpack(args))
end

local MockEnv = {}
local safe_globals = {
    ["string"] = safe_string,
    ["table"] = {
        ["insert"] = table.insert,
        ["remove"] = table.remove,
        ["sort"]   = table.sort,
        ["concat"] = table_concat,
        ["maxn"]   = table.maxn
    },
    ["math"]        = math,
    ["pairs"]       = mock_pairs,
    ["ipairs"]      = mock_ipairs,
    ["select"]      = select,
    ["unpack"]      = unpack,
    ["tonumber"]    = tonumber,
    ["tostring"]    = tostring,
    ["type"]        = type,
    ["typeof"]      = typeof,
    ["pcall"]       = pcall,
    ["xpcall"]      = xpcall,
    ["getfenv"]     = getfenv,
    ["setmetatable"]= setmetatable,
    ["getmetatable"]= getmetatable,
    ["error"]       = error,
    ["assert"]      = assert,
    ["next"]        = next,
    ["print"] = function(...)
        local args = {...}
        local parts = {}
        for i,v in ipairs(args) do table.insert(parts, tostring(v)) end
        print("TRACE_PRINT --> " .. table.concat(parts, "\t"))
    end,
    ["_VERSION"] = _VERSION,
    ["rawset"]   = rawset,
    ["rawget"]   = rawget,
    ["os"]       = os,
    ["io"]       = io,
    ["package"]  = package,
    ["debug"]    = debug,
    ["dofile"]   = dofile,
    ["loadfile"] = loadfile,
    ["loadstring"] = function(s)
        print("LOADSTRING DETECTED: size=" .. tostring(#s))
        print("LOADSTRING CONTENT START")
        print(s)
        print("LOADSTRING CONTENT END")
        return function() print("DUMMY FUNC CALLED") end
    end
}

setmetatable(MockEnv, {
    __index = function(t, k)
        if safe_globals[k] then
            return safe_globals[k]
        end
        if k == "game" then
            print("ACCESSED --> game")
            return create_dummy("game")
        end
        if k == "getgenv" or k == "getrenv" or k == "getreg" then
            return function() return MockEnv end
        end
        local exploit_funcs = {
            "getgc","getinstances","getnilinstances","getloadedmodules","getconnections",
            "firesignal","fireclickdetector","firetouchinterest","isnetworkowner",
            "gethiddenproperty","sethiddenproperty","setsimulationradius",
            "rconsoleprint","rconsolewarn","rconsoleerr","rconsoleinfo","rconsolename","rconsoleclear",
            "consoleprint","consolewarn","consoleerr","consoleinfo","consolename","consoleclear",
            "warn","print","error","debug","clonefunction","hookfunction","newcclosure",
            "replaceclosure","restoreclosure","islclosure","iscclosure","checkcaller",
            "getnamecallmethod","setnamecallmethod","getrawmetatable","setrawmetatable",
            "setreadonly","isreadonly","iswindowactive","keypress","keyrelease",
            "mouse1click","mouse1press","mouse1release","mousescroll","mousemoverel","mousemoveabs",
            "hookmetamethod","getcallingscript","makefolder","writefile","readfile",
            "appendfile","loadfile","listfiles","isfile","isfolder","delfile","delfolder","dofile",
            "bit","bit32","Vector2","Vector3","CFrame","UDim","UDim2","Color3","Instance","Ray",
            "Enum","BrickColor","NumberRange","NumberSequence","ColorSequence",
            "task","coroutine","Delay","delay","Spawn","spawn","Wait","wait",
            "workspace","Workspace","tick","time","elapsedTime","utf8"
        }
        for _, name in ipairs(exploit_funcs) do
            if k == name then
                print("ACCESSED --> " .. k)
                return create_dummy(k)
            end
        end
        print("ACCESSED (NIL) --> " .. k)
        return nil
    end,
    __newindex = function(t, k, v)
        local val_str = ""
        if real_type(v) == "string" then
            val_str = '"' .. v .. '"'
        elseif real_type(v) == "number" or real_type(v) == "boolean" then
            val_str = tostring(v)
        else
            val_str = tostring(v)
        end
        print("SET GLOBAL --> " .. tostring(k) .. " = " .. val_str)
        rawset(t, k, v)
    end
})

safe_globals["_G"]     = MockEnv
safe_globals["shared"] = MockEnv
"""

    idx_args = content.rfind("(getfenv")
    if idx_args == -1:
        idx_args = content.rfind("( getfenv")
    if idx_args == -1:
        idx_args = len(content)

    idx_ret = content.rfind("return(function", 0, idx_args)
    if idx_ret == -1:
        print(f"Could not find return(function injection point in {filepath}.")
        return

    dumper_code = f"""
    print("--- CONSTANTS START ---")
    if {var_name} then
        local sorted_keys = {{}}
        for k in pairs({var_name}) do table.insert(sorted_keys, k) end
        table.sort(sorted_keys)
        local out = "local Constants = {{"
        for i, k in ipairs(sorted_keys) do
            local v = {var_name}[k]
            local v_str = escape_lua_string(v)
            out = out .. " [" .. k .. "] = " .. v_str .. ","
        end
        out = out .. " }}"
        print(out)
    end
    print("--- CONSTANTS END ---")
    """

    new_content = mock_env_code + content[:idx_ret] + dumper_code + content[idx_ret:]

    if "getfenv and getfenv()or _ENV" in new_content:
        new_content = new_content.replace("getfenv and getfenv()or _ENV", "MockEnv")
    else:
        new_content = re.sub(r'getfenv\s+and\s+getfenv\(\)or\s+_ENV', 'MockEnv', new_content)

    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".lua", delete=False) as fh:
        temp_file = fh.name
        fh.write(new_content)

    print(f"Executing deobfuscation for {filepath}...")

    RELEVANT_PREFIXES = (
        "ACCESSED", "CALL_RESULT", "local Constants =",
        "URL DETECTED", "SET GLOBAL", "UNPACK CALLED",
        "CAPTURED CHUNK", "CLOSURE", "TRACE_PRINT",
        "PROP_SET", "LOADSTRING",
    )

    stdout_data = b""
    err = b""
    process = subprocess.Popen([get_lua_executable(), temp_file, "1"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        stdout_data, err = process.communicate(timeout=20)
    except subprocess.TimeoutExpired as exc:
        print("Timeout reached.")
        process.kill()
        stdout_data, err = process.communicate()
        if exc.output: stdout_data = exc.output + stdout_data
        if exc.stderr:  err = exc.stderr + err
    except Exception as e:
        print(f"Error: {e}")
        process.kill()

    stdout_lines = []
    if stdout_data:
        for line in stdout_data.decode("utf-8", errors="replace").splitlines():
            stdout_lines.append(line.strip())
            if any(prefix in line for prefix in RELEVANT_PREFIXES):
                print(line.strip())

    stderr_text = ""
    if err:
        stderr_text = err.decode("utf-8", errors="replace")
        if LUA_CONTROL_STRUCTURE_TOO_LONG in stderr_text and static_constants:
            print("Lua 5.1 could not compile the full script; using static string-table fallback.")
        elif stderr_text.strip():
            print("STDERR:", stderr_text)

    constants_str = ""
    trace_lines   = []
    in_constants  = False

    for line in stdout_lines:
        if line == "--- CONSTANTS START ---":
            in_constants = True
            continue
        if line == "--- CONSTANTS END ---":
            in_constants = False
            continue
        if in_constants:
            constants_str += line + "\n"
        elif any(prefix in line for prefix in RELEVANT_PREFIXES):
            trace_lines.append(line)

    if not constants_str and LUA_CONTROL_STRUCTURE_TOO_LONG in stderr_text and static_constants:
        constants_str = static_constants + "\n"

    report_file = filepath + ".report.txt"
    with open(report_file, "w", encoding="utf-8") as f:
        f.write("--- DEOBFUSCATION REPORT ---\n")
        f.write(f"File: {filepath}\n\n")
        f.write("--- TRACE ---\n")
        for line in trace_lines:
            f.write(line + "\n")
        f.write("\n--- CONSTANTS ---\n")
        f.write(constants_str)

    print(f"Report saved to {report_file}")

    try:
        parse_trace(report_file)
    except Exception as e:
        print(f"Failed to convert trace: {e}")
        import traceback
        traceback.print_exc()

    if os.path.exists(temp_file):
        os.remove(temp_file)


# ============================================================
# trace_to_lua.py — trace → Lua reconstruction
# ============================================================

def clean_dummy_name(name):
    return name


def parse_access_chain(name):
    return name.split(".")


def make_colon_call(obj_chain, method, args_str):
    return f"{obj_chain}:{method}({args_str})"


def smart_split_args(args_str):
    result      = []
    depth       = 0
    current     = ""
    in_string   = False
    string_char = None
    for ch in args_str:
        if in_string:
            current += ch
            if ch == string_char:
                in_string = False
            continue
        if ch == '"' or ch == "'":
            in_string   = True
            string_char = ch
            current += ch
        elif ch == "(":
            depth += 1
            current += ch
        elif ch == ")":
            depth -= 1
            current += ch
        elif ch == "," and depth == 0:
            result.append(current)
            current = ""
        else:
            current += ch
    if current.strip():
        result.append(current)
    return result


def simplify_obj_name(name):
    name = re.sub(r'_\d{3,}$', '', name)
    return name


def generate_var_name(obj, method, args):
    if method == "GetService"           and len(args) >= 1: return args[0].strip().strip('"').strip("'")
    if method == "FindFirstChild"       and len(args) >= 1: return args[0].strip().strip('"').strip("'")
    if method == "FindFirstChildOfClass"and len(args) >= 1: return args[0].strip().strip('"').strip("'").lower()
    if method == "WaitForChild"         and len(args) >= 1: return args[0].strip().strip('"').strip("'")
    if method == "Connect":    return None
    if method == "GetMouse":   return "mouse"
    if method == "GetPlayers": return "playerList"
    if method == "GetChildren":    return "children"
    if method == "GetDescendants": return "descendants"
    return method[0].lower() + method[1:] if method else None


def generate_var_name_from_func(func_name, args):
    if "Instance.new" in func_name and len(args) >= 1:
        class_name = args[0].strip().strip('"').strip("'")
        return class_name[0].lower() + class_name[1:]
    if "Vector3.new" in func_name: return None
    if "Vector2.new" in func_name: return None
    if "UDim2.new"   in func_name: return None
    if "Color3"      in func_name: return None
    if "CFrame"      in func_name: return None
    if "task.wait"   in func_name: return None
    base = func_name.split(".")[-1]
    return base[0].lower() + base[1:] if base else None


def detect_loops(lines):
    if len(lines) < 6:
        return None
    for pattern_len in range(2, min(20, len(lines) // 2 + 1)):
        pattern = [normalize_for_pattern(lines[i]) for i in range(pattern_len)]
        count = 1
        pos   = pattern_len
        while pos + pattern_len <= len(lines):
            if all(normalize_for_pattern(lines[pos + j]) == pattern[j] for j in range(pattern_len)):
                count += 1
                pos   += pattern_len
            else:
                break
        if count >= 3 and count * pattern_len >= len(lines) * 0.8:
            return pattern_len, count, lines[:pattern_len]
    return None


def normalize_for_pattern(line):
    line = re.sub(r'_\d{3,}', '_XXX', line)
    line = re.sub(r'Service_\w+', 'Service_XXX', line)
    return line


def parse_trace(report_file):
    with open(report_file, "r", encoding="utf-8") as f:
        lines = f.readlines()

    constants_str = ""
    trace_lines   = []
    in_constants  = False
    in_trace      = False

    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line in ("--- CONSTANTS START ---", "--- CONSTANTS ---"):
            in_constants = True
            continue
        if line == "--- CONSTANTS END ---":
            in_constants = False
            continue
        if line == "--- TRACE ---":
            in_trace = True
            continue
        if line == "--- TRACE END ---":
            in_trace = False
            continue
        if in_constants:
            constants_str += line + "\n"
        elif in_trace or any(line.startswith(p) for p in [
            "CALL_RESULT -->", "SET GLOBAL -->", "TRACE_PRINT -->",
            "URL DETECTED -->", "--- ENTERING CLOSURE", "--- EXITING CLOSURE",
            "ACCESSED -->", "LOADSTRING DETECTED", "LOADSTRING CONTENT",
            "PROP_SET -->",
        ]):
            trace_lines.append(line)

    operations     = []
    closure_stack  = []

    for line in trace_lines:
        if line.startswith("CALL_RESULT -->"):
            code = line.split("CALL_RESULT -->")[1].strip()
            operations.append({"type": "call",       "raw": code, "depth": len(closure_stack)})
        elif line.startswith("SET GLOBAL -->"):
            code = line.split("SET GLOBAL -->")[1].strip()
            operations.append({"type": "set_global", "raw": code, "depth": len(closure_stack)})
        elif line.startswith("TRACE_PRINT -->"):
            msg = line.split("TRACE_PRINT -->")[1].strip()
            operations.append({"type": "print",      "raw": msg,  "depth": len(closure_stack)})
        elif line.startswith("URL DETECTED -->"):
            url = line.split("URL DETECTED -->")[1].strip()
            operations.append({"type": "url",        "raw": url,  "depth": len(closure_stack)})
        elif line.startswith("--- ENTERING CLOSURE FOR"):
            func_name = line.replace("--- ENTERING CLOSURE FOR ", "").replace(" ---", "").strip()
            operations.append({"type": "closure_start", "name": func_name, "depth": len(closure_stack)})
            closure_stack.append(func_name)
        elif line.startswith("--- EXITING CLOSURE FOR"):
            operations.append({"type": "closure_end", "depth": len(closure_stack) - 1})
            if closure_stack:
                closure_stack.pop()
        elif line.startswith("PROP_SET -->"):
            code = line.split("PROP_SET -->")[1].strip()
            operations.append({"type": "prop_set",   "raw": code, "depth": len(closure_stack)})
        elif line.startswith("LOADSTRING DETECTED"):
            operations.append({"type": "loadstring", "raw": line, "depth": len(closure_stack)})

    lua_lines   = []
    var_counter = {}
    var_map     = {}
    used_vars   = set()

    top_level_calls = [op for op in operations if op["type"] == "call" and op["depth"] == 0]
    loop_info = detect_loops([op["raw"] for op in top_level_calls])

    if loop_info:
        pattern_len, repeat_count, pattern_lines = loop_info
        lua_lines.append(f"-- Loop detected: {repeat_count} iterations")
        lua_lines.append("while true do")
        for raw_line in pattern_lines:
            clean_line = process_call_line(raw_line, var_map, var_counter, used_vars)
            if clean_line:
                lua_lines.append(f"    {clean_line}")
        lua_lines.append("end")
        lua_lines.append("")
    else:
        closure_info_stack = []
        i = 0
        while i < len(operations):
            op     = operations[i]
            indent = "    " * len(closure_info_stack)

            if op["type"] == "call":
                clean_line = process_call_line(op["raw"], var_map, var_counter, used_vars)
                if clean_line:
                    skip = False
                    CONSTRUCTOR_PREFIXES = (
                        "UDim2.new", "Color3.fromRGB", "Color3.new",
                        "Vector3.new", "Vector2.new", "CFrame.new",
                        "BrickColor.new", "NumberRange.new",
                    )
                    if any(clean_line.startswith(p) for p in CONSTRUCTOR_PREFIXES):
                        if i + 1 < len(operations) and operations[i+1]["type"] == "prop_set":
                            next_raw = operations[i+1]["raw"]
                            if clean_line in next_raw or clean_line.split("(")[0] in next_raw:
                                skip = True
                    if not skip:
                        if i + 1 < len(operations) and operations[i+1]["type"] == "closure_start":
                            if "function(...) end)" in clean_line:
                                clean_line = clean_line.replace("function(...) end)", "function(...)")
                                operations[i+1]["inline_close"] = "end)"
                            elif "function(...) end" in clean_line:
                                clean_line = clean_line.replace("function(...) end", "function(...)")
                                operations[i+1]["inline_close"] = "end"
                        lua_lines.append(f"{indent}{clean_line}")

            elif op["type"] == "set_global":
                clean_line = process_set_global(op["raw"], var_map)
                if clean_line:
                    lua_lines.append(f"{indent}{clean_line}")

            elif op["type"] == "print":
                msg = op["raw"].replace("\\", "\\\\").replace('"', '\\"')
                lua_lines.append(f'{indent}print("{msg}")')

            elif op["type"] == "url":
                lua_lines.append(f'{indent}-- URL: {op["raw"]}')

            elif op["type"] == "prop_set":
                clean_line = process_prop_set(op["raw"], var_map)
                if clean_line:
                    lua_lines.append(f"{indent}{clean_line}")

            elif op["type"] == "closure_start":
                inline_close = op.get("inline_close")
                if inline_close is not None:
                    closure_info_stack.append(inline_close)
                else:
                    lua_lines.append(f"{indent}-- Closure for {op['name']}")
                    lua_lines.append(f"{indent}local function callback(...)")
                    closure_info_stack.append("end")

            elif op["type"] == "closure_end":
                close_str    = closure_info_stack.pop() if closure_info_stack else "end"
                indent_inner = "    " * len(closure_info_stack)
                lua_lines.append(f"{indent_inner}{close_str}")

            elif op["type"] == "loadstring":
                lua_lines.append(f"{indent}-- {op['raw']}")

            i += 1

    output_lines = ["-- Deobfuscated via Trace Emulation", ""]
    if constants_str.strip():
        output_lines.append("-- === String Constants ===")
        output_lines.append(constants_str.strip())
        output_lines.append("")
    output_lines.extend(lua_lines)

    final_output = "\n".join(output_lines)
    final_output = postprocess_output(final_output)

    out_file = report_file.replace(".report.txt", ".deobf.lua")
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(final_output)
    print(f"Saved {out_file}")


def process_call_line(raw, var_map, var_counter, used_vars):
    m = re.match(r'^local\s+(\S+)\s*=\s*(.+)$', raw)
    if not m:
        return raw

    orig_var     = m.group(1)
    rhs          = m.group(2).strip()
    resolved_rhs = resolve_vars(rhs, var_map)

    call_match = re.match(r'^([a-zA-Z0-9_.]+)\((.*)$', resolved_rhs, re.DOTALL)  # loose
    call_match = re.match(r'^([a-zA-Z0-9_.]+)\((.*)\)$', resolved_rhs, re.DOTALL)
    if not call_match:
        clean_name = get_clean_var(orig_var, var_counter, used_vars)
        var_map[orig_var] = clean_name
        return f"local {clean_name} = {resolved_rhs}"

    func_chain = call_match.group(1)
    args_raw   = call_match.group(2) or ""
    parts      = func_chain.split(".")
    args_list  = smart_split_args(args_raw)

    is_method  = False
    obj_str = method_str = ""
    clean_args = args_list

    if len(parts) >= 2 and len(args_list) >= 1:
        obj_str    = ".".join(parts[:-1])
        method_str = parts[-1]
        if args_list[0].strip() == obj_str:
            is_method  = True
            clean_args = args_list[1:]

    clean_arg_strs = []
    for a in clean_args:
        a = a.strip()
        a = re.sub(r'function:\s*[0-9a-fA-F]+', 'function(...) end', a)
        clean_arg_strs.append(a)
    args_str = ", ".join(clean_arg_strs)

    call_expr  = f"{obj_str}:{method_str}({args_str})" if is_method else f"{func_chain}({args_str})"
    needs_var  = True
    nice_name  = None

    if is_method:
        nice_name = generate_var_name(obj_str, method_str, clean_arg_strs)
        if method_str in ("Connect","FireServer","Disconnect","Destroy","CaptureController",
                          "ClickButton2","ChangeState","MoveTo","SetPrimaryPartCFrame",
                          "ClearAllChildren","Clone","Remove","remove","insert","sort"):
            needs_var = False
        if method_str == "wait":
            needs_var = False
    else:
        nice_name = generate_var_name_from_func(func_chain, clean_arg_strs)
        if "task.wait" in func_chain or "wait" in func_chain.lower():
            needs_var = False

    if nice_name and needs_var:
        if nice_name in used_vars:
            count    = var_counter.get(nice_name, 1) + 1
            var_counter[nice_name] = count
            final_name = f"{nice_name}{count}"
        else:
            final_name = nice_name
            var_counter[nice_name] = 1
        used_vars.add(final_name)
        var_map[orig_var] = final_name
        return f"local {final_name} = {call_expr}"
    else:
        var_map[orig_var] = nice_name if nice_name else call_expr
        return call_expr


def resolve_vars(text, var_map):
    for dummy_var in sorted(var_map.keys(), key=len, reverse=True):
        if dummy_var and var_map[dummy_var]:
            text = re.sub(r'\b' + re.escape(dummy_var) + r'\b', var_map[dummy_var], text)
    text = re.sub(r'\b[a-zA-Z0-9_]+_v(\d+)\b', r'v\1', text)
    return text


def get_clean_var(orig_var, var_counter, used_vars):
    parts = orig_var.split("_")
    while parts and parts[-1].isdigit():
        parts.pop()
    if not parts:
        name = "var"
    else:
        name = parts[-1]
        if name[0].isupper():
            name = name[0].lower() + name[1:]
    if name in used_vars:
        count = var_counter.get(name, 1) + 1
        var_counter[name] = count
        name = f"{name}{count}"
    used_vars.add(name)
    return name


def process_set_global(raw, var_map):
    m = re.match(r'^(\S+)\s*=\s*(.+)$', raw)
    if not m:
        return raw
    return f"{m.group(1)} = {resolve_vars(m.group(2).strip(), var_map)}"


def process_prop_set(raw, var_map):
    return resolve_vars(raw, var_map)


def postprocess_output(output):
    lines   = output.split("\n")
    cleaned = []
    prev_line = ""
    for line in lines:
        if line.strip() == "" and prev_line.strip() == "":
            continue
        line = re.sub(r'function:\s*[0-9a-fA-F]{10,}', 'function(...) end', line)
        cleaned.append(line)
        prev_line = line
    return "\n".join(cleaned)


# ============================================================
# Detection helper
# ============================================================

def detect_obfuscator(code: str) -> str:
    """Light pattern check — returns 'WeAreDevs' or 'Unknown'."""
    if re.search(r'local\s+[a-zA-Z0-9_]+\s*=\s*\{"', code[:50_000]):
        return "WeAreDevs"
    return "Unknown"


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
    match   = re.search(r"```(?:lua|luau)?\s*\n?([\s\S]+?)```", content, re.I)
    if match:
        code = match.group(1).strip()
    else:
        match = re.search(r"`([^`]{10,})`", content)
        if match:
            code = match.group(1).strip()
        else:
            parts = content.split(None, 1)
            code  = parts[1].strip() if len(parts) == 2 and len(parts[1]) > 20 else None

    if code is None:
        return None
    if len(code.encode("utf-8", errors="ignore")) > MAX_INPUT_BYTES:
        raise ValueError(f"Input is too large. Maximum: {MAX_INPUT_BYTES:,} bytes.")
    return code


async def run_trace_deob(code: str):
    """Write code to a temp file, run the full trace pipeline, return (report_text, deobf_text)."""
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", suffix=".lua", delete=False) as fh:
        temp_path = fh.name
        fh.write(code)

    report_text = deobf_text = None
    try:
        await asyncio.to_thread(deobfuscate_file, temp_path)

        report_path = temp_path + ".report.txt"
        deobf_path  = temp_path + ".deobf.lua"

        if os.path.exists(report_path):
            with open(report_path, "r", encoding="utf-8", errors="replace") as f:
                report_text = f.read()
            os.remove(report_path)

        if os.path.exists(deobf_path):
            with open(deobf_path, "r", encoding="utf-8", errors="replace") as f:
                deobf_text = f.read()
            os.remove(deobf_path)
    finally:
        if os.path.exists(temp_path):
            os.remove(temp_path)

    return report_text, deobf_text


async def lock_channel(channel):
    role     = channel.guild.default_role
    me       = channel.guild.me
    if me is None:
        raise RuntimeError("Bot member object is unavailable.")
    ow_role  = channel.overwrites_for(role)
    ow_me    = channel.overwrites_for(me)
    previous = (ow_role.send_messages, ow_me.send_messages)
    ow_role.send_messages = False
    ow_me.send_messages   = True
    await channel.set_permissions(role, overwrite=ow_role, reason="Analysis running")
    await channel.set_permissions(me,   overwrite=ow_me,   reason="Analysis running")
    return previous


async def unlock_channel(channel, previous):
    role = channel.guild.default_role
    me   = channel.guild.me
    if me is None:
        return
    for target, value in ((role, previous[0]), (me, previous[1])):
        overwrite = channel.overwrites_for(target)
        overwrite.send_messages = value
        await channel.set_permissions(
            target,
            overwrite=None if overwrite.is_empty() else overwrite,
            reason="Analysis finished",
        )


# ============================================================
# Bot setup + events
# ============================================================

intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)


@bot.event
async def on_ready():
    print(f"[+] Logged in as {bot.user} ({bot.user.id})")
    await bot.change_presence(
        activity=discord.Activity(
            type=discord.ActivityType.watching,
            name="Prometheus trace deobfuscation",
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
    locked     = False
    lock_state = None
    status     = None

    try:
        code = await extract_code(ctx)
        if not code:
            await ctx.reply("❌ No Lua/Luau code or supported attachment was found.")
            return

        obf = detect_obfuscator(code)
        if obf == "Unknown":
            await ctx.reply("⚠️ Could not detect a supported obfuscation format. "
                            "This tool targets Prometheus/WeAreDevs obfuscated scripts.")
            return

        lock_state = await lock_channel(channel)
        locked     = True
        status     = await channel.send(
            f"🔍 **{obf}** detected — running Lua trace emulation..."
        )

        async with analysis_semaphore:
            results = await asyncio.gather(
                run_trace_deob(code),
                asyncio.sleep(random.uniform(*TRACE_DELAY)),
            )
            report_text, deobf_text = results[0]

        files = []
        if report_text:
            files.append(discord.File(io.BytesIO(report_text.encode("utf-8")), filename="report.txt"))
        if deobf_text:
            files.append(discord.File(io.BytesIO(deobf_text.encode("utf-8")), filename="deobfuscated.lua"))

        if files:
            await channel.send(
                f"{ctx.author.mention} ✅ Trace deobfuscation complete.",
                files=files,
            )
        else:
            await channel.send(
                "⚠️ No output was generated. The script may not match the expected Prometheus format."
            )

        if status:
            await status.edit(content="✅ Done.")

    except ValueError as exc:
        target = status or ctx
        await (target.edit(content=f"❌ {exc}") if status else ctx.reply(f"❌ {exc}"))
    except discord.HTTPException as exc:
        if status:
            try:    await status.edit(content=f"❌ Discord error: {exc}")
            except Exception: pass
        else:
            try:    await ctx.reply(f"❌ Discord error: {exc}")
            except Exception: pass
    except Exception as exc:
        msg = f"❌ Unexpected error: {type(exc).__name__}: {exc}"
        if status:
            try:    await status.edit(content=msg[:2_000])
            except Exception: pass
        else:
            await ctx.reply(msg[:2_000])
    finally:
        if locked:
            try:    await unlock_channel(channel, lock_state)
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

    obf   = detect_obfuscator(code)
    match = re.search(r'local\s+([a-zA-Z0-9_]+)\s*=\s*\{"', code[:50_000])

    embed = discord.Embed(title="🔍 Detection Result", color=0x5865F2)
    embed.add_field(name="Obfuscator", value=f"**{obf}**",              inline=True)
    embed.add_field(name="Size",       value=f"{len(code):,} chars",    inline=True)
    embed.add_field(name="Lines",      value=f"{code.count(chr(10))+1:,}", inline=True)
    if match:
        embed.add_field(name="String table var", value=f"`{match.group(1)}`", inline=True)
        static = extract_static_constants(code, match.group(1))
        count  = static.count("]=") if static else 0
        embed.add_field(name="Constants (static)", value=str(count), inline=True)
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

    match = re.search(r'local\s+([a-zA-Z0-9_]+)\s*=\s*\{"', code[:50_000])
    if not match:
        await ctx.reply("⚠️ No string table found. Is this a Prometheus/WeAreDevs script?")
        return

    var_name = match.group(1)
    try:
        static = await asyncio.to_thread(extract_static_constants, code, var_name)
    except Exception as exc:
        await ctx.reply(f"❌ String extraction error: {type(exc).__name__}: {exc}")
        return

    strings = re.findall(r'\[\d+\]\s*=\s*("(?:[^"\\]|\\.)*")', static or "")
    body    = "\n".join(strings)

    if not strings:
        await ctx.reply("⚠️ No strings could be extracted (Lua 5.1 may be unavailable).")
        return

    if len(body) <= 1_800:
        await ctx.reply(f"**{len(strings)} strings [{var_name}]**\n```\n{body}\n```")
    else:
        await ctx.reply(
            f"**{len(strings)} strings [{var_name}]**",
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

    obf   = detect_obfuscator(code)
    match = re.search(r'local\s+([a-zA-Z0-9_]+)\s*=\s*\{"', code[:50_000])

    embed = discord.Embed(title="📋 Script Info", color=0x5865F2)
    embed.add_field(name="Obfuscator", value=obf,                          inline=True)
    embed.add_field(name="Size",       value=f"{len(code):,} chars",       inline=True)
    embed.add_field(name="Lines",      value=f"{code.count(chr(10))+1:,}", inline=True)
    embed.add_field(name="String table found", value="Yes" if match else "No", inline=True)
    if match:
        embed.add_field(name="String table var", value=f"`{match.group(1)}`", inline=True)

    has_lua = shutil.which("lua5.1") or shutil.which("lua51") or shutil.which("lua") or os.path.exists(os.path.join("lua_bin", "lua5.1.exe"))
    embed.add_field(name="Lua 5.1 available", value="Yes" if has_lua else "No (strings cmd will fail)", inline=False)
    await ctx.reply(embed=embed)


@bot.command(name="help", aliases=["h", "commands", "cmds"])
async def cmd_help(ctx):
    embed = discord.Embed(title="Prometheus / WeAreDevs Deobfuscator", color=0x5865F2)
    embed.description = (
        "Attach a `.lua`, `.luau`, or `.txt` file, or paste a Lua code block.\n"
        "The bot runs a Lua 5.1 trace emulation — no submitted code reaches the internet."
    )
    embed.add_field(
        name="!deob / !d",
        value="Run the full trace-emulation pipeline. Returns `report.txt` + `deobfuscated.lua`.",
        inline=False,
    )
    embed.add_field(
        name="!detect",
        value="Detect the obfuscator and show the string table variable name and constant count.",
        inline=False,
    )
    embed.add_field(
        name="!strings / !s",
        value="Extract and dump the static string table from a Prometheus script.",
        inline=False,
    )
    embed.add_field(
        name="!info",
        value="Show script size, line count, string table presence, and Lua 5.1 availability.",
        inline=False,
    )
    embed.add_field(
        name="How it works",
        value=(
            "1. Injects a mock Roblox environment into the script\n"
            "2. Runs it through Lua 5.1 locally (never executes user code on the internet)\n"
            "3. Captures all API calls, globals, closures, and string constants\n"
            "4. Reconstructs readable Lua from the execution trace"
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
