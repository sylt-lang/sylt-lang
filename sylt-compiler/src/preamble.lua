-- Begin Sylt preamble
-- Built in types

-- THE nil-table
__NIL = setmetatable( { "nil" }, { __tostring = function() return "nil" end } )

__INDEX = function(o, i)
    local m = getmetatable(o)
    if m._type == "tuple" or m._type == "list" then
        local e = o[i + 1]
        assert(e ~= nil, "Tuple/list index out of range \"" .. i .. "\"")
        return e
    end
    if m._type == "blob" then
        assert(false, "Accessing fields \"" .. i .. "\" - which doesn't exist")
    end
    return __NIL
end

__ADD = function(a, b)
    if type(a) == "string" and type(b) == "string" then
        return a .. b
    end
    return a + b
end

__TUPLE_META = { _type = "tuple" }
__TUPLE_META.__newindex = function()
    assert(false, "Tuples are immutable")
end
__TUPLE_META.__add = function(a, b)
    local out = {}
    for x = 1, #a, 1 do
        out[x] = a[x] + b[x]
    end
    return __TUPLE(out)
end
__TUPLE_META.__sub = function(a, b)
    local out = {}
    for x = 1, #a, 1 do
        out[x] = a[x] - b[x]
    end
    return __TUPLE(out)
end
__TUPLE_META.__div = function(a, b)
    local out = {}
    for x = 1, #a, 1 do
        out[x] = a[x] / b[x]
    end
    return __TUPLE(out)
end
__TUPLE_META.__mul = function(a, b)
    local out = {}
    for x = 1, #a, 1 do
        out[x] = a[x] * b[x]
    end
    return __TUPLE(out)
end
__TUPLE_META.__unm = function(a)
    local out = {}
    for x = 1, #a, 1 do
        out[x] = -a[x]
    end
    return __TUPLE(out)
end
__TUPLE_META.__eq = function(a, b)
    for x = 1, #a, 1 do
        if not (a[x] == b[x]) then
            return false
        end
    end
    return true
end
__TUPLE_META.__lt = function(a, b)
    for x = 1, #a, 1 do
        if not (a[x] < b[x]) then
            return false
        end
    end
    return true
end
__TUPLE_META.__le = function(a, b)
    for x = 1, #a, 1 do
        if not (a[x] <= b[x]) then
            return false
        end
    end
    return true
end
__TUPLE_META.__tostring = function(a)
    local out = "("
    for x = 1, #a, 1 do
        if x ~= 1 then
            out = out .. ", "
        end
        out = out .. tostring(a[x])
    end
    out = out .. ")"
    return out
end
function __TUPLE(obj)
    return setmetatable(obj, __TUPLE_META)
end

__LIST_META = { _type = "list" }
__LIST_META.__eq = function(a, b)
    if not (#a == #b) then
        return false
    end
    for x = 1, #a, 1 do
        if not (a[x] == b[x]) then
            return false
        end
    end
    return true
end
__LIST_META.__lt = function(a, b)
    for x = 1, #a, 1 do
        if not (a[x] < b[x]) then
            return false
        end
    end
    return true
end
__LIST_META.__le = function(a, b)
    for x = 1, #a, 1 do
        if not (a[x] <= b[x]) then
            return false
        end
    end
    return true
end
__LIST_META.__tostring = function(a)
    local out = "["
    for x = 1, #a, 1 do
        if x ~= 1 then
            out = out .. ", "
        end
        out = out .. tostring(a[x])
    end
    out = out .. "]"
    return out
end
function __LIST(obj)
    return setmetatable(obj, __LIST_META)
end

__DICT_META = { _type = "dict" }
__DICT_META.__eq = function(a, b)
    for k, v in pairs(a) do
        if not (v == b[k]) then
            return false
        end
    end
    for k, v in pairs(b) do
        if not (v == a[k]) then
            return false
        end
    end
    return true
end
__DICT_META.__tostring = function(a)
    local out = "{"
    local first = true
    for k, v in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. tostring(k) .. ": " .. tostring(v)
    end
    out = out .. "}"
    return out
end
function __DICT(obj)
    return setmetatable(obj, __DICT_META)
end

__SET_META = { _type = "set" }
-- TODO(ed): add - sub - mul?
__SET_META.__eq = function(a, b)
    for k, _ in pairs(a) do
        if not b[k] then
            return false
        end
    end
    for k, _ in pairs(b) do
        if not a[k] then
            return false
        end
    end
    return true
end
__SET_META.__tostring = function(a)
    local out = "{"
    local first = true
    for k, _ in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. tostring(k)
    end
    out = out .. "}"
    return out
end
function __SET(obj)
    return setmetatable(obj, __SET_META)
end

__BLOB_META = { _type = "blob" }
__BLOB_META.__eq = function(a, b)
    -- TODO(ed): The actual blob-instance
    for k, _ in pairs(a) do
        if not b[k] then
            return false
        end
    end
    for k, _ in pairs(b) do
        if not a[k] then
            return false
        end
    end
    return true
end
__BLOB_META.__tostring = function(a)
    local out = "blob {"
    local first = true
    for k, v in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. tostring(k) .. " = " .. tostring(v)
    end
    out = out .. "}"
    return out
end
function __BLOB(obj)
    return setmetatable(obj, __BLOB_META)
end

-- std-sylt

function atan2(x, y) return math.atan2(y, x) end
function dbg(x) print(x); return x end
function random_choice(l) return l[math.random(1, #l)] end

function for_each(l, f)
    for _, v in pairs(l) do
        f(v)
    end
end

function map(l, f)
    local o = {}
    for k, v in pairs(l) do
        o[k] = f(v)
    end
    return __LIST(o)
end

function reduce(l, f)
    if #l == 0 then
        return NIL
    end
    local a = l[1]
    for k, v in pairs(l) do
        if k ~= 1 then
            a = f(a, v)
        end
    end
    return a
end

function fold(l, a, f)
    for k, v in pairs(l) do
        if k ~= 1 then
            a = f(v, a)
        end
    end
    return a
end

function filter(l, f)
    local o = {}
    for _, v in pairs(l) do
        if f(v) then
            table.insert(o, v)
        end
    end
    return __LIST(o)
end

push = table.insert

function prepend(l, v)
    table.insert(l, 1, v)
end

function add(s, v)
    s[v] = true
end

function len(c)
    return #c
end

sin = math.sin
cos = math.cos

function as_float(x) return x end
as_int = math.floor
floor = math.floor
as_char = string.byte
function as_chars(s)
    return __LIST(string.byte(s, 1, string.len(s)))
end

sqrt = math.sqrt
abs = math.abs
function sign(x)
    if x > 0 then
        return 1
    elseif x < 0 then
        return -1
    else
        return 0
    end
end
function clamp(x, lo, hi)
    return math.min(hi, math.max(x, lo))
end
min = math.min
max = math.max
function rem(x, y)
    return x % y
end
pow = math.pow
function angle(v)
    return atan2(v[1], v[2])
end

function dot(a, b)
    return a[1] * b[1] + a[2] * b[2]
end

function magnitude_squared(a)
    return dot(a, a)
end

function magnitude(a)
    return math.sqrt(dot(a, a))
end

function __crash(msg)
    return function() assert(false, "crash" .. (msg or "")) end
end

normalize = __crash("normalize is not implemented")
reflect = __crash("reflect is not implemented")
debug_assertions = __crash("debug_assertions is not implemented")
thread_sleep = __crash("thread_sleep is not implemented")

pop = __crash("pop is not implemented")
last = __crash("las is not implemented")

as_str = tostring
print = print
function spy(tag, x)
    print(tag, x)
    return x
end

function __contains(a, b)
    local ty = getmetatable(b)._type
    if ty == "list" then
        for _, v in pairs(b) do
            if v == a then
                return true
            end
        end
        return false
    end
    if ty == "dict" then
        return b[a] ~= nil
    end
    if ty == "set" then
        return b[a] ~= nil
    end
    assert(false, "Invalid contains!")
end

-- End Sylt preamble
