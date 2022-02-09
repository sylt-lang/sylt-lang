-- Begin Sylt preamble
-- Built in types

-- THE nil-table
__NIL = setmetatable( { "nil" }, { __tostring = function() return "nil" end } )

__IDENTITY = function(x) return x end

-- Table used to avoid infinite recursion when calling tostring on our custom
-- datatypes.
__SEEN = {}

__INDEX = function(o, i)
    if o == nil then return nil end
    local m = getmetatable(o)
    if m == nil then
        return o[i]
    end
    if m._type == "tuple" or m._type == "list" then
        local e = o[i + 1]
        assert(e ~= nil, "Tuple/list index out of range \"" .. i .. "\"")
        return e
    end
    local e = o[i]
    if m._type == "blob" then
        assert(e ~= nil, "Accessing fields \"" .. i .. "\" - which doesn't exist")
        return e
    end
    if e ~= nil then
        return e
    end
    return __NIL
end

__ASSIGN_INDEX = function(o, i, v)
    if o == nil then return nil end
    local m = getmetatable(o)
    if m == nil then
        o[i] = v
        return
    end
    if m._type == "tuple" then
        assert(nil, "Cannot assign to tuple!")
    end
    if m._type == "list" then
        local e = o[i + 1]
        assert(e ~= nil, "Tuple/list index out of range \"" .. i .. "\"")
        o[i + 1] = v
        return
    end
    if m._type == "blob" then
        local e = o[i]
        assert(e ~= nil, "Accessing fields \"" .. i .. "\" - which doesn't exist")
        o[i] = v
        return
    end
    o[i] = v
    return
end


__ADD = function(a, b)
    if type(a) == "string" and type(b) == "string" then
        return a .. b
    end
    return a + b
end

__VARIANT_META = { _type = "variant" }
__VARIANT_META.__newindex = function()
    assert(false, "Variants are immutable")
end
__VARIANT_META.__eq = function(a, b)
    return a[1] == b[1] and a[2] == b[2]
end
__VARIANT_META.__tostring = function(a)
    return tostring(a[1]) .. " " .. tostring(a[2])
end
function __VARIANT(obj)
    return setmetatable(obj, __VARIANT_META)
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
        if a[x] ~= b[x] then
            return a[x] < b[x]
        end
    end
    return false
end
__TUPLE_META.__le = function(a, b)
    for x = 1, #a, 1 do
        if a[x] ~= b[x] then
            return a[x] < b[x]
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
    if #a == 1 then
        out = out .. ","
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
    if __SEEN[a] then
        return "[...]"
    end
    __SEEN[a] = true
    local out = "["
    for x = 1, #a, 1 do
        if x ~= 1 then
            out = out .. ", "
        end
        out = out .. tostring(a[x])
    end
    out = out .. "]"
    __SEEN[a] = nil
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
    if #a == 0 then
        out = out .. ":"
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
    if __SEEN[a] then
        return "{...}"
    end
    __SEEN[a] = true
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
    __SEEN[a] = nil
    return out
end
function __SET(obj)
    return setmetatable(obj, __SET_META)
end

__BLOB_META = { _type = "blob" }
__BLOB_META.__eq = function(a, b)
    for k, v in pairs(a) do
        if v ~= b[k] then
            return false
        end
    end
    for k, _ in pairs(b) do
        if a[k] == nil then
            return false
        end
    end
    return true
end
__BLOB_META.__tostring = function(a)
    if __SEEN[a] then
        return "blob {...}"
    end
    __SEEN[a] = true
    local out = "blob {"
    local first = true
    for k, v in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. "." .. tostring(k) .. " = " .. tostring(v)
    end
    out = out .. "}"
    __SEEN[a] = nil
    return out
end
function __BLOB(obj)
    return setmetatable(obj, __BLOB_META)
end

-- std-sylt

function atan2(x, y) return math.atan2(y, x) end
function random_choice(l) return l[math.random(1, #l)] end

function varargs(f)
    return function(xs)
        return f(unpack(xs))
    end
end

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
        return __NIL
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
    for _, v in pairs(l) do
        a = f(v, a)
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

function remove(s, v)
    s[v] = nil
end

function len(c)
    local s = 0
    for _ in pairs(c) do
        s = s + 1
    end
    return s
end

function clear(c)
    for i, _ in pairs(c) do
        c[i] = nil
    end
end

sin = math.sin
cos = math.cos

function as_float(x) return x end
function as_int(x)
    local f, _ = math.modf(x)
    return f
end
floor = math.floor
as_char = string.byte
function as_chars(s)
    local chars = {}
    local len = string.len(s)
    for i = 1, len, 1 do
        table.insert(chars, string.byte(s, i))
    end
    return __LIST(chars)
end

function split(s)
    local t={}
    for str in string.gmatch(s, "([^%s]+)") do
        table.insert(t, str)
    end
    return __LIST(t)
end

sqrt = math.sqrt
function div(a, b)
    if b == 0 then return 0 end
    return math.floor(a / b)
end
function sign(x)
    if x > 0 then
        return 1
    elseif x < 0 then
        return -1
    else
        return 0
    end
end
function rem(x, y)
    return math.abs(x % y)
end
pow = math.pow

function __CRASH(msg)
    return function() assert(false, "!!CRASH!!: " .. (msg or "")) end
end

reflect = __CRASH("reflect is not implemented")
debug_assertions = __CRASH("debug_assertions is not implemented")
thread_sleep = __CRASH("thread_sleep is not implemented")

function pop(l)
    local popped = l[#l]
    l[#l] = nil
    return popped
end

as_str = tostring
print = print
function dbg(x) print(x); return x end

unsafe_force = __IDENTITY

function __CONTAINS(a, b)
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

random = math.random
randint = math.random

-- End Sylt preamble
