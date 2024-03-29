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
    if type(b) == "table" then
        local out = {}
        for x = 1, #a, 1 do
            out[x] = a[x] / b[x]
        end
        return __TUPLE(out)
    else
        local out = {}
        for x = 1, #a, 1 do
            out[x] = a[x] / b
        end
        return __TUPLE(out)
    end
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
function list_random_choice(l) return list_get(l, math.random(0, #l - 1)) end

function varargs(f)
    return function(xs)
        return f(unpack(xs))
    end
end

function list_for_each(l, f)
    for _, v in pairs(l) do
        f(v)
    end
end

function list_map(l, f)
    local o = {}
    for k, v in pairs(l) do
        o[k] = f(v)
    end
    return __LIST(o)
end

function list_get(l, i)
    x = l[i+1]
    if x ~= nil then
        return __VARIANT({"Just", x})
    else
        return __VARIANT({"None", nil})
    end
end

function list_set(l, i, x)
    if #l > i then
        l[i+1] = x
    end
end

function list_fold(l, a, f)
    for _, v in pairs(l) do
        a = f(v, a)
    end
    return a
end

function list_filter(l, f)
    local o = {}
    for _, v in pairs(l) do
        if f(v) then
            table.insert(o, v)
        end
    end
    return __LIST(o)
end

list_push = table.insert

function list_prepend(l, v)
    list_push(l, 1, v)
end

function list_find(l, p)
    for _, x in pairs(l) do
        if p(x) then
            return __VARIANT({"Just", x})
        end
    end
    return __VARIANT({"None", nil})
end

function xx_len(c)
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
function as_char(s)
   char = string.byte(s)
   if char ~= nil then
      return __VARIANT({"Just", char})
   else
      return __VARIANT({"None", nil})
   end
end
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

function list_pop(l)
    local popped = list_get(l, #l - 1)
    list_set(l, #l - 1, nil)
    return popped
end

as_str = tostring
print = print
function dbg(x) print(x); return x end

unsafe_force = __IDENTITY

random = math.random
randint = math.random

-- Dict
__LUA_DICT_META = { _type = "dict" }
__LUA_DICT_META.__eq = function(a, b)
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
__LUA_DICT_META.__tostring = function(a)
    local out = "dict {"
    local first = true
    for _k, v in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. tostring(v[1]) .. ": " .. tostring(v[2])
    end
    out = out .. "}"
    return out
end

function dict_new()
    return setmetatable({}, __LUA_DICT_META)
end

function dict_from_list(l)
    local out = dict_new()
    for _, e in pairs(l) do
        dict_update(out, e[1], e[2])
    end
    return out
end

function dict_update(dict, k, v)
    dict[tostring(k)] = __TUPLE {k, v}
end

function dict_remove(dict, k)
    dict[k] = nil
end

function dict_get(dict, k)
    local x = dict[tostring(k)]
    if x == nil then
       return __VARIANT({"None", nil})
    else
       return __VARIANT({"Just", x[2]})
    end
end

function dict_for_each(dict, f)
    for _k, v in pairs(dict) do
        f(v)
    end
end

function dict_map(dict, f)
    local out = dict_new()
    for _k, v in pairs(dict) do
        x = f(v)
        dict_update(out, x[1], x[2])
    end
    return out
end


-- Set
__LUA_SET_META = { _type = "set" }
__LUA_SET_META.__eq = function(a, b)
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
__LUA_SET_META.__tostring = function(a)
    local out = "set {"
    local first = true
    for _k, v in pairs(a) do
        if not first then
            out = out .. ", "
        end
        first = false
        out = out .. tostring(v)
    end
    out = out .. "}"
    return out
end

function set_new()
    return setmetatable({}, __LUA_SET_META)
end

function set_from_list(l)
    local out = set_new()
    for _, e in pairs(l) do
        set_add(out, e)
    end
    return out
end

function set_add(set, k)
    set[tostring(k)] = k
end

function set_remove(set, k)
    set[tostring(k)] = nil
end

function set_contains(set, k)
    return set[tostring(k)] ~= nil
end

function set_for_each(set, f)
    for _k, v in pairs(set) do
        f(v)
    end
end

function set_map(set, f)
    local out = dict_new()
    for _k, v in pairs(set) do
        x = f(v)
        set_add(out, x)
    end
    return out
end


-- End Sylt preamble
