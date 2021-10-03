__TEST = false
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

if __TEST then
    local a = __TUPLE { 1, 2, 3 }
    local b = __TUPLE { 3, 2, 1 }
    print(a)
    print(b * a + a)
    print(-a)
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

if __TEST then
    local a = __LIST { 1, 2, 3 }
    print(a)
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
        out = out .. tostring(k) .. ":" .. tostring(v)
    end
    out = out .. "}"
    return out
end
function __DICT(obj)
    return setmetatable(obj, __DICT_META)
end

if __TEST then
    local a = __DICT { [1] = 1, [2] = 3, [3] = 2 }
    print(a)
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

if __TEST then
    local a = __SET { 1, 3, 2 }
    print(a)
end

