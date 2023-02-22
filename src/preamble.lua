-- The sylt namespace
local Sylt = {}

-- Utility
Sylt.Util = {}
function Sylt.Util.inspect(obj)
  local ty = type(obj)
  if ty == 'table' then
    local meta = getmetatable(obj)
    if meta ~= nil then
      ty = meta.__type or ty
    end
  end

  if ty == 'table' or ty == 'record' then
    local s = ty:sub(1, 3) .. '{'
    local first = true

    for k, v in pairs(obj) do
      if first then
        first = false
        s = s .. ' '
      else
        s = s .. ', '
      end

      s = s .. Sylt.Util.inspect(k) .. ': ' .. Sylt.Util.inspect(v)
    end

    s = s .. ' }'

    return s
  elseif ty == 'enum' then
    return obj[1] .. ' ' .. Sylt.Util.inspect(obj[2])
  elseif ty == 'string' then
    return '"' .. obj .. '"'
  else
    return tostring(obj)
  end
end

-- Enums
Sylt.Enum = {}

Sylt.Enum.Meta = {
  __type = 'enum',
  __tostring = function(t)
    return tostring(t[1]) .. ' ' .. tostring(t[2])
  end,
}

function Sylt.Enum.new(k, v)
  local e = { k, v }
  setmetatable(e, Sylt.Enum.Meta)
  return e
end

-- Records
Sylt.Record = {}

Sylt.Record.Meta = {
  __type = 'record',
  __tostring = function(record)
    local s = '{'
    local first = true
    for k, v in pairs(record) do
      if first then
        first = false
        s = s .. ' '
      else
        s = s .. ', '
      end

      s = s .. tostring(k) .. ': ' .. tostring(v)
    end
    s = s .. ' }'
    return s
  end,
}

function Sylt.Record.new(record)
  setmetatable(record, Sylt.Record.Meta)
  return record
end

function Sylt.Record.merge(a, b)
  -- fields in `a` take precedence over `b`
  -- Since everything is immutable we get away with a shallow copy here :D
  local out = {}
  for k, v in pairs(a) do
    out[k] = v
  end
  for k, v in pairs(b) do
    out[k] = v
  end
  return out
end

-- Patterns
Sylt.Pattern = {}
function Sylt.Pattern.check_pattern(kind, expected, given)
  assert(expected == given, 'Invalid pattern match: ' .. tostring(expected) .. ' != ' .. tostring(given))
end

function Sylt.Pattern.check_const(thing, const)
  assert(const == thing[1], 'Invalid pattern match: "' .. const .. '" != ' .. tostring(thing[1]))
  return thing[2]
end

function Sylt.Pattern.id(e)
  return e
end
