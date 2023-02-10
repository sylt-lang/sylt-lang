Enum = {}

function Enum.__tostring(t)
  return tostring(t[1]) .. " " .. tostring(t[2])
end

function Enum.new(k, v)
  local e = { k, v }
  setmetatable(e, Enum)
  return e
end

RecordMeta = {}
function RecordMeta.__tostring(record)
  local s = '{'
  local first = true
  for k, v in pairs(record) do
    if first then
      first = false
    else
      s = s .. ', '
    end

    s = s .. tostring(k) .. ': ' .. tostring(v)
  end
  s = s .. '}'
  return s
end

Record = {}
function Record.new(record)
  setmetatable(record, RecordMeta)
  return record
end

function sy_id(a) return a end

function sy_record_merge(a, b)
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

function _sy_intern_check_pattern(kind, expected, given)
  assert(expected == given, "Invalid pattern match: " .. tostring(expected) .. " != " .. tostring(given))
end

function _sy_intern_check_const(thing, const)
  assert(const == thing[1], "Invalid pattern match: \"" .. const .. "\" != " .. tostring(thing[1]))
  return thing[2]
end
