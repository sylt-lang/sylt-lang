Enum = {}

function Enum.__tostring(t)
  return tostring(t[1]) .. " " .. tostring(t[2])
end

function Enum.new(k, v)
  local e = {k, v}
  setmetatable(e, Enum)
  return e
end

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
