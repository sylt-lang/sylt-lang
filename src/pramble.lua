Enum = {}

function Enum.__tostring(t)
  return tostring(t[1]) .. " " .. tostring(t[2])
end

function Enum.new(k, v)
  local e = {k, v}
  setmetatable(e, Enum)
  return e
end

function sy_concat(a)
  return function(b) 
    return a .. b
  end
end

function sy_print_stuff(a)
  for k, v in pairs(a) do
    print(k, v)
  end
end

