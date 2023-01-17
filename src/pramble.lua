
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

