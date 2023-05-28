local strings = {"Hello", "world"}

local function log(str)
    print(str)
end

local index = 1
while index <= #strings do
    log(strings[index])
    index = index + 1
end