#!/usr/bin/lua5.1

local tool_re = "^([%w%.]+)"
local test_re = "([%w%./_-]+)"
local rc_re = string.char(27).."%[%d+;%d+m([%a]+)"..string.char(27).."%[0m"
local time_re = "(%d+m%d+%.%d+s)"
local mark_re = "(%d+)"
local opt_re = "(gc%-%a+)$"
local sep = "%s+"

local fmt = "INSERT bench "..
	"(result, compilation, test, time, timeuser, mark, options) "..
	"VALUES ('%s', '%s', '%s', %d, %d, '%s', '%s');\n"

-- build the huge regex
local re = tool_re .. sep .. test_re .. sep .. rc_re .. sep .. 
	time_re .. sep ..time_re .. sep ..time_re .. sep .. 
	mark_re .. sep .. opt_re 

-- the string to cents of seconds function
function s2t(s)
	local _,_,min,sec,cents = string.find(s,"(%d+)m(%d+)%.(%d+)s")
	return min * 6000 + sec * 100 + cents
end
function t2s(s)
  s = tonumber(s)
  local min, sec, cents
  cents = s % 100
  min = math.floor(s / 6000)
  sec = math.floor((s - min * 6000 - cents) / 100)
  return string.format("%dm%02d.%02ds",min,sec,cents)
end

-- logfile to sql conversion
function log2sql(file)
local t = {}
local f = io.stdin
if file ~= "-" then 
	f = io.open(file,"r")
end
for l in f:lines() do
	local x,_,tool,test,rc,real,user,_,mark,opt = string.find(l,re)

	if x == nil then
    error("regex failed on '"..l.."'")
	end

	-- check the result is valid
	if tool ~= "matitac" and tool ~= "matitac.opt" then
		error("unknown tool " .. tool)
	else
		if tool == "matitac" then tool = "byte" else tool = "opt" end
	end
	if rc ~= "OK" and rc ~= "FAIL" then
		error("unknown result " .. rc)
	else
		rc = string.lower(rc)
	end
	if opt ~= "gc-on" and opt ~= "gc-off" then
		error("unknown option "..opt)
	end
	real = s2t(real)
	user = s2t(user)

	-- print the sql statement
	table.insert(t,string.format(fmt,rc,tool,test,real,user,mark,opt))
end
return table.concat(t)
end

-- proportions
function proportion(x,y,a,b)
  local rc
  if x == "x" then
    rc = y * a / b
  elseif y == "x" then
    rc = x * b / a
  elseif a == "x" then
    rc = x * b / y
  elseif b == "x" then
    rc = y * a / x
  end
  return string.format("%d",rc)
end

-- conversion from the old db to the new one
function convertsql(file)
  local f = io.open(file)
  return string.gsub(f:read("*a"),time_re,
    function(s)
      return s2t(s)
    end)
end

-- call the desired function and print the result
fun = arg[1]
table.remove(arg,1)
f = _G[fun] or error("no " .. fun .. " defined")
print(f(unpack(arg)) or "")

-- eof
