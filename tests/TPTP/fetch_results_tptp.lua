#! /usr/bin/lua50

require "luasocket"

SYSTEM = "Matita---0.1.0.UNS-Ref.s"
URL = "http://www.cs.miami.edu/~tptp/cgi-bin/DVTPTP2WWW/view_file.pl?Category=Solutions&Domain=%s&File=%s&System=%s"

function url_for(system, problem)
	local domain = string.sub(problem,1,3)
	local url = string.format(URL,domain,problem,system)
	return url
end

function load_todo_list(file)
	local f = io.open(file,"r")
	local todo = {}
	for l in f:lines() do
		table.insert(todo,l)
	end
	f:close()
	return todo
end

function main(argv)
	assert(table.getn(argv) == 1,
		"Only one paarmeter: the file containing the problems")
	local todo = load_todo_list(argv[1])
	local todo_size = table.getn(todo)
	for i=1,todo_size do
		local filename = todo[i]
		local url = url_for(SYSTEM,filename)
		print("Fetching "..filename.." ("..i.."/"..todo_size..") "..url)
		local data,err = socket.http.get(url)
		assert(data,err)
		local logfilename = "log."..filename
		local f = io.open(logfilename,"w")
		f:write(data)
		f:close()
		os.execute("gzip -f "..logfilename)
	end
end

main(arg)
