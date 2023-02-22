function process(s) {
	if(match(s,/^__docfor:(.*)/,data)){
		s=docfor[data[1]];
	} 	
	return s;
}

function emit(s) {
	lines[length(lines)] = s;	
}

function emit_line() {
	if (! line_done) emit(indent $0);
	line_done = 0;
}

function emit_docfor(k) {
	emit();
	emit("__docfor:" k);	
	emit();
}

function emit_img(key) {
	emit();
	emit("![" key "][" key "]");
	emit();
}

function done() { line_done = 1; }

function check_begin_docfor(s){
	if (match(s,/^\(\*D\[([^\]]*)\]/,data)) {
		curdocblock = data[1];	
	} else if (match(s,/^D\[([^\]]*)\]/,data)) {
		curdocblock = data[1];	
       	} else {
		curdocblock = "";
	}
}

function store_docfor_if_docforblock(s) {
	if (!line_done && curdocblock != "") {
		docfor[curdocblock] = docfor[curdocblock] "\n" s;
		done();
	}
}

BEGIN { 
	do_print = 1; 
	indent = ""; 
	refs["matita"] = "http://matita.cs.unibo.it";
	docfor[0]=""
	curdocblock="";
	lines[0]="";
	line_done =0;
	} 

# markdown mangling
/screenshot *".*"/ { 
	match($0, "screenshot *\"([^\"]+)\"", data);
	key = data[1];
	refs[key] = key ".png"; 
	$0 = gensub(/\(\*\* *screenshot[^*]*\*\)/,"",$0);
	emit_line();
	emit_img(key);
	emit_docfor(key);
	done();
	}

# literate programming
/^\(\*D/ { 
	check_begin_docfor($0);
	indent = ""; 
	done();
	}
/^D\[.*\]/ { 
	check_begin_docfor($0);
	indent = ""; 
	done();
	}
/^D\*\)/ { 
	indent = "    "; 
	curdocblock = "";
	emit();
	done();
	} 
/HIDE/ { 
	do_print = 0; }
{ 
	if (do_print == 1) {
		store_docfor_if_docforblock($0);
		emit_line(); 
	}
	}	
/UNHIDE/ { 
	do_print = 1; }

# closing
END { 
	print length(lines) > "/dev/stderr";
	for (i =0; i< length(lines); i++){
		print process(lines[i]);	
	}
	for (i in refs) {
		print "[" i "]: " refs[i];	
	}
} 
