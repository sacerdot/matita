{
   module O = Options
   
   let out s = if !O.debug_lexer then prerr_endline s
}

let OL  = "(*"
let CL  = "*)" 
let UNI = ['\x80'-'\xBF']+
let SPC = ['\r' '\n' '\t' ' ']+
let QT  = '"'

rule token = parse
   | OL     { out "COM"; block lexbuf; token lexbuf                     }
   | QT     { out "STR"; O.count := !O.count + str lexbuf; token lexbuf }
   | SPC    { out "SPC"; incr O.count; token lexbuf                     }
   | UNI    { out "UNI"; token lexbuf                                   }
   | _      { out "CHR"; incr O.count; token lexbuf                     }
   | eof    { out "EOF"                                                 }
and str = parse
   | QT     { 2 }
   | "\\\"" { succ (str lexbuf)                                         }
   | UNI    { str lexbuf                                                }
   | _      { succ (str lexbuf)                                         }
and block = parse
   | CL     { ()                                                        }
   | OL     { block lexbuf; block lexbuf                                }
   | QT     { let _ = str lexbuf in block lexbuf                        }
   | _      { block lexbuf                                              }
