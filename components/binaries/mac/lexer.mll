(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

{
   module O = Options
   
   let out s = if !O.debug_lexer then prerr_endline s
}

let OL  = "(*"
let CL  = "*)" 
let UNI = ['\x80'-'\xBF']+
let SPC = ['\r' '\n' '\t' ' ']+
let WRD = ['0'-'9' 'A'-'Z' 'a'-'z' '_']+
let QT  = '"'

rule token = parse
   | OL     { out "COM"; block lexbuf; token lexbuf                     }
   | QT     { out "STR"; O.count := !O.count + str lexbuf; token lexbuf }
   | SPC    { out "SPC"; incr O.count; token lexbuf                     }
   | UNI    { out "UNI"; incr O.count; token lexbuf                     }
   | WRD    { out "WRD"; incr O.count; token lexbuf                     }
   | _      { out "CHR"; incr O.count; token lexbuf                     }
   | eof    { out "EOF"                                                 }
and str = parse
   | QT     { 2 }
   | "\\\"" { succ (str lexbuf)                                         }
   | UNI    { succ (str lexbuf)                                         }
   | WRD    { succ (str lexbuf)                                         }
   | _      { succ (str lexbuf)                                         }
and block = parse
   | CL     { ()                                                        }
   | OL     { block lexbuf; block lexbuf                                }
   | QT     { let _ = str lexbuf in block lexbuf                        }
   | _      { block lexbuf                                              }
