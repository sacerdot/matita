{
  module EP = RecommParser

  let debug = ref false

  let keys = [|
    "Note";
    "NOTE";
  |]

  let heads = [|
    "Advanced";
    "Alternative";
    "Basic";
    "Constructions";
    "Forward";
    "Destructions";
    "Eliminations";
    "Eliminators";
    "Equalities";
    "Helper";
    "Inversion";
    "Inversions";
    "Iterators";
    "Main";
    "Properties";
  |]

  let str c = String.make 1 c

  let nl lexbuf = Lexing.new_line lexbuf

  let is_uppercase_ascii s =
    let rec aux i =
       if i < 0 then true else
       if 'a' <= s.[i] && s.[i] <= 'z' then false else
       aux (pred i)  
    in
    aux (String.length s - 1)

  let disambiguate_word s =
    if Array.mem s keys then EP.KW s else
    if Array.mem s heads then EP.HW s else
    if is_uppercase_ascii s then EP.CW s else
    EP.SW s

  let log s =
    if !debug then Printf.eprintf "lezer: %s\n" s

  let log_s s =
    if !debug then Printf.eprintf "lexer: %S\n" s

  let log_c c =
    if !debug then Printf.eprintf "lexer: %C\n" c
}

let CR = "\r"
let SP = " "
let NL = "\n"
let SR = "*"
let OP = "(*"
let CP = SR* "*)"  
let PP = CP SP* OP
let WF = ['A'-'Z' 'a'-'z']
let WB = ['A'-'Z' 'a'-'z' '_' '-']*
let WD = WF WB

rule src_token = parse
  | CR       { src_token lexbuf                   } 
  | NL  as c { log "NL"; nl lexbuf; EP.NL (str c) }
  | SP+ as s { log "SP"; EP.SP s                  }
  | PP  as s { log "PP"; EP.PP s                  }
  | OP  as s { log "OP"; EP.OP s                  }
  | CP  as s { log "CP"; EP.CP s                  }
  | SR  as c { log "SR"; EP.SR (str c)            }
  | WD  as s { log_s s ; disambiguate_word s      }
  | _   as c { log_c c ; EP.OT (str c)            }
  | eof      { log "EF"; EP.EF                    }
