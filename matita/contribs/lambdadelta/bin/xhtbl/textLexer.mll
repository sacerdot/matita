{
   module S  = String
   
   module O  = Options
   module TP = TextParser
   
   let out s = if !O.debug_lexer then prerr_endline s
}

let SPC = ['\r' '\n' '\t' ' ']+
let QT  = "\""
let NUM = ['0'-'9']+

rule token = parse
   | SPC      { token lexbuf                    }
   | QT       { let s = str lexbuf in 
                out s; TP.TEXT s                }
   | NUM as s { out s; TP.NUM (int_of_string s) }
   | "(*"     { block lexbuf; token lexbuf      }
   | "{"      { out "{"; TP.OC                  }
   | "}"      { out "}"; TP.CC                  }
   | "["      { out "["; TP.OB                  }
   | "]"      { out "]"; TP.CB                  }   
   | "*"      { out "*"; TP.SR                  }
   | "^"      { out "^"; TP.CF                  }
   | "+"      { out "+"; TP.PS                  }
   | "("      { out "("; TP.OP                  }
   | ")"      { out ")"; TP.CP                  }   
   | "@"      { out ")"; TP.AT                  }    
   | "space"  { out "space"; TP.SPACE           }
   | "name"   { out "name"; TP.NAME             }   
   | "table"  { out "table"; TP.TABLE           }
   | "class"  { out "class"; TP.CSS             }
   | "uri"    { out "uri"; TP.URI               }
   | "ext"    { out "ext"; TP.EXT               }
   | eof      { TP.EOF                          }
and str = parse
   | QT       { ""                              }
   | "\\\\"   { "\\" ^ str lexbuf               }
   | "\\\""   { "\"" ^ str lexbuf               }
   | _ as c   { S.make 1 c ^ str lexbuf         }
and block = parse
   | "*)"     { ()                              }
   | "(*"     { block lexbuf; block lexbuf      }
   | QT       { let _ = str lexbuf in
                block lexbuf                    }
   | _        { block lexbuf                    }
