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
  module EG = RolesGlobal
  module EP = RolesParser

  let out s = if !EG.debug_lexer then prerr_endline s
}

let SPC  = ['\r' '\n' '\t' ' ']+
let QT   = "\""
let TEXT = ['0'-'9' 'A'-'Z' 'a'-'z' '/' '.' '_']+

rule token = parse
  | SPC          { token lexbuf           }
  | QT           { let s = text lexbuf in
                   out s; EP.TEXT s       }
  | ":"          { out ":"; EP.SC         }
  | "("          { out "("; EP.OP         }
  | ")"          { out ")"; EP.CP         }
  | "ver"   as s { out s; EP.VER          }
  | "old"   as s { out s; EP.OLD          }
  | "new"   as s { out s; EP.NEW          }
  | "rel"   as s { out s; EP.REL          }
  | "base"  as s { out s; EP.BASE         }
  | "top"   as s { out s; EP.TOP          }
  | "roles" as s { out s; EP.ROLES        }
  | eof          { EP.EOF                 }

and text = parse
   | QT          { ""                     }
   | TEXT   as s { s ^ text lexbuf        }
