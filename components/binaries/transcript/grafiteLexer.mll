(* Copyright (C) 2000, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

{
   module O = Options
   module P = GrafiteParser

   let out t s = if !O.verbose_lexer then prerr_endline (t ^ " " ^ s)
}

let SPC   = [' ' '\t' '\n' '\r']+
let ALPHA = ['A'-'Z' 'a'-'z']
let FIG   = ['0'-'9']
let DECOR = "?" | "'" | "`"
let IDENT = ALPHA (ALPHA | '_' | FIG )* DECOR*

rule token = parse
   | "(*"              { let s = Lexing.lexeme lexbuf in out "OK" s; P.OK s   }
   | "*)"              { let s = Lexing.lexeme lexbuf in out "CK" s; P.CK s   }
   | SPC               { let s = Lexing.lexeme lexbuf in out "SPC" s; P.SPC s }
   | "axiom"           { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "definition"      { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "theorem"         { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "lemma"           { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
(*    
   | "fact"            { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
*)   
   | "remark"          { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "variant"         { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "inductive"       { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "coinductive"     { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "record"          { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "let rec"         { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "let corec"       { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s   }
   | "notation"        { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "interpretation"  { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "alias"           { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "coercion"        { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "prefer coercion" { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "default"         { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "include"         { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "inline"          { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "pump"            { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s }
   | "qed"             { let s = Lexing.lexeme lexbuf in out "QED" s; P.QED s }
   | "elim"            { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | "apply"           { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | "intros"          { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | "assume"          { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | "the"             { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | "rewrite"         { let s = Lexing.lexeme lexbuf in out "PS" s; P.PS s   }
   | IDENT             { let s = Lexing.lexeme lexbuf in out "ID" s; P.ID s   }
   | "." SPC           { let s = Lexing.lexeme lexbuf in out "FS" s; P.FS s   }
   | "."               { let s = Lexing.lexeme lexbuf in out "FS" s; P.FS s   }
   | _                 { let s = Lexing.lexeme lexbuf in out "RAW" s; P.RAW s }
   | eof               { let s = Lexing.lexeme lexbuf in out "EOF" s; P.EOF   }
