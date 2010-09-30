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
   module P = Gallina8Parser

   let out t s = if !O.verbose_lexer then prerr_endline (t ^ " " ^ s)

   let check s =
      let c = Char.code s.[0] in
      if c <= 127 then s else 
      let escaped = Printf.sprintf "\\%3u\\" c in
      begin 
         if !O.verbose_escape then Printf.eprintf "ESCAPED: %s %s\n" s escaped;
	 escaped 
      end
}

let QT    = '"'
let SPC   = [' ' '\t' '\n' '\r']+
let ALPHA = ['A'-'Z' 'a'-'z' '_']
let FIG   = ['0'-'9']
let ID    = ALPHA (ALPHA | FIG | "\'")*
let RAWID = QT [^ '"']* QT
let NUM   = "-"? FIG+
	    
rule token = parse
   | "Let"         { let s = Lexing.lexeme lexbuf in out "LET" s; P.LET s    }
   | "Remark"      { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "Lemma"       { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "Theorem"     { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "Definition"  { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "Fixpoint"    { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "CoFixpoint"  { let s = Lexing.lexeme lexbuf in out "TH" s; P.TH s      }
   | "Qed"         { let s = Lexing.lexeme lexbuf in out "QED" s; P.QED s    }
   | "Save"        { let s = Lexing.lexeme lexbuf in out "QED" s; P.QED s    }
   | "Defined"     { let s = Lexing.lexeme lexbuf in out "QED" s; P.QED s    }
   | "Proof"       { let s = Lexing.lexeme lexbuf in out "PRF" s; P.PROOF s  }
   | "Variable"    { let s = Lexing.lexeme lexbuf in out "VAR" s; P.VAR s    }
   | "Variables"   { let s = Lexing.lexeme lexbuf in out "VAR" s; P.VAR s    }
   | "Hypothesis"  { let s = Lexing.lexeme lexbuf in out "VAR" s; P.VAR s    } 
   | "Hypotheses"  { let s = Lexing.lexeme lexbuf in out "VAR" s; P.VAR s    } 
   | "Axiom"       { let s = Lexing.lexeme lexbuf in out "AX" s; P.AX s      }
   | "Parameter"   { let s = Lexing.lexeme lexbuf in out "AX" s; P.AX s      }
   | "Parameters"  { let s = Lexing.lexeme lexbuf in out "AX" s; P.AX s      }
   | "Inductive"   { let s = Lexing.lexeme lexbuf in out "IND" s; P.IND s    }
   | "CoInductive" { let s = Lexing.lexeme lexbuf in out "IND" s; P.IND s    }
   | "Record"      { let s = Lexing.lexeme lexbuf in out "IND" s; P.IND s    }
   | "Scheme"      { let s = Lexing.lexeme lexbuf in out "GEN" s; P.GEN s    }
   | "Section"     { let s = Lexing.lexeme lexbuf in out "SEC" s; P.SEC s    }
   | "End"         { let s = Lexing.lexeme lexbuf in out "END" s; P.END s    }
   | "Hint"        { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Hints"       { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Unset"       { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Print"       { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Opaque"      { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Transparent" { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Ltac"        { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Tactic"      { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Declare"     { let s = Lexing.lexeme lexbuf in out "UNX" s; P.UNX s    }
   | "Require"     { let s = Lexing.lexeme lexbuf in out "REQ" s; P.REQ s    }
   | "Export"      { let s = Lexing.lexeme lexbuf in out "XP" s; P.XP s      }
   | "Import"      { let s = Lexing.lexeme lexbuf in out "XP" s; P.XP s      }
   | "Load"        { let s = Lexing.lexeme lexbuf in out "LOAD" s; P.LOAD s  }
   | "Set"         { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Reset"       { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Implicit"    { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Delimit"     { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Bind"        { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Arguments"   { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Open"        { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "V7only"      { let s = Lexing.lexeme lexbuf in out "SET" s; P.SET s    }
   | "Notation"    { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Reserved"    { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Infix"       { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Grammar"     { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Syntax"      { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Add" SPC "Morphism"
      { let s = Lexing.lexeme lexbuf in out "MOR" s; P.MOR s }
   | "Add"         { let s = Lexing.lexeme lexbuf in out "NOT" s; P.NOT s    }
   | "Identity"    { let s = Lexing.lexeme lexbuf in out "ID" s; P.ID s      }
   | "Coercion"    { let s = Lexing.lexeme lexbuf in out "CO" s; P.COERC s   }
   | "let"         { let s = Lexing.lexeme lexbuf in out "ABBR" s; P.ABBR s  }
   | "in"          { let s = Lexing.lexeme lexbuf in out "IN" s; P.IN s      }
   | "with"        { let s = Lexing.lexeme lexbuf in out "WITH" s; P.WITH s  }
   | SPC           { let s = Lexing.lexeme lexbuf in out "SPC" s; P.SPC s    }
   | ID            { let s = Lexing.lexeme lexbuf in out "ID" s; P.IDENT s   }
   | RAWID         { let s = Lexing.lexeme lexbuf in out "STR" s; P.STR s    }
   | NUM           { let s = Lexing.lexeme lexbuf in out "INT" s; P.INT s    }
   | ":="          { let s = Lexing.lexeme lexbuf in out "DEF" s; P.DEF s    }
   | ":>"          { let s = Lexing.lexeme lexbuf in out "COE" s; P.COE s    }
   | "." ID        { let s = Lexing.lexeme lexbuf in out "AC" s; P.AC s      }
   | "." SPC       { let s = Lexing.lexeme lexbuf in out "FS" s; P.FS s      }
   | "." eof       { let s = Lexing.lexeme lexbuf in out "FS" s; P.FS s      }
   | "(*"          { let s = Lexing.lexeme lexbuf in out "OQ" s; P.OQ s      }
   | "*)"          { let s = Lexing.lexeme lexbuf in out "CQ" s; P.CQ s      }
   | "("           { let s = Lexing.lexeme lexbuf in out "OP" s; P.OP s      }
   | ")"           { let s = Lexing.lexeme lexbuf in out "CP" s; P.CP s      }
   | "{"           { let s = Lexing.lexeme lexbuf in out "OC" s; P.OC s      }
   | "}"           { let s = Lexing.lexeme lexbuf in out "CC" s; P.CC s      }
   | ";"           { let s = Lexing.lexeme lexbuf in out "SC" s; P.SC s      }
   | ":"           { let s = Lexing.lexeme lexbuf in out "CN" s; P.CN s      }
   | ","           { let s = Lexing.lexeme lexbuf in out "CM" s; P.CM s      }
   | _             
      { let s = check (Lexing.lexeme lexbuf) in out "SPEC" s; P.EXTRA s }
   | eof           { let s = Lexing.lexeme lexbuf in out "EOF" s; P.EOF      }
