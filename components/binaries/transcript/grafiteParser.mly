/* Copyright (C) 2000, HELM Team.
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
 */

%{
   module T = Types
   module O = Options

   let out t s = if !O.verbose_parser then prerr_endline ("-- " ^ t ^ " " ^ s)

   let mk_flavour str =
      match str with
	| "record"      -> T.Ind, None
	| "inductive"   -> T.Ind, None
	| "coinductive" -> T.Ind, None
	| "axiom"       -> T.Con, None
	| "definition"  -> T.Con, Some `Definition
        | "let rec"     -> T.Con, Some `Definition
        | "let corec"   -> T.Con, Some `Definition	
        | "theorem"     -> T.Con, Some `Theorem
        | "lemma"       -> T.Con, Some `Lemma
        | "fact"        -> T.Con, Some `Fact 
        | "remark"      -> T.Con, Some `Remark        
        | "variant"     -> T.Con, Some `Variant
	| _             -> assert false

%}
   %token <string> SPC OK CK FS QED TH UNX PS ID RAW
   %token EOF

   %start items
   %type <Types.items> items
%%

/* LINES ITEMS ***************************************************************/

   extra:
      | ID           { $1           }      
      | QED          { $1           }
      | RAW          { $1           }
   ;
   text:
      | extra   { $1 }
      | TH      { $1 }
      | UNX     { $1 }
      | PS      { $1 }
      | comment { $1 }
   ;
   texts:
      |            { ""      }
      | text texts { $1 ^ $2 }
   ;
   line:
      | texts FS { $1 ^ $2 }
   ;
   drop:
      | extra line { $1 ^ $2 }
   ;
   drops:
      |            { ""      }
      | drop drops { $1 ^ $2 }
   ;

/* SPACE ITEMS  *************************************************************/
   
   verbatim:
      | text    { $1 }
      | FS      { $1 }
   ;
   verbatims:
      |                    { ""      }
      | verbatim verbatims { $1 ^ $2 }
   ;
   comment:
      | SPC             { $1 }
      | OK verbatims CK { $1 ^ $2 ^ $3 }
   ;

/* STEPS ********************************************************************/

   step:
      | comment { $1 }
      | FS      { $1 }
      | TH      { $1 }
      | UNX     { $1 }
      | PS      { $1 }
      | ID      { $1 }
      | RAW     { $1 }
   ;
   steps:
      | QED FS     { $1 ^ $2 }
      | step steps { $1 ^ $2 }
   ;

/* ITEMS ********************************************************************/

   id:
      | ID  { $1 }
      | TH  { $1 }
      | UNX { $1 }
      | PS  { $1 }
   ;
   
   item:
      | comment
         { out "OK" $1; [T.Verbatim $1] }
      | TH SPC id line drops
         { out "TH" $3;
	   let a, b = mk_flavour $1 in [T.Inline (false, a, $3, "", b, [])] 
	 }
      | UNX line drops { out "UNX" $1; [T.Verbatim ($1 ^ $2 ^ $3)] }
      | PS steps       { out "PS" $2; [] }
      | QED FS         { [] }
   ;
   items:
      | EOF        { []      }
      | item items { $1 @ $2 }
/*      | error      { out "ERROR" ""; failwith ("item id " ^ "") } */
  ;
