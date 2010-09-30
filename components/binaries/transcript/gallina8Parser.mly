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

   let trim = HExtlib.trim_blanks

   let hd = List.hd

   let cat x = String.concat " " x

   let mk_vars local idents =
      let kind = if local then T.Var else T.Con in
      let map ident = T.Inline (local, kind, trim ident, "", None, []) in
      List.map map idents

   let strip2 s =
      String.sub s 1 (String.length s - 2)

   let strip1 s = 
      String.sub s 1 (String.length s - 1)

   let coercion str = 
      [T.Coercion (false, str); T.Coercion (true, str)]

   let notation str =
      [T.Notation (false, str); T.Notation (true, str)]

   let mk_flavour str =
      match trim str with
        | "Remark"     -> Some `Remark 
        | "Lemma"      -> Some `Lemma
        | "Theorem"    -> Some `Theorem
        | "Definition" -> Some `Definition
        | "Fixpoint"   -> Some `Definition
        | "CoFixpoint" -> Some `Definition
        | "Let"        -> Some `Definition
	| "Scheme"     -> Some `Theorem
        | _            -> assert false

   let mk_morphism ext =
      let generate s = T.Inline (false, T.Con, ext ^ s, "", Some `Theorem, []) in
      List.rev_map generate ["2"; "1"]

%}
   %token <string> SPC STR IDENT INT EXTRA AC OP CP OC CC OQ CQ DEF FS COE CN SC CM
   %token <string> WITH ABBR IN LET TH PROOF QED VAR AX IND GEN SEC END UNX REQ XP SET NOT LOAD ID COERC MOR
   %token EOF

   %start items
   %type <Types.items> items
%%
/* SPACED TOKENS ************************************************************/
   
   ident: xident spcs { $1 ^ $2 };
   fs: FS spcs { $1 ^ $2 };
   mor: MOR spcs { $1 ^ $2 };
   th: TH spcs { $1 ^ $2 };
   xlet: LET spcs { $1 ^ $2 };
   proof: PROOF spcs { $1 ^ $2 };
   qed: QED spcs { $1 ^ $2 };
   gen: GEN spcs { $1 ^ $2 };
   sec: SEC spcs { $1 ^ $2 };
   xend: END spcs { $1 ^ $2 };
   unx: UNX spcs { $1 ^ $2 };
   def: DEF spcs { $1 ^ $2 };
   op: OP spcs { $1 ^ $2 };
   abbr: ABBR spcs { $1 ^ $2 };
   var: VAR spcs { $1 ^ $2 };
   ax: AX spcs { $1 ^ $2 };
   req: REQ spcs { $1 ^ $2 };
   load: LOAD spcs { $1 ^ $2 };
   xp: XP spcs { $1 ^ $2 };
   ind: IND spcs { $1 ^ $2 };
   set: SET spcs { $1 ^ $2 };
   notation: NOT spcs { $1 ^ $2 };
   cn: CN spcs { $1 ^ $2 };
   str: STR spcs { $1 ^ $2 };
   id: ID spcs { $1 ^ $2 };
   coerc: COERC spcs { $1 ^ $2 };
   cm: CM spcs { $1 ^ $2 } | { "" }
   wh: WITH spcs { $1 ^ $2 };

/* SPACES *******************************************************************/

   comment:
      | OQ verbatims CQ { $1 ^ $2 ^ $3 }
   ;
   spc:
      | SPC     { $1 }
      | comment { $1 }
   ;
   spcs:
     |          { ""      }
     | spc spcs { $1 ^ $2 }
   ;
   rspcs:
     |           { ""      }
     | SPC rspcs { $1 ^ $2 }
   ;

/* IDENTIFIERS **************************************************************/

   outer_keyword:
      | LET   { $1 }
      | TH    { $1 }
      | VAR   { $1 }
      | AX    { $1 }
      | IND   { $1 }
      | GEN   { $1 }
      | SEC   { $1 }
      | END   { $1 }
      | UNX   { $1 }
      | REQ   { $1 }
      | LOAD  { $1 }
      | SET   { $1 }
      | NOT   { $1 }
      | ID    { $1 }
      | COERC { $1 }
      | MOR   { $1 }
   ;
   inner_keyword:
      | XP    { $1 }
   ;
   xident:
      | IDENT         { $1 }
      | outer_keyword { $1 }
      | WITH          { $1 }
   ;
   qid:
      | xident { [$1]            }
      | qid AC { strip1 $2 :: $1 }
   ;
   idents:
      | ident           { [$1]     }
      | ident cm idents { $1 :: $3 }
   ;

/* PLAIN SKIP ***************************************************************/

   plain_skip:
      | IDENT           { $1 }
      | inner_keyword   { $1 }
      | STR             { $1 }
      | INT             { $1 }
      | COE             { $1 }
      | OC              { $1 }
      | CC              { $1 }
      | SC              { $1 }
      | CN              { $1 }
      | CM              { $1 }
      | EXTRA           { $1 }
   ;
   inner_skip:
      | plain_skip     { $1 }
      | outer_keyword  { $1 }
      | AC             { $1 }
      | DEF            { $1 }
      | PROOF          { $1 }
      | QED            { $1 }
      | FS             { $1 }
      | WITH           { $1 }
   ;

/* LEFT SKIP ****************************************************************/

   rlskip:
      | plain_skip       { $1, []                   }
      | abbr li_skips IN { $1 ^ fst $2 ^ $3, snd $2 }
      | op ocp_skips CP  { $1 ^ fst $2 ^ $3, snd $2 }
      | IN               { $1, []                   }
      | CP               { $1, []                   }
   ;
   xlskip:
      | outer_keyword { $1, [] }
      | AC            { $1, [] }
      | WITH          { $1, [] }
      | rlskip        { $1     }
   ;
   xlskips:
      | xlskip spcs         { fst $1 ^ $2, snd $1                   }
      | xlskip spcs xlskips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;
   lskips:
      | rlskip spcs         { fst $1 ^ $2, snd $1                   }
      | rlskip spcs xlskips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;
   opt_lskips:
      | lskips { $1     }
      |        { "", [] }
   ;

/* GENERAL SKIP *************************************************************/ 

   rskip:
      | rlskip { $1     }
      | DEF    { $1, [] }
   ;
   xskip:
      | outer_keyword { $1, [] }
      | AC            { $1, [] }
      | WITH          { $1, [] }
      | rskip         { $1     }
   ;
   xskips:
      | xskip spcs        { fst $1 ^ $2, snd $1                   }
      | xskip spcs xskips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;
   skips:
      | rskip spcs        { fst $1 ^ $2, snd $1                   }
      | rskip spcs xskips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;

/* ABBREVIATION SKIP ********************************************************/

   li_skip:
      | inner_skip       { $1, []                   }
      | abbr li_skips IN { $1 ^ fst $2 ^ $3, snd $2 }
      | op ocp_skips CP  { $1 ^ fst $2 ^ $3, snd $2 }
   ;
   li_skips:
      | li_skip spcs          { fst $1 ^ $2, snd $1                   }
      | li_skip spcs li_skips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;

/* PARENTETIC SKIP **********************************************************/

   ocp_skip:
      | inner_skip       { $1, []                   }
      | abbr li_skips IN { $1 ^ fst $2 ^ $3, snd $2 }
      | op ocp_skips CP  { $1 ^ fst $2 ^ $3, snd $2 }
      | IN               { $1, []                   }
   ;
   ocp_skips:
      | ocp_skip spcs           { fst $1 ^ $2, snd $1                   }
      | ocp_skip spcs ocp_skips { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;

/* VERBATIM SKIP ************************************************************/
   
   verbatim:
      | comment        { $1 }
      | inner_skip     { $1 }
      | ABBR           { $1 }
      | IN             { $1 }
      | OP             { $1 }
      | CP             { $1 }
      | SPC            { $1 }
   ;
   verbatims:
      |                    { ""      }
      | verbatim verbatims { $1 ^ $2 }
   ;   

/* PROOF STEPS **************************************************************/

   step:
      | macro_step   { $1     }
      | skips FS     { snd $1 }
   ;
   steps:
      | step spcs       { $1      }
      | step spcs steps { $1 @ $3 }
   ;
   just:
      | steps qed                   { $1          }
      | proof fs steps qed          { $3          }
      | proof skips                 { snd $2      }
      | proof wh skips fs steps qed { snd $3 @ $5 }
   ;
   macro_step:
      | th ident opt_lskips def xskips FS
         { out "TH" $2;
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1, [])]
	 }
      | th ident lskips fs just FS 
         { out "TH" $2;
	   $5 @ [T.Inline (false, T.Con, trim $2, "", mk_flavour $1, [])]
	 }
      | gen ident def xskips FS
         { out "TH" $2;
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1, [])]
	 }      
      | mor ident cn ident fs just FS
         { out "MOR" $4; $6 @ mk_morphism (trim $4)                 }
      | xlet ident opt_lskips def xskips FS
         { out "TH" $2;
	   [T.Inline (true, T.Con, trim $2, "", mk_flavour $1, [])]
	 }
      | xlet ident lskips fs just FS 
         { out "TH" $2;
	   $5 @ [T.Inline (true, T.Con, trim $2, "", mk_flavour $1, [])]
	 }
      | var idents cn xskips FS
         { out "VAR" (cat $2); mk_vars true $2                      }
      | ax idents cn xskips FS
         { out "AX" (cat $2); mk_vars false $2                      }
      | ind ident skips FS
         { out "IND" $2;
	   T.Inline (false, T.Ind, trim $2, "", None, []) :: snd $3
	 }
      | sec ident FS
         { out "SEC" $2; [T.Section (true, trim $2, $1 ^ $2)]       }
      | xend ident FS
         { out "END" $2; [T.Section (false, trim $2, $1 ^ $2)]      }
      | unx xskips FS
         { out "UNX" (fst $2); [T.Unexport ($1 ^ fst $2 ^ trim $3)] }
      | req xp ident FS
         { out "REQ" $3; [T.Include (true, trim $3)]               }
      | req ident FS
         { out "REQ" $2; [T.Include (true, trim $2)]               } 
      | load str FS
         { out "REQ" $2; [T.Include (true, strip2 (trim $2))]      }
      | coerc qid spcs skips FS
         { out "COERCE" (hd $2); coercion (hd $2)                   }
      | id coerc qid spcs skips FS
         { out "COERCE" (hd $3); coercion (hd $3)                   }
      | th ident error 
         { out "ERROR" $2; failwith ("macro_step " ^ $2)            }
      | ind ident error 
         { out "ERROR" $2; failwith ("macro_step " ^ $2)            }
      | var idents error 
         { let vs = cat $2 in
	   out "ERROR" vs; failwith ("macro_step " ^ vs)            }
      | ax idents error 
         { let vs = cat $2 in
	   out "ERROR" vs; failwith ("macro_step " ^ vs)            }
   ;

/* VERNACULAR ITEMS *********************************************************/

   item:
      | OQ verbatims CQ       { [T.Comment $2]                       }
      | macro_step            { $1                                   }
      | set xskips FS         { [T.Unexport ($1 ^ fst $2 ^ trim $3)] }
      | notation xskips FS    { notation ($1 ^ fst $2 ^ trim $3)     }
      | error                 { out "ERROR" "item"; failwith "item"  }
    ;
    items:
      | rspcs EOF        { []      }
      | rspcs item items { $2 @ $3 }
    ;


/*
   oc: OC spcs { $1 ^ $2 };
   coe: COE spcs { $1 ^ $2 };
   sc: SC spcs { $1 ^ $2 };

   cnot:
      | EXTRA { $1 }
      | INT   { $1 }
   ;
   cnots:
      | cnot spcs       { $1 ^ $2      }
      | cnot spcs cnots { $1 ^ $2 ^ $3 }
   ;
   
   xstrict:
      | AC               { $1           }
      | INT              { $1           }
      | EXTRA            { $1           }
      | CN               { $1           }
      | SC               { $1           }
      | OC               { $1           }
      | CC               { $1           }
      | COE              { $1           }
      | STR              { $1           }   
      | abbr extends0 IN { $1 ^ $2 ^ $3 }
      | op extends1 CP   { $1 ^ $2 ^ $3 }      
   ;
   strict:
      | xstrict { $1 }
      | IDENT   { $1 } 
      | SET     { $1 }
      | NOT     { $1 }
   ;
   restrict: 
      | strict  { $1 }
      | IN      { $1 }
      | CP      { $1 }
   ;
   xre:
      | xstrict { $1 }
      | IN      { $1 }
      | CP      { $1 }   
   ;
   restricts:
      | restrict spcs           { $1 ^ $2      }
      | restrict spcs restricts { $1 ^ $2 ^ $3 }
   ;
   xres:
      | xre spcs           { $1 ^ $2      }
      | xre spcs restricts { $1 ^ $2 ^ $3 }   
   ;
   extend0:
      | strict { $1 }
      | DEF    { $1 }
   ;
   extends0:
      | extend0 spcs          { $1 ^ $2      }
      | extend0 spcs extends0 { $1 ^ $2 ^ $3 }
   ;
   extend1:
      | strict { $1 }
      | DEF    { $1 }
      | IN     { $1 }
   ;
   extends1:
      | extend1 spcs          { $1 ^ $2      }
      | extend1 spcs extends1 { $1 ^ $2 ^ $3 }
   ;
   unexport_ff:
      | IDENT          { $1 }
      | AC             { $1 }
      | STR            { $1 }
      | OP             { $1 }
      | ABBR           { $1 }
      | IN             { $1 }
      | CP             { $1 }
      | SET            { $1 }
   ;   
   unexport_rr:
      | unexport_ff { $1 }
      | INT         { $1 }
      | EXTRA       { $1 }
      | CN          { $1 }
      | COE         { $1 }
      | DEF         { $1 }
   ;
   unexport_r:
      | unexport_rr       { $1, []                   }
      | oc fields CC      { $1 ^ fst $2 ^ $3, snd $2 }
      | oc unexport_ff CC { $1, []                   }
   ;
   unexports_r:
      | unexport_r spcs             { fst $1 ^ $2, snd $1                   }
      | unexport_r spcs unexports_r { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;
   field: 
      | ident cn unexports_r
         { $1 ^ $2 ^ fst $3, snd $3                      }
      | ident def unexports_r
         { $1 ^ $2 ^ fst $3, snd $3                      }
      | ident coe unexports_r 
         { $1 ^ $2 ^ fst $3, snd $3 @ coercion (trim $1) }
   ;  
   fields:
      | field           { $1                                      }
      | field sc fields { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3   } 
      | cnots           { $1, []                                  }
      | error           { out "ERROR" "fields"; failwith "fields" }
   ;
   unexport:
      | unexport_r { $1     }
      | SC         { $1, [] }
      | CC         { $1, [] }
      | IP         { $1, [] }
      | LET        { $1, [] }       
      | VAR        { $1, [] }
      
   ;   
   unexports:
      | unexport spcs           { fst $1 ^ $2, snd $1                   }
      | unexport spcs unexports { fst $1 ^ $2 ^ fst $3, snd $1 @ snd $3 }
   ;
   verbatim:
      | unexport_rr    { $1 }
      | reserved_ident { $1 }
      | comment        { $1 }
      | OC             { $1 }
      | CC             { $1 }
      | SC             { $1 }
      | XP             { $1 } 
      | IP             { $1 } 
      | FS             { $1 }
      | SPC            { $1 }
   ;
   verbatims:
      |                    { ""      }
      | verbatim verbatims { $1 ^ $2 }
   ;   
   step:
      | macro_step   { $1 }
      | restricts FS { [] }
   ;
   steps:
      | step spcs       { []      }
      | step spcs steps { $1 @ $3 }
   ;
      
   macro_step:
      | th ident restricts fs proof FS steps qed FS 
         { out "TH" $2;
	   $7 @ [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | th ident restricts fs proof restricts FS
         { out "TH" $2; 
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | th ident restricts fs steps qed FS 
         { out "TH" $2;
	   $5 @ [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | th ident restricts def restricts FS
         { out "TH" $2;
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | th ident def restricts FS
         { out "TH" $2;
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | gen ident def restricts FS
         { out "TH" $2;
	   [T.Inline (false, T.Con, trim $2, "", mk_flavour $1)]
	 }      
      | xlet ident restricts fs proof FS steps qed FS 
         { out "LET" $2;
	   $7 @ [T.Inline (true, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | xlet ident restricts fs proof restricts FS
         { out "LET" $2;
	   [T.Inline (true, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | xlet ident restricts fs steps qed FS 
         { out "LET" $2;
	   $5 @ [T.Inline (true, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | xlet ident restricts def restricts FS
         { out "LET" $2;
	   [T.Inline (true, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | xlet ident def restricts FS
         { out "LET" $2;
	   [T.Inline (true, T.Con, trim $2, "", mk_flavour $1)]
	 }
      | var idents xres FS
         { out "VAR" (cat $2); mk_vars true $2                      }
      | ax idents xres FS
         { out "AX" (cat $2); mk_vars false $2                      }
      | ind ident unexports FS
         { out "IND" $2;
	   T.Inline (false, T.Ind, trim $2, "", None) :: snd $3
	 }
      | sec ident FS
         { out "SEC" $2; [T.Section (true, trim $2, $1 ^ $2)]       }
      | xend ident FS
         { out "END" $2; [T.Section (false, trim $2, $1 ^ $2)]      }
      | unx unexports FS
         { out "UNX" (fst $2); [T.Unexport ($1 ^ fst $2 ^ trim $3)] }
      | req xp ident FS
         { out "REQ" $3; [T.Include (trim $3)]                      }
      | req ip ident FS
         { out "REQ" $3; [T.Include (trim $3)]                      }
      | req ident FS
         { out "REQ" $2; [T.Include (trim $2)]                      } 
      | load str FS
         { out "REQ" $2; [T.Include (strip2 (trim $2))]             }
      | coerc qid spcs cn unexports FS
         { out "COERCE" (hd $2); coercion (hd $2)                   }
      | id coerc qid spcs cn unexports FS
         { out "COERCE" (hd $3); coercion (hd $3)                   }
      | th ident error 
         { out "ERROR" $2; failwith ("macro_step " ^ $2)            }
      | ind ident error 
         { out "ERROR" $2; failwith ("macro_step " ^ $2)            }
      | var idents error 
         { let vs = cat $2 in
	   out "ERROR" vs; failwith ("macro_step " ^ vs)            }
      | ax idents error 
         { let vs = cat $2 in
	   out "ERROR" vs; failwith ("macro_step " ^ vs)            }
   ;
   item:
      | OQ verbatims CQ       { [T.Comment $2]                       }
      | macro_step            { $1                                   }
      | set unexports FS      { [T.Unexport ($1 ^ fst $2 ^ trim $3)] }
      | notation unexports FS { notation ($1 ^ fst $2 ^ trim $3)     }
      | error                 { out "ERROR" "item"; failwith "item"  }
    ;
    items:
      | rspcs EOF        { []      }
      | rspcs item items { $2 @ $3 }
    ;
*/
