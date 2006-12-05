(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/CoRN-Decl/model/structures/Zsec".

include "CoRN.ma".

(* $Id: Zsec.v,v 1.5 2004/04/06 15:46:05 lcf Exp $ *)

(*#* printing {#Z} %\ensuremath{\mathrel\#_{\mathbb Z}}% *)

include "algebra/CLogic.ma".

(*#* *[Z]
** About [Z]
We consider the implementation of integers as signed binary sequences (the 
datatype [Z] as defined in [ZArith], in the standard library).

***Apartness
We define the apartness as the negation of the Leibniz equality:
*)

inline "cic:/CoRN/model/structures/Zsec/ap_Z.con".

(* NOTATION
Infix "{#Z}" := ap_Z (no associativity, at level 90).
*)

(*#* Some properties of apartness:
*)

inline "cic:/CoRN/model/structures/Zsec/ap_Z_irreflexive0.con".

inline "cic:/CoRN/model/structures/Zsec/ap_Z_symmetric0.con".

inline "cic:/CoRN/model/structures/Zsec/ap_Z_cotransitive0.con".

inline "cic:/CoRN/model/structures/Zsec/ap_Z_tight0.con".

inline "cic:/CoRN/model/structures/Zsec/ONE_neq_O.con".

(*#* ***Addition
Some properties of the addition. [Zplus] is also defined in the standard 
library.
*)

inline "cic:/CoRN/model/structures/Zsec/Zplus_wd0.con".

inline "cic:/CoRN/model/structures/Zsec/Zplus_strext0.con".

(*#* ***Multiplication
The multiplication is extensional:
*)

inline "cic:/CoRN/model/structures/Zsec/Zmult_strext0.con".

(*#* ***Miscellaneous
*)

inline "cic:/CoRN/model/structures/Zsec/Zpos.con".

(* begin hide *)

coercion cic:/Coq/ZArith/BinInt/Z.ind#xpointer(1/1/2) 0 (* compounds *).

(* end hide *)

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma1.con".

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma2.con".

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma3.con".

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma4.con".

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma5.con".

inline "cic:/CoRN/model/structures/Zsec/Zpos_pos.con".

inline "cic:/CoRN/model/structures/Zsec/Zpos_neg.con".

inline "cic:/CoRN/model/structures/Zsec/Zpos_Zsgn.con".

inline "cic:/CoRN/model/structures/Zsec/Zpos_Zsgn2.con".

inline "cic:/CoRN/model/structures/Zsec/a_very_specific_lemma5'.con".

