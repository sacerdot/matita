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

set "baseuri" "cic:/matita/CoRN-Decl/model/structures/Qsec".

include "CoRN.ma".

(* $Id: Qsec.v,v 1.7 2004/04/08 08:20:35 lcf Exp $ *)

(*#* printing Q %\ensuremath{\mathbb{Q}}% *)

(*#* printing QZERO %\ensuremath{0_\mathbb{Q}}% #0<sub>Q</sub># *)

(*#* printing QONE %\ensuremath{1_\mathbb{Q}}% #1<sub>Q</sub># *)

(*#* printing QTWO %\ensuremath{2_\mathbb{Q}}% #2<sub>Q</sub># *)

(*#* printing QFOUR %\ensuremath{4_\mathbb{Q}}% #4<sub>Q</sub># *)

include "algebra/CLogic.ma".

include "model/structures/Zsec.ma".

(*#* *[Q]
**About [Q]
We define the structure of rational numbers as follows. First of all,
it consists of the set of rational numbers, defined as the set of
pairs $\langle a,n\rangle$#&lang;a,n&rang;# with [a:Z] and
[n:positive]. Intuitively, $\langle a,n\rangle$#&lang;a,n&rang;#
represents the rational number [a[/]n]. Then there is the equality on
[Q]: $\langle a,m\rangle=\langle
b,n\rangle$#&lang;a,m&rang;=&lang;b,n&rang;# iff [an [=] bm]. We
also define apartness, order, addition, multiplication, opposite,
inverse an de constants 0 and 1.  *)

(* UNEXPORTED
Section Q
*)

inline "cic:/CoRN/model/structures/Qsec/Q.ind".

inline "cic:/CoRN/model/structures/Qsec/Qeq.con".

inline "cic:/CoRN/model/structures/Qsec/Qap.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt.con".

inline "cic:/CoRN/model/structures/Qsec/Qplus.con".

inline "cic:/CoRN/model/structures/Qsec/Qmult.con".

inline "cic:/CoRN/model/structures/Qsec/Qopp.con".

inline "cic:/CoRN/model/structures/Qsec/QZERO.con".

inline "cic:/CoRN/model/structures/Qsec/QONE.con".

inline "cic:/CoRN/model/structures/Qsec/Qinv.con".

(* UNEXPORTED
End Q
*)

(* NOTATION
Infix "{=Q}" := Qeq (no associativity, at level 90).
*)

(* NOTATION
Infix "{#Q}" := Qap (no associativity, at level 90).
*)

(* NOTATION
Infix "{<Q}" := Qlt (no associativity, at level 90).
*)

(* NOTATION
Infix "{+Q}" := Qplus (no associativity, at level 85).
*)

(* NOTATION
Infix "{*Q}" := Qmult (no associativity, at level 80).
*)

(* NOTATION
Notation "{-Q}" := Qopp (at level 1, left associativity).
*)

(*#* ***Constants
*)

inline "cic:/CoRN/model/structures/Qsec/QTWO.con".

inline "cic:/CoRN/model/structures/Qsec/QFOUR.con".

(*#* ***Equality
Here we prove that [QONE] is #<i>#%\emph{%not equal%}%#</i># to [QZERO]: 
*)

inline "cic:/CoRN/model/structures/Qsec/ONEQ_neq_ZEROQ.con".

inline "cic:/CoRN/model/structures/Qsec/refl_Qeq.con".

inline "cic:/CoRN/model/structures/Qsec/sym_Qeq.con".

inline "cic:/CoRN/model/structures/Qsec/trans_Qeq.con".

(*#*
 The equality is decidable: 
*)

inline "cic:/CoRN/model/structures/Qsec/dec_Qeq.con".

(*#* ***Apartness
*)

inline "cic:/CoRN/model/structures/Qsec/Q_non_zero.con".

inline "cic:/CoRN/model/structures/Qsec/ap_Q_irreflexive0.con".

inline "cic:/CoRN/model/structures/Qsec/ap_Q_symmetric0.con".

inline "cic:/CoRN/model/structures/Qsec/ap_Q_cotransitive0.con".

inline "cic:/CoRN/model/structures/Qsec/ap_Q_tight0.con".

(*#* ***Addition
*)

inline "cic:/CoRN/model/structures/Qsec/Qplus_simpl.con".

(*#* 
 Addition is associative:
*)

inline "cic:/CoRN/model/structures/Qsec/Qplus_assoc.con".

(*#*
 [QZERO] as the neutral element for addition:
*)

inline "cic:/CoRN/model/structures/Qsec/QZERO_right.con".

(*#*
 Commutativity of addition:
*)

inline "cic:/CoRN/model/structures/Qsec/Qplus_sym.con".

inline "cic:/CoRN/model/structures/Qsec/Qplus_strext0.con".

inline "cic:/CoRN/model/structures/Qsec/ZEROQ_as_rht_unit0.con".

inline "cic:/CoRN/model/structures/Qsec/ZEROQ_as_lft_unit0.con".

inline "cic:/CoRN/model/structures/Qsec/Qplus_is_commut0.con".

(*#* ***Opposite
 [{-Q}] is a well defined unary operation: 
*)

inline "cic:/CoRN/model/structures/Qsec/Qopp_simpl.con".

(*#*
 The group equation for [{-Q}]
*)

inline "cic:/CoRN/model/structures/Qsec/Qplus_inverse_r.con".

(*#* ***Multiplication
Next we shall prove the properties of multiplication. First we prove
that [{*Q}] is well-defined
*)

inline "cic:/CoRN/model/structures/Qsec/Qmult_simpl.con".

(*#*
 and it is associative:
*)

inline "cic:/CoRN/model/structures/Qsec/Qmult_assoc.con".

(*#*
 [QONE] is the neutral element for multiplication:
*)

inline "cic:/CoRN/model/structures/Qsec/Qmult_n_1.con".

(*#*
 The commutativity for [{*Q}]:
*)

inline "cic:/CoRN/model/structures/Qsec/Qmult_sym.con".

inline "cic:/CoRN/model/structures/Qsec/Qmult_plus_distr_r.con".

(*#*
 And a property of multiplication which says if [x [~=] Zero] and [xy [=] Zero] then [y [=] Zero]:
*)

inline "cic:/CoRN/model/structures/Qsec/Qmult_eq.con".

inline "cic:/CoRN/model/structures/Qsec/Qmult_strext0.con".

inline "cic:/CoRN/model/structures/Qsec/nonZero.con".

(*#* ***Inverse
*)

inline "cic:/CoRN/model/structures/Qsec/Qinv_strext.con".

inline "cic:/CoRN/model/structures/Qsec/Qinv_is_inv.con".

(*#* ***Less-than
*)

inline "cic:/CoRN/model/structures/Qsec/Qlt_wd_right.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_wd_left.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_eq_gt_dec.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_is_transitive_unfolded.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_strext_unfolded.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_is_irreflexive_unfolded.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_is_antisymmetric_unfolded.con".

inline "cic:/CoRN/model/structures/Qsec/Qplus_resp_Qlt.con".

inline "cic:/CoRN/model/structures/Qsec/Qmult_resp_pos_Qlt.con".

inline "cic:/CoRN/model/structures/Qsec/Qlt_gives_apartness.con".

(*#* ***Miscellaneous
We consider the injection [inject_Z] from [Z] to [Q] as a coercion.
*)

inline "cic:/CoRN/model/structures/Qsec/inject_Z.con".

coercion cic:/matita/CoRN-Decl/model/structures/Qsec/inject_Z.con 0 (* compounds *).

inline "cic:/CoRN/model/structures/Qsec/injz_plus.con".

inline "cic:/CoRN/model/structures/Qsec/injZ_One.con".

(*#* We can always find a natural number that is bigger than a given rational
number.
*)

inline "cic:/CoRN/model/structures/Qsec/Q_is_archemaedian0.con".

