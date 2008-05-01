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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/Basics".

include "CoRN.ma".

(* $Id: Basics.v,v 1.7 2004/04/09 15:58:31 lcf Exp $ *)

(*#* printing alpha %\ensuremath{\alpha}% #&alpha;# *)

(*#* printing beta %\ensuremath{\beta}% #&beta;# *)

(*#* printing delta %\ensuremath{\delta}% #&delta;# *)

(*#* printing eps %\ensuremath{\varepsilon}% #&epsilon;# *)

(*#* printing phi %\ensuremath{\phi}% #&phi;# *)

(*#* printing eta %\ensuremath{\eta}% #&eta;# *)

(*#* printing omega %\ensuremath{\omega}% #&omega;# *)

(*#* printing nat %\ensuremath{\mathbb N}% #<b>N</b># *)

(*#* printing Z %\ensuremath{\mathbb Z}% #<b>Z</b># *)

include "algebra/ListType.ma".

(*#* *Basics
This is random stuff that should be in the Coq basic library.
*)

inline "cic:/CoRN/algebra/Basics/lt_le_dec.con".

inline "cic:/CoRN/algebra/Basics/lt_z_two.con".

inline "cic:/CoRN/algebra/Basics/le_pred.con".

inline "cic:/CoRN/algebra/Basics/lt_mult_right.con".

inline "cic:/CoRN/algebra/Basics/le_mult_right.con".

(*#* The power function does not exist in the standard library *)

inline "cic:/CoRN/algebra/Basics/power.con".

(*#* Factorial function. Does not exist in Arith.
Needed for special operations on polynomials. *)

inline "cic:/CoRN/algebra/Basics/fac.con".

inline "cic:/CoRN/algebra/Basics/nat_fac_gtzero.con".

(* needed for computational behavior of "Inversion" tactic *)

(* UNEXPORTED
Transparent sym_eq.
*)

(* UNEXPORTED
Transparent f_equal.
*)

(* NOTATION
Notation Pair := (pair (B:=_)).
*)

(* NOTATION
Notation Proj1 := (proj1 (B:=_)).
*)

(* NOTATION
Notation Proj2 := (proj2 (B:=_)).
*)

(* Following only needed in finite, but tha's now obsolete

Lemma deMorgan_or_and: (A,B,X:Prop)((A\/B)->X)->(A->X)/\(B->X).
Tauto.
Qed.

Lemma deMorgan_and_or: (A,B,X:Prop)(A->X)/\(B->X)->(A\/B->X).
Tauto.
Qed.

Lemma deMorgan_ex_all:
  (A:Set)(P:A->Prop)(X:Prop)((Ex P)->X)->(a:A)(P a)->X.
Intros. Apply H; Exists a; Assumption.
Qed.

Lemma deMorgan_all_ex:
  (A:Set)(P:A->Prop)(X:Prop)((a:A)(P a)->X)->(Ex P)->X.
Intros. Elim H0; Assumption.
Qed.

Implicit Arguments Off.

Three lemmas for proving properties about definitions made with case
distinction to a sumbool, i.e. [{A} + {B}].

Lemma sumbool_rec_or : (A,B:Prop)(S:Set)(l,r:S)(s:{A}+{B})
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = l \/
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = r.
Intros. Elim s.
Intros. Left. Reflexivity.
Intros. Right. Reflexivity.
Qed.
*)

inline "cic:/CoRN/algebra/Basics/not_r_sumbool_rec.con".

inline "cic:/CoRN/algebra/Basics/not_l_sumbool_rec.con".

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

(*#* **Some results about [Z]

We consider the injection [inject_nat] from [nat] to [Z] as a
coercion. *)

(* begin hide *)

coercion cic:/Coq/ZArith/BinInt/Z_of_nat.con 0 (* compounds *).

(* end hide *)

inline "cic:/CoRN/algebra/Basics/POS_anti_convert.con".

inline "cic:/CoRN/algebra/Basics/NEG_anti_convert.con".

inline "cic:/CoRN/algebra/Basics/lt_O_positive_to_nat.con".

inline "cic:/CoRN/algebra/Basics/anti_convert_pred_convert.con".

inline "cic:/CoRN/algebra/Basics/p_is_some_anti_convert.con".

inline "cic:/CoRN/algebra/Basics/convert_is_POS.con".

inline "cic:/CoRN/algebra/Basics/min_convert_is_NEG.con".

inline "cic:/CoRN/algebra/Basics/inject_nat_convert.con".

inline "cic:/CoRN/algebra/Basics/Z_exh.con".

inline "cic:/CoRN/algebra/Basics/nats_Z_ind.con".

inline "cic:/CoRN/algebra/Basics/pred_succ_Z_ind.con".

inline "cic:/CoRN/algebra/Basics/Zmult_minus_distr_r.con".

inline "cic:/CoRN/algebra/Basics/Zodd_Zeven_min1.con".

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

inline "cic:/CoRN/algebra/Basics/caseZ_diff.con".

(* begin hide *)

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

(* end hide *)

inline "cic:/CoRN/algebra/Basics/caseZ_diff_O.con".

inline "cic:/CoRN/algebra/Basics/caseZ_diff_Pos.con".

inline "cic:/CoRN/algebra/Basics/caseZ_diff_Neg.con".

inline "cic:/CoRN/algebra/Basics/proper_caseZ_diff.con".

inline "cic:/CoRN/algebra/Basics/diff_Z_ind.con".

inline "cic:/CoRN/algebra/Basics/Zlt_reg_mult_l.con".

inline "cic:/CoRN/algebra/Basics/Zlt_opp.con".

inline "cic:/CoRN/algebra/Basics/Zlt_conv_mult_l.con".

inline "cic:/CoRN/algebra/Basics/Zgt_not_eq.con".

inline "cic:/CoRN/algebra/Basics/Zmult_absorb.con".

(* UNEXPORTED
Section Well_foundedT
*)

alias id "A" = "cic:/CoRN/algebra/Basics/Well_foundedT/A.var".

alias id "R" = "cic:/CoRN/algebra/Basics/Well_foundedT/R.var".

(*#* The accessibility predicate is defined to be non-informative *)

inline "cic:/CoRN/algebra/Basics/Acc.ind".

(* UNEXPORTED
End Well_foundedT
*)

(* UNEXPORTED
Section AccT
*)

alias id "A" = "cic:/CoRN/algebra/Basics/AccT/A.var".

inline "cic:/CoRN/algebra/Basics/well_founded.con".

(* UNEXPORTED
End AccT
*)

(* UNEXPORTED
Implicit Arguments Acc [A].
*)

(* UNEXPORTED
Section IndT
*)

alias id "A" = "cic:/CoRN/algebra/Basics/IndT/A.var".

alias id "R" = "cic:/CoRN/algebra/Basics/IndT/R.var".

(* UNEXPORTED
Section AccIter
*)

alias id "P" = "cic:/CoRN/algebra/Basics/IndT/AccIter/P.var".

alias id "F" = "cic:/CoRN/algebra/Basics/IndT/AccIter/F.var".

inline "cic:/CoRN/algebra/Basics/Acc_inv.con".

inline "cic:/CoRN/algebra/Basics/Acc_iter.con".

(* UNEXPORTED
End AccIter
*)

alias id "Rwf" = "cic:/CoRN/algebra/Basics/IndT/Rwf.var".

inline "cic:/CoRN/algebra/Basics/well_founded_induction_type.con".

(* UNEXPORTED
End IndT
*)

(* UNEXPORTED
Section InductionT
*)

alias id "A" = "cic:/CoRN/algebra/Basics/InductionT/A.var".

alias id "f" = "cic:/CoRN/algebra/Basics/InductionT/f.var".

inline "cic:/CoRN/algebra/Basics/ltof.con".

inline "cic:/CoRN/algebra/Basics/well_founded_ltof.con".

inline "cic:/CoRN/algebra/Basics/induction_ltof2T.con".

(* UNEXPORTED
End InductionT
*)

(* UNEXPORTED
Section InductionTT
*)

inline "cic:/CoRN/algebra/Basics/lt_wf_rect.con".

(* UNEXPORTED
End InductionTT
*)

