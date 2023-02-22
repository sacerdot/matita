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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CRings".

include "CoRN.ma".

(* $Id: CRings.v,v 1.8 2004/04/23 10:00:53 lcf Exp $ *)

(*#* printing [*] %\ensuremath\times% #&times;# *)

(*#* printing [^] %\ensuremath{\hat{\ }}% #^# *)

(*#* printing {*} %\ensuremath\times% #&times;# *)

(*#* printing {**} %\ensuremath\ast% #&lowast;# *)

(*#* printing {^} %\ensuremath{\hat{\ }}% #^# *)

(*#* printing One %\ensuremath{\mathbf1}% #1# *)

(*#* printing Two %\ensuremath{\mathbf2}% #2# *)

(*#* printing Three %\ensuremath{\mathbf3}% #3# *)

(*#* printing Four %\ensuremath{\mathbf4}% #4# *)

(*#* printing Six %\ensuremath{\mathbf6}% #6# *)

(*#* printing Eight %\ensuremath{\mathbf8}% #8# *)

(*#* printing Nine %\ensuremath{\mathbf9}% #9# *)

(*#* printing Twelve %\ensuremath{\mathbf{12}}% #12# *)

(*#* printing Sixteen %\ensuremath{\mathbf{16}}% #16# *)

(*#* printing Eighteen %\ensuremath{\mathbf{18}}% #18# *)

(*#* printing TwentyFour %\ensuremath{\mathbf{24}}% #24# *)

(*#* printing FortyEight %\ensuremath{\mathbf{48}}% #48# *)

include "algebra/CSums.ma".

(* UNEXPORTED
Transparent sym_eq.
*)

(* UNEXPORTED
Transparent f_equal.
*)

(* Begin_SpecReals *)

(* Constructive RINGS *)

(*#* * Rings
We actually define commutative rings with identity.
** Definition of the notion of Ring
*)

inline "cic:/CoRN/algebra/CRings/distributive.con".

(* UNEXPORTED
Implicit Arguments distributive [S].
*)

inline "cic:/CoRN/algebra/CRings/is_CRing.ind".

inline "cic:/CoRN/algebra/CRings/CRing.ind".

coercion cic:/matita/CoRN-Decl/algebra/CRings/cr_crr.con 0 (* compounds *).

inline "cic:/CoRN/algebra/CRings/cr_plus.con".

inline "cic:/CoRN/algebra/CRings/cr_inv.con".

inline "cic:/CoRN/algebra/CRings/cr_minus.con".

(* NOTATION
Notation One := (cr_one _).
*)

(* End_SpecReals *)

(* Begin_SpecReals *)

(*#*
%\begin{nameconvention}%
In the names of lemmas, we will denote [One] with [one],
and [[*]] with [mult].
%\end{nameconvention}%
*)

(* UNEXPORTED
Implicit Arguments cr_mult [c].
*)

(* NOTATION
Infix "[*]" := cr_mult (at level 40, left associativity).
*)

(* UNEXPORTED
Section CRing_axioms
*)

(*#*
** Ring axioms
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/CRing_axioms/R.var".

inline "cic:/CoRN/algebra/CRings/CRing_is_CRing.con".

inline "cic:/CoRN/algebra/CRings/mult_assoc.con".

inline "cic:/CoRN/algebra/CRings/mult_commutes.con".

inline "cic:/CoRN/algebra/CRings/mult_mon.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CRings/dist.con".

inline "cic:/CoRN/algebra/CRings/ring_non_triv.con".

inline "cic:/CoRN/algebra/CRings/mult_wd.con".

inline "cic:/CoRN/algebra/CRings/mult_wdl.con".

inline "cic:/CoRN/algebra/CRings/mult_wdr.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End CRing_axioms
*)

(* UNEXPORTED
Section Ring_constructions
*)

(*#*
** Ring constructions
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/Ring_constructions/R.var".

(*#*
The multiplicative monoid of a ring is defined as follows.
*)

inline "cic:/CoRN/algebra/CRings/Build_multCMonoid.con".

(* UNEXPORTED
End Ring_constructions
*)

(* End_SpecReals *)

(* UNEXPORTED
Section Ring_unfolded
*)

(*#*
** Ring unfolded
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/Ring_unfolded/R.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CRings/Ring_unfolded/mmR.con" "Ring_unfolded__".

(* end hide *)

inline "cic:/CoRN/algebra/CRings/mult_assoc_unfolded.con".

inline "cic:/CoRN/algebra/CRings/mult_commut_unfolded.con".

(* UNEXPORTED
Hint Resolve mult_commut_unfolded: algebra.
*)

inline "cic:/CoRN/algebra/CRings/mult_one.con".

inline "cic:/CoRN/algebra/CRings/one_mult.con".

inline "cic:/CoRN/algebra/CRings/ring_dist_unfolded.con".

(* UNEXPORTED
Hint Resolve ring_dist_unfolded: algebra.
*)

inline "cic:/CoRN/algebra/CRings/ring_distl_unfolded.con".

(* UNEXPORTED
End Ring_unfolded
*)

(* UNEXPORTED
Hint Resolve mult_assoc_unfolded: algebra.
*)

(* UNEXPORTED
Hint Resolve ring_non_triv mult_one one_mult mult_commut_unfolded: algebra.
*)

(* UNEXPORTED
Hint Resolve ring_dist_unfolded ring_distl_unfolded: algebra.
*)

(* UNEXPORTED
Section Ring_basics
*)

(*#*
** Ring basics
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/Ring_basics/R.var".

inline "cic:/CoRN/algebra/CRings/one_ap_zero.con".

inline "cic:/CoRN/algebra/CRings/is_zero_rht.con".

inline "cic:/CoRN/algebra/CRings/is_zero_lft.con".

(* UNEXPORTED
Implicit Arguments is_zero_rht [S].
*)

(* UNEXPORTED
Implicit Arguments is_zero_lft [S].
*)

inline "cic:/CoRN/algebra/CRings/cring_mult_zero.con".

(* UNEXPORTED
Hint Resolve cring_mult_zero: algebra.
*)

inline "cic:/CoRN/algebra/CRings/x_mult_zero.con".

inline "cic:/CoRN/algebra/CRings/cring_mult_zero_op.con".

(* UNEXPORTED
Hint Resolve cring_mult_zero_op: algebra.
*)

inline "cic:/CoRN/algebra/CRings/cring_inv_mult_lft.con".

(* UNEXPORTED
Hint Resolve cring_inv_mult_lft: algebra.
*)

inline "cic:/CoRN/algebra/CRings/cring_inv_mult_rht.con".

(* UNEXPORTED
Hint Resolve cring_inv_mult_rht: algebra.
*)

inline "cic:/CoRN/algebra/CRings/cring_mult_ap_zero.con".

inline "cic:/CoRN/algebra/CRings/cring_mult_ap_zero_op.con".

inline "cic:/CoRN/algebra/CRings/inv_mult_invol.con".

inline "cic:/CoRN/algebra/CRings/ring_dist_minus.con".

(* UNEXPORTED
Hint Resolve ring_dist_minus: algebra.
*)

inline "cic:/CoRN/algebra/CRings/ring_distl_minus.con".

(* UNEXPORTED
Hint Resolve ring_distl_minus: algebra.
*)

(* UNEXPORTED
End Ring_basics
*)

(* UNEXPORTED
Hint Resolve cring_mult_zero cring_mult_zero_op: algebra.
*)

(* UNEXPORTED
Hint Resolve inv_mult_invol: algebra.
*)

(* UNEXPORTED
Hint Resolve cring_inv_mult_lft cring_inv_mult_rht: algebra.
*)

(* UNEXPORTED
Hint Resolve ring_dist_minus: algebra.
*)

(* UNEXPORTED
Hint Resolve ring_distl_minus: algebra.
*)

(* Begin_SpecReals *)

(*#*
** Ring Definitions
Some auxiliary functions and operations over a ring;
especially geared towards CReals.
*)

(* UNEXPORTED
Section exponentiation
*)

(*#*
*** Exponentiation
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/exponentiation/R.var".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CRings/nexp.con".

inline "cic:/CoRN/algebra/CRings/nexp_well_def.con".

inline "cic:/CoRN/algebra/CRings/nexp_strong_ext.con".

inline "cic:/CoRN/algebra/CRings/nexp_op.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End exponentiation
*)

(* End_SpecReals *)

(* NOTATION
Notation "x [^] n" := (nexp_op _ n x) (at level 20).
*)

(* UNEXPORTED
Implicit Arguments nexp_op [R].
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Section nat_injection
*)

(*#*
*** The injection of natural numbers into a ring
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/nat_injection/R.var".

(*#*
The injection of Coq natural numbers into a ring is called [nring].
Note that this need not really be an injection; when it is, the ring is said
to have characteristic [0].
*)

inline "cic:/CoRN/algebra/CRings/nring.con".

inline "cic:/CoRN/algebra/CRings/Char0.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CRings/nring_comm_plus.con".

inline "cic:/CoRN/algebra/CRings/nring_comm_mult.con".

(* Begin_SpecReals *)

(* UNEXPORTED
End nat_injection
*)

(* End_SpecReals *)

(* UNEXPORTED
Hint Resolve nring_comm_plus nring_comm_mult: algebra.
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Implicit Arguments nring [R].
*)

(* End_SpecReals *)

(* NOTATION
Notation Two := (nring 2).
*)

(* NOTATION
Notation Three := (nring 3).
*)

(* NOTATION
Notation Four := (nring 4).
*)

(* NOTATION
Notation Six := (nring 6).
*)

(* NOTATION
Notation Eight := (nring 8).
*)

(* NOTATION
Notation Twelve := (nring 12).
*)

(* NOTATION
Notation Sixteen := (nring 16).
*)

(* NOTATION
Notation Nine := (nring 9).
*)

(* NOTATION
Notation Eighteen := (nring 18).
*)

(* NOTATION
Notation TwentyFour := (nring 24).
*)

(* NOTATION
Notation FortyEight := (nring 48).
*)

inline "cic:/CoRN/algebra/CRings/one_plus_one.con".

inline "cic:/CoRN/algebra/CRings/x_plus_x.con".

(* UNEXPORTED
Hint Resolve one_plus_one x_plus_x: algebra.
*)

(*#*
In a ring of characteristic zero, [nring] is really an injection.
*)

inline "cic:/CoRN/algebra/CRings/nring_different.con".

(* UNEXPORTED
Section int_injection
*)

(*#*
*** The injection of integers into a ring
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/int_injection/R.var".

(*#*
The injection of Coq integers into a ring is called [zring]. Again,
this need not really be an injection.

The first definition is now obsolete, having been replaced by a more efficient
one. It is kept to avoid having to redo all the proofs.
*)

inline "cic:/CoRN/algebra/CRings/zring_old.con".

inline "cic:/CoRN/algebra/CRings/zring_old_zero.con".

(* UNEXPORTED
Hint Resolve zring_old_zero: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_diff.con".

(* UNEXPORTED
Hint Resolve zring_old_diff.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_plus_nat.con".

(* UNEXPORTED
Hint Resolve zring_old_plus_nat: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_inv_nat.con".

(* UNEXPORTED
Hint Resolve zring_old_inv_nat: algebra.
*)

(* UNEXPORTED
Hint Resolve zring_old_diff: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_plus.con".

(* UNEXPORTED
Hint Resolve zring_old_plus: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_inv.con".

(* UNEXPORTED
Hint Resolve zring_old_inv: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_minus.con".

(* UNEXPORTED
Hint Resolve zring_old_minus: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_mult.con".

(* UNEXPORTED
Hint Resolve zring_old_mult: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_one.con".

(* UNEXPORTED
Hint Resolve zring_old_one: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_old_inv_one.con".

(*#************** new def of zring. ***********************)

(*#* The [zring] function can be defined directly.  This is done here.
*)

inline "cic:/CoRN/algebra/CRings/pring_aux.con".

inline "cic:/CoRN/algebra/CRings/pring.con".

inline "cic:/CoRN/algebra/CRings/zring.con".

inline "cic:/CoRN/algebra/CRings/pring_aux_lemma.con".

inline "cic:/CoRN/algebra/CRings/double_nring.con".

(* UNEXPORTED
Hint Resolve pring_aux_lemma double_nring: algebra.
*)

inline "cic:/CoRN/algebra/CRings/pring_aux_nring.con".

(* UNEXPORTED
Hint Resolve pring_aux_nring: algebra.
*)

inline "cic:/CoRN/algebra/CRings/pring_convert.con".

(* UNEXPORTED
Hint Resolve pring_convert: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_zring_old.con".

(* UNEXPORTED
Hint Resolve zring_zring_old: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zring_zero.con".

inline "cic:/CoRN/algebra/CRings/zring_diff.con".

inline "cic:/CoRN/algebra/CRings/zring_plus_nat.con".

inline "cic:/CoRN/algebra/CRings/zring_inv_nat.con".

inline "cic:/CoRN/algebra/CRings/zring_plus.con".

inline "cic:/CoRN/algebra/CRings/zring_inv.con".

inline "cic:/CoRN/algebra/CRings/zring_minus.con".

inline "cic:/CoRN/algebra/CRings/zring_mult.con".

inline "cic:/CoRN/algebra/CRings/zring_one.con".

inline "cic:/CoRN/algebra/CRings/zring_inv_one.con".

(* UNEXPORTED
End int_injection
*)

(* UNEXPORTED
Implicit Arguments zring [R].
*)

(* UNEXPORTED
Hint Resolve pring_convert zring_zero zring_diff zring_plus_nat zring_inv_nat
  zring_plus zring_inv zring_minus zring_mult zring_one zring_inv_one:
  algebra.
*)

(* UNEXPORTED
Section Ring_sums
*)

(*#*
** Ring sums
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/Ring_sums/R.var".

(*#*
*** Infinite Ring sums
*)

(* UNEXPORTED
Section infinite_ring_sums
*)

inline "cic:/CoRN/algebra/CRings/Sum_upto.con".

inline "cic:/CoRN/algebra/CRings/sum_upto_O.con".

inline "cic:/CoRN/algebra/CRings/Sum_from_upto.con".

(*#*
Here's an alternative def of [Sum_from_upto], with a lemma that
it's equivalent to the original.
*)

inline "cic:/CoRN/algebra/CRings/seq_from.con".

inline "cic:/CoRN/algebra/CRings/Sum_from_upto_alt.con".

(* UNEXPORTED
End infinite_ring_sums
*)

(* UNEXPORTED
Section ring_sums_over_lists
*)

(*#* *** Ring Sums over Lists
*)

inline "cic:/CoRN/algebra/CRings/RList_Mem.con".

inline "cic:/CoRN/algebra/CRings/List_Sum_upto.con".

inline "cic:/CoRN/algebra/CRings/list_sum_upto_O.con".

inline "cic:/CoRN/algebra/CRings/List_Sum_from_upto.con".

(* UNEXPORTED
End ring_sums_over_lists
*)

(* UNEXPORTED
End Ring_sums
*)

(*#*
** Distribution properties
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

(* UNEXPORTED
Section Dist_properties
*)

alias id "R" = "cic:/CoRN/algebra/CRings/Dist_properties/R.var".

inline "cic:/CoRN/algebra/CRings/dist_1b.con".

(* UNEXPORTED
Hint Resolve dist_1b: algebra.
*)

inline "cic:/CoRN/algebra/CRings/dist_2a.con".

(* UNEXPORTED
Hint Resolve dist_2a: algebra.
*)

inline "cic:/CoRN/algebra/CRings/dist_2b.con".

(* UNEXPORTED
Hint Resolve dist_2b: algebra.
*)

inline "cic:/CoRN/algebra/CRings/mult_distr_sum0_lft.con".

(* UNEXPORTED
Hint Resolve mult_distr_sum0_lft.
*)

inline "cic:/CoRN/algebra/CRings/mult_distr_sum_lft.con".

(* UNEXPORTED
Hint Resolve mult_distr_sum_lft: algebra.
*)

inline "cic:/CoRN/algebra/CRings/mult_distr_sum_rht.con".

inline "cic:/CoRN/algebra/CRings/sumx_const.con".

(* UNEXPORTED
End Dist_properties
*)

(* UNEXPORTED
Hint Resolve dist_1b dist_2a dist_2b mult_distr_sum_lft mult_distr_sum_rht
  sumx_const: algebra.
*)

(*#*
** Properties of exponentiation (with the exponent in [nat])
%\begin{convention}%
Let [R] be a ring.
%\end{convention}%
*)

(* UNEXPORTED
Section NExp_properties
*)

alias id "R" = "cic:/CoRN/algebra/CRings/NExp_properties/R.var".

inline "cic:/CoRN/algebra/CRings/nexp_wd.con".

inline "cic:/CoRN/algebra/CRings/nexp_strext.con".

inline "cic:/CoRN/algebra/CRings/nexp_Sn.con".

(* UNEXPORTED
Hint Resolve nexp_wd nexp_Sn: algebra.
*)

inline "cic:/CoRN/algebra/CRings/nexp_plus.con".

(* UNEXPORTED
Hint Resolve nexp_plus: algebra.
*)

inline "cic:/CoRN/algebra/CRings/one_nexp.con".

(* UNEXPORTED
Hint Resolve one_nexp: algebra.
*)

inline "cic:/CoRN/algebra/CRings/mult_nexp.con".

(* UNEXPORTED
Hint Resolve mult_nexp: algebra.
*)

inline "cic:/CoRN/algebra/CRings/nexp_mult.con".

(* UNEXPORTED
Hint Resolve nexp_mult: algebra.
*)

inline "cic:/CoRN/algebra/CRings/zero_nexp.con".

(* UNEXPORTED
Hint Resolve zero_nexp: algebra.
*)

inline "cic:/CoRN/algebra/CRings/inv_nexp_even.con".

(* UNEXPORTED
Hint Resolve inv_nexp_even: algebra.
*)

inline "cic:/CoRN/algebra/CRings/inv_nexp_two.con".

(* UNEXPORTED
Hint Resolve inv_nexp_two: algebra.
*)

inline "cic:/CoRN/algebra/CRings/inv_nexp_odd.con".

(* UNEXPORTED
Hint Resolve inv_nexp_odd: algebra.
*)

inline "cic:/CoRN/algebra/CRings/nexp_one.con".

(* UNEXPORTED
Hint Resolve nexp_one: algebra.
*)

inline "cic:/CoRN/algebra/CRings/nexp_two.con".

(* UNEXPORTED
Hint Resolve nexp_two: algebra.
*)

inline "cic:/CoRN/algebra/CRings/inv_one_even_nexp.con".

(* UNEXPORTED
Hint Resolve inv_one_even_nexp: algebra.
*)

inline "cic:/CoRN/algebra/CRings/inv_one_odd_nexp.con".

(* UNEXPORTED
Hint Resolve inv_one_odd_nexp: algebra.
*)

inline "cic:/CoRN/algebra/CRings/square_plus.con".

inline "cic:/CoRN/algebra/CRings/square_minus.con".

inline "cic:/CoRN/algebra/CRings/nexp_funny.con".

(* UNEXPORTED
Hint Resolve nexp_funny: algebra.
*)

inline "cic:/CoRN/algebra/CRings/nexp_funny'.con".

(* UNEXPORTED
Hint Resolve nexp_funny': algebra.
*)

(* UNEXPORTED
End NExp_properties
*)

(* UNEXPORTED
Hint Resolve nexp_wd nexp_Sn nexp_plus one_nexp mult_nexp nexp_mult zero_nexp
  inv_nexp_even inv_nexp_two inv_nexp_odd nexp_one nexp_two nexp_funny
  inv_one_even_nexp inv_one_odd_nexp nexp_funny' one_nexp square_plus
  square_minus: algebra.
*)

(* UNEXPORTED
Section CRing_Ops
*)

(*#*
** Functional Operations

Now for partial functions.

%\begin{convention}%
Let [R] be a ring and let [F,G:(PartFunct R)] with predicates
respectively [P] and [Q].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CRings/CRing_Ops/R.var".

alias id "F" = "cic:/CoRN/algebra/CRings/CRing_Ops/F.var".

alias id "G" = "cic:/CoRN/algebra/CRings/CRing_Ops/G.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CRings/CRing_Ops/P.con" "CRing_Ops__".

inline "cic:/CoRN/algebra/CRings/CRing_Ops/Q.con" "CRing_Ops__".

(* end hide *)

(* UNEXPORTED
Section Part_Function_Mult
*)

inline "cic:/CoRN/algebra/CRings/part_function_mult_strext.con".

inline "cic:/CoRN/algebra/CRings/Fmult.con".

(* UNEXPORTED
End Part_Function_Mult
*)

(* UNEXPORTED
Section Part_Function_Nth_Power
*)

alias id "n" = "cic:/CoRN/algebra/CRings/CRing_Ops/Part_Function_Nth_Power/n.var".

inline "cic:/CoRN/algebra/CRings/part_function_nth_strext.con".

inline "cic:/CoRN/algebra/CRings/Fnth.con".

(* UNEXPORTED
End Part_Function_Nth_Power
*)

(*#*
%\begin{convention}% Let [R':R->CProp].
%\end{convention}%
*)

alias id "R'" = "cic:/CoRN/algebra/CRings/CRing_Ops/R'.var".

inline "cic:/CoRN/algebra/CRings/included_FMult.con".

inline "cic:/CoRN/algebra/CRings/included_FMult'.con".

inline "cic:/CoRN/algebra/CRings/included_FMult''.con".

alias id "n" = "cic:/CoRN/algebra/CRings/CRing_Ops/n.var".

inline "cic:/CoRN/algebra/CRings/included_FNth.con".

inline "cic:/CoRN/algebra/CRings/included_FNth'.con".

(* UNEXPORTED
End CRing_Ops
*)

inline "cic:/CoRN/algebra/CRings/Fscalmult.con".

(* UNEXPORTED
Implicit Arguments Fmult [R].
*)

(* NOTATION
Infix "{*}" := Fmult (at level 40, left associativity).
*)

(* UNEXPORTED
Implicit Arguments Fscalmult [R].
*)

(* NOTATION
Infix "{**}" := Fscalmult (at level 40, left associativity).
*)

(* UNEXPORTED
Implicit Arguments Fnth [R].
*)

(* NOTATION
Infix "{^}" := Fnth (at level 30, right associativity).
*)

(* UNEXPORTED
Section ScalarMultiplication
*)

alias id "R" = "cic:/CoRN/algebra/CRings/ScalarMultiplication/R.var".

alias id "F" = "cic:/CoRN/algebra/CRings/ScalarMultiplication/F.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CRings/ScalarMultiplication/P.con" "ScalarMultiplication__".

(* end hide *)

alias id "R'" = "cic:/CoRN/algebra/CRings/ScalarMultiplication/R'.var".

inline "cic:/CoRN/algebra/CRings/included_FScalMult.con".

inline "cic:/CoRN/algebra/CRings/included_FScalMult'.con".

(* UNEXPORTED
End ScalarMultiplication
*)

(* UNEXPORTED
Hint Resolve included_FMult included_FScalMult included_FNth : included.
*)

(* UNEXPORTED
Hint Immediate included_FMult' included_FMult'' included_FScalMult'
    included_FNth' : included.
*)

