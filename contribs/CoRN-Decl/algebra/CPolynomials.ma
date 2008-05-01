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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CPolynomials".

include "CoRN.ma".

(* $Id: CPolynomials.v,v 1.9 2004/04/23 10:00:53 lcf Exp $ *)

(*#* printing _X_ %\ensuremath{x}% *)

(*#* printing _C_ %\ensuremath\diamond% *)

(*#* printing [+X*] %\ensuremath{+x\times}% #+x&times;# *)

(*#* printing RX %\ensuremath{R[x]}% #R[x]# *)

(*#* printing FX %\ensuremath{F[x]}% #F[x]# *)

include "tactics/RingReflection.ma".

(*#* * Polynomials
The first section only proves the polynomials form a ring, and nothing more
interesting.
Section%~\ref{section:poly-equality}% gives some basic properties of
equality and induction of polynomials.
** Definition of polynomials; they form a ring
%\label{section:poly-ring}%
*)

(* UNEXPORTED
Section CPoly_CRing
*)

(*#*
%\begin{convention}% Let [CR] be a ring.
%\end{convention}%
*)

alias id "CR" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing/CR.var".

(*#*
The intuition behind the type [cpoly] is the following
- [(cpoly CR)] is $CR[X]$ #CR[X]#;
- [cpoly_zero] is the `empty' polynomial with no coefficients;
- [(cpoly_linear c p)] is [c[+]X[*]p]

*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly.ind".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_constant.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_one.con".

(*#*
Some useful induction lemmas for doubly quantified propositions.
*)

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_ind0.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_sym_ind0.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_ind0'.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_ind0.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_sym_ind0.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_ind0'.con".

(*#* *** The polynomials form a setoid
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_eq_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_eq.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_eq_p_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_ap_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_ap_p_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/irreflexive_cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/symmetric_cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/cotransitive_cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/tight_apart_cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_is_CSetoid.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_csetoid.con".

(*#*
Now that we know that the polynomials form a setoid, we can use the
notation with [ [#] ] and [ [=] ]. In order to use this notation,
we introduce [cpoly_zero_cs] and [cpoly_linear_cs], so that Coq
recognizes we are talking about a setoid.
We formulate the induction properties and
the most basic properties of equality and apartness
in terms of these generators.
*)

inline "cic:/CoRN/algebra/CPolynomials/CPoly_CRing/cpoly_zero_cs.con" "CPoly_CRing__".

inline "cic:/CoRN/algebra/CPolynomials/CPoly_CRing/cpoly_linear_cs.con" "CPoly_CRing__".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_ind_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_ind0_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_sym_ind0_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_ind_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_ind0_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_sym_ind0_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_eq_zero_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_lin_eq_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_eq_lin_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_zero_eq_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_eq_lin_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_lin_eq_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_ap_zero_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_lin_ap_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_ap_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_ap_lin_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_zero_ap_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_ap_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_ap_lin_.con".

inline "cic:/CoRN/algebra/CPolynomials/_cpoly_lin_ap_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_ap_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_linear_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_linear_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_linear_fun.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_triple_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_triple_comp_ind.con".

(*#*
*** The polynomials form a semi-group and a monoid
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_plus.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_plus_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_commutative.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_q_ap_q.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_p_plus_ap_p.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_ap_zero_plus.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_op_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_op_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_op.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_plus_associative.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_csemi_grp.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cm_proof.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cmonoid.con".

(*#* *** The polynomials form a group
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_op_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_op_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_inv_op.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cg_proof.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cgroup.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cag_proof.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cabgroup.con".

(*#* *** The polynomials form a ring
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_mult_cr.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_mult_cr.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cs.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_zero_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_op_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_op_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_op.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_dist.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cr_dist.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_assoc_mult_cr.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_assoc_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_lin.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_commutative.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_dist_rht.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_assoc.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_cr_one.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_one_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_one.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_mult_monoid.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cr_non_triv.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_is_CRing.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_cring.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_constant_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_constant_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/_C_.con".

inline "cic:/CoRN/algebra/CPolynomials/_X_.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_x_minus_c.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_x_minus_c_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_x_minus_c_wd.con".

(* UNEXPORTED
End CPoly_CRing
*)

(* UNEXPORTED
Implicit Arguments _C_ [CR].
*)

(* UNEXPORTED
Implicit Arguments _X_ [CR].
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_linear_fun'.con".

(* UNEXPORTED
Implicit Arguments cpoly_linear_fun' [CR].
*)

(* NOTATION
Infix "[+X*]" := cpoly_linear_fun' (at level 50, left associativity).
*)

(*#* ** Apartness, equality, and induction
%\label{section:poly-equality}%
*)

(* UNEXPORTED
Section CPoly_CRing_ctd
*)

(*#*
%\begin{convention}%
Let [CR] be a ring, [p] and [q] polynomials over that ring, and [c] and [d]
elements of the ring.
%\end{convention}%
*)

alias id "CR" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing_ctd/CR.var".

(* NOTATION
Notation RX := (cpoly_cring CR).
*)

(* UNEXPORTED
Section helpful_section
*)

alias id "p" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing_ctd/helpful_section/p.var".

alias id "q" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing_ctd/helpful_section/q.var".

alias id "c" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing_ctd/helpful_section/c.var".

alias id "d" = "cic:/CoRN/algebra/CPolynomials/CPoly_CRing_ctd/helpful_section/d.var".

inline "cic:/CoRN/algebra/CPolynomials/linear_eq_zero_.con".

inline "cic:/CoRN/algebra/CPolynomials/_linear_eq_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/zero_eq_linear_.con".

inline "cic:/CoRN/algebra/CPolynomials/_zero_eq_linear.con".

inline "cic:/CoRN/algebra/CPolynomials/linear_eq_linear_.con".

inline "cic:/CoRN/algebra/CPolynomials/_linear_eq_linear.con".

inline "cic:/CoRN/algebra/CPolynomials/linear_ap_zero_.con".

inline "cic:/CoRN/algebra/CPolynomials/_linear_ap_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/linear_ap_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/zero_ap_linear_.con".

inline "cic:/CoRN/algebra/CPolynomials/_zero_ap_linear.con".

inline "cic:/CoRN/algebra/CPolynomials/zero_ap_linear.con".

inline "cic:/CoRN/algebra/CPolynomials/linear_ap_linear_.con".

inline "cic:/CoRN/algebra/CPolynomials/_linear_ap_linear.con".

inline "cic:/CoRN/algebra/CPolynomials/linear_ap_linear.con".

(* UNEXPORTED
End helpful_section
*)

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_induc.con".

inline "cic:/CoRN/algebra/CPolynomials/Ccpoly_double_sym_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/Cpoly_double_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/Cpoly_triple_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_induc.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_sym_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/poly_double_comp_ind.con".

inline "cic:/CoRN/algebra/CPolynomials/poly_triple_comp_ind.con".

(* UNEXPORTED
Transparent cpoly_cring.
*)

(* UNEXPORTED
Transparent cpoly_cgroup.
*)

(* UNEXPORTED
Transparent cpoly_csetoid.
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_apply_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_apply_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_apply_fun.con".

(* UNEXPORTED
End CPoly_CRing_ctd
*)

(*#*
%\begin{convention}%
[cpoly_apply_fun] is denoted infix by [!]
The first argument is left implicit, so the application of
polynomial [f] (seen as a function) to argument [x] can be written as [f!x].
In the names of lemmas, we write [apply].
%\end{convention}%
*)

(* UNEXPORTED
Implicit Arguments cpoly_apply_fun [CR].
*)

(* NOTATION
Infix "!" := cpoly_apply_fun (at level 1, no associativity).
*)

(*#*
** Basic properties of polynomials
%\begin{convention}%
Let [R] be a ring and write [RX] for the ring of polynomials over [R].
%\end{convention}%
*)

(* UNEXPORTED
Section Poly_properties
*)

alias id "R" = "cic:/CoRN/algebra/CPolynomials/Poly_properties/R.var".

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(*#*
*** Constant and identity
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_X_.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_C_.con".

(* UNEXPORTED
Hint Resolve cpoly_X_ cpoly_C_: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_const_eq.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_one.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_mult.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_lin.con".

(* UNEXPORTED
Hint Resolve cpoly_lin: algebra.
*)

(* SUPERFLUOUS *)

inline "cic:/CoRN/algebra/CPolynomials/poly_linear.con".

(* UNEXPORTED
Hint Resolve _c_zero: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/poly_c_apzero.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_mult_lin.con".

(* SUPERFLUOUS ? *)

inline "cic:/CoRN/algebra/CPolynomials/lin_mult.con".

(* UNEXPORTED
Hint Resolve lin_mult: algebra.
*)

(*#* *** Application of polynomials
*)

inline "cic:/CoRN/algebra/CPolynomials/poly_eq_zero.con".

inline "cic:/CoRN/algebra/CPolynomials/apply_wd.con".

inline "cic:/CoRN/algebra/CPolynomials/cpolyap_pres_eq.con".

inline "cic:/CoRN/algebra/CPolynomials/cpolyap_strext.con".

inline "cic:/CoRN/algebra/CPolynomials/cpoly_csetoid_op.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/_x_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/plus_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/inv_apply.con".

(* UNEXPORTED
Hint Resolve plus_apply inv_apply: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/minus_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/_c_mult_apply.con".

(* UNEXPORTED
Hint Resolve _c_mult_apply: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/mult_apply.con".

(* UNEXPORTED
Hint Resolve mult_apply: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/one_apply.con".

(* UNEXPORTED
Hint Resolve one_apply: algebra.
*)

inline "cic:/CoRN/algebra/CPolynomials/nexp_apply.con".

(* SUPERFLUOUS *)

inline "cic:/CoRN/algebra/CPolynomials/poly_inv_apply.con".

inline "cic:/CoRN/algebra/CPolynomials/Sum0_cpoly_ap.con".

inline "cic:/CoRN/algebra/CPolynomials/Sum_cpoly_ap.con".

(* UNEXPORTED
End Poly_properties
*)

(*#* ** Induction properties of polynomials for [Prop]
*)

(* UNEXPORTED
Section Poly_Prop_Induction
*)

alias id "CR" = "cic:/CoRN/algebra/CPolynomials/Poly_Prop_Induction/CR.var".

(* NOTATION
Notation Cpoly := (cpoly CR).
*)

(* NOTATION
Notation Cpoly_zero := (cpoly_zero CR).
*)

(* NOTATION
Notation Cpoly_linear := (cpoly_linear CR).
*)

(* NOTATION
Notation Cpoly_cring := (cpoly_cring CR).
*)

inline "cic:/CoRN/algebra/CPolynomials/cpoly_double_ind.con".

(* UNEXPORTED
End Poly_Prop_Induction
*)

(* UNEXPORTED
Hint Resolve poly_linear cpoly_lin: algebra.
*)

(* UNEXPORTED
Hint Resolve apply_wd cpoly_const_eq: algebra_c.
*)

(* UNEXPORTED
Hint Resolve _c_apply _x_apply inv_apply plus_apply minus_apply mult_apply
  nexp_apply: algebra.
*)

(* UNEXPORTED
Hint Resolve one_apply _c_zero _c_one _c_mult: algebra.
*)

(* UNEXPORTED
Hint Resolve poly_inv_apply: algebra.
*)

(* UNEXPORTED
Hint Resolve _c_mult_lin: algebra.
*)

