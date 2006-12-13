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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CPoly_NthCoeff".

include "CoRN.ma".

(* $Id: CPoly_NthCoeff.v,v 1.6 2004/04/23 10:00:53 lcf Exp $ *)

include "algebra/CPolynomials.ma".

(*#*
* Polynomials: Nth Coefficient
%\begin{convention}% Let [R] be a ring and write [RX] for the ring of
polynomials over [R].
%\end{convention}%

** Definitions
*)

(* UNEXPORTED
Section NthCoeff_def
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_NthCoeff/NthCoeff_def/R.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

(*#*
The [n]-th coefficient of a polynomial. The default value is
[Zero:CR] e.g. if the [n] is higher than the length. For the
polynomial $a_0 +a_1 X +a_2 X^2 + \cdots + a_n X^n$ #a0 +a1 X +a2 X^2
+ ... + an X^n#, the [Zero]-th coefficient is $a_0$#a0#, the first
is $a_1$#a1# etcetera.  *)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_strext.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_wd.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_fun.con".

(*#*
%\begin{shortcoming}%
We would like to use [nth_coeff_fun n] all the time.
However, Coq's coercion mechanism doesn't support this properly:
the term
[(nth_coeff_fun n p)] won't get parsed, and has to be written as
[((nth_coeff_fun n) p)] instead.

So, in the names of lemmas, we write [(nth_coeff n p)],
which always (e.g. in proofs) can be converted
to [((nth_coeff_fun n) p)].
%\end{shortcoming}%
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nonConst.con".

(*#*
The following is probably NOT needed.  These functions are
NOT extensional, that is, they are not CSetoid functions.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_ok.con".

(* The in_coeff predicate*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/in_coeff.con".

(*#*
The [cpoly_zero] case should be [c [=] Zero] in order to be extensional.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_S.con".

(* UNEXPORTED
End NthCoeff_def
*)

(* UNEXPORTED
Implicit Arguments nth_coeff [R].
*)

(* UNEXPORTED
Implicit Arguments nth_coeff_fun [R].
*)

(* UNEXPORTED
Hint Resolve nth_coeff_wd: algebra_c.
*)

(* UNEXPORTED
Section NthCoeff_props
*)

(*#* ** Properties of [nth_coeff] *)

alias id "R" = "cic:/CoRN/algebra/CPoly_NthCoeff/NthCoeff_props/R.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_zero.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_O_lin.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_Sm_lin.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_O_c_.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_O_x_mult.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_Sm_x_mult.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/coeff_Sm_mult_x_.con".

(* UNEXPORTED
Hint Resolve nth_coeff_zero coeff_O_lin coeff_Sm_lin coeff_O_c_
  coeff_O_x_mult coeff_Sm_x_mult coeff_Sm_mult_x_: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_ap_zero_imp.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_plus.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_inv.con".

(* UNEXPORTED
Hint Resolve nth_coeff_inv: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_c_mult_p.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_p_mult_c_.con".

(* UNEXPORTED
Hint Resolve nth_coeff_c_mult_p nth_coeff_p_mult_c_ nth_coeff_plus: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_complicated.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/all_nth_coeff_eq_imp.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/poly_at_zero.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_inv'.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_minus.con".

(* UNEXPORTED
Hint Resolve nth_coeff_minus: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_sum0.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_sum.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_nexp_eq.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_nexp_neq.con".

inline "cic:/CoRN/algebra/CPoly_NthCoeff/nth_coeff_mult.con".

(* UNEXPORTED
End NthCoeff_props
*)

(* UNEXPORTED
Hint Resolve nth_coeff_wd: algebra_c.
*)

(* UNEXPORTED
Hint Resolve nth_coeff_complicated poly_at_zero nth_coeff_inv: algebra.
*)

(* UNEXPORTED
Hint Resolve nth_coeff_inv' nth_coeff_c_mult_p nth_coeff_mult: algebra.
*)

(* UNEXPORTED
Hint Resolve nth_coeff_zero nth_coeff_plus nth_coeff_minus: algebra.
*)

(* UNEXPORTED
Hint Resolve nth_coeff_nexp_eq nth_coeff_nexp_neq: algebra.
*)

