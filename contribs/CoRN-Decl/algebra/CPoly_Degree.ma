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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CPoly_Degree".

include "CoRN.ma".

(* $Id: CPoly_Degree.v,v 1.5 2004/04/23 10:00:53 lcf Exp $ *)

include "algebra/CPoly_NthCoeff.ma".

include "algebra/CFields.ma".

(*#* *Degrees of Polynomials
** Degrees of polynomials over a ring
%\begin{convention}%
Let [R] be a ring and write [RX] for the ring of polynomials
over [R].
%\end{convention}%
*)

(* UNEXPORTED
Section Degree_def
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_Degree/Degree_def/R.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

(*#*
The length of a polynomial is the number of its coefficients. This is
a syntactical property, as the highest coefficient may be [0]. Note that
the `zero' polynomial [cpoly_zero] has length [0],
a constant polynomial has length [1] and so forth. So the length
is always [1] higher than the `degree' (assuming that the highest
coefficient is [[#]Zero])!
*)

inline "cic:/CoRN/algebra/CPoly_Degree/lth_of_poly.con".

(*#*
When dealing with constructive polynomials, notably over the reals or
complex numbers, the degree may be unknown, as we can not decide
whether the highest coefficient is [[#]Zero]. Hence,
degree is a relation between polynomials and natural numbers; if the
degree is unknown for polynomial [p], degree(n,p) doesn't hold for
any [n].  If we don't know the degree of [p], we may still
know it to be below or above a certain number. E.g. for the polynomial
$p_0 +p_1 X +\cdots + p_{n-1} X^{n-1}$#p0 +p1 X + ... + p(n-1)
X^(n-1)#, if $p_i \mathrel{\#}0$#pi apart from 0#, we can say that the
`degree is at least [i]' and if $p_{j+1} = \ldots =p_n =0$#p(j+1)
= ... =pn =0# (with [n] the length of the polynomial), we can say
that the `degree is at most [j]'.
*)

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic.con".

inline "cic:/CoRN/algebra/CPoly_Degree/odd_cpoly.con".

inline "cic:/CoRN/algebra/CPoly_Degree/even_cpoly.con".

inline "cic:/CoRN/algebra/CPoly_Degree/regular.con".

(* UNEXPORTED
End Degree_def
*)

(* UNEXPORTED
Implicit Arguments degree_le [R].
*)

(* UNEXPORTED
Implicit Arguments degree [R].
*)

(* UNEXPORTED
Implicit Arguments monic [R].
*)

(* UNEXPORTED
Implicit Arguments lth_of_poly [R].
*)

(* UNEXPORTED
Section Degree_props
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_Degree/Degree_props/R.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_wd.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_wd.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_wd.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_imp_degree_le.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_c_.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_c_.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_c_one.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_x_.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_x_.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_x_.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_mon.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_inv.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_plus.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_minus.con".

inline "cic:/CoRN/algebra/CPoly_Degree/Sum_degree_le.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_inv.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_plus_rht.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_minus_lft.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_plus.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_minus.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_mult.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_mult_aux.con".

(* UNEXPORTED
Hint Resolve degree_mult_aux: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_Degree/monic_mult.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_nexp.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_nexp.con".

inline "cic:/CoRN/algebra/CPoly_Degree/lt_i_lth_of_poly.con".

inline "cic:/CoRN/algebra/CPoly_Degree/poly_degree_lth.con".

inline "cic:/CoRN/algebra/CPoly_Degree/Cpoly_ex_degree.con".

inline "cic:/CoRN/algebra/CPoly_Degree/poly_as_sum''.con".

(* UNEXPORTED
Hint Resolve poly_as_sum'': algebra.
*)

inline "cic:/CoRN/algebra/CPoly_Degree/poly_as_sum'.con".

inline "cic:/CoRN/algebra/CPoly_Degree/poly_as_sum.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_zero.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_1_imp.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_cpoly_linear.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_cpoly_linear.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_one.con".

inline "cic:/CoRN/algebra/CPoly_Degree/monic_apzero.con".

(* UNEXPORTED
End Degree_props
*)

(* UNEXPORTED
Hint Resolve poly_as_sum'' poly_as_sum' poly_as_sum: algebra.
*)

(* UNEXPORTED
Hint Resolve degree_mult_aux: algebra.
*)

(* UNEXPORTED
Section degree_props_Field
*)

(*#* ** Degrees of polynomials over a field
%\begin{convention}% Let [F] be a field and write [FX] for the ring of
polynomials over [F].
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CPoly_Degree/degree_props_Field/F.var".

(* begin hide *)

(* NOTATION
Notation FX := (cpoly_cring F).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CPoly_Degree/degree_mult.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_nexp.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_le_mult_imp.con".

inline "cic:/CoRN/algebra/CPoly_Degree/degree_mult_imp.con".

(* UNEXPORTED
End degree_props_Field
*)

