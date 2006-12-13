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

set "baseuri" "cic:/matita/CoRN-Decl/fta/CPoly_Rev".

include "CoRN.ma".

(* $Id: CPoly_Rev.v,v 1.3 2004/04/23 10:00:56 lcf Exp $ *)

include "algebra/CPoly_Degree.ma".

(*#* * Reverse of polynomials
*)

(* UNEXPORTED
Section Monomials
*)

(*#*
%\begin{convention}% Let [R] be a ring, and let [RX] be the
polynomials over this ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/fta/CPoly_Rev/Monomials/R.var".

(* begin hide *)

inline "cic:/CoRN/fta/CPoly_Rev/Monomials/RX.con" "Monomials__".

(* end hide *)

inline "cic:/CoRN/fta/CPoly_Rev/monom.con".

inline "cic:/CoRN/fta/CPoly_Rev/monom_coeff.con".

inline "cic:/CoRN/fta/CPoly_Rev/monom_coeff'.con".

(* UNEXPORTED
Hint Resolve monom_coeff monom_coeff': algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/monom_degree.con".

inline "cic:/CoRN/fta/CPoly_Rev/monom_S.con".

(* UNEXPORTED
Hint Resolve monom_S: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/monom_wd_lft.con".

(* UNEXPORTED
Hint Resolve monom_wd_lft: algebra_c.
*)

inline "cic:/CoRN/fta/CPoly_Rev/monom_mult'.con".

(* UNEXPORTED
Hint Resolve monom_mult': algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/monom_mult.con".

inline "cic:/CoRN/fta/CPoly_Rev/monom_sum.con".

(* UNEXPORTED
End Monomials
*)

(* UNEXPORTED
Hint Resolve monom_coeff monom_coeff' monom_mult monom_sum: algebra.
*)

(* UNEXPORTED
Implicit Arguments monom [R].
*)

(* UNEXPORTED
Section Poly_Reverse
*)

alias id "R" = "cic:/CoRN/fta/CPoly_Rev/Poly_Reverse/R.var".

(* begin hide *)

inline "cic:/CoRN/fta/CPoly_Rev/Poly_Reverse/RX.con" "Poly_Reverse__".

(* end hide *)

inline "cic:/CoRN/fta/CPoly_Rev/Rev.con".

inline "cic:/CoRN/fta/CPoly_Rev/Rev_coeff.con".

inline "cic:/CoRN/fta/CPoly_Rev/Rev_coeff'.con".

(* UNEXPORTED
Hint Resolve Rev_coeff Rev_coeff': algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_wd.con".

(* UNEXPORTED
Hint Resolve Rev_wd: algebra_c.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_rev.con".

(* UNEXPORTED
Hint Resolve Rev_rev: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_degree_le.con".

inline "cic:/CoRN/fta/CPoly_Rev/Rev_degree.con".

inline "cic:/CoRN/fta/CPoly_Rev/Rev_monom.con".

(* UNEXPORTED
Hint Resolve Rev_monom: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_zero.con".

(* UNEXPORTED
Hint Resolve Rev_zero: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_plus.con".

(* UNEXPORTED
Hint Resolve Rev_plus: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_minus.con".

(* UNEXPORTED
Hint Resolve Rev_minus: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_sum0.con".

(* UNEXPORTED
Hint Resolve Rev_sum0: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Rev/Rev_sum.con".

inline "cic:/CoRN/fta/CPoly_Rev/Rev_mult.con".

(* UNEXPORTED
End Poly_Reverse
*)

(* UNEXPORTED
Hint Resolve Rev_wd: algebra_c.
*)

(* UNEXPORTED
Hint Resolve Rev_rev Rev_mult: algebra.
*)

(* UNEXPORTED
Implicit Arguments Rev [R].
*)

