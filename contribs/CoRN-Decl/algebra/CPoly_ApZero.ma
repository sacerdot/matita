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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CPoly_ApZero".

include "CoRN.ma".

(* $Id: CPoly_ApZero.v,v 1.3 2004/04/23 10:00:53 lcf Exp $ *)

include "algebra/CPoly_Degree.ma".

include "algebra/COrdFields2.ma".

(*#* * Polynomials apart from zero *)

inline "cic:/CoRN/algebra/CPoly_ApZero/distinct1.con".

(* UNEXPORTED
Implicit Arguments distinct1 [A].
*)

(* UNEXPORTED
Section Poly_Representation
*)

(*#*
** Representation of polynomials
%\begin{convention}% Let [R] be a field, [RX] the ring of polynomials
over [R], [a_ : nat->R] with [(distinct1 a_)] and let [f] be a
polynomial over [R], [n] a natural with [(degree_le n f)], i.e. [f]
has degree at most [n].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/R.var".

alias id "a_" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/a_.var".

alias id "distinct_a_" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/distinct_a_.var".

alias id "f" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/f.var".

alias id "n" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/n.var".

alias id "degree_f" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_Representation/degree_f.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

include "tactics/Transparent_algebra.ma".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_linear_shifted.con".

include "tactics/Opaque_algebra.ma".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_linear_factor.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/zero_poly.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/identical_poly.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor'.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor'_degree.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor'_zero.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor'_apzero.con".

(* UNEXPORTED
Hint Resolve poly_01_factor'_zero.
*)

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor_degree.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor_zero.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_factor_one.con".

(* UNEXPORTED
Hint Resolve poly_01_factor_zero poly_01_factor_one: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_degree'.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_degree.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_zero.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_01_one.con".

(* UNEXPORTED
Hint Resolve poly_01_zero poly_01_one: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_representation''.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_representation'.con".

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_representation.con".

(* UNEXPORTED
Hint Resolve poly_representation: algebra.
*)

inline "cic:/CoRN/algebra/CPoly_ApZero/Cpoly_choose_apzero.con".

(* UNEXPORTED
End Poly_Representation
*)

(* UNEXPORTED
Section Characteristic_zero
*)

(*#*
If we are in a field of characteristic zero, the previous result can be
strengthened.
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_ApZero/Characteristic_zero/R.var".

(* begin show *)

alias id "H" = "cic:/CoRN/algebra/CPoly_ApZero/Characteristic_zero/H.var".

(* end show *)

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_apzero.con".

(*#*
Also, in this situation polynomials are extensional functions.
*)

inline "cic:/CoRN/algebra/CPoly_ApZero/poly_extensional.con".

(* UNEXPORTED
End Characteristic_zero
*)

(*#*
** Polynomials are nonzero on any interval
*)

(* UNEXPORTED
Section Poly_ApZero_Interval
*)

alias id "R" = "cic:/CoRN/algebra/CPoly_ApZero/Poly_ApZero_Interval/R.var".

(* begin hide *)

(* NOTATION
Notation RX := (cpoly_cring R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/CPoly_ApZero/Cpoly_apzero_interval.con".

(* UNEXPORTED
End Poly_ApZero_Interval
*)

