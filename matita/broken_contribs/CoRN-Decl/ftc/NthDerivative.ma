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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/NthDerivative".

include "CoRN.ma".

(* $Id: NthDerivative.v,v 1.5 2004/04/20 22:38:50 hinderer Exp $ *)

include "ftc/Differentiability.ma".

(* UNEXPORTED
Section Nth_Derivative
*)

(*#* *Nth Derivative

We now study higher order differentiability.

%\begin{convention}% Throughout this section:
 - [a, b] will be real numbers with [a [<] b];
 - [I] will denote the compact interval [[a,b]];
 - [F, G, H] will denote partial functions.

%\end{convention}%

**Definitions

We first define what we mean by the derivative of order [n] of a function.
*)

alias id "a" = "cic:/CoRN/ftc/NthDerivative/Nth_Derivative/a.var".

alias id "b" = "cic:/CoRN/ftc/NthDerivative/Nth_Derivative/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/NthDerivative/Nth_Derivative/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/NthDerivative/Nth_Derivative/Hab.con" "Nth_Derivative__".

inline "cic:/CoRN/ftc/NthDerivative/Nth_Derivative/I.con" "Nth_Derivative__".

(* end hide *)

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n.con".

(*#*
Unlike first order differentiability, for our definition to be
workable it is better to define directly what it means for a function
to be [n] times differentiable instead of quantifying over the
[Derivative_I_n] relation.
*)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_n.con".

(* UNEXPORTED
End Nth_Derivative
*)

(* UNEXPORTED
Implicit Arguments Derivative_I_n [a b].
*)

(* UNEXPORTED
Implicit Arguments Diffble_I_n [a b].
*)

(* UNEXPORTED
Section Trivia
*)

(*#* **Trivia

These are the expected extensionality and uniqueness results.
*)

alias id "a" = "cic:/CoRN/ftc/NthDerivative/Trivia/a.var".

alias id "b" = "cic:/CoRN/ftc/NthDerivative/Trivia/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/NthDerivative/Trivia/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/NthDerivative/Trivia/Hab.con" "Trivia__".

inline "cic:/CoRN/ftc/NthDerivative/Trivia/I.con" "Trivia__".

(* end hide *)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_n_wd.con".

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_wdr.con".

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_wdl.con".

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_unique.con".

(* UNEXPORTED
End Trivia
*)

(* UNEXPORTED
Section Basic_Results
*)

(*#* **Basic Results

We now explore the concept of [n] times differentiability.  Notice
that, unlike the first order case, we do not pay so much attention to
the relation of [n] times derivative, but focus rather on the
definition of [Diffble_I_n].
*)

alias id "a" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/NthDerivative/Basic_Results/Hab.con" "Basic_Results__".

inline "cic:/CoRN/ftc/NthDerivative/Basic_Results/I.con" "Basic_Results__".

(* end hide *)

(*#*
We begin by showing that having a higher order derivative implies being differentiable.
*)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_n_imp_diffble.con".

inline "cic:/CoRN/ftc/NthDerivative/deriv_n_imp_diffble.con".

(*#*
If a function is [n] times differentiable then it is also [m] times differentiable for every [m] less or equal than [n].
*)

inline "cic:/CoRN/ftc/NthDerivative/le_imp_Diffble_I.con".

(*#*
The next result consolidates our intuition that a function is [n]
times differentiable if we can build from it a chain of [n]
derivatives.
*)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_imp_le.con".

(*#*
As expected, an [n] times differentiable in [[a,b]] function must be
defined in that interval.
*)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_n_imp_inc.con".

(*#*
Also, the notions of derivative and differentiability are related as expected.
*)

inline "cic:/CoRN/ftc/NthDerivative/Diffble_I_n_imp_deriv_n.con".

inline "cic:/CoRN/ftc/NthDerivative/deriv_n_imp_Diffble_I_n.con".

(*#*
From this we can prove that if [F] has an nth order derivative in
[[a,b]] then both [F] and its derivative are defined in that interval.
*)

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_imp_inc.con".

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_imp_inc'.con".

(* UNEXPORTED
Section aux
*)

(*#*
First order differentiability is just a special case.
*)

(* begin show *)

alias id "F" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/aux/F.var".

alias id "diffF" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/aux/diffF.var".

alias id "diffFn" = "cic:/CoRN/ftc/NthDerivative/Basic_Results/aux/diffFn.var".

(* end show *)

inline "cic:/CoRN/ftc/NthDerivative/deriv_1_deriv.con".

inline "cic:/CoRN/ftc/NthDerivative/deriv_1_deriv'.con".

(* UNEXPORTED
End aux
*)

(*#*
As usual, nth order derivability is preserved by shrinking the interval.
*)

inline "cic:/CoRN/ftc/NthDerivative/included_imp_deriv_n.con".

inline "cic:/CoRN/ftc/NthDerivative/included_imp_diffble_n.con".

(*#*
And finally we have an addition rule for the order of the derivative.
*)

inline "cic:/CoRN/ftc/NthDerivative/Derivative_I_n_plus.con".

(* UNEXPORTED
End Basic_Results
*)

(* UNEXPORTED
Section More_Results
*)

alias id "a" = "cic:/CoRN/ftc/NthDerivative/More_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/NthDerivative/More_Results/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/NthDerivative/More_Results/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/NthDerivative/More_Results/Hab.con" "More_Results__".

inline "cic:/CoRN/ftc/NthDerivative/More_Results/I.con" "More_Results__".

(* end hide *)

(*#* **The Nth Derivative

We now define an operator that returns an nth order derivative of an
n-times differentiable function.  This is analogous to the quantifier
elimination which we would get if we had defined nth differentiability
as an existential quantification of the nth derivative relation.
*)

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_I.con".

(*#*
This operator is well defined and works as expected.
*)

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_I_wd.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_lemma.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_inc.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_inc'.con".

(*#*
Some basic properties of this operation.
*)

inline "cic:/CoRN/ftc/NthDerivative/n_Sn_deriv.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_plus.con".

(* UNEXPORTED
End More_Results
*)

(* UNEXPORTED
Section More_on_n_deriv
*)

(*#*
Some not so basic properties of this operation (needed in rather specific situations).
*)

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_I_wd'.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_I_wd''.con".

inline "cic:/CoRN/ftc/NthDerivative/n_deriv_I_strext'.con".

(* UNEXPORTED
End More_on_n_deriv
*)

