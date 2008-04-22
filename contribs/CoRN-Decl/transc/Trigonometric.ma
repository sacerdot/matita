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

set "baseuri" "cic:/matita/CoRN-Decl/transc/Trigonometric".

include "CoRN.ma".

(* $Id: Trigonometric.v,v 1.5 2004/04/23 10:01:08 lcf Exp $ *)

include "transc/TaylorSeries.ma".

(*#* *The Trigonometric Functions

In this section, we explore the properties of the trigonometric functions which we previously defined.
*)

(* UNEXPORTED
Section Lemmas
*)

(*#* First, we need a lemma on mappings. *)

inline "cic:/CoRN/transc/Trigonometric/maps_translation.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Section Sine_and_Cosine
*)

(*#* Sine, cosine and tangent at [Zero]. *)

inline "cic:/CoRN/transc/Trigonometric/Sin_zero.con".

inline "cic:/CoRN/transc/Trigonometric/Cos_zero.con".

(* UNEXPORTED
Hint Resolve Sin_zero Cos_zero: algebra.
*)

(* UNEXPORTED
Opaque Sine Cosine.
*)

inline "cic:/CoRN/transc/Trigonometric/Tan_zero.con".

(* UNEXPORTED
Transparent Sine Cosine.
*)

(*#*
Continuity of sine and cosine are trivial.
*)

inline "cic:/CoRN/transc/Trigonometric/Continuous_Sin.con".

inline "cic:/CoRN/transc/Trigonometric/Continuous_Cos.con".

(*#*
The rules for the derivative of the sine and cosine function; we begin by proving that their defining sequences can be expressed in terms of one another.
*)

inline "cic:/CoRN/transc/Trigonometric/cos_sin_seq.con".

inline "cic:/CoRN/transc/Trigonometric/sin_cos_seq.con".

inline "cic:/CoRN/transc/Trigonometric/Derivative_Sin.con".

inline "cic:/CoRN/transc/Trigonometric/Derivative_Cos.con".

(* UNEXPORTED
Hint Resolve Derivative_Sin Derivative_Cos: derivate.
*)

(* UNEXPORTED
Hint Resolve Continuous_Sin Continuous_Cos: continuous.
*)

(* UNEXPORTED
Section Sine_of_Sum
*)

(*#*
We now prove the rule for the sine and cosine of the sum.  These rules
have to be proved first as functional equalities, which is why we also
state the results in a function form (which we won't do in other
situations).

%\begin{convention}% Let:
 - [F := fun y => Sine[o] (FId{+} [-C-]y)];
 - [G := fun y => (Sine{*} [-C-] (Cos y)) {+} (Cosine{*} [-C-] (Sin y))].

%\end{convention}%
*)

(* begin hide *)

inline "cic:/CoRN/transc/Trigonometric/Sine_and_Cosine/Sine_of_Sum/F.con" "Sine_and_Cosine__Sine_of_Sum__".

inline "cic:/CoRN/transc/Trigonometric/Sine_and_Cosine/Sine_of_Sum/G.con" "Sine_and_Cosine__Sine_of_Sum__".

inline "cic:/CoRN/transc/Trigonometric/Sine_and_Cosine/Sine_of_Sum/F'.con" "Sine_and_Cosine__Sine_of_Sum__".

inline "cic:/CoRN/transc/Trigonometric/Sine_and_Cosine/Sine_of_Sum/G'.con" "Sine_and_Cosine__Sine_of_Sum__".

(* end hide *)

(* UNEXPORTED
Opaque Sine Cosine.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_Taylor_bnd_lft.con".

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_Taylor_bnd_rht.con".

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_eq.con".

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_der_lft.con".

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_der_rht.con".

inline "cic:/CoRN/transc/Trigonometric/Sin_plus_fun.con".

(* UNEXPORTED
End Sine_of_Sum
*)

(* UNEXPORTED
Opaque Sine Cosine.
*)

inline "cic:/CoRN/transc/Trigonometric/Cos_plus_fun.con".

(* UNEXPORTED
End Sine_and_Cosine
*)

