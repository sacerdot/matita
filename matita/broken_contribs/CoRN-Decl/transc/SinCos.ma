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

set "baseuri" "cic:/matita/CoRN-Decl/transc/SinCos".

include "CoRN.ma".

(* $Id: SinCos.v,v 1.6 2004/04/23 10:01:08 lcf Exp $ *)

include "transc/Trigonometric.ma".

(* UNEXPORTED
Section Sum_and_so_on
*)

(* UNEXPORTED
Opaque Sine Cosine.
*)

(* begin hide *)

inline "cic:/CoRN/transc/SinCos/Sum_and_so_on/F.con" "Sum_and_so_on__".

inline "cic:/CoRN/transc/SinCos/Sum_and_so_on/G.con" "Sum_and_so_on__".

inline "cic:/CoRN/transc/SinCos/Sum_and_so_on/F'.con" "Sum_and_so_on__".

inline "cic:/CoRN/transc/SinCos/Sum_and_so_on/G'.con" "Sum_and_so_on__".

(* end hide *)

inline "cic:/CoRN/transc/SinCos/Sin_plus.con".

inline "cic:/CoRN/transc/SinCos/Cos_plus.con".

(* UNEXPORTED
Opaque Sine Cosine.
*)

(* UNEXPORTED
Hint Resolve Cos_plus Sin_plus: algebra.
*)

(*#* As a corollary we get the rule for the tangent of the sum. *)

inline "cic:/CoRN/transc/SinCos/Tan_plus.con".

(* UNEXPORTED
Transparent Sine Cosine.
*)

(*#* Sine, cosine and tangent of [[--]x]. *)

inline "cic:/CoRN/transc/SinCos/Cos_inv.con".

inline "cic:/CoRN/transc/SinCos/Sin_inv.con".

(* UNEXPORTED
Opaque Sine Cosine.
*)

(* UNEXPORTED
Hint Resolve Cos_inv Sin_inv: algebra.
*)

inline "cic:/CoRN/transc/SinCos/Tan_inv.con".

(* UNEXPORTED
Transparent Sine Cosine.
*)

(*#*
The fundamental formulas of trigonometry: $\cos(x)^2+\sin(x)^2=1$#cos(x)<sup>2</sup>+sin(x)<sup>2</sup>=1# and, equivalently, $1+\tan(x)^2=\frac1{\cos(x)^2}$#1+tan(x)<sup>2</sup>=1/(cos(x)<sup>2</sup>)#.
*)

(* UNEXPORTED
Hint Resolve Cos_zero: algebra.
*)

inline "cic:/CoRN/transc/SinCos/FFT.con".

(* UNEXPORTED
Opaque Sine Cosine.
*)

(* UNEXPORTED
Hint Resolve FFT: algebra.
*)

inline "cic:/CoRN/transc/SinCos/FFT'.con".

(* UNEXPORTED
End Sum_and_so_on
*)

(* UNEXPORTED
Hint Resolve Derivative_Sin Derivative_Cos: derivate.
*)

(* UNEXPORTED
Hint Resolve Continuous_Sin Continuous_Cos: continuous.
*)

(* UNEXPORTED
Hint Resolve Sin_zero Cos_zero Tan_zero Sin_plus Cos_plus Tan_plus Sin_inv
  Cos_inv Tan_inv FFT FFT': algebra.
*)

(* UNEXPORTED
Opaque Min Sine Cosine.
*)

(* UNEXPORTED
Section Basic_Properties
*)

(*#* **Basic properties

We now prove most of the usual trigonometric (in)equalities.

Sine, cosine and tangent are strongly extensional and well defined.
*)

inline "cic:/CoRN/transc/SinCos/Sin_strext.con".

inline "cic:/CoRN/transc/SinCos/Cos_strext.con".

inline "cic:/CoRN/transc/SinCos/Tan_strext.con".

inline "cic:/CoRN/transc/SinCos/Sin_wd.con".

inline "cic:/CoRN/transc/SinCos/Cos_wd.con".

inline "cic:/CoRN/transc/SinCos/Tan_wd.con".

(*#*
The sine and cosine produce values in [[-1,1]].
*)

inline "cic:/CoRN/transc/SinCos/AbsIR_Sin_leEq_One.con".

inline "cic:/CoRN/transc/SinCos/AbsIR_Cos_leEq_One.con".

inline "cic:/CoRN/transc/SinCos/Sin_leEq_One.con".

inline "cic:/CoRN/transc/SinCos/Cos_leEq_One.con".

(*#*
If the cosine is positive then the sine is in [(-1,1)].
*)

inline "cic:/CoRN/transc/SinCos/Sin_less_One.con".

inline "cic:/CoRN/transc/SinCos/AbsIR_Sin_less_One.con".

(* UNEXPORTED
End Basic_Properties
*)

(* UNEXPORTED
Hint Resolve Sin_wd Cos_wd Tan_wd: algebra.
*)

