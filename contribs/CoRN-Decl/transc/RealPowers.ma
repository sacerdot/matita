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

set "baseuri" "cic:/matita/CoRN-Decl/transc/RealPowers".

include "CoRN.ma".

(* $Id: RealPowers.v,v 1.5 2004/04/23 10:01:08 lcf Exp $ *)

(*#* printing [!] %\ensuremath{\hat{\ }}% #^# *)

(*#* printing {!} %\ensuremath{\hat{\ }}% #^# *)

include "transc/Exponential.ma".

(* UNEXPORTED
Opaque Expon.
*)

(*#* *Arbitrary Real Powers

**Powers of Real Numbers

We now define
$x^y=e^{y\times\log(x)}$#x<sup>y</sup>=e<sup>y*log(x)</sup>#, whenever
[x [>] 0], inspired by the rules for manipulating these expressions.
*)

inline "cic:/CoRN/transc/RealPowers/power.con".

(* NOTATION
Notation "x [!] y [//] Hy" := (power x y Hy) (at level 20).
*)

(*#*
This definition yields a well defined, strongly extensional function
which extends the algebraic exponentiation to an integer power and
still has all the good properties of that operation; when [x [=] e] it
coincides with the exponential function.
*)

inline "cic:/CoRN/transc/RealPowers/power_wd.con".

inline "cic:/CoRN/transc/RealPowers/power_strext.con".

inline "cic:/CoRN/transc/RealPowers/power_plus.con".

inline "cic:/CoRN/transc/RealPowers/power_inv.con".

(* UNEXPORTED
Hint Resolve power_wd power_plus power_inv: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/power_minus.con".

inline "cic:/CoRN/transc/RealPowers/power_nat.con".

(* UNEXPORTED
Hint Resolve power_minus power_nat: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/power_zero.con".

inline "cic:/CoRN/transc/RealPowers/power_one.con".

(* UNEXPORTED
Hint Resolve power_zero power_one: algebra.
*)

(* UNEXPORTED
Opaque nexp_op.
*)

inline "cic:/CoRN/transc/RealPowers/power_int.con".

(* UNEXPORTED
Hint Resolve power_int: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/Exp_power.con".

inline "cic:/CoRN/transc/RealPowers/mult_power.con".

inline "cic:/CoRN/transc/RealPowers/recip_power.con".

(* UNEXPORTED
Hint Resolve Exp_power mult_power recip_power: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/div_power.con".

(* UNEXPORTED
Hint Resolve div_power: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/power_ap_zero.con".

inline "cic:/CoRN/transc/RealPowers/power_mult.con".

inline "cic:/CoRN/transc/RealPowers/power_pos.con".

(* UNEXPORTED
Hint Resolve power_mult: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/power_recip.con".

(* UNEXPORTED
Hint Resolve power_recip: algebra.
*)

inline "cic:/CoRN/transc/RealPowers/power_div.con".

(* UNEXPORTED
Hint Resolve power_div: algebra.
*)

(* UNEXPORTED
Section Power_Function
*)

(*#* **Power Function

This operation on real numbers gives birth to an analogous operation
on partial functions which preserves continuity.

%\begin{convention}% Let [F, G : PartIR].
%\end{convention}%
*)

alias id "J" = "cic:/CoRN/transc/RealPowers/Power_Function/J.var".

alias id "F" = "cic:/CoRN/transc/RealPowers/Power_Function/F.var".

alias id "G" = "cic:/CoRN/transc/RealPowers/Power_Function/G.var".

inline "cic:/CoRN/transc/RealPowers/FPower.con".

inline "cic:/CoRN/transc/RealPowers/FPower_domain.con".

inline "cic:/CoRN/transc/RealPowers/Continuous_power.con".

(* UNEXPORTED
End Power_Function
*)

(* NOTATION
Notation "F {!} G" := (FPower F G) (at level 20).
*)

(* UNEXPORTED
Section More_on_Power_Function
*)

(* UNEXPORTED
Opaque Expon Logarithm.
*)

(*#* From global continuity we can obviously get local continuity: *)

inline "cic:/CoRN/transc/RealPowers/continuous_I_power.con".

(*#* The rule for differentiation is a must. *)

(* UNEXPORTED
Transparent Logarithm.
*)

(* UNEXPORTED
Opaque Logarithm.
*)

inline "cic:/CoRN/transc/RealPowers/Derivative_power.con".

inline "cic:/CoRN/transc/RealPowers/Diffble_power.con".

(* UNEXPORTED
End More_on_Power_Function
*)

(* UNEXPORTED
Hint Resolve Derivative_power: derivate.
*)

