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

set "baseuri" "cic:/matita/CoRN-Decl/transc/Pi".

include "CoRN.ma".

include "transc/SinCos.ma".

(* UNEXPORTED
Section Properties_of_Pi
*)

(*#* printing Pi %\ensuremath{\pi}% #&pi;# *)

(*#* **Definition of Pi

[Pi] is defined as twice the first positive zero of the cosine.  In order to do this, we follow the construction described in Bishop 1969, section 7.
*)

inline "cic:/CoRN/transc/Pi/pi_seq.con".

(* UNEXPORTED
Opaque Cosine.
*)

(* begin hide *)

(* UNEXPORTED
Opaque Sine.
*)

inline "cic:/CoRN/transc/Pi/pi_seq_lemma.con".

(* end hide *)

(*#*
This sequence is nonnegative and the cosine of any number between
[Zero] and any of its values is strictly positive; therefore the
sequence is strictly increasing.
*)

inline "cic:/CoRN/transc/Pi/pi_seq_nonneg.con".

inline "cic:/CoRN/transc/Pi/cos_pi_seq_pos.con".

inline "cic:/CoRN/transc/Pi/pi_seq_incr.con".

(*#* Trivial---but useful---consequences. *)

inline "cic:/CoRN/transc/Pi/sin_pi_seq_mon.con".

inline "cic:/CoRN/transc/Pi/sin_pi_seq_nonneg.con".

inline "cic:/CoRN/transc/Pi/sin_pi_seq_gt_one.con".

inline "cic:/CoRN/transc/Pi/cos_pi_seq_mon.con".

(* begin hide *)

inline "cic:/CoRN/transc/Pi/pi_seq_gt_one.con".

(* UNEXPORTED
Opaque Sine Cosine.
*)

inline "cic:/CoRN/transc/Pi/pi_seq_bnd.con".

inline "cic:/CoRN/transc/Pi/pi_seq_bnd'.con".

inline "cic:/CoRN/transc/Pi/pi_seq_bnd''.con".

(* end hide *)

(*#* An auxiliary result. *)

inline "cic:/CoRN/transc/Pi/Sin_One_pos.con".

(*#* We can now prove that this is a Cauchy sequence.  We define [Pi] as 
twice its limit.
*)

inline "cic:/CoRN/transc/Pi/pi_seq_Cauchy.con".

inline "cic:/CoRN/transc/Pi/Pi.con".

(*#*
For $x\in[0,\frac{\pi}2)$#x&isin;[0,&pi;/2)#, [(Cos x) [>] 0];
$\cos(\frac{pi}2)=0$#cos(&pi;/2)=0#.
*)

inline "cic:/CoRN/transc/Pi/pos_cos.con".

inline "cic:/CoRN/transc/Pi/Cos_HalfPi.con".

(*#* Convergence to [Pi [/] Two] is increasing; therefore, [Pi] is positive. *)

inline "cic:/CoRN/transc/Pi/HalfPi_gt_pi_seq.con".

inline "cic:/CoRN/transc/Pi/pos_Pi.con".

(* UNEXPORTED
End Properties_of_Pi
*)

(* UNEXPORTED
Hint Resolve Cos_HalfPi: algebra.
*)

(* UNEXPORTED
Section Pi_and_Order
*)

(*#* **Properties of Pi

The following are trivial ordering properties of multiples of [Pi]
that will be used so often that it is convenient to state as lemmas;
also, we define a hint database that automatically tries to apply this
lemmas, to make proof development easier.

A summary of what is being proved is simply:
[[
[--]Pi [<] [--]Pi[/]Two [<] [--] Pi[/]Four [<] Zero [<] Pi[/]Four [<] Pi[/]Two [<] Pi
]]

[PiSolve] will prove any of these inequalities.
*)

inline "cic:/CoRN/transc/Pi/pos_HalfPi.con".

inline "cic:/CoRN/transc/Pi/pos_QuarterPi.con".

inline "cic:/CoRN/transc/Pi/QuarterPi_less_HalfPi.con".

inline "cic:/CoRN/transc/Pi/HalfPi_less_Pi.con".

inline "cic:/CoRN/transc/Pi/QuarterPi_less_Pi.con".

inline "cic:/CoRN/transc/Pi/neg_invPi.con".

inline "cic:/CoRN/transc/Pi/neg_invHalfPi.con".

inline "cic:/CoRN/transc/Pi/neg_invQuarterPi.con".

inline "cic:/CoRN/transc/Pi/invHalfPi_less_invQuarterPi.con".

inline "cic:/CoRN/transc/Pi/invPi_less_invHalfPi.con".

inline "cic:/CoRN/transc/Pi/invPi_less_invQuarterPi.con".

inline "cic:/CoRN/transc/Pi/invPi_less_Pi.con".

inline "cic:/CoRN/transc/Pi/invPi_less_HalfPi.con".

inline "cic:/CoRN/transc/Pi/invPi_less_QuarterPi.con".

inline "cic:/CoRN/transc/Pi/invHalfPi_less_Pi.con".

inline "cic:/CoRN/transc/Pi/invHalfPi_less_HalfPi.con".

inline "cic:/CoRN/transc/Pi/invHalfPi_less_QuarterPi.con".

inline "cic:/CoRN/transc/Pi/invQuarterPi_less_Pi.con".

inline "cic:/CoRN/transc/Pi/invQuarterPi_less_HalfPi.con".

inline "cic:/CoRN/transc/Pi/invQuarterPi_less_QuarterPi.con".

(* UNEXPORTED
End Pi_and_Order
*)

(* UNEXPORTED
Hint Resolve pos_Pi pos_HalfPi pos_QuarterPi QuarterPi_less_HalfPi
  HalfPi_less_Pi QuarterPi_less_Pi neg_invPi neg_invHalfPi neg_invQuarterPi
  invHalfPi_less_invQuarterPi invPi_less_invHalfPi invPi_less_invQuarterPi
  invPi_less_Pi invPi_less_HalfPi invPi_less_QuarterPi invHalfPi_less_Pi
  invHalfPi_less_HalfPi invHalfPi_less_QuarterPi invQuarterPi_less_Pi
  invQuarterPi_less_HalfPi invQuarterPi_less_QuarterPi: piorder.
*)

(* begin hide *)

(* UNEXPORTED
Ltac PiSolve := try apply less_leEq; auto with piorder.
*)

(* end hide *)

(* UNEXPORTED
Section Sin_And_Cos
*)

(*#* **More formulas

We now move back to trigonometric identities: sine, cosine and tangent of
the double.
*)

inline "cic:/CoRN/transc/Pi/Cos_double.con".

inline "cic:/CoRN/transc/Pi/Sin_double.con".

inline "cic:/CoRN/transc/Pi/Tan_double.con".

(* begin hide *)

inline "cic:/CoRN/transc/Pi/sqrt_lemma.con".

(* end hide *)

(*#* Value of trigonometric functions at [Pi[/]Four]. *)

inline "cic:/CoRN/transc/Pi/Cos_QuarterPi.con".

inline "cic:/CoRN/transc/Pi/Sin_QuarterPi.con".

(* UNEXPORTED
Hint Resolve Sin_QuarterPi Cos_QuarterPi: algebra.
*)

(* UNEXPORTED
Opaque Sine Cosine.
*)

inline "cic:/CoRN/transc/Pi/Tan_QuarterPi.con".

(*#* Shifting sine and cosine by [Pi[/]Two] and [Pi]. *)

inline "cic:/CoRN/transc/Pi/Sin_HalfPi.con".

(* UNEXPORTED
Hint Resolve Sin_HalfPi: algebra.
*)

inline "cic:/CoRN/transc/Pi/Sin_plus_HalfPi.con".

inline "cic:/CoRN/transc/Pi/Sin_HalfPi_minus.con".

inline "cic:/CoRN/transc/Pi/Cos_plus_HalfPi.con".

inline "cic:/CoRN/transc/Pi/Cos_HalfPi_minus.con".

inline "cic:/CoRN/transc/Pi/Sin_Pi.con".

inline "cic:/CoRN/transc/Pi/Cos_Pi.con".

inline "cic:/CoRN/transc/Pi/Sin_plus_Pi.con".

inline "cic:/CoRN/transc/Pi/Cos_plus_Pi.con".

(* UNEXPORTED
Hint Resolve Sin_plus_Pi Cos_plus_Pi: algebra.
*)

(*#* Sine and cosine have period [Two Pi], tangent has period [Pi]. *)

inline "cic:/CoRN/transc/Pi/Sin_periodic.con".

inline "cic:/CoRN/transc/Pi/Cos_periodic.con".

inline "cic:/CoRN/transc/Pi/Tan_periodic.con".

(* UNEXPORTED
End Sin_And_Cos
*)

(* UNEXPORTED
Hint Resolve Cos_double Sin_double Tan_double Cos_QuarterPi Sin_QuarterPi
  Tan_QuarterPi Sin_Pi Cos_Pi Sin_HalfPi Sin_plus_HalfPi Sin_HalfPi_minus
  Cos_plus_HalfPi Cos_HalfPi_minus Sin_plus_Pi Cos_plus_Pi Sin_periodic
  Cos_periodic Tan_periodic: algebra.
*)

