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

set "baseuri" "cic:/matita/CoRN-Decl/transc/Exponential".

include "CoRN.ma".

(* $Id: Exponential.v,v 1.7 2004/04/23 10:01:07 lcf Exp $ *)

include "transc/TaylorSeries.ma".

(* UNEXPORTED
Opaque Min Max.
*)

(*#* *Exponential and Logarithmic Functions

The main properties of the exponential and logarithmic functions.

**Properties of Exponential

Exponential is strongly extensional and well defined.
*)

inline "cic:/CoRN/transc/Exponential/Exp_strext.con".

inline "cic:/CoRN/transc/Exponential/Exp_wd.con".

(* UNEXPORTED
Hint Resolve Exp_wd: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Exp_zero.con".

(*#* $e^1=e$#e<sup>1</sup>=e#, where [e] was defined a long time ago.
*)

inline "cic:/CoRN/transc/Exponential/Exp_one.con".

(* UNEXPORTED
Hint Resolve Exp_zero Exp_one: algebra.
*)

(*#*
The exponential function is its own derivative, and continuous.
*)

inline "cic:/CoRN/transc/Exponential/Derivative_Exp.con".

(* UNEXPORTED
Hint Resolve Derivative_Exp: derivate.
*)

inline "cic:/CoRN/transc/Exponential/Continuous_Exp.con".

(* UNEXPORTED
Hint Resolve Continuous_Exp: continuous.
*)

(*#*
Negative numbers are projected into the interval [[0,1]].
*)

inline "cic:/CoRN/transc/Exponential/One_less_Exp.con".

inline "cic:/CoRN/transc/Exponential/One_leEq_Exp.con".

inline "cic:/CoRN/transc/Exponential/Exp_pos'.con".

(*#*
Exponential is the unique function which evaluates to 1 at 0 and is
its own derivative.
*)

inline "cic:/CoRN/transc/Exponential/Exp_unique_lemma.con".

inline "cic:/CoRN/transc/Exponential/Exp_bnd.con".

(* UNEXPORTED
Opaque Expon.
*)

(* UNEXPORTED
Transparent Expon.
*)

inline "cic:/CoRN/transc/Exponential/Exp_unique.con".

(* UNEXPORTED
Opaque Expon.
*)

inline "cic:/CoRN/transc/Exponential/Exp_plus_pos.con".

(*#* The usual rules for computing the exponential of a sum. *)

inline "cic:/CoRN/transc/Exponential/Exp_plus.con".

(* UNEXPORTED
Hint Resolve Exp_plus: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Exp_plus'.con".

inline "cic:/CoRN/transc/Exponential/Exp_inv_char.con".

(* UNEXPORTED
Hint Resolve Exp_inv_char: algebra.
*)

(*#* The exponential of any number is always positive---and thus apart
from zero.
*)

inline "cic:/CoRN/transc/Exponential/Exp_pos.con".

inline "cic:/CoRN/transc/Exponential/Exp_ap_zero.con".

(*#*
And the rules for the exponential of differences.
*)

inline "cic:/CoRN/transc/Exponential/Exp_inv.con".

(* UNEXPORTED
Hint Resolve Exp_inv: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Exp_minus.con".

(* UNEXPORTED
Hint Resolve Exp_minus: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Exp_inv'.con".

inline "cic:/CoRN/transc/Exponential/Exp_minus'.con".

(*#* Exponential is a monotonous function. *)

inline "cic:/CoRN/transc/Exponential/Exp_less_One.con".

inline "cic:/CoRN/transc/Exponential/Exp_leEq_One.con".

inline "cic:/CoRN/transc/Exponential/Exp_resp_less.con".

inline "cic:/CoRN/transc/Exponential/Exp_resp_leEq.con".

(*#* **Properties of Logarithm

The logarithm is a continuous function with derivative [One[/]x].
*)

inline "cic:/CoRN/transc/Exponential/Derivative_Log.con".

(* UNEXPORTED
Hint Resolve Derivative_Log: derivate.
*)

inline "cic:/CoRN/transc/Exponential/Continuous_Log.con".

(* UNEXPORTED
Hint Resolve Continuous_Log: continuous.
*)

(*#* Logarithm of [One]. *)

inline "cic:/CoRN/transc/Exponential/Log_one.con".

(* UNEXPORTED
Hint Resolve Log_one: algebra.
*)

(*#* The logarithm is (strongly) extensional. *)

inline "cic:/CoRN/transc/Exponential/Log_strext.con".

inline "cic:/CoRN/transc/Exponential/Log_wd.con".

(* UNEXPORTED
Hint Resolve Log_wd: algebra.
*)

(*#* The rule for the logarithm of the product. *)

(* UNEXPORTED
Opaque Logarithm.
*)

(* UNEXPORTED
Transparent Logarithm.
*)

inline "cic:/CoRN/transc/Exponential/Log_mult.con".

(* UNEXPORTED
Hint Resolve Log_mult: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Log_mult'.con".

(*#* A characterization of the domain of the logarithm. *)

inline "cic:/CoRN/transc/Exponential/Log_domain.con".

(* UNEXPORTED
Opaque Expon Logarithm.
*)

(*#* $\log(e^x)=x$#log(e<sup>x</sup>)=x# for all [x], both as a
numerical and as a functional equation.
*)

inline "cic:/CoRN/transc/Exponential/Log_Exp_inv.con".

inline "cic:/CoRN/transc/Exponential/Log_Exp.con".

(* UNEXPORTED
Transparent Logarithm.
*)

(* UNEXPORTED
Hint Resolve Log_Exp: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Exp_Log_lemma.con".

(*#* The converse expression. *)

inline "cic:/CoRN/transc/Exponential/Exp_Log.con".

(* UNEXPORTED
Hint Resolve Exp_Log: algebra.
*)

(*#* Exponential and logarithm are injective. *)

inline "cic:/CoRN/transc/Exponential/Exp_cancel.con".

inline "cic:/CoRN/transc/Exponential/Log_cancel.con".

(* UNEXPORTED
Opaque Logarithm.
*)

(*#* And the final characterization as inverse functions. *)

inline "cic:/CoRN/transc/Exponential/Exp_Log_inv.con".

inline "cic:/CoRN/transc/Exponential/Log_E.con".

(* UNEXPORTED
Hint Resolve Log_E: algebra.
*)

(*#* Several rules regarding inequalities. *)

inline "cic:/CoRN/transc/Exponential/Log_cancel_less.con".

inline "cic:/CoRN/transc/Exponential/Log_cancel_leEq.con".

inline "cic:/CoRN/transc/Exponential/Log_resp_less.con".

inline "cic:/CoRN/transc/Exponential/Log_resp_leEq.con".

inline "cic:/CoRN/transc/Exponential/Exp_cancel_less.con".

inline "cic:/CoRN/transc/Exponential/Exp_cancel_leEq.con".

inline "cic:/CoRN/transc/Exponential/Log_less_Zero.con".

inline "cic:/CoRN/transc/Exponential/Log_leEq_Zero.con".

inline "cic:/CoRN/transc/Exponential/Zero_less_Log.con".

inline "cic:/CoRN/transc/Exponential/Zero_leEq_Log.con".

(*#* Finally, rules for logarithm of quotients. *)

inline "cic:/CoRN/transc/Exponential/Log_recip_char.con".

inline "cic:/CoRN/transc/Exponential/Log_recip.con".

(* UNEXPORTED
Hint Resolve Log_recip: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Log_recip'.con".

inline "cic:/CoRN/transc/Exponential/Log_div.con".

(* UNEXPORTED
Hint Resolve Log_div: algebra.
*)

inline "cic:/CoRN/transc/Exponential/Log_div'.con".

