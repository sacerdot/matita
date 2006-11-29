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

set "baseuri" "cic:/matita/CoRN-Decl/transc/PowerSeries".

include "CoRN.ma".

(* $Id: PowerSeries.v,v 1.8 2004/04/23 10:01:08 lcf Exp $ *)

(*#* printing Exp %\ensuremath{\exp}% *)

(*#* printing Sin %\ensuremath{\sin}% *)

(*#* printing Cos %\ensuremath{\cos}% *)

(*#* printing Log %\ensuremath{\log}% *)

(*#* printing Tan %\ensuremath{\tan}% *)

include "ftc/FTC.ma".

(*#* *More on Power Series

We will now formally define an operator that defines a function as the
sum of some series given a number sequence.  Along with it, we will
prove some important properties of these entities.
*)

(* UNEXPORTED
Section Power_Series
*)

(*#* **General results

%\begin{convention}% Let [J : interval] and [x0 : IR] be a point of [J].
Let [a : nat -> IR].
%\end{convention}%
*)

inline "cic:/CoRN/transc/PowerSeries/Power_Series/J.var" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/Power_Series/x0.var" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/Power_Series/Hx0.var" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/Power_Series/a.var" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries.con".

(*#*
The most important convergence criterium specifically for power series
is the Dirichlet criterium.
*)

(* begin show *)

inline "cic:/CoRN/transc/PowerSeries/Power_Series/Ha.var" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/Power_Series/r.con" "Power_Series__".

inline "cic:/CoRN/transc/PowerSeries/Power_Series/Hr.con" "Power_Series__".

(* end show *)

inline "cic:/CoRN/transc/PowerSeries/Dirichlet_crit.con".

(*#*
When defining a function using its Taylor series as a motivation, the following operator can be of use.
*)

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries'.con".

(*#*
This function is also continuous and has a good convergence ratio.
*)

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries'_cont.con".

inline "cic:/CoRN/transc/PowerSeries/included_FPowerSeries'.con".

(* begin show *)

inline "cic:/CoRN/transc/PowerSeries/Power_Series/Ha'.var" "Power_Series__".

(* end show *)

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries'_conv'.con".

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries'_conv.con".

(* UNEXPORTED
End Power_Series
*)

(* UNEXPORTED
Hint Resolve FPowerSeries'_cont: continuous.
*)

(* UNEXPORTED
Section More_on_PowerSeries
*)

(*#*
%\begin{convention}% Let [F] and [G] be the power series defined
respectively by [a] and by [fun n => (a (S n))].
%\end{convention}%
*)

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/x0.var" "More_on_PowerSeries__".

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/a.var" "More_on_PowerSeries__".

(* begin hide *)

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/F.con" "More_on_PowerSeries__".

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/G.con" "More_on_PowerSeries__".

(* end hide *)

(* begin show *)

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/Hf.var" "More_on_PowerSeries__".

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/Hf'.var" "More_on_PowerSeries__".

inline "cic:/CoRN/transc/PowerSeries/More_on_PowerSeries/Hg.var" "More_on_PowerSeries__".

(* end show *)

(*#* We get a comparison test for power series. *)

inline "cic:/CoRN/transc/PowerSeries/FPowerSeries'_comp.con".

(*#* And a rule for differentiation. *)

(* UNEXPORTED
Opaque nring fac.
*)

inline "cic:/CoRN/transc/PowerSeries/Derivative_FPowerSeries1'.con".

(* UNEXPORTED
End More_on_PowerSeries
*)

(* UNEXPORTED
Section Definitions
*)

(*#* **Function definitions through power series

We now define the exponential, sine and cosine functions as power
series, and prove their convergence.  Tangent is defined as the
quotient of sine over cosine.
*)

inline "cic:/CoRN/transc/PowerSeries/Exp_ps.con".

inline "cic:/CoRN/transc/PowerSeries/sin_seq.con".

inline "cic:/CoRN/transc/PowerSeries/sin_ps.con".

inline "cic:/CoRN/transc/PowerSeries/cos_seq.con".

inline "cic:/CoRN/transc/PowerSeries/cos_ps.con".

inline "cic:/CoRN/transc/PowerSeries/Exp_conv'.con".

inline "cic:/CoRN/transc/PowerSeries/Exp_conv.con".

inline "cic:/CoRN/transc/PowerSeries/sin_conv.con".

inline "cic:/CoRN/transc/PowerSeries/cos_conv.con".

inline "cic:/CoRN/transc/PowerSeries/Expon.con".

inline "cic:/CoRN/transc/PowerSeries/Sine.con".

inline "cic:/CoRN/transc/PowerSeries/Cosine.con".

inline "cic:/CoRN/transc/PowerSeries/Tang.con".

(*#*
Some auxiliary domain results.
*)

inline "cic:/CoRN/transc/PowerSeries/Exp_domain.con".

inline "cic:/CoRN/transc/PowerSeries/sin_domain.con".

inline "cic:/CoRN/transc/PowerSeries/cos_domain.con".

inline "cic:/CoRN/transc/PowerSeries/included_Exp.con".

inline "cic:/CoRN/transc/PowerSeries/included_Sin.con".

inline "cic:/CoRN/transc/PowerSeries/included_Cos.con".

(*#*
Definition of the logarithm.
*)

inline "cic:/CoRN/transc/PowerSeries/log_defn_lemma.con".

inline "cic:/CoRN/transc/PowerSeries/Logarithm.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Hint Resolve included_Exp included_Sin included_Cos: included.
*)

(*#*
As most of these functions are total, it makes sense to treat them as setoid functions on the reals.  In the case of logarithm and tangent, this is not possible; however, we still define some abbreviations for aesthetical reasons.
*)

inline "cic:/CoRN/transc/PowerSeries/Exp.con".

inline "cic:/CoRN/transc/PowerSeries/Sin.con".

inline "cic:/CoRN/transc/PowerSeries/Cos.con".

inline "cic:/CoRN/transc/PowerSeries/Log.con".

inline "cic:/CoRN/transc/PowerSeries/Tan.con".

