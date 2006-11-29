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

set "baseuri" "cic:/matita/CoRN-Decl/transc/TrigMon".

include "CoRN.ma".

(* $Id: TrigMon.v,v 1.9 2004/04/23 10:01:08 lcf Exp $ *)

include "transc/Pi.ma".

(* UNEXPORTED
Opaque Sine Cosine.
*)

(*#*
Sign properties: cosine is positive in
$(-\frac{\pi}2,\frac{\pi}2)$#(-&pi;/2,&pi;/2)#, sine in
$(0,\pi)$#(0,&pi;)# and tangent in $(0,\frac{\pi}2)$#0,&pi;/2)#.
*)

inline "cic:/CoRN/transc/TrigMon/Cos_pos.con".

inline "cic:/CoRN/transc/TrigMon/Sin_pos.con".

inline "cic:/CoRN/transc/TrigMon/Tan_pos.con".

inline "cic:/CoRN/transc/TrigMon/Cos_nonneg.con".

inline "cic:/CoRN/transc/TrigMon/Sin_nonneg.con".

(*#* Consequences. *)

inline "cic:/CoRN/transc/TrigMon/Abs_Sin_less_One.con".

inline "cic:/CoRN/transc/TrigMon/Abs_Cos_less_One.con".

(*#*
Sine is (strictly) increasing in [[ [--]Pi[/]Two,Pi[/]Two]]; cosine
is (strictly) decreasing in [[Zero,Pi]].
*)

inline "cic:/CoRN/transc/TrigMon/Sin_resp_leEq.con".

inline "cic:/CoRN/transc/TrigMon/Cos_resp_leEq.con".

(* begin hide *)

inline "cic:/CoRN/transc/TrigMon/Cos_resp_less_aux.con".

inline "cic:/CoRN/transc/TrigMon/Cos_resp_less_aux'.con".

(* end hide *)

inline "cic:/CoRN/transc/TrigMon/Cos_resp_less.con".

inline "cic:/CoRN/transc/TrigMon/Sin_resp_less.con".

(* UNEXPORTED
Section Tangent
*)

(*#* **Derivative of Tangent

Finally, two formulas for the derivative of the tangent function and
monotonicity properties.
*)

inline "cic:/CoRN/transc/TrigMon/bnd_Cos.con".

(* UNEXPORTED
Opaque Sine Cosine.
*)

inline "cic:/CoRN/transc/TrigMon/Derivative_Tan_1.con".

inline "cic:/CoRN/transc/TrigMon/Derivative_Tan_2.con".

inline "cic:/CoRN/transc/TrigMon/Tan_resp_less.con".

inline "cic:/CoRN/transc/TrigMon/Tan_resp_leEq.con".

(* UNEXPORTED
End Tangent
*)

(* UNEXPORTED
Hint Resolve Derivative_Tan_1 Derivative_Tan_2: derivate.
*)

