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

set "baseuri" "cic:/matita/CoRN-Decl/complex/Complex_Exponential".

include "CoRN.ma".

(* $Id: Complex_Exponential.v,v 1.4 2004/04/23 10:00:55 lcf Exp $ *)

(*#* printing ExpCC %\ensuremath{\exp_{\mathbb C}}% *)

include "complex/AbsCC.ma".

include "transc/Exponential.ma".

include "transc/Pi.ma".

(*#* ** The Complex Exponential *)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC.con".

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_wd.con".

(* begin hide *)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_equation_aid_1.con".

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_equation_aid_2.con".

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_equation_aid_3.con".

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_equation_aid_4.con".

(* end hide *)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_plus.con".

(* UNEXPORTED
Hint Resolve ExpCC_plus: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_Zero.con".

(* UNEXPORTED
Hint Resolve ExpCC_Zero: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_inv_aid.con".

(* UNEXPORTED
Hint Resolve ExpCC_inv_aid: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_ap_zero.con".

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_inv.con".

(* UNEXPORTED
Hint Resolve ExpCC_inv: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_pow.con".

(* UNEXPORTED
Hint Resolve ExpCC_pow: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/AbsCC_ExpCC.con".

(* UNEXPORTED
Hint Resolve AbsCC_ExpCC: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_Periodic.con".

(* UNEXPORTED
Hint Resolve ExpCC_Periodic: algebra.
*)

inline "cic:/CoRN/complex/Complex_Exponential/ExpCC_Exp.con".

(* UNEXPORTED
Hint Resolve ExpCC_Exp: algebra.
*)

(* UNEXPORTED
Opaque Sin Cos Exp.
*)

inline "cic:/CoRN/complex/Complex_Exponential/Euler.con".

