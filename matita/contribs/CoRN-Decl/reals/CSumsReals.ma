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

set "baseuri" "cic:/matita/CoRN-Decl/reals/CSumsReals".

include "CoRN.ma".

(* $Id: CSumsReals.v,v 1.5 2004/04/23 10:01:04 lcf Exp $ *)

include "reals/CReals1.ma".

(*#* * Sums over Reals

%\begin{convention}% Let [c] be a real.
%\end{convention}%

Here we prove that
$\Sigma_{m\leq i \leq n}~c^k = \frac{c^{n+1}-c^m}{c-1}.$
#sum_(m&le; i &le; n) c^k = frac (c^(n+1) -c^m) (c-1)#
*)

(* UNEXPORTED
Section Sums_over_Reals
*)

alias id "c" = "cic:/CoRN/reals/CSumsReals/Sums_over_Reals/c.var".

inline "cic:/CoRN/reals/CSumsReals/Sum0_c_exp.con".

(* UNEXPORTED
Hint Resolve Sum0_c_exp.
*)

inline "cic:/CoRN/reals/CSumsReals/Sum_c_exp.con".

(* UNEXPORTED
Hint Resolve Sum_c_exp.
*)

(*#* The following formulation is often more useful if [c [<] 1]. *)

inline "cic:/CoRN/reals/CSumsReals/Sum_c_exp'.con".

(* UNEXPORTED
Hint Resolve Sum_c_exp'.
*)

(* UNEXPORTED
End Sums_over_Reals
*)

(* UNEXPORTED
Hint Resolve Sum0_c_exp Sum_c_exp Sum_c_exp': algebra.
*)

inline "cic:/CoRN/reals/CSumsReals/diff_is_Sum0.con".

inline "cic:/CoRN/reals/CSumsReals/diff_is_sum.con".

inline "cic:/CoRN/reals/CSumsReals/Sum0_pres_less.con".

inline "cic:/CoRN/reals/CSumsReals/Sum_pres_less.con".

inline "cic:/CoRN/reals/CSumsReals/Sum_pres_leEq.con".

inline "cic:/CoRN/reals/CSumsReals/Sum0_comm_scal.con".

(* UNEXPORTED
Hint Resolve Sum0_comm_scal: algebra.
*)

inline "cic:/CoRN/reals/CSumsReals/Sum_comm_scal.con".

inline "cic:/CoRN/reals/CSumsReals/Sum0_comm_scal'.con".

inline "cic:/CoRN/reals/CSumsReals/Sum_comm_scal'.con".

inline "cic:/CoRN/reals/CSumsReals/Sumx_comm_scal'.con".

inline "cic:/CoRN/reals/CSumsReals/Sum2_comm_scal'.con".

