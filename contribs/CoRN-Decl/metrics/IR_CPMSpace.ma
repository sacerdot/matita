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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/IR_CPMSpace".

include "CoRN.ma".

(* $Id: IR_CPMSpace.v,v 1.4 2004/04/23 10:01:02 lcf Exp $ *)

include "metrics/ContFunctions.ma".

(* UNEXPORTED
Section Reals
*)

(*#* **Real numbers
*)

(*#* 
%\begin{convention}%
Let [X] be a  pseudo metric space.
%\end{convention}%
*)

(*#*
The real numbers with the usual distance form a pseudo metric space. 
*)

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/bin_fun_strext_dIR.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR_as_CSetoid_fun.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR_nneg.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR_com.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR_pos_imp_ap.con".

(* begin hide *)

inline "cic:/CoRN/metrics/IR_CPMSpace/IR_tri_ineq.con".

(* end hide *)

inline "cic:/CoRN/metrics/IR_CPMSpace/dIR_tri_ineq.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/IR_dIR_is_CPsMetricSpace.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/IR_as_CPsMetricSpace.con".

alias id "X" = "cic:/CoRN/metrics/IR_CPMSpace/Reals/X.var".

inline "cic:/CoRN/metrics/IR_CPMSpace/rev_tri_ineq'.con".

(*#*
A pseudo metric is Lipschitz. Hence it is uniformly continuous and continuous.
*)

inline "cic:/CoRN/metrics/IR_CPMSpace/d_is_lipschitz.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/d_is_uni_continuous.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/d_is_continuous.con".

(* UNEXPORTED
End Reals
*)

(* UNEXPORTED
Section Addition
*)

(*#* **Addition of continuous functions
*)

(*#*
The sum of two Lipschitz/uniformly continous/continuous functions is again 
Lipschitz/uniformly continuous/continuous.
*)

inline "cic:/CoRN/metrics/IR_CPMSpace/plus_resp_lipschitz.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/plus_resp_uni_continuous.con".

inline "cic:/CoRN/metrics/IR_CPMSpace/plus_resp_continuous.con".

(* UNEXPORTED
End Addition
*)

