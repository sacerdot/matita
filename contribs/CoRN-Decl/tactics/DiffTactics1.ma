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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/DiffTactics1".

include "CoRN.ma".

(* begin hide *)

(* UNEXPORTED
Ltac Contin := auto with continuous included.
*)

(* UNEXPORTED
Ltac Deriv := eauto with derivate continuous included.
*)

(* end hide *)

(*#* *Search tactics for reasoning in Real Analysis

The following tactics are defined:
 - [Contin] will solve [(Continuous_I H F)]
 - [Deriv] will solve [(Derivative_I H F F')].

All these tactics are defined using [eauto].
*)

