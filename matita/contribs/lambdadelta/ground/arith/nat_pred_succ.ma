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

include "ground/arith/nat_succ.ma".
include "ground/arith/nat_pred.ma".

(* PREDECESSOR FOR NON-NEGATIVE INTEGERS ************************************)

(* Rewrites with nsucc ******************************************************)

(*** pred_Sn *)
lemma npred_succ (n): n = ↓↑n.
* //
qed.
