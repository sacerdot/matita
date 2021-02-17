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

include "ground/arith/ynat_pred_succ.ma".
include "ground/arith/ynat_lminus.ma".

(* LEFT SUBTRACTION FOR NON-NEGATIVE INTEGERS WITH INFINITY *****************)

(* Constructions with ysucc *************************************************)

(*** yminus_succ *)
lemma ylminus_succ_bi (x:ynat) (n): x - n = ↑x - ↑n.
// qed.
