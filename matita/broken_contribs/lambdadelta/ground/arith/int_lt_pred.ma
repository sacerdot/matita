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

include "ground/arith/int_lt.ma".
include "ground/arith/int_le_pred.ma".

(* STRICT ORDER FOR INTEGERS ************************************************)

(* Advanced inversions with zle *********************************************)

lemma zlt_inv_succ_dx_le (z1) (z2):
      z1 < ↑z2 → z1 ≤ z2.
/2 width=1 by zle_inv_succ_bi/
qed-.
