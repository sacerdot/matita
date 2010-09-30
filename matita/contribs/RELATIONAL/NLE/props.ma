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



include "NLE/order.ma".

theorem nle_trans_succ: ∀x,y. x ≤ y → x ≤ succ y.
 intros; elim H; clear H x y; autobatch.
qed.

theorem nle_gt_or_le: ∀x, y. y > x ∨ y ≤ x.
 intros 2; elim y; clear y;
 [ autobatch
 | decompose;
   [ lapply linear nle_inv_succ_1 to H1
   | lapply linear nle_lt_or_eq to H1
   ]; decompose; destruct; autobatch depth = 4
 ].
qed.
