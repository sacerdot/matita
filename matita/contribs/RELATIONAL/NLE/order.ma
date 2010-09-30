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



include "NLE/inv.ma".

theorem nle_refl: ∀x. x ≤ x.
 intros; elim x; clear x; autobatch.
qed.

theorem nle_trans: ∀x,y. x ≤ y → ∀z. y ≤ z → x ≤ z.
 intros 3; elim H; clear H x y;
 [ autobatch
 | lapply linear nle_inv_succ_1 to H3. decompose. destruct. 
   autobatch
 ].
qed.

theorem nle_false: ∀x,y. x ≤ y → y < x → False.
 intros 3; elim H; clear H x y; autobatch.
qed.

theorem nle_irrefl: ∀x. x < x → False.
 intros. autobatch.
qed.

theorem nle_irrefl_ei: ∀x, z. z ≤ x → z = succ x → False.
 intros 3; elim H; clear H x z; destruct; autobatch.
qed.

theorem nle_irrefl_smart: ∀x. x < x → False.
 intros 1. elim x; clear x; autobatch.
qed.

theorem nle_lt_or_eq: ∀y, x. x ≤ y → x < y ∨ x = y.
 intros; elim H; clear H x y;
 [ elim n; clear n
 | decompose
 ]; autobatch.
qed.
