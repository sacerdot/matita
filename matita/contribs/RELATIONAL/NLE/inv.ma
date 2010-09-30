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



include "NLE/defs.ma".

theorem nle_inv_succ_1: ∀x,y. x < y → 
                        ∃z. y = succ z ∧ x ≤ z.
 intros; inversion H; clear H; intros; destruct. autobatch.
qed.

theorem nle_inv_succ_succ: ∀x,y. x < succ y → x ≤ y.
 intros; inversion H; clear H; intros; destruct. autobatch.
qed.

theorem nle_inv_succ_zero: ∀x. x < zero → False.
 intros. inversion H; clear H; intros; destruct.
qed.

theorem nle_inv_zero_2: ∀x. x ≤ zero → x = zero.
 intros; inversion H; clear H; intros; destruct. autobatch.
qed.

theorem nle_inv_succ_2: ∀y,x. x ≤ succ y →
                        x = zero ∨ ∃z. x = succ z ∧ z ≤ y.
 intros; inversion H; clear H; intros; destruct;
 autobatch depth = 4.
qed.
