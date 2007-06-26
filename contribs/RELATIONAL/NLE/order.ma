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

set "baseuri" "cic:/matita/RELATIONAL/NLE/order".

include "NLE/inv.ma".

theorem nle_refl: \forall x. x <= x.
 intros; elim x; clear x; autobatch.
qed.

theorem nle_trans: \forall x,y. x <= y \to
                   \forall z. y <= z \to x <= z.
 intros 3. elim H; clear H x y;
 [ autobatch
 | lapply linear nle_inv_succ_1 to H3. decompose. subst. 
   autobatch
 ].
qed.

theorem nle_false: \forall x,y. x <= y \to y < x \to False.
 intros 3; elim H; clear H x y; autobatch.
qed.

theorem nle_irrefl: \forall x. x < x \to False.
 intros. autobatch.
qed.

theorem nle_irrefl_ei: \forall x, z. z <= x \to z = succ x \to False.
 intros 3. elim H; clear H x z; subst. autobatch.
qed.

theorem nle_irrefl_smart: \forall x. x < x \to False.
 intros 1. elim x; clear x; autobatch.
qed.

theorem nle_lt_or_eq: \forall y, x. x <= y \to x < y \lor x = y.
 intros. elim H; clear H x y;
 [ elim n; clear n
 | decompose
 ]; autobatch.
qed.
