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

include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL CONVERSION ON LOCAL ENVIRONMENTS **********************)

definition lfpc: relation lenv ≝
   λL1,L2. ⦃L1⦄ ➡ ⦃L2⦄ ∨ ⦃L2⦄ ➡ ⦃L1⦄.

interpretation
   "focalized parallel conversion (local environment)"
   'FocalizedPConv L1 L2 = (lfpc L1 L2).

(* Basic properties *********************************************************)

lemma lfpc_refl: ∀L. ⦃L⦄ ⬌ ⦃L⦄.
/2 width=1/ qed.

lemma lfpc_sym: ∀L1,L2. ⦃L1⦄ ⬌ ⦃L2⦄ → ⦃L2⦄ ⬌ ⦃L1⦄.
#L1 #L2 * /2 width=1/
qed.

lemma lfpc_lfpr: ∀L1,L2. ⦃L1⦄ ⬌ ⦃L2⦄ → ∃∃L. ⦃L1⦄ ➡ ⦃L⦄ & ⦃L2⦄ ➡ ⦃L⦄.
#L1 #L2 * /2 width=3/
qed.
