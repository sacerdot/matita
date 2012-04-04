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

include "basic_2/reducibility/lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL CONVERSION ON LOCAL ENVIRONMENTS **************)

definition lcpc: relation lenv ≝
   λL1,L2. L1 ⊢ ➡ L2 ∨ L2 ⊢ ➡ L1.

interpretation
   "context-sensitive parallel conversion (local environment)"
   'CPConv L1 L2 = (lcpc L1 L2).

(* Basic properties *********************************************************)

lemma lcpc_refl: ∀L. L ⊢ ⬌ L.
/2 width=1/ qed.

lemma lcpc_sym: ∀L1,L2. L1 ⊢ ⬌ L2 → L2 ⊢ ⬌ L1.
#L1 #L2 * /2 width=1/
qed.

lemma lcpc_lcpr: ∀L1,L2. L1 ⊢ ⬌ L2 → ∃∃L. L1 ⊢ ➡ L & L2 ⊢ ➡ L.
#L1 #L2 * /2 width=3/
qed.
