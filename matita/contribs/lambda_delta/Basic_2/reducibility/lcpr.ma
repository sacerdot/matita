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

include "Basic_2/unfold/ltpss.ma".
include "Basic_2/reducibility/ltpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS *************)

definition lcpr: relation lenv ≝
   λL1,L2. ∃∃L. L1 ⇒ L & L [0, |L|] ≫* L2
.

interpretation
  "context-sensitive parallel reduction (environment)"
  'CPRed L1 L2 = (lcpr L1 L2).

(* Basic properties *********************************************************)

lemma lcpr_refl: ∀L. L ⊢ ⇒ L.
/2 width=3/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lcpr_inv_atom1: ∀L2. ⋆ ⊢ ⇒ L2 → L2 = ⋆.
#L2 * #L #HL >(ltpr_inv_atom1 … HL) -HL #HL2 >(ltpss_inv_atom1 … HL2) -HL2 //
qed-.
