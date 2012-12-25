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

include "basic_2/grammar/lenv_px.ma".
include "basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

definition ltpr: relation lenv ≝ lpx tpr.

interpretation
  "context-free parallel reduction (environment)"
  'PRed L1 L2 = (ltpr L1 L2).

(* Basic properties *********************************************************)

lemma ltpr_refl: reflexive … ltpr.
/2 width=1/ qed.

lemma ltpr_append: ∀K1,K2. K1 ➡ K2 → ∀L1,L2:lenv. L1 ➡ L2 → K1 @@ L1 ➡ K2 @@ L2.
/2 width=1/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: wcpr0_gen_sort *)
lemma ltpr_inv_atom1: ∀L2. ⋆ ➡ L2 → L2 = ⋆.
/2 width=2 by lpx_inv_atom1/ qed-.

(* Basic_1: was: wcpr0_gen_head *)
lemma ltpr_inv_pair1: ∀K1,I,V1,L2. K1. ⓑ{I} V1 ➡ L2 →
                      ∃∃K2,V2. K1 ➡ K2 & V1 ➡ V2 & L2 = K2. ⓑ{I} V2.
/2 width=1 by lpx_inv_pair1/ qed-.

lemma ltpr_inv_atom2: ∀L1. L1 ➡ ⋆ → L1 = ⋆.
/2 width=2 by lpx_inv_atom2/ qed-.

lemma ltpr_inv_pair2: ∀L1,K2,I,V2. L1 ➡ K2. ⓑ{I} V2 →
                      ∃∃K1,V1. K1 ➡ K2 & V1 ➡ V2 & L1 = K1. ⓑ{I} V1.
/2 width=1 by lpx_inv_pair2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma ltpr_fwd_length: ∀L1,L2. L1 ➡ L2 → |L1| = |L2|.
/2 width=2 by lpx_fwd_length/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma ltpr_inv_append1: ∀K1,L1. ∀L:lenv. K1 @@ L1 ➡ L →
                        ∃∃K2,L2. K1 ➡ K2 & L1 ➡ L2 & L = K2 @@ L2.
/2 width=1 by lpx_inv_append1/ qed-.

lemma ltpr_inv_append2: ∀L:lenv. ∀K2,L2. L ➡ K2 @@ L2 →
                        ∃∃K1,L1. K1 ➡ K2 & L1 ➡ L2 & L = K1 @@ L1.
/2 width=1 by lpx_inv_append2/ qed-.

(* Basic_1: removed theorems 2: wcpr0_getl wcpr0_getl_back *)
