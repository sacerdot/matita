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

include "basic_2/unfold/lpss.ma".
include "basic_2/restricted/cpqs.ma".

(* SN RESTRICTED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS ****************)

definition lpqs: relation lenv ≝ lpx_sn cpqs. 

interpretation "restricted parallel computation (local environment, sn variant)"
   'PRestStarSn L1 L2 = (lpqs L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpqs_inv_atom1: ∀L2. ⋆ ⊢ ➤* L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

lemma lpqs_inv_pair1: ∀I,K1,V1,L2. K1. ⓑ{I} V1 ⊢ ➤* L2 →
                      ∃∃K2,V2. K1 ⊢ ➤* K2 & K1 ⊢ V1 ➤* V2 & L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

lemma lpqs_inv_atom2: ∀L1. L1 ⊢ ➤* ⋆ → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

lemma lpqs_inv_pair2: ∀I,L1,K2,V2. L1 ⊢ ➤* K2. ⓑ{I} V2 →
                      ∃∃K1,V1. K1 ⊢ ➤* K2 & K1 ⊢ V1 ➤* V2 & L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was by definition: csubst1_refl *)
lemma lpqs_refl: ∀L. L ⊢ ➤* L.
/2 width=1 by lpx_sn_refl/ qed.

lemma lpqs_append: ∀K1,K2. K1 ⊢ ➤* K2 → ∀L1,L2. L1 ⊢ ➤* L2 →
                   L1 @@ K1 ⊢ ➤* L2 @@ K2.
/3 width=1 by lpx_sn_append, cpqs_append/ qed.

lemma lpss_lpqs: ∀L1,L2. L1 ⊢ ▶* L2 → L1 ⊢ ➤* L2.
#L1 #L2 #H elim H -L1 -L2 // /3 width=1/
qed.

(* Basic forward lemmas *****************************************************)

lemma lpqs_fwd_length: ∀L1,L2. L1 ⊢ ➤* L2 → |L1| = |L2|.
/2 width=2 by lpx_sn_fwd_length/ qed-.
