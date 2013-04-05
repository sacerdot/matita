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

include "basic_2/unfold/cpss.ma".

(* SN PARALLEL UNFOLD FOR LOCAL ENVIRONMENTS ********************************)

inductive lcpss: relation lenv ≝
| lcpss_atom: lcpss (⋆) (⋆)
| lcpss_pair: ∀I,L1,L2,V1,V2. lcpss L1 L2 → L1 ⊢ V1 ▶* V2 →
              lcpss (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
.

interpretation "parallel unfold (local environment, sn variant)"
   'PSubstStarSn L1 L2 = (lcpss L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lcpss_inv_atom1_aux: ∀L1,L2. L1 ⊢ ▶* L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lcpss_inv_atom1: ∀L2. ⋆ ⊢ ▶* L2 → L2 = ⋆.
/2 width=5 by lcpss_inv_atom1_aux/ qed-.

fact lcpss_inv_pair1_aux: ∀L1,L2. L1 ⊢ ▶* L2 → ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                          ∃∃K2,V2. K1 ⊢ ▶* K2 & K1 ⊢ V1 ▶* V2 & L2 = K2. ⓑ{I} V2.
#L1 #L2 * -L1 -L2
[ #I #K1 #V1 #H destruct
| #I #L1 #L2 #V1 #V2 #HL12 #HV12 #J #K1 #W1 #H destruct /2 width=5/
]
qed-.

lemma lcpss_inv_pair1: ∀I,K1,V1,L2. K1. ⓑ{I} V1 ⊢ ▶* L2 →
                       ∃∃K2,V2. K1 ⊢ ▶* K2 & K1 ⊢ V1 ▶* V2 & L2 = K2. ⓑ{I} V2.
/2 width=5 by lcpss_inv_pair1_aux/ qed-.

fact lcpss_inv_atom2_aux: ∀L1,L2. L1 ⊢ ▶* L2 → L2 = ⋆ → L1 = ⋆.
#L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lcpss_inv_atom2: ∀L1. L1 ⊢ ▶* ⋆ → L1 = ⋆.
/2 width=5 by lcpss_inv_atom2_aux/ qed-.

fact lcpss_inv_pair2_aux: ∀L1,L2. L1 ⊢ ▶* L2 → ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                          ∃∃K1,V1. K1 ⊢ ▶* K2 & K1 ⊢ V1 ▶* V2 & L1 = K1. ⓑ{I} V1.
#L1 #L2 * -L1 -L2
[ #I #K1 #V1 #H destruct
| #I #L1 #L2 #V1 #V2 #HL12 #HV12 #J #K2 #W2 #H destruct /2 width=5/
]
qed-.

lemma lcpss_inv_pair2: ∀I,L1,K2,V2. L1 ⊢ ▶* K2. ⓑ{I} V2 →
                       ∃∃K1,V1. K1 ⊢ ▶* K2 & K1 ⊢ V1 ▶* V2 & L1 = K1. ⓑ{I} V1.
/2 width=5 by lcpss_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

lemma lcpss_refl: ∀L. L ⊢ ▶* L.
#L elim L -L // /2 width=1/
qed.

lemma lcpss_append: ∀K1,K2. K1 ⊢ ▶* K2 → ∀L1,L2. L1 ⊢ ▶* L2 →
                    L1 @@ K1 ⊢ ▶* L2 @@ K2.
#K1 #K2 #H elim H -K1 -K2 // /3 width=1/
qed.

(* Basic forward lemmas *****************************************************)

lemma lcpss_fwd_length: ∀L1,L2. L1 ⊢ ▶* L2 → |L1| = |L2|.
#L1 #L2 #H elim H -L1 -L2 normalize //
qed-.
