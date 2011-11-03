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

include "Basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

inductive ltpr: relation lenv ≝
| ltpr_stom: ltpr (⋆) (⋆)
| ltpr_pair: ∀K1,K2,I,V1,V2.
             ltpr K1 K2 → V1 ⇒ V2 → ltpr (K1. 𝕓{I} V1) (K2. 𝕓{I} V2) (*𝕓*)
.

interpretation
  "context-free parallel reduction (environment)"
  'PRed L1 L2 = (ltpr L1 L2).

(* Basic properties *********************************************************)

lemma ltpr_refl: ∀L:lenv. L ⇒ L.
#L elim L -L /2/
qed.

(* Basic inversion lemmas ***************************************************)

fact ltpr_inv_atom1_aux: ∀L1,L2. L1 ⇒ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 L2
[ //
| #K1 #K2 #I #V1 #V2 #_ #_ #H destruct
]
qed.

(* Basic_1: was: wcpr0_gen_sort *)
lemma ltpr_inv_atom1: ∀L2. ⋆ ⇒ L2 → L2 = ⋆.
/2/ qed.

fact ltpr_inv_pair1_aux: ∀L1,L2. L1 ⇒ L2 → ∀K1,I,V1. L1 = K1. 𝕓{I} V1 →
                         ∃∃K2,V2. K1 ⇒ K2 & V1 ⇒ V2 & L2 = K2. 𝕓{I} V2.
#L1 #L2 * -L1 L2
[ #K1 #I #V1 #H destruct
| #K1 #K2 #I #V1 #V2 #HK12 #HV12 #L #J #W #H destruct - K1 I V1 /2 width=5/
]
qed.

(* Basic_1: was: wcpr0_gen_head *)
lemma ltpr_inv_pair1: ∀K1,I,V1,L2. K1. 𝕓{I} V1 ⇒ L2 →
                      ∃∃K2,V2. K1 ⇒ K2 & V1 ⇒ V2 & L2 = K2. 𝕓{I} V2.
/2/ qed.

fact ltpr_inv_atom2_aux: ∀L1,L2. L1 ⇒ L2 → L2 = ⋆ → L1 = ⋆.
#L1 #L2 * -L1 L2
[ //
| #K1 #K2 #I #V1 #V2 #_ #_ #H destruct
]
qed.

lemma ltpr_inv_atom2: ∀L1. L1 ⇒ ⋆ → L1 = ⋆.
/2/ qed.

fact ltpr_inv_pair2_aux: ∀L1,L2. L1 ⇒ L2 → ∀K2,I,V2. L2 = K2. 𝕓{I} V2 →
                         ∃∃K1,V1. K1 ⇒ K2 & V1 ⇒ V2 & L1 = K1. 𝕓{I} V1.
#L1 #L2 * -L1 L2
[ #K2 #I #V2 #H destruct
| #K1 #K2 #I #V1 #V2 #HK12 #HV12 #K #J #W #H destruct -K2 I V2 /2 width=5/
]
qed.

lemma ltpr_inv_pair2: ∀L1,K2,I,V2. L1 ⇒ K2. 𝕓{I} V2 →
                      ∃∃K1,V1. K1 ⇒ K2 & V1 ⇒ V2 & L1 = K1. 𝕓{I} V1.
/2/ qed.

(* Basic forward lemmas *****************************************************)

lemma ltpr_fwd_length: ∀L1,L2. L1 ⇒ L2 → |L1| = |L2|.
#L1 #L2 #H elim H -H L1 L2; normalize //
qed.

(* Basic_1: removed theorems 2: wcpr0_getl wcpr0_getl_back *)
