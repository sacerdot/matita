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

include "basic_2/multiple/frees_append.ma".
include "basic_2/multiple/llor.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

(* Alternative definition ***************************************************)

lemma llor_tail_frees: ∀L1,L2,L,U,d. L1 ⩖[U, d] L2 ≡ L → d ≤ yinj (|L1|) →
                       ∀I1,W1. ⓑ{I1}W1.L1 ⊢ |L1| ϵ 𝐅*[d]⦃U⦄ →
                       ∀I2,W2. ⓑ{I1}W1.L1 ⩖[U, d] ⓑ{I2}W2.L2 ≡ ⓑ{I2}W2.L.
#L1 #L2 #L #U #d * #HL12 #HL1 #IH #Hd #I1 #W1 #HU #I2 #W2
@and3_intro [1,2: >ltail_length /2 width=1 by le_S_S/ ]
#J1 #J2 #J #K1 #K2 #K #V1 #V2 #V #i #HLK1 #HLK2 #HLK
lapply (drop_fwd_length_lt2 … HLK1) >ltail_length #H
lapply (lt_plus_SO_to_le … H) -H #H
elim (le_to_or_lt_eq … H) -H #H
[ elim (drop_O1_lt (Ⓕ) … H) #Z1 #Y1 #X1 #HLY1
  elim (drop_O1_lt (Ⓕ) L2 i) // #Z2 #Y2 #X2 #HLY2
  elim (drop_O1_lt (Ⓕ) L i) // #Z #Y #X #HLY
  lapply (drop_O1_inv_append1_le … HLK1 … HLY1) /2 width=1 by lt_to_le/ -HLK1 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK2 … HLY2) /2 width=1 by lt_to_le/ -HLK2 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK … HLY) /2 width=1 by lt_to_le/ -HLK normalize #H destruct
  elim (IH … HLY1 HLY2 HLY) -IH -HLY1 -HLY2 -HLY *
  [ /3 width=1 by and3_intro, or3_intro0/
  | /6 width=2 by frees_inv_append, lt_to_le, or3_intro1, and3_intro/
  | /5 width=1 by frees_append, lt_to_le, or3_intro2, and4_intro/
  ]
| -IH -HLK1 destruct
  lapply (drop_O1_inv_append1_le … HLK2 … (⋆) ?) // -HLK2 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK … (⋆) ?) // -HLK normalize #H destruct
  /3 width=1 by or3_intro2, and4_intro/
]
qed.

lemma llor_tail_cofrees: ∀L1,L2,L,U,d. L1 ⩖[U, d] L2 ≡ L →
                         ∀I1,W1. (ⓑ{I1}W1.L1 ⊢ |L1| ϵ 𝐅*[d]⦃U⦄ → ⊥) →
                         ∀I2,W2. ⓑ{I1}W1.L1 ⩖[U, d] ⓑ{I2}W2.L2 ≡ ⓑ{I1}W1.L.
#L1 #L2 #L #U #d * #HL12 #HL1 #IH #I1 #W1 #HU #I2 #W2
@and3_intro [1,2: >ltail_length /2 width=1 by le_S_S/ ]
#J1 #J2 #J #K1 #K2 #K #V1 #V2 #V #i #HLK1 #HLK2 #HLK
lapply (drop_fwd_length_lt2 … HLK1) >ltail_length #H
lapply (lt_plus_SO_to_le … H) -H #H
elim (le_to_or_lt_eq … H) -H #H
[ elim (drop_O1_lt (Ⓕ) … H) #Z1 #Y1 #X1 #HLY1
  elim (drop_O1_lt (Ⓕ) L2 i) // #Z2 #Y2 #X2 #HLY2
  elim (drop_O1_lt (Ⓕ) L i) // #Z #Y #X #HLY
  lapply (drop_O1_inv_append1_le … HLK1 … HLY1) /2 width=1 by lt_to_le/ -HLK1 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK2 … HLY2) /2 width=1 by lt_to_le/ -HLK2 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK … HLY) /2 width=1 by lt_to_le/ -HLK normalize #H destruct
  elim (IH … HLY1 HLY2 HLY) -IH -HLY1 -HLY2 -HLY *
  [ /3 width=1 by and3_intro, or3_intro0/
  | /6 width=2 by frees_inv_append, lt_to_le, or3_intro1, and3_intro/
  | /5 width=1 by frees_append, lt_to_le, or3_intro2, and4_intro/
  ]
| -IH -HLK2 destruct
  lapply (drop_O1_inv_append1_le … HLK1 … (⋆) ?) // -HLK1 normalize #H destruct
  lapply (drop_O1_inv_append1_le … HLK … (⋆) ?) // -HLK normalize #H destruct
  /4 width=1 by or3_intro1, and3_intro/
]
qed.
