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

include "basic_2/substitution/ldrop_append.ma".
include "basic_2/multiple/llor_ldrop.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

lemma lt_plus_SO_to_le: ∀x,y. x < y + 1 → x ≤ y.
/2 width=1 by monotonic_pred/ qed-.

(*
lemma llor_tail_frees: ∀L1,L2,L,U,d. L1 ⩖[U, d] L2 ≡ L → d < yinj (|L1|) →
                       ∀I1,W1. ⓑ{I1}W1.L1 ⊢ |L1| ϵ 𝐅*[d]⦃U⦄ →
                       ∀I2,W2. ⓑ{I1}W1.L1 ⩖[U, d] ⓑ{I2}W2.L2 ≡ ⓑ{I1}W2.L.
#L1 #L2 #L #U #d * #HL12 #HL1 #IH #Hd #I1 #W1 #HU #I2 #W2
@and3_intro [1,2: >ltail_length /2 width=1 by le_S_S/ ]
#J1 #J2 #J #K1 #K2 #K #V1 #V2 #V #i #HLK1 #HLK2 #HLK
lapply (ldrop_fwd_length_lt2 … HLK1) >ltail_length #H
lapply (lt_plus_SO_to_le … H) -H #H
elim (le_to_or_lt_eq … H) -H #H
[ elim (ldrop_O1_lt (Ⓕ) … H) #Z1 #Y1 #X1 #HLY1
  elim (ldrop_O1_lt (Ⓕ) L2 i) [2: /2 width=3 by lt_to_le_to_lt/ ] #Z2 #Y2 #X2 #HLY2
  elim (ldrop_O1_lt (Ⓕ) L i) // #Z #Y #X #HLY
  lapply (ldrop_O1_inv_append1_le … HLK1 … HLY1) /2 width=1 by lt_to_le/ -HLK1 normalize #H destruct
  lapply (ldrop_O1_inv_append1_le … HLK2 … HLY2) /3 width=3 by lt_to_le_to_lt, lt_to_le/ -HLK2 normalize #H destruct
  lapply (ldrop_O1_inv_append1_le … HLK … HLY) /2 width=1 by lt_to_le/ -HLK normalize #H destruct
  elim (IH … HLY1 HLY2 HLY) -IH -HLY1 -HLY2 -HLY *
  [ /3 width=1 by and3_intro, or3_intro0/
  | #HnU #HZ #HX
  | #Hdi #H2U #HZ #HX
  ]
| -IH destruct
  lapply (ldrop_O1_inv_append1_le … HLK1 … (⋆) ?) // -HLK1 normalize #H destruct
  lapply (ldrop_O1_inv_append1_le … HLK2 … HL12)
  lapply (ldrop_O1_inv_append1_le … HLK … (⋆) ?) // -HLK normalize #H destruct
  @or3_intro2 @and4_intro /2 width=1 by ylt_fwd_le/
]
*)
