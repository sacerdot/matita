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

include "Basic-2/grammar/term_weight.ma".

(* RELOCATION ***************************************************************)

(* Basic-1: includes:
            lift_sort lift_lref_lt lift_lref_ge lift_bind lift_flat
*)
inductive lift: term → nat → nat → term → Prop ≝
| lift_sort   : ∀k,d,e. lift (⋆k) d e (⋆k)
| lift_lref_lt: ∀i,d,e. i < d → lift (#i) d e (#i)
| lift_lref_ge: ∀i,d,e. d ≤ i → lift (#i) d e (#(i + e))
| lift_bind   : ∀I,V1,V2,T1,T2,d,e.
                lift V1 d e V2 → lift T1 (d + 1) e T2 →
                lift (𝕓{I} V1. T1) d e (𝕓{I} V2. T2)
| lift_flat   : ∀I,V1,V2,T1,T2,d,e.
                lift V1 d e V2 → lift T1 d e T2 →
                lift (𝕗{I} V1. T1) d e (𝕗{I} V2. T2)
.

interpretation "relocation" 'RLift T1 d e T2 = (lift T1 d e T2).

(* Basic properties *********************************************************)

(* Basic-1: was: lift_lref_gt *)
lemma lift_lref_ge_minus: ∀d,e,i. d + e ≤ i → ↑[d, e] #(i - e) ≡ #i.
#d #e #i #H >(plus_minus_m_m i e) in ⊢ (? ? ? ? %) /3/
qed.

(* Basic-1: was: lift_r *)
lemma lift_refl: ∀T,d. ↑[d, 0] T ≡ T.
#T elim T -T
[ * #i // #d elim (lt_or_ge i d) /2/
| * /2/
]
qed.

lemma lift_total: ∀T1,d,e. ∃T2. ↑[d,e] T1 ≡ T2.
#T1 elim T1 -T1
[ * #i /2/ #d #e elim (lt_or_ge i d) /3/
| * #I #V1 #T1 #IHV1 #IHT1 #d #e
  elim (IHV1 d e) -IHV1 #V2 #HV12
  [ elim (IHT1 (d+1) e) -IHT1 /3/
  | elim (IHT1 d e) -IHT1 /3/
  ]
]
qed.

(* Basic-1: was: lift_free (right to left) *)
lemma lift_split: ∀d1,e2,T1,T2. ↑[d1, e2] T1 ≡ T2 → ∀d2,e1.
                                d1 ≤ d2 → d2 ≤ d1 + e1 → e1 ≤ e2 →
                                ∃∃T. ↑[d1, e1] T1 ≡ T & ↑[d2, e2 - e1] T ≡ T2.
#d1 #e2 #T1 #T2 #H elim H -H d1 e2 T1 T2
[ /3/
| #i #d1 #e2 #Hid1 #d2 #e1 #Hd12 #_ #_
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2 /4/
| #i #d1 #e2 #Hid1 #d2 #e1 #_ #Hd21 #He12
  lapply (transitive_le …(i+e1) Hd21 ?) /2/ -Hd21 #Hd21
  <(arith_d1 i e2 e1) // /3/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT (d2+1) … ? ? He12) /3 width = 5/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT d2 … ? ? He12) /3 width = 5/
]
qed.

(* Basic forward lemmas *****************************************************)

lemma tw_lift: ∀d,e,T1,T2. ↑[d, e] T1 ≡ T2 → #[T1] = #[T2].
#d #e #T1 #T2 #H elim H -d e T1 T2; normalize //
qed.

(* Basic inversion lemmas ***************************************************)

fact lift_inv_refl_aux: ∀d,e,T1,T2. ↑[d, e] T1 ≡ T2 → e = 0 → T1 = T2.
#d #e #T1 #T2 #H elim H -H d e T1 T2 /3/
qed.

lemma lift_inv_refl: ∀d,T1,T2. ↑[d, 0] T1 ≡ T2 → T1 = T2.
/2/ qed.

fact lift_inv_sort1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T1 = ⋆k → T2 = ⋆k.
#d #e #T1 #T2 * -d e T1 T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

lemma lift_inv_sort1: ∀d,e,T2,k. ↑[d,e] ⋆k ≡ T2 → T2 = ⋆k.
/2 width=5/ qed.

fact lift_inv_lref1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀i. T1 = #i →
                         (i < d ∧ T2 = #i) ∨ (d ≤ i ∧ T2 = #(i + e)).
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3/
| #j #d #e #Hj #i #Hi destruct /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
]
qed.

lemma lift_inv_lref1: ∀d,e,T2,i. ↑[d,e] #i ≡ T2 →
                      (i < d ∧ T2 = #i) ∨ (d ≤ i ∧ T2 = #(i + e)).
/2/ qed.

lemma lift_inv_lref1_lt: ∀d,e,T2,i. ↑[d,e] #i ≡ T2 → i < d → T2 = #i.
#d #e #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hdi #_ #Hid lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (lt_refl_false … Hdd)
qed.

lemma lift_inv_lref1_ge: ∀d,e,T2,i. ↑[d,e] #i ≡ T2 → d ≤ i → T2 = #(i + e).
#d #e #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hid #_ #Hdi lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (lt_refl_false … Hdd)
qed.

fact lift_inv_bind1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                         ∀I,V1,U1. T1 = 𝕓{I} V1.U1 →
                         ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                                  T2 = 𝕓{I} V2. U2.
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct
]
qed.

lemma lift_inv_bind1: ∀d,e,T2,I,V1,U1. ↑[d,e] 𝕓{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                               T2 = 𝕓{I} V2. U2.
/2/ qed.

fact lift_inv_flat1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                         ∀I,V1,U1. T1 = 𝕗{I} V1.U1 →
                         ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                                  T2 = 𝕗{I} V2. U2.
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct /2 width=5/
]
qed.

lemma lift_inv_flat1: ∀d,e,T2,I,V1,U1. ↑[d,e] 𝕗{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                               T2 = 𝕗{I} V2. U2.
/2/ qed.

fact lift_inv_sort2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#d #e #T1 #T2 * -d e T1 T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

(* Basic-1: was: lift_gen_sort *)
lemma lift_inv_sort2: ∀d,e,T1,k. ↑[d,e] T1 ≡ ⋆k → T1 = ⋆k.
/2 width=5/ qed.

fact lift_inv_lref2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀i. T2 = #i →
                         (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3/
| #j #d #e #Hj #i #Hi destruct <minus_plus_m_m /4/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
]
qed.

(* Basic-1: was: lift_gen_lref *)
lemma lift_inv_lref2: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i →
                      (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
/2/ qed.

(* Basic-1: was: lift_gen_lref_lt *)
lemma lift_inv_lref2_lt: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i → i < d → T1 = #i.
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hdi #_ #Hid lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (plus_lt_false … Hdd)
qed.

(* Basic-1: was: lift_gen_lref_false *)

(* Basic-1: was: lift_gen_lref_ge *)
lemma lift_inv_lref2_ge: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i → d + e ≤ i → T1 = #(i - e).
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hid #_ #Hdi lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (plus_lt_false … Hdd)
qed.

fact lift_inv_bind2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                         ∀I,V2,U2. T2 = 𝕓{I} V2.U2 →
                         ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                                  T1 = 𝕓{I} V1. U1.
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct
]
qed.

(* Basic-1: was: lift_gen_bind *)
lemma lift_inv_bind2: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  𝕓{I} V2. U2 →
                      ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                               T1 = 𝕓{I} V1. U1.
/2/ qed.

fact lift_inv_flat2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                         ∀I,V2,U2. T2 = 𝕗{I} V2.U2 →
                         ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                                  T1 = 𝕗{I} V1. U1.
#d #e #T1 #T2 * -d e T1 T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct /2 width = 5/
]
qed.

(* Basic-1: was: lift_gen_flat *)
lemma lift_inv_flat2: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  𝕗{I} V2. U2 →
                      ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                               T1 = 𝕗{I} V1. U1.
/2/ qed.

(* Basic-1: removed theorems 7:
            lift_head lift_gen_head
            lift_weight_map lift_weight lift_weight_add lift_weight_add_O
            lift_tlt_dx
*)
