(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "lambda-delta/syntax/term.ma".

(* RELOCATION ***************************************************************)

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

(* The basic properties *****************************************************)

lemma lift_lref_ge_minus: ∀d,e,i. d + e ≤ i → ↑[d, e] #(i - e) ≡ #i.
#d #e #i #H >(plus_minus_m_m i e) in ⊢ (? ? ? ? %) /3/
qed.

lemma lift_refl: ∀T,d. ↑[d, 0] T ≡ T.
#T elim T -T
[ //
| #i #d elim (lt_or_ge i d) /2/
| #I elim I -I /2/
]
qed.

(* The basic inversion lemmas ***********************************************)

lemma lift_inv_refl_aux: ∀d,e,T1,T2. ↑[d, e] T1 ≡ T2 → e = 0 → T1 = T2.
#d #e #T1 #T2 #H elim H -H d e T1 T2 /3/
qed.

lemma lift_inv_refl: ∀d,T1,T2. ↑[d, 0] T1 ≡ T2 → T1 = T2.
/2/ qed.

lemma lift_inv_sort1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T1 = ⋆k → T2 = ⋆k.
#d #e #T1 #T2 #H elim H -H d e T1 T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #k #H destruct
]
qed.

lemma lift_inv_sort1: ∀d,e,T2,k. ↑[d,e] ⋆k ≡ T2 → T2 = ⋆k.
/2 width=5/ qed.

lemma lift_inv_lref1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀i. T1 = #i →
                          (i < d ∧ T2 = #i) ∨ (d ≤ i ∧ T2 = #(i + e)).
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3/
| #j #d #e #Hj #i #Hi destruct /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #i #H destruct
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

lemma lift_inv_bind1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                          ∀I,V1,U1. T1 = 𝕓{I} V1.U1 →
                          ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                                   T2 = 𝕓{I} V2. U2.
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V1 #U1 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V1 #U1 #H destruct
]
qed.

lemma lift_inv_bind1: ∀d,e,T2,I,V1,U1. ↑[d,e] 𝕓{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                               T2 = 𝕓{I} V2. U2.
/2/ qed.

lemma lift_inv_flat1_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                          ∀I,V1,U1. T1 = 𝕗{I} V1.U1 →
                          ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                                   T2 = 𝕗{I} V2. U2.
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V1 #U1 #H destruct /2 width=5/
]
qed.

lemma lift_inv_flat1: ∀d,e,T2,I,V1,U1. ↑[d,e] 𝕗{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                               T2 = 𝕗{I} V2. U2.
/2/ qed.

lemma lift_inv_sort2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#d #e #T1 #T2 #H elim H -H d e T1 T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #k #H destruct
]
qed.

lemma lift_inv_sort2: ∀d,e,T1,k. ↑[d,e] T1 ≡ ⋆k → T1 = ⋆k.
/2 width=5/ qed.

lemma lift_inv_lref2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 → ∀i. T2 = #i →
                          (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3/
| #j #d #e #Hj #i #Hi destruct <minus_plus_m_m /4/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #i #H destruct
]
qed.

lemma lift_inv_lref2: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i →
                      (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
/2/ qed.

lemma lift_inv_lref2_lt: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i → i < d → T1 = #i.
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hdi #_ #Hid lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (plus_lt_false … Hdd)
qed.

lemma lift_inv_lref2_ge: ∀d,e,T1,i. ↑[d,e] T1 ≡ #i → d + e ≤ i → T1 = #(i - e).
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hid #_ #Hdi lapply (le_to_lt_to_lt … Hdi Hid) -Hdi Hid #Hdd
elim (plus_lt_false … Hdd)
qed.

lemma lift_inv_bind2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                          ∀I,V2,U2. T2 = 𝕓{I} V2.U2 →
                          ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                                   T1 = 𝕓{I} V1. U1.
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct
]
qed.

lemma lift_inv_bind2: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  𝕓{I} V2. U2 →
                      ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d+1,e] U1 ≡ U2 &
                               T1 = 𝕓{I} V1. U1.
/2/ qed.

lemma lift_inv_flat2_aux: ∀d,e,T1,T2. ↑[d,e] T1 ≡ T2 →
                          ∀I,V2,U2. T2 = 𝕗{I} V2.U2 →
                          ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                                   T1 = 𝕗{I} V1. U1.
#d #e #T1 #T2 #H elim H -H d e T1 T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #_ #_ #I #V2 #U2 #H destruct /2 width = 5/
]
qed.

lemma lift_inv_flat2: ∀d,e,T1,I,V2,U2. ↑[d,e] T1 ≡  𝕗{I} V2. U2 →
                      ∃∃V1,U1. ↑[d,e] V1 ≡ V2 & ↑[d,e] U1 ≡ U2 &
                               T1 = 𝕗{I} V1. U1.
/2/ qed.
