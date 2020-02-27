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

include "ground/xoa/ex_3_2.ma".
include "basic_2A/notation/relations/rlift_4.ma".
include "basic_2A/grammar/term_weight.ma".
include "basic_2A/grammar/term_simple.ma".

(* BASIC TERM RELOCATION ****************************************************)

(* Basic_1: includes:
            lift_sort lift_lref_lt lift_lref_ge lift_bind lift_flat
*)
inductive lift: relation4 nat nat term term ≝
| lift_sort   : ∀k,l,m. lift l m (⋆k) (⋆k)
| lift_lref_lt: ∀i,l,m. i < l → lift l m (#i) (#i)
| lift_lref_ge: ∀i,l,m. l ≤ i → lift l m (#i) (#(i + m))
| lift_gref   : ∀p,l,m. lift l m (§p) (§p)
| lift_bind   : ∀a,I,V1,V2,T1,T2,l,m.
                lift l m V1 V2 → lift (l + 1) m T1 T2 →
                lift l m (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| lift_flat   : ∀I,V1,V2,T1,T2,l,m.
                lift l m V1 V2 → lift l m T1 T2 →
                lift l m (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
.

interpretation "relocation" 'RLift l m T1 T2 = (lift l m T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lift_inv_O2_aux: ∀l,m,T1,T2. ⬆[l, m] T1 ≡ T2 → m = 0 → T1 = T2.
#l #m #T1 #T2 #H elim H -l -m -T1 -T2 /3 width=1 by eq_f2/
qed-.

lemma lift_inv_O2: ∀l,T1,T2. ⬆[l, 0] T1 ≡ T2 → T1 = T2.
/2 width=4 by lift_inv_O2_aux/ qed-.

fact lift_inv_sort1_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀k. T1 = ⋆k → T2 = ⋆k.
#l #m #T1 #T2 * -l -m -T1 -T2 //
[ #i #l #m #_ #k #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
]
qed-.

lemma lift_inv_sort1: ∀l,m,T2,k. ⬆[l,m] ⋆k ≡ T2 → T2 = ⋆k.
/2 width=5 by lift_inv_sort1_aux/ qed-.

fact lift_inv_lref1_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀i. T1 = #i →
                         (i < l ∧ T2 = #i) ∨ (l ≤ i ∧ T2 = #(i + m)).
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #i #H destruct
| #j #l #m #Hj #i #Hi destruct /3 width=1 by or_introl, conj/
| #j #l #m #Hj #i #Hi destruct /3 width=1 by or_intror, conj/
| #p #l #m #i #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #i #H destruct
]
qed-.

lemma lift_inv_lref1: ∀l,m,T2,i. ⬆[l,m] #i ≡ T2 →
                      (i < l ∧ T2 = #i) ∨ (l ≤ i ∧ T2 = #(i + m)).
/2 width=3 by lift_inv_lref1_aux/ qed-.

lemma lift_inv_lref1_lt: ∀l,m,T2,i. ⬆[l,m] #i ≡ T2 → i < l → T2 = #i.
#l #m #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hli #_ #Hil lapply (le_to_lt_to_lt … Hli Hil) -Hli -Hil #Hll
elim (lt_refl_false … Hll)
qed-.

lemma lift_inv_lref1_ge: ∀l,m,T2,i. ⬆[l,m] #i ≡ T2 → l ≤ i → T2 = #(i + m).
#l #m #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hil #_ #Hli lapply (le_to_lt_to_lt … Hli Hil) -Hli -Hil #Hll
elim (lt_refl_false … Hll)
qed-.

fact lift_inv_gref1_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀p. T1 = §p → T2 = §p.
#l #m #T1 #T2 * -l -m -T1 -T2 //
[ #i #l #m #_ #k #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
]
qed-.

lemma lift_inv_gref1: ∀l,m,T2,p. ⬆[l,m] §p ≡ T2 → T2 = §p.
/2 width=5 by lift_inv_gref1_aux/ qed-.

fact lift_inv_bind1_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 →
                         ∀a,I,V1,U1. T1 = ⓑ{a,I} V1.U1 →
                         ∃∃V2,U2. ⬆[l,m] V1 ≡ V2 & ⬆[l+1,m] U1 ≡ U2 &
                                  T2 = ⓑ{a,I} V2. U2.
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #a #I #V1 #U1 #H destruct
| #i #l #m #_ #a #I #V1 #U1 #H destruct
| #i #l #m #_ #a #I #V1 #U1 #H destruct
| #p #l #m #a #I #V1 #U1 #H destruct
| #b #J #W1 #W2 #T1 #T2 #l #m #HW #HT #a #I #V1 #U1 #H destruct /2 width=5 by ex3_2_intro/
| #J #W1 #W2 #T1 #T2 #l #m #_ #HT #a #I #V1 #U1 #H destruct
]
qed-.

lemma lift_inv_bind1: ∀l,m,T2,a,I,V1,U1. ⬆[l,m] ⓑ{a,I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ⬆[l,m] V1 ≡ V2 & ⬆[l+1,m] U1 ≡ U2 &
                               T2 = ⓑ{a,I} V2. U2.
/2 width=3 by lift_inv_bind1_aux/ qed-.

fact lift_inv_flat1_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 →
                         ∀I,V1,U1. T1 = ⓕ{I} V1.U1 →
                         ∃∃V2,U2. ⬆[l,m] V1 ≡ V2 & ⬆[l,m] U1 ≡ U2 &
                                  T2 = ⓕ{I} V2. U2.
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #I #V1 #U1 #H destruct
| #i #l #m #_ #I #V1 #U1 #H destruct
| #i #l #m #_ #I #V1 #U1 #H destruct
| #p #l #m #I #V1 #U1 #H destruct
| #a #J #W1 #W2 #T1 #T2 #l #m #_ #_ #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #l #m #HW #HT #I #V1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lift_inv_flat1: ∀l,m,T2,I,V1,U1. ⬆[l,m] ⓕ{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ⬆[l,m] V1 ≡ V2 & ⬆[l,m] U1 ≡ U2 &
                               T2 = ⓕ{I} V2. U2.
/2 width=3 by lift_inv_flat1_aux/ qed-.

fact lift_inv_sort2_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#l #m #T1 #T2 * -l -m -T1 -T2 //
[ #i #l #m #_ #k #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
]
qed-.

(* Basic_1: was: lift_gen_sort *)
lemma lift_inv_sort2: ∀l,m,T1,k. ⬆[l,m] T1 ≡ ⋆k → T1 = ⋆k.
/2 width=5 by lift_inv_sort2_aux/ qed-.

fact lift_inv_lref2_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀i. T2 = #i →
                         (i < l ∧ T1 = #i) ∨ (l + m ≤ i ∧ T1 = #(i - m)).
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #i #H destruct
| #j #l #m #Hj #i #Hi destruct /3 width=1 by or_introl, conj/
| #j #l #m #Hj #i #Hi destruct <minus_plus_m_m /4 width=1 by monotonic_le_plus_l, or_intror, conj/
| #p #l #m #i #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #i #H destruct
]
qed-.

(* Basic_1: was: lift_gen_lref *)
lemma lift_inv_lref2: ∀l,m,T1,i. ⬆[l,m] T1 ≡ #i →
                      (i < l ∧ T1 = #i) ∨ (l + m ≤ i ∧ T1 = #(i - m)).
/2 width=3 by lift_inv_lref2_aux/ qed-.

(* Basic_1: was: lift_gen_lref_lt *)
lemma lift_inv_lref2_lt: ∀l,m,T1,i. ⬆[l,m] T1 ≡ #i → i < l → T1 = #i.
#l #m #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hli #_ #Hil lapply (le_to_lt_to_lt … Hli Hil) -Hli -Hil #Hll
elim (lt_inv_plus_l … Hll) -Hll #Hll
elim (lt_refl_false … Hll)
qed-.

(* Basic_1: was: lift_gen_lref_false *)
lemma lift_inv_lref2_be: ∀l,m,T1,i. ⬆[l,m] T1 ≡ #i →
                         l ≤ i → i < l + m → ⊥.
#l #m #T1 #i #H elim (lift_inv_lref2 … H) -H *
[ #H1 #_ #H2 #_ | #H2 #_ #_ #H1 ]
lapply (le_to_lt_to_lt … H2 H1) -H2 -H1 #H
elim (lt_refl_false … H)
qed-.

(* Basic_1: was: lift_gen_lref_ge *)
lemma lift_inv_lref2_ge: ∀l,m,T1,i. ⬆[l,m] T1 ≡ #i → l + m ≤ i → T1 = #(i - m).
#l #m #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hil #_ #Hli lapply (le_to_lt_to_lt … Hli Hil) -Hli -Hil #Hll
elim (lt_inv_plus_l … Hll) -Hll #Hll
elim (lt_refl_false … Hll)
qed-.

fact lift_inv_gref2_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 → ∀p. T2 = §p → T1 = §p.
#l #m #T1 #T2 * -l -m -T1 -T2 //
[ #i #l #m #_ #k #H destruct
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #k #H destruct
]
qed-.

lemma lift_inv_gref2: ∀l,m,T1,p. ⬆[l,m] T1 ≡ §p → T1 = §p.
/2 width=5 by lift_inv_gref2_aux/ qed-.

fact lift_inv_bind2_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 →
                         ∀a,I,V2,U2. T2 = ⓑ{a,I} V2.U2 →
                         ∃∃V1,U1. ⬆[l,m] V1 ≡ V2 & ⬆[l+1,m] U1 ≡ U2 &
                                  T1 = ⓑ{a,I} V1. U1.
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #a #I #V2 #U2 #H destruct
| #i #l #m #_ #a #I #V2 #U2 #H destruct
| #i #l #m #_ #a #I #V2 #U2 #H destruct
| #p #l #m #a #I #V2 #U2 #H destruct
| #b #J #W1 #W2 #T1 #T2 #l #m #HW #HT #a #I #V2 #U2 #H destruct /2 width=5 by ex3_2_intro/
| #J #W1 #W2 #T1 #T2 #l #m #_ #_ #a #I #V2 #U2 #H destruct
]
qed-.

(* Basic_1: was: lift_gen_bind *)
lemma lift_inv_bind2: ∀l,m,T1,a,I,V2,U2. ⬆[l,m] T1 ≡ ⓑ{a,I} V2. U2 →
                      ∃∃V1,U1. ⬆[l,m] V1 ≡ V2 & ⬆[l+1,m] U1 ≡ U2 &
                               T1 = ⓑ{a,I} V1. U1.
/2 width=3 by lift_inv_bind2_aux/ qed-.

fact lift_inv_flat2_aux: ∀l,m,T1,T2. ⬆[l,m] T1 ≡ T2 →
                         ∀I,V2,U2. T2 = ⓕ{I} V2.U2 →
                         ∃∃V1,U1. ⬆[l,m] V1 ≡ V2 & ⬆[l,m] U1 ≡ U2 &
                                  T1 = ⓕ{I} V1. U1.
#l #m #T1 #T2 * -l -m -T1 -T2
[ #k #l #m #I #V2 #U2 #H destruct
| #i #l #m #_ #I #V2 #U2 #H destruct
| #i #l #m #_ #I #V2 #U2 #H destruct
| #p #l #m #I #V2 #U2 #H destruct
| #a #J #W1 #W2 #T1 #T2 #l #m #_ #_ #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #l #m #HW #HT #I #V2 #U2 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: was: lift_gen_flat *)
lemma lift_inv_flat2: ∀l,m,T1,I,V2,U2. ⬆[l,m] T1 ≡  ⓕ{I} V2. U2 →
                      ∃∃V1,U1. ⬆[l,m] V1 ≡ V2 & ⬆[l,m] U1 ≡ U2 &
                               T1 = ⓕ{I} V1. U1.
/2 width=3 by lift_inv_flat2_aux/ qed-.

lemma lift_inv_pair_xy_x: ∀l,m,I,V,T. ⬆[l, m] ②{I} V. T ≡ V → ⊥.
#l #m #J #V elim V -V
[ * #i #T #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct
  | elim (lift_inv_lref2 … H) -H * #_ #H destruct
  | lapply (lift_inv_gref2 … H) -H #H destruct
  ]
| * [ #a ] #I #W2 #U2 #IHW2 #_ #T #H
  [ elim (lift_inv_bind2 … H) -H #W1 #U1 #HW12 #_ #H destruct /2 width=2 by/
  | elim (lift_inv_flat2 … H) -H #W1 #U1 #HW12 #_ #H destruct /2 width=2 by/
  ]
]
qed-.

(* Basic_1: was: thead_x_lift_y_y *)
lemma lift_inv_pair_xy_y: ∀I,T,V,l,m. ⬆[l, m] ②{I} V. T ≡ T → ⊥.
#J #T elim T -T
[ * #i #V #l #m #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct
  | elim (lift_inv_lref2 … H) -H * #_ #H destruct
  | lapply (lift_inv_gref2 … H) -H #H destruct
  ]
| * [ #a ] #I #W2 #U2 #_ #IHU2 #V #l #m #H
  [ elim (lift_inv_bind2 … H) -H #W1 #U1 #_ #HU12 #H destruct /2 width=4 by/
  | elim (lift_inv_flat2 … H) -H #W1 #U1 #_ #HU12 #H destruct /2 width=4 by/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lift_fwd_pair1: ∀I,T2,V1,U1,l,m. ⬆[l,m] ②{I}V1.U1 ≡ T2 →
                      ∃∃V2,U2. ⬆[l,m] V1 ≡ V2 & T2 = ②{I}V2.U2.
* [ #a ] #I #T2 #V1 #U1 #l #m #H
[ elim (lift_inv_bind1 … H) -H /2 width=4 by ex2_2_intro/
|  elim (lift_inv_flat1 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

lemma lift_fwd_pair2: ∀I,T1,V2,U2,l,m. ⬆[l,m] T1 ≡ ②{I}V2.U2 →
                      ∃∃V1,U1. ⬆[l,m] V1 ≡ V2 & T1 = ②{I}V1.U1.
* [ #a ] #I #T1 #V2 #U2 #l #m #H
[ elim (lift_inv_bind2 … H) -H /2 width=4 by ex2_2_intro/
|  elim (lift_inv_flat2 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

lemma lift_fwd_tw: ∀l,m,T1,T2. ⬆[l, m] T1 ≡ T2 → ♯{T1} = ♯{T2}.
#l #m #T1 #T2 #H elim H -l -m -T1 -T2 normalize //
qed-.

lemma lift_simple_dx: ∀l,m,T1,T2. ⬆[l, m] T1 ≡ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#l #m #T1 #T2 #H elim H -l -m -T1 -T2 //
#a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #_ #_ #H
elim (simple_inv_bind … H)
qed-.

lemma lift_simple_sn: ∀l,m,T1,T2. ⬆[l, m] T1 ≡ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
#l #m #T1 #T2 #H elim H -l -m -T1 -T2 //
#a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #_ #_ #H
elim (simple_inv_bind … H)
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: lift_lref_gt *)
lemma lift_lref_ge_minus: ∀l,m,i. l + m ≤ i → ⬆[l, m] #(i - m) ≡ #i.
#l #m #i #H >(plus_minus_m_m i m) in ⊢ (? ? ? ? %); /3 width=2 by lift_lref_ge, le_plus_to_minus_r, le_plus_b/
qed.

lemma lift_lref_ge_minus_eq: ∀l,m,i,j. l + m ≤ i → j = i - m → ⬆[l, m] #j ≡ #i.
/2 width=1 by lift_lref_ge_minus/ qed-.

(* Basic_1: was: lift_r *)
lemma lift_refl: ∀T,l. ⬆[l, 0] T ≡ T.
#T elim T -T
[ * #i // #l elim (lt_or_ge i l) /2 width=1 by lift_lref_lt, lift_lref_ge/
| * /2 width=1 by lift_bind, lift_flat/
]
qed.

lemma lift_total: ∀T1,l,m. ∃T2. ⬆[l,m] T1 ≡ T2.
#T1 elim T1 -T1
[ * #i /2 width=2 by lift_sort, lift_gref, ex_intro/
  #l #m elim (lt_or_ge i l) /3 width=2 by lift_lref_lt, lift_lref_ge, ex_intro/
| * [ #a ] #I #V1 #T1 #IHV1 #IHT1 #l #m
  elim (IHV1 l m) -IHV1 #V2 #HV12
  [ elim (IHT1 (l+1) m) -IHT1 /3 width=2 by lift_bind, ex_intro/
  | elim (IHT1 l m) -IHT1 /3 width=2 by lift_flat, ex_intro/
  ]
]
qed.

(* Basic_1: was: lift_free (right to left) *)
lemma lift_split: ∀l1,m2,T1,T2. ⬆[l1, m2] T1 ≡ T2 →
                  ∀l2,m1. l1 ≤ l2 → l2 ≤ l1 + m1 → m1 ≤ m2 →
                  ∃∃T. ⬆[l1, m1] T1 ≡ T & ⬆[l2, m2 - m1] T ≡ T2.
#l1 #m2 #T1 #T2 #H elim H -l1 -m2 -T1 -T2
[ /3 width=3 by lift_sort, ex2_intro/
| #i #l1 #m2 #Hil1 #l2 #m1 #Hl12 #_ #_
  lapply (lt_to_le_to_lt … Hil1 Hl12) -Hl12 #Hil2 /4 width=3 by lift_lref_lt, ex2_intro/
| #i #l1 #m2 #Hil1 #l2 #m1 #_ #Hl21 #Hm12
  lapply (transitive_le … (i+m1) Hl21 ?) /2 width=1 by monotonic_le_plus_l/ -Hl21 #Hl21
  >(plus_minus_m_m m2 m1 ?) /3 width=3 by lift_lref_ge, ex2_intro/
| /3 width=3 by lift_gref, ex2_intro/
| #a #I #V1 #V2 #T1 #T2 #l1 #m2 #_ #_ #IHV #IHT #l2 #m1 #Hl12 #Hl21 #Hm12
  elim (IHV … Hl12 Hl21 Hm12) -IHV #V0 #HV0a #HV0b
  elim (IHT (l2+1) … ? ? Hm12) /3 width=5 by lift_bind, monotonic_le_plus_l, ex2_intro/
| #I #V1 #V2 #T1 #T2 #l1 #m2 #_ #_ #IHV #IHT #l2 #m1 #Hl12 #Hl21 #Hm12
  elim (IHV … Hl12 Hl21 Hm12) -IHV #V0 #HV0a #HV0b
  elim (IHT l2 … ? ? Hm12) /3 width=5 by lift_flat, ex2_intro/
]
qed.

(* Basic_1: was only: dnf_dec2 dnf_dec *)
lemma is_lift_dec: ∀T2,l,m. Decidable (∃T1. ⬆[l,m] T1 ≡ T2).
#T1 elim T1 -T1
[ * [1,3: /3 width=2 by lift_sort, lift_gref, ex_intro, or_introl/ ] #i #l #m
  elim (lt_or_ge i l) #Hli
  [ /4 width=3 by lift_lref_lt, ex_intro, or_introl/
  | elim (lt_or_ge i (l + m)) #Hilm
    [ @or_intror * #T1 #H elim (lift_inv_lref2_be … H Hli Hilm)
    | -Hli /4 width=2 by lift_lref_ge_minus, ex_intro, or_introl/
    ]
  ]
| * [ #a ] #I #V2 #T2 #IHV2 #IHT2 #l #m
  [ elim (IHV2 l m) -IHV2
    [ * #V1 #HV12 elim (IHT2 (l+1) m) -IHT2
      [ * #T1 #HT12 @or_introl /3 width=2 by lift_bind, ex_intro/
      | -V1 #HT2 @or_intror * #X #H
        elim (lift_inv_bind2 … H) -H /3 width=2 by ex_intro/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lift_inv_bind2 … H) -H /3 width=2 by ex_intro/
    ]
  | elim (IHV2 l m) -IHV2
    [ * #V1 #HV12 elim (IHT2 l m) -IHT2
      [ * #T1 #HT12 /4 width=2 by lift_flat, ex_intro, or_introl/
      | -V1 #HT2 @or_intror * #X #H
        elim (lift_inv_flat2 … H) -H /3 width=2 by ex_intro/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lift_inv_flat2 … H) -H /3 width=2 by ex_intro/
    ]
  ]
]
qed.

(* Basic_1: removed theorems 7:
            lift_head lift_gen_head
            lift_weight_map lift_weight lift_weight_add lift_weight_add_O
            lift_tlt_dx
*)
