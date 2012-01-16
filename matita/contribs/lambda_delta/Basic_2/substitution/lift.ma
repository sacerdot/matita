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

include "Basic_2/grammar/term_weight.ma".
include "Basic_2/grammar/term_simple.ma".

(* BASIC TERM RELOCATION ****************************************************)

(* Basic_1: includes:
            lift_sort lift_lref_lt lift_lref_ge lift_bind lift_flat
*)
inductive lift: nat → nat → relation term ≝
| lift_sort   : ∀k,d,e. lift d e (⋆k) (⋆k)
| lift_lref_lt: ∀i,d,e. i < d → lift d e (#i) (#i)
| lift_lref_ge: ∀i,d,e. d ≤ i → lift d e (#i) (#(i + e))
| lift_gref   : ∀p,d,e. lift d e (§p) (§p)
| lift_bind   : ∀I,V1,V2,T1,T2,d,e.
                lift d e V1 V2 → lift (d + 1) e T1 T2 →
                lift d e (𝕓{I} V1. T1) (𝕓{I} V2. T2)
| lift_flat   : ∀I,V1,V2,T1,T2,d,e.
                lift d e V1 V2 → lift d e T1 T2 →
                lift d e (𝕗{I} V1. T1) (𝕗{I} V2. T2)
.

interpretation "relocation" 'RLift d e T1 T2 = (lift d e T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lift_inv_refl_O2_aux: ∀d,e,T1,T2. ⇧[d, e] T1 ≡ T2 → e = 0 → T1 = T2.
#d #e #T1 #T2 #H elim H -d -e -T1 -T2 // /3 width=1/
qed.

lemma lift_inv_refl_O2: ∀d,T1,T2. ⇧[d, 0] T1 ≡ T2 → T1 = T2.
/2 width=4/ qed-.

fact lift_inv_sort1_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀k. T1 = ⋆k → T2 = ⋆k.
#d #e #T1 #T2 * -d -e -T1 -T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

lemma lift_inv_sort1: ∀d,e,T2,k. ⇧[d,e] ⋆k ≡ T2 → T2 = ⋆k.
/2 width=5/ qed-.

fact lift_inv_lref1_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀i. T1 = #i →
                         (i < d ∧ T2 = #i) ∨ (d ≤ i ∧ T2 = #(i + e)).
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3 width=1/
| #j #d #e #Hj #i #Hi destruct /3 width=1/
| #p #d #e #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
]
qed.

lemma lift_inv_lref1: ∀d,e,T2,i. ⇧[d,e] #i ≡ T2 →
                      (i < d ∧ T2 = #i) ∨ (d ≤ i ∧ T2 = #(i + e)).
/2 width=3/ qed-.

lemma lift_inv_lref1_lt: ∀d,e,T2,i. ⇧[d,e] #i ≡ T2 → i < d → T2 = #i.
#d #e #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hdi #_ #Hid lapply (le_to_lt_to_lt … Hdi Hid) -Hdi -Hid #Hdd
elim (lt_refl_false … Hdd)
qed-.

lemma lift_inv_lref1_ge: ∀d,e,T2,i. ⇧[d,e] #i ≡ T2 → d ≤ i → T2 = #(i + e).
#d #e #T2 #i #H elim (lift_inv_lref1 … H) -H * //
#Hid #_ #Hdi lapply (le_to_lt_to_lt … Hdi Hid) -Hdi -Hid #Hdd
elim (lt_refl_false … Hdd)
qed-.

fact lift_inv_gref1_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀p. T1 = §p → T2 = §p.
#d #e #T1 #T2 * -d -e -T1 -T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

lemma lift_inv_gref1: ∀d,e,T2,p. ⇧[d,e] §p ≡ T2 → T2 = §p.
/2 width=5/ qed-.

fact lift_inv_bind1_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 →
                         ∀I,V1,U1. T1 = 𝕓{I} V1.U1 →
                         ∃∃V2,U2. ⇧[d,e] V1 ≡ V2 & ⇧[d+1,e] U1 ≡ U2 &
                                  T2 = 𝕓{I} V2. U2.
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #p #d #e #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct
]
qed.

lemma lift_inv_bind1: ∀d,e,T2,I,V1,U1. ⇧[d,e] 𝕓{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ⇧[d,e] V1 ≡ V2 & ⇧[d+1,e] U1 ≡ U2 &
                               T2 = 𝕓{I} V2. U2.
/2 width=3/ qed-.

fact lift_inv_flat1_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 →
                         ∀I,V1,U1. T1 = 𝕗{I} V1.U1 →
                         ∃∃V2,U2. ⇧[d,e] V1 ≡ V2 & ⇧[d,e] U1 ≡ U2 &
                                  T2 = 𝕗{I} V2. U2.
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #i #d #e #_ #I #V1 #U1 #H destruct
| #p #d #e #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V1 #U1 #H destruct /2 width=5/
]
qed.

lemma lift_inv_flat1: ∀d,e,T2,I,V1,U1. ⇧[d,e] 𝕗{I} V1. U1 ≡ T2 →
                      ∃∃V2,U2. ⇧[d,e] V1 ≡ V2 & ⇧[d,e] U1 ≡ U2 &
                               T2 = 𝕗{I} V2. U2.
/2 width=3/ qed-.

fact lift_inv_sort2_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀k. T2 = ⋆k → T1 = ⋆k.
#d #e #T1 #T2 * -d -e -T1 -T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

(* Basic_1: was: lift_gen_sort *)
lemma lift_inv_sort2: ∀d,e,T1,k. ⇧[d,e] T1 ≡ ⋆k → T1 = ⋆k.
/2 width=5/ qed-.

fact lift_inv_lref2_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀i. T2 = #i →
                         (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #i #H destruct
| #j #d #e #Hj #i #Hi destruct /3 width=1/
| #j #d #e #Hj #i #Hi destruct <minus_plus_m_m /4 width=1/
| #p #d #e #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #i #H destruct
]
qed.

(* Basic_1: was: lift_gen_lref *)
lemma lift_inv_lref2: ∀d,e,T1,i. ⇧[d,e] T1 ≡ #i →
                      (i < d ∧ T1 = #i) ∨ (d + e ≤ i ∧ T1 = #(i - e)).
/2 width=3/ qed-.

(* Basic_1: was: lift_gen_lref_lt *)
lemma lift_inv_lref2_lt: ∀d,e,T1,i. ⇧[d,e] T1 ≡ #i → i < d → T1 = #i.
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hdi #_ #Hid lapply (le_to_lt_to_lt … Hdi Hid) -Hdi -Hid #Hdd
elim (lt_inv_plus_l … Hdd) -Hdd #Hdd
elim (lt_refl_false … Hdd)
qed-.

(* Basic_1: was: lift_gen_lref_false *)
lemma lift_inv_lref2_be: ∀d,e,T1,i. ⇧[d,e] T1 ≡ #i →
                         d ≤ i → i < d + e → False.
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H *
[ #H1 #_ #H2 #_ | #H2 #_ #_ #H1 ]
lapply (le_to_lt_to_lt … H2 H1) -H2 -H1 #H
elim (lt_refl_false … H)
qed-.

(* Basic_1: was: lift_gen_lref_ge *)
lemma lift_inv_lref2_ge: ∀d,e,T1,i. ⇧[d,e] T1 ≡ #i → d + e ≤ i → T1 = #(i - e).
#d #e #T1 #i #H elim (lift_inv_lref2 … H) -H * //
#Hid #_ #Hdi lapply (le_to_lt_to_lt … Hdi Hid) -Hdi -Hid #Hdd
elim (lt_inv_plus_l … Hdd) -Hdd #Hdd
elim (lt_refl_false … Hdd)
qed-.

fact lift_inv_gref2_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 → ∀p. T2 = §p → T1 = §p.
#d #e #T1 #T2 * -d -e -T1 -T2 //
[ #i #d #e #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #k #H destruct
]
qed.

lemma lift_inv_gref2: ∀d,e,T1,p. ⇧[d,e] T1 ≡ §p → T1 = §p.
/2 width=5/ qed-.

fact lift_inv_bind2_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 →
                         ∀I,V2,U2. T2 = 𝕓{I} V2.U2 →
                         ∃∃V1,U1. ⇧[d,e] V1 ≡ V2 & ⇧[d+1,e] U1 ≡ U2 &
                                  T1 = 𝕓{I} V1. U1.
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #p #d #e #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct /2 width=5/
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct
]
qed.

(* Basic_1: was: lift_gen_bind *)
lemma lift_inv_bind2: ∀d,e,T1,I,V2,U2. ⇧[d,e] T1 ≡  𝕓{I} V2. U2 →
                      ∃∃V1,U1. ⇧[d,e] V1 ≡ V2 & ⇧[d+1,e] U1 ≡ U2 &
                               T1 = 𝕓{I} V1. U1.
/2 width=3/ qed-.

fact lift_inv_flat2_aux: ∀d,e,T1,T2. ⇧[d,e] T1 ≡ T2 →
                         ∀I,V2,U2. T2 = 𝕗{I} V2.U2 →
                         ∃∃V1,U1. ⇧[d,e] V1 ≡ V2 & ⇧[d,e] U1 ≡ U2 &
                                  T1 = 𝕗{I} V1. U1.
#d #e #T1 #T2 * -d -e -T1 -T2
[ #k #d #e #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #i #d #e #_ #I #V2 #U2 #H destruct
| #p #d #e #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct
| #J #W1 #W2 #T1 #T2 #d #e #HW #HT #I #V2 #U2 #H destruct /2 width=5/
]
qed.

(* Basic_1: was: lift_gen_flat *)
lemma lift_inv_flat2: ∀d,e,T1,I,V2,U2. ⇧[d,e] T1 ≡  𝕗{I} V2. U2 →
                      ∃∃V1,U1. ⇧[d,e] V1 ≡ V2 & ⇧[d,e] U1 ≡ U2 &
                               T1 = 𝕗{I} V1. U1.
/2 width=3/ qed-.

lemma lift_inv_pair_xy_x: ∀d,e,I,V,T. ⇧[d, e] 𝕔{I} V. T ≡ V → False.
#d #e #J #V elim V -V
[ * #i #T #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct
  | elim (lift_inv_lref2 … H) -H * #_ #H destruct
  | lapply (lift_inv_gref2 … H) -H #H destruct
  ]
| * #I #W2 #U2 #IHW2 #_ #T #H
  [ elim (lift_inv_bind2 … H) -H #W1 #U1 #HW12 #_ #H destruct /2 width=2/
  | elim (lift_inv_flat2 … H) -H #W1 #U1 #HW12 #_ #H destruct /2 width=2/
  ]
]
qed-.

lemma lift_inv_pair_xy_y: ∀I,T,V,d,e. ⇧[d, e] 𝕔{I} V. T ≡ T → False.
#J #T elim T -T
[ * #i #V #d #e #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct
  | elim (lift_inv_lref2 … H) -H * #_ #H destruct
  | lapply (lift_inv_gref2 … H) -H #H destruct
  ]
| * #I #W2 #U2 #_ #IHU2 #V #d #e #H
  [ elim (lift_inv_bind2 … H) -H #W1 #U1 #_ #HU12 #H destruct /2 width=4/
  | elim (lift_inv_flat2 … H) -H #W1 #U1 #_ #HU12 #H destruct /2 width=4/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma tw_lift: ∀d,e,T1,T2. ⇧[d, e] T1 ≡ T2 → #[T1] = #[T2].
#d #e #T1 #T2 #H elim H -d -e -T1 -T2 normalize //
qed-.

lemma lift_simple_dx: ∀d,e,T1,T2. ⇧[d, e] T1 ≡ T2 → 𝕊[T1] → 𝕊[T2].
#d #e #T1 #T2 #H elim H -d -e -T1 -T2 //
#I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #H
elim (simple_inv_bind … H)
qed-.

lemma lift_simple_sn: ∀d,e,T1,T2. ⇧[d, e] T1 ≡ T2 → 𝕊[T2] → 𝕊[T1].
#d #e #T1 #T2 #H elim H -d -e -T1 -T2 //
#I #V1 #V2 #T1 #T2 #d #e #_ #_ #_ #_ #H
elim (simple_inv_bind … H)
qed-. 

(* Basic properties *********************************************************)

(* Basic_1: was: lift_lref_gt *)
lemma lift_lref_ge_minus: ∀d,e,i. d + e ≤ i → ⇧[d, e] #(i - e) ≡ #i.
#d #e #i #H >(plus_minus_m_m i e) in ⊢ (? ? ? ? %); /2 width=2/ /3 width=2/
qed.

lemma lift_lref_ge_minus_eq: ∀d,e,i,j. d + e ≤ i → j = i - e → ⇧[d, e] #j ≡ #i.
/2 width=1/ qed-.

(* Basic_1: was: lift_r *)
lemma lift_refl: ∀T,d. ⇧[d, 0] T ≡ T.
#T elim T -T
[ * #i // #d elim (lt_or_ge i d) /2 width=1/
| * /2 width=1/
]
qed.

lemma lift_total: ∀T1,d,e. ∃T2. ⇧[d,e] T1 ≡ T2.
#T1 elim T1 -T1
[ * #i /2 width=2/ #d #e elim (lt_or_ge i d) /3 width=2/
| * #I #V1 #T1 #IHV1 #IHT1 #d #e
  elim (IHV1 d e) -IHV1 #V2 #HV12
  [ elim (IHT1 (d+1) e) -IHT1 /3 width=2/
  | elim (IHT1 d e) -IHT1 /3 width=2/
  ]
]
qed.

(* Basic_1: was: lift_free (right to left) *)
lemma lift_split: ∀d1,e2,T1,T2. ⇧[d1, e2] T1 ≡ T2 →
                  ∀d2,e1. d1 ≤ d2 → d2 ≤ d1 + e1 → e1 ≤ e2 →
                  ∃∃T. ⇧[d1, e1] T1 ≡ T & ⇧[d2, e2 - e1] T ≡ T2.
#d1 #e2 #T1 #T2 #H elim H -d1 -e2 -T1 -T2
[ /3 width=3/
| #i #d1 #e2 #Hid1 #d2 #e1 #Hd12 #_ #_
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2 /4 width=3/
| #i #d1 #e2 #Hid1 #d2 #e1 #_ #Hd21 #He12
  lapply (transitive_le … (i+e1) Hd21 ?) /2 width=1/ -Hd21 #Hd21
  >(plus_minus_m_m e2 e1 ?) // /3 width=3/
| /3 width=3/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT (d2+1) … ? ? He12) /2 width=1/ /3 width=5/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT d2 … ? ? He12) // /3 width=5/
]
qed.

(* Basic_1: was only: dnf_dec2 dnf_dec *)
lemma is_lift_dec: ∀T2,d,e. Decidable (∃T1. ⇧[d,e] T1 ≡ T2).
#T1 elim T1 -T1
[ * [1,3: /3 width=2/ ] #i #d #e
  elim (lt_dec i d) #Hid
  [ /4 width=2/
  | lapply (false_lt_to_le … Hid) -Hid #Hid
    elim (lt_dec i (d + e)) #Hide
    [ @or_intror * #T1 #H
      elim (lift_inv_lref2_be … H Hid Hide)
    | lapply (false_lt_to_le … Hide) -Hide /4 width=2/
    ]
  ]
| * #I #V2 #T2 #IHV2 #IHT2 #d #e
  [ elim (IHV2 d e) -IHV2
    [ * #V1 #HV12 elim (IHT2 (d+1) e) -IHT2
      [ * #T1 #HT12 @or_introl /3 width=2/
      | -V1 #HT2 @or_intror * #X #H
        elim (lift_inv_bind2 … H) -H /3 width=2/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lift_inv_bind2 … H) -H /3 width=2/
    ]
  | elim (IHV2 d e) -IHV2
    [ * #V1 #HV12 elim (IHT2 d e) -IHT2
      [ * #T1 #HT12 /4 width=2/
      | -V1 #HT2 @or_intror * #X #H
        elim (lift_inv_flat2 … H) -H /3 width=2/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lift_inv_flat2 … H) -H /3 width=2/
    ]
  ]
]
qed.

(* Basic_1: removed theorems 7:
            lift_head lift_gen_head
            lift_weight_map lift_weight lift_weight_add lift_weight_add_O
            lift_tlt_dx
*)
