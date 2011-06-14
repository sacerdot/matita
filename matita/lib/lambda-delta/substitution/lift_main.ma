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

include "lambda-delta/substitution/lift_defs.ma".

(* RELOCATION ***************************************************************)

(* the main properies *******************************************************)

theorem lift_conf_rev: ∀d1,e1,T1,T. ↑[d1,e1] T1 ≡ T →
                       ∀d2,e2,T2. ↑[d2 + e1, e2] T2 ≡ T →
                       d1 ≤ d2 →
                       ∃∃T0. ↑[d1, e1] T0 ≡ T2 & ↑[d2, e2] T0 ≡ T1.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #T2 #Hk #Hd12
  lapply (lift_inv_sort2 … Hk) -Hk #Hk destruct -T2 /3/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  lapply (lift_inv_lref2 … Hi) -Hi * * #Hid2 #H destruct -T2
  [ -Hid2 /4/
  | elim (lt_false d1 ?)
    @(le_to_lt_to_lt … Hd12) -Hd12 @(le_to_lt_to_lt … Hid1) -Hid1 /2/
  ]
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  lapply (lift_inv_lref2 … Hi) -Hi * * #Hid2 #H destruct -T2
  [ -Hd12; lapply (lt_plus_to_lt_l … Hid2) -Hid2 #Hid2 /3/
  | -Hid1; lapply (arith1 … Hid2) -Hid2 #Hid2
    @(ex2_1_intro … #(i - e2))
    [ >le_plus_minus_comm [ @lift_lref_ge @(transitive_le … Hd12) -Hd12 /2/ | -Hd12 /2/ ]
    | -Hd12 >(plus_minus_m_m i e2) in ⊢ (? ? ? ? %) /3/
    ]
  ]
| #I #W1 #W #U1 #U #d1 #e1 #_ #_ #IHW #IHU #d2 #e2 #T2 #H #Hd12
  lapply (lift_inv_bind2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct -T2;
  elim (IHW … HW2 ?) // -IHW HW2 #W0 #HW2 #HW1
  >plus_plus_comm_23 in HU2 #HU2 elim (IHU … HU2 ?) /3 width = 5/
| #I #W1 #W #U1 #U #d1 #e1 #_ #_ #IHW #IHU #d2 #e2 #T2 #H #Hd12
  lapply (lift_inv_flat2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct -T2;
  elim (IHW … HW2 ?) // -IHW HW2 #W0 #HW2 #HW1
  elim (IHU … HU2 ?) /3 width = 5/
]
qed.

theorem lift_free: ∀d1,e2,T1,T2. ↑[d1, e2] T1 ≡ T2 → ∀d2,e1.
                                 d1 ≤ d2 → d2 ≤ d1 + e1 → e1 ≤ e2 →
                                 ∃∃T. ↑[d1, e1] T1 ≡ T & ↑[d2, e2 - e1] T ≡ T2.
#d1 #e2 #T1 #T2 #H elim H -H d1 e2 T1 T2
[ /3/
| #i #d1 #e2 #Hid1 #d2 #e1 #Hd12 #_ #_
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2 /4/
| #i #d1 #e2 #Hid1 #d2 #e1 #_ #Hd21 #He12
  lapply (transitive_le …(i+e1) Hd21 ?) /2/ -Hd21 #Hd21
  <(plus_plus_minus_m_m e1 e2 i) /3/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT (d2+1) … ? ? He12) /3 width = 5/
| #I #V1 #V2 #T1 #T2 #d1 #e2 #_ #_ #IHV #IHT #d2 #e1 #Hd12 #Hd21 #He12
  elim (IHV … Hd12 Hd21 He12) -IHV #V0 #HV0a #HV0b
  elim (IHT d2 … ? ? He12) /3 width = 5/
]
qed.

theorem lift_trans: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                    ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 →
                    d1 ≤ d2 → d2 ≤ d1 + e1 → ↑[d1, e1 + e2] T1 ≡ T2.
#d1 #e1 #T1 #T #H elim H -d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #T2 #HT2 #_ #_
  >(lift_inv_sort1 … HT2) -HT2 //
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #Hd12 #_
  lapply (lift_inv_lref1 … HT2) -HT2 * * #Hid2 #H destruct -T2
  [ -Hd12 Hid2 /2/
  | lapply (le_to_lt_to_lt … d1 Hid2 ?) // -Hid1 Hid2 #Hd21
    lapply (le_to_lt_to_lt … d1 Hd12 ?) // -Hd12 Hd21 #Hd11
    elim (lt_false … Hd11)
  ]
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #_ #Hd21
  lapply (lift_inv_lref1 … HT2) -HT2 * * #Hid2 #H destruct -T2
  [ lapply (lt_to_le_to_lt … (d1+e1) Hid2 ?) // -Hid2 Hd21 #H
    lapply (lt_plus_to_lt_l … H) -H #H
    lapply (le_to_lt_to_lt … d1 Hid1 ?) // -Hid1 H #Hd11
    elim (lt_false … Hd11)
  | -Hd21 Hid2 /2/
  ]
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  lapply (lift_inv_bind1 … HX) -HX * #V0 #T0 #HV20 #HT20 #HX destruct -X;
  lapply (IHV12 … HV20 ? ?) // -IHV12 HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  lapply (lift_inv_flat1 … HX) -HX * #V0 #T0 #HV20 #HT20 #HX destruct -X;
  lapply (IHV12 … HV20 ? ?) // -IHV12 HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2/
]
qed.

axiom lift_trans_le: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                     ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 → d2 ≤ d1 →
                     ∃∃T0. ↑[d2, e2] T1 ≡ T0 & ↑[d1 + e2, e1] T0 ≡ T2.

axiom lift_trans_ge: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                     ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 → d1 + e1 ≤ d2 →
                     ∃∃T0. ↑[d2 - e1, e2] T1 ≡ T0 & ↑[d1, e1] T0 ≡ T2.
