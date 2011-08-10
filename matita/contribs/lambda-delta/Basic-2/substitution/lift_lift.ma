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

include "Basic-2/substitution/lift.ma".

(* RELOCATION ***************************************************************)

(* Main properies ***********************************************************)

theorem lift_inj:  ∀d,e,T1,U. ↑[d,e] T1 ≡ U → ∀T2. ↑[d,e] T2 ≡ U → T1 = T2.
#d #e #T1 #U #H elim H -H d e T1 U
[ #k #d #e #X #HX
  lapply (lift_inv_sort2 … HX) -HX //
| #i #d #e #Hid #X #HX 
  lapply (lift_inv_lref2_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX 
  lapply (lift_inv_lref2_ge … HX ?) -HX /2/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
]
qed.

theorem lift_div_le: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                     ∀d2,e2,T2. ↑[d2 + e1, e2] T2 ≡ T →
                     d1 ≤ d2 →
                     ∃∃T0. ↑[d1, e1] T0 ≡ T2 & ↑[d2, e2] T0 ≡ T1.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #T2 #Hk #Hd12
  lapply (lift_inv_sort2 … Hk) -Hk #Hk destruct -T2 /3/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
  lapply (lift_inv_lref2_lt … Hi ?) -Hi /3/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  elim (lift_inv_lref2 … Hi) -Hi * #Hid2 #H destruct -T2
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

theorem lift_mono:  ∀d,e,T,U1. ↑[d,e] T ≡ U1 → ∀U2. ↑[d,e] T ≡ U2 → U1 = U2.
#d #e #T #U1 #H elim H -H d e T U1
[ #k #d #e #X #HX
  lapply (lift_inv_sort1 … HX) -HX //
| #i #d #e #Hid #X #HX 
  lapply (lift_inv_lref1_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX 
  lapply (lift_inv_lref1_ge … HX ?) -HX //
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind1 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat1 … HX) -HX #V #T #HV1 #HT1 #HX destruct -X /3/
]
qed.

theorem lift_trans_be: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 →
                       d1 ≤ d2 → d2 ≤ d1 + e1 → ↑[d1, e1 + e2] T1 ≡ T2.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #T2 #HT2 #_ #_
  >(lift_inv_sort1 … HT2) -HT2 //
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #Hd12 #_
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
  lapply (lift_inv_lref1_lt … HT2 Hid2) /2/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #_ #Hd21
  lapply (lift_inv_lref1_ge … HT2 ?) -HT2
  [ @(transitive_le … Hd21 ?) -Hd21 /2/
  | -Hd21 /2/
  ]
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  lapply (IHV12 … HV20 ? ?) // -IHV12 HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  lapply (IHV12 … HV20 ? ?) // -IHV12 HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2/
]
qed.

theorem lift_trans_le: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 → d2 ≤ d1 →
                       ∃∃T0. ↑[d2, e2] T1 ≡ T0 & ↑[d1 + e2, e1] T0 ≡ T2.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #_
  lapply (lt_to_le_to_lt … (d1+e2) Hid1 ?) // #Hie2
  elim (lift_inv_lref1 … HX) -HX * #Hid2 #HX destruct -X /4/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #Hd21
  lapply (transitive_le … Hd21 Hid1) -Hd21 #Hid2
  lapply (lift_inv_lref1_ge … HX ?) -HX /2/ #HX destruct -X;
  >plus_plus_comm_23 /4/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  elim (IHV12 … HV20 ?) -IHV12 HV20 //
  elim (IHT12 … HT20 ?) -IHT12 HT20 /3 width=5/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  elim (IHV12 … HV20 ?) -IHV12 HV20 //
  elim (IHT12 … HT20 ?) -IHT12 HT20 /3 width=5/
]
qed.

theorem lift_trans_ge: ∀d1,e1,T1,T. ↑[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ↑[d2, e2] T ≡ T2 → d1 + e1 ≤ d2 →
                       ∃∃T0. ↑[d2 - e1, e2] T1 ≡ T0 & ↑[d1, e1] T0 ≡ T2.
#d1 #e1 #T1 #T #H elim H -H d1 e1 T1 T
[ #k #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #Hded
  lapply (lt_to_le_to_lt … (d1+e1) Hid1 ?) // #Hid1e
  lapply (lt_to_le_to_lt … (d2-e1) Hid1 ?) /2/ #Hid2e
  lapply (lt_to_le_to_lt … Hid1e Hded) -Hid1e Hded #Hid2
  lapply (lift_inv_lref1_lt … HX ?) -HX // #HX destruct -X /3/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #_
  elim (lift_inv_lref1 … HX) -HX * #Hied #HX destruct -X;
  [2: >plus_plus_comm_23] /4/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hded
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  elim (IHV12 … HV20 ?) -IHV12 HV20 //
  elim (IHT12 … HT20 ?) -IHT12 HT20 /2/ #T
  <plus_minus /3 width=5/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hded
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct -X;
  elim (IHV12 … HV20 ?) -IHV12 HV20 //
  elim (IHT12 … HT20 ?) -IHT12 HT20 /3 width=5/
]
qed.
