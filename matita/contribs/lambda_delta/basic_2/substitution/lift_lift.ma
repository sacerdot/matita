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

include "basic_2/substitution/lift.ma".

(* BASIC TERM RELOCATION ****************************************************)

(* Main properies ***********************************************************)

(* Basic_1: was: lift_inj *)
theorem lift_inj: ∀d,e,T1,U. ⇧[d,e] T1 ≡ U → ∀T2. ⇧[d,e] T2 ≡ U → T1 = T2.
#d #e #T1 #U #H elim H -d -e -T1 -U
[ #k #d #e #X #HX
  lapply (lift_inv_sort2 … HX) -HX //
| #i #d #e #Hid #X #HX
  lapply (lift_inv_lref2_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX
  lapply (lift_inv_lref2_ge … HX ?) -HX // /2 width=1/
| #p #d #e #X #HX
  lapply (lift_inv_gref2 … HX) -HX //
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1/
]
qed-.

(* Basic_1: was: lift_gen_lift *)
theorem lift_div_le: ∀d1,e1,T1,T. ⇧[d1, e1] T1 ≡ T →
                     ∀d2,e2,T2. ⇧[d2 + e1, e2] T2 ≡ T →
                     d1 ≤ d2 →
                     ∃∃T0. ⇧[d1, e1] T0 ≡ T2 & ⇧[d2, e2] T0 ≡ T1.
#d1 #e1 #T1 #T #H elim H -d1 -e1 -T1 -T
[ #k #d1 #e1 #d2 #e2 #T2 #Hk #Hd12
  lapply (lift_inv_sort2 … Hk) -Hk #Hk destruct /3 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
  lapply (lift_inv_lref2_lt … Hi ?) -Hi /2 width=3/ /3 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #Hi #Hd12
  elim (lift_inv_lref2 … Hi) -Hi * #Hid2 #H destruct
  [ -Hd12 lapply (lt_plus_to_lt_l … Hid2) -Hid2 #Hid2 /3 width=3/
  | -Hid1 >plus_plus_comm_23 in Hid2; #H lapply (le_plus_to_le_r … H) -H #H
    elim (le_inv_plus_l … H) -H #Hide2 #He2i
    lapply (transitive_le … Hd12 Hide2) -Hd12 #Hd12
    >le_plus_minus_comm // >(plus_minus_m_m i e2) in ⊢ (? ? ? %); // -He2i
    /4 width=3/
  ]
| #p #d1 #e1 #d2 #e2 #T2 #Hk #Hd12
  lapply (lift_inv_gref2 … Hk) -Hk #Hk destruct /3 width=3/
| #I #W1 #W #U1 #U #d1 #e1 #_ #_ #IHW #IHU #d2 #e2 #T2 #H #Hd12
  lapply (lift_inv_bind2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct
  elim (IHW … HW2 ?) // -IHW -HW2 #W0 #HW2 #HW1
  >plus_plus_comm_23 in HU2; #HU2 elim (IHU … HU2 ?) /2 width=1/ /3 width=5/
| #I #W1 #W #U1 #U #d1 #e1 #_ #_ #IHW #IHU #d2 #e2 #T2 #H #Hd12
  lapply (lift_inv_flat2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct
  elim (IHW … HW2 ?) // -IHW -HW2 #W0 #HW2 #HW1
  elim (IHU … HU2 ?) // /3 width=5/
]
qed.

(* Note: apparently this was missing in Basic_1 *)
theorem lift_div_be: ∀d1,e1,T1,T. ⇧[d1, e1] T1 ≡ T →
                     ∀e,e2,T2. ⇧[d1 + e, e2] T2 ≡ T →
                     e ≤ e1 → e1 ≤ e + e2 →
                     ∃∃T0. ⇧[d1, e] T0 ≡ T2 & ⇧[d1, e + e2 - e1] T0 ≡ T1.
#d1 #e1 #T1 #T #H elim H -d1 -e1 -T1 -T
[ #k #d1 #e1 #e #e2 #T2 #H >(lift_inv_sort2 … H) -H /2 width=3/
| #i #d1 #e1 #Hid1 #e #e2 #T2 #H #He1 #He1e2
  >(lift_inv_lref2_lt … H) -H [ /3 width=3/ | /2 width=3/ ]
| #i #d1 #e1 #Hid1 #e #e2 #T2 #H #He1 #He1e2
  elim (lt_or_ge (i+e1) (d1+e+e2)) #Hie1d1e2
  [ elim (lift_inv_lref2_be … H ? ?) -H // /2 width=1/
  | >(lift_inv_lref2_ge … H ?) -H //
    lapply (le_plus_to_minus … Hie1d1e2) #Hd1e21i
    elim (le_inv_plus_l … Hie1d1e2) -Hie1d1e2 #Hd1e12 #He2ie1
    @ex2_1_intro [2: /2 width=1/ | skip ] -Hd1e12
    @lift_lref_ge_minus_eq [ >plus_minus_commutative // | /2 width=1/ ]
  ]
| #p #d1 #e1 #e #e2 #T2 #H >(lift_inv_gref2 … H) -H /2 width=3/
| #I #V1 #V #T1 #T #d1 #e1 #_ #_ #IHV1 #IHT1 #e #e2 #X #H #He1 #He1e2
  elim (lift_inv_bind2 … H) -H #V2 #T2 #HV2 #HT2 #H destruct
  elim (IHV1 … HV2 ? ?) -V // >plus_plus_comm_23 in HT2; #HT2
  elim (IHT1 … HT2 ? ?) -T // -He1 -He1e2 /3 width=5/
| #I #V1 #V #T1 #T #d1 #e1 #_ #_ #IHV1 #IHT1 #e #e2 #X #H #He1 #He1e2
  elim (lift_inv_flat2 … H) -H #V2 #T2 #HV2 #HT2 #H destruct
  elim (IHV1 … HV2 ? ?) -V //
  elim (IHT1 … HT2 ? ?) -T // -He1 -He1e2 /3 width=5/
]
qed.

theorem lift_mono: ∀d,e,T,U1. ⇧[d,e] T ≡ U1 → ∀U2. ⇧[d,e] T ≡ U2 → U1 = U2.
#d #e #T #U1 #H elim H -d -e -T -U1
[ #k #d #e #X #HX
  lapply (lift_inv_sort1 … HX) -HX //
| #i #d #e #Hid #X #HX 
  lapply (lift_inv_lref1_lt … HX ?) -HX //
| #i #d #e #Hdi #X #HX 
  lapply (lift_inv_lref1_ge … HX ?) -HX //
| #p #d #e #X #HX
  lapply (lift_inv_gref1 … HX) -HX //
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind1 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1/
| #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat1 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1/
]
qed-.

(* Basic_1: was: lift_free (left to right) *)
theorem lift_trans_be: ∀d1,e1,T1,T. ⇧[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ⇧[d2, e2] T ≡ T2 →
                       d1 ≤ d2 → d2 ≤ d1 + e1 → ⇧[d1, e1 + e2] T1 ≡ T2.
#d1 #e1 #T1 #T #H elim H -d1 -e1 -T1 -T
[ #k #d1 #e1 #d2 #e2 #T2 #HT2 #_ #_
  >(lift_inv_sort1 … HT2) -HT2 //
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #Hd12 #_
  lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
  lapply (lift_inv_lref1_lt … HT2 Hid2) /2 width=1/
| #i #d1 #e1 #Hid1 #d2 #e2 #T2 #HT2 #_ #Hd21
  lapply (lift_inv_lref1_ge … HT2 ?) -HT2
  [ @(transitive_le … Hd21 ?) -Hd21 /2 width=1/
  | -Hd21 /2 width=1/
  ]
| #p #d1 #e1 #d2 #e2 #T2 #HT2 #_ #_
  >(lift_inv_gref1 … HT2) -HT2 //
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  lapply (IHV12 … HV20 ? ?) // -IHV12 -HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2 width=1/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd12 #Hd21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  lapply (IHV12 … HV20 ? ?) // -IHV12 -HV20 #HV10
  lapply (IHT12 … HT20 ? ?) // /2 width=1/
]
qed.

(* Basic_1: was: lift_d (right to left) *)
theorem lift_trans_le: ∀d1,e1,T1,T. ⇧[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ⇧[d2, e2] T ≡ T2 → d2 ≤ d1 →
                       ∃∃T0. ⇧[d2, e2] T1 ≡ T0 & ⇧[d1 + e2, e1] T0 ≡ T2.
#d1 #e1 #T1 #T #H elim H -d1 -e1 -T1 -T
[ #k #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #_
  lapply (lt_to_le_to_lt … (d1+e2) Hid1 ?) // #Hie2
  elim (lift_inv_lref1 … HX) -HX * #Hid2 #HX destruct /3 width=3/ /4 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #Hd21
  lapply (transitive_le … Hd21 Hid1) -Hd21 #Hid2
  lapply (lift_inv_lref1_ge … HX ?) -HX /2 width=3/ #HX destruct
  >plus_plus_comm_23 /4 width=3/
| #p #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_gref1 … HX) -HX /2 width=3/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20 ?) -IHV12 -HV20 //
  elim (IHT12 … HT20 ?) -IHT12 -HT20 /2 width=1/ /3 width=5/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hd21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20 ?) -IHV12 -HV20 //
  elim (IHT12 … HT20 ?) -IHT12 -HT20 // /3 width=5/
]
qed.

(* Basic_1: was: lift_d (left to right) *)
theorem lift_trans_ge: ∀d1,e1,T1,T. ⇧[d1, e1] T1 ≡ T →
                       ∀d2,e2,T2. ⇧[d2, e2] T ≡ T2 → d1 + e1 ≤ d2 →
                       ∃∃T0. ⇧[d2 - e1, e2] T1 ≡ T0 & ⇧[d1, e1] T0 ≡ T2.
#d1 #e1 #T1 #T #H elim H -d1 -e1 -T1 -T
[ #k #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #Hded
  lapply (lt_to_le_to_lt … (d1+e1) Hid1 ?) // #Hid1e
  lapply (lt_to_le_to_lt … (d2-e1) Hid1 ?) /2 width=1/ #Hid2e
  lapply (lt_to_le_to_lt … Hid1e Hded) -Hid1e -Hded #Hid2
  lapply (lift_inv_lref1_lt … HX ?) -HX // #HX destruct /3 width=3/
| #i #d1 #e1 #Hid1 #d2 #e2 #X #HX #_
  elim (lift_inv_lref1 … HX) -HX * #Hied #HX destruct /4 width=3/
| #p #d1 #e1 #d2 #e2 #X #HX #_
  >(lift_inv_gref1 … HX) -HX /2 width=3/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hded
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20 ?) -IHV12 -HV20 //
  elim (IHT12 … HT20 ?) -IHT12 -HT20 /2 width=1/ #T
  <plus_minus /2 width=2/ /3 width=5/
| #I #V1 #V2 #T1 #T2 #d1 #e1 #_ #_ #IHV12 #IHT12 #d2 #e2 #X #HX #Hded
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20 ?) -IHV12 -HV20 //
  elim (IHT12 … HT20 ?) -IHT12 -HT20 // /3 width=5/
]
qed.