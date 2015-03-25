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

(* Main properties ***********************************************************)

(* Basic_1: was: lift_inj *)
theorem lift_inj: ∀l,m,T1,U. ⬆[l, m] T1 ≡ U → ∀T2. ⬆[l, m] T2 ≡ U → T1 = T2.
#l #m #T1 #U #H elim H -l -m -T1 -U
[ #k #l #m #X #HX
  lapply (lift_inv_sort2 … HX) -HX //
| #i #l #m #Hil #X #HX
  lapply (lift_inv_lref2_lt … HX ?) -HX //
| #i #l #m #Hli #X #HX
  lapply (lift_inv_lref2_ge … HX ?) -HX /2 width=1 by monotonic_yle_plus_dx/
| #p #l #m #X #HX
  lapply (lift_inv_gref2 … HX) -HX //
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
]
qed-.

(* Basic_1: was: lift_gen_lift *)
theorem lift_div_le: ∀l1,m1,T1,T. ⬆[l1, m1] T1 ≡ T →
                     ∀l2,m2,T2. ⬆[l2 + m1, m2] T2 ≡ T →
                     l1 ≤ l2 →
                     ∃∃T0. ⬆[l1, m1] T0 ≡ T2 & ⬆[l2, m2] T0 ≡ T1.
#l1 #m1 #T1 #T #H elim H -l1 -m1 -T1 -T
[ #k #l1 #m1 #l2 #m2 #T2 #Hk #Hl12
  lapply (lift_inv_sort2 … Hk) -Hk #Hk destruct /3 width=3 by lift_sort, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #T2 #Hi #Hl12
  lapply (ylt_yle_trans … Hl12 Hil1) -Hl12 #Hil2
  lapply (lift_inv_lref2_lt … Hi ?) -Hi /3 width=3 by lift_lref_lt, ylt_plus_dx1_trans, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #T2 #Hi #Hl12
  elim (lift_inv_lref2 … Hi) -Hi * <yplus_inj #Hil2 #H destruct
  [ -Hl12 lapply (ylt_inv_monotonic_plus_dx … Hil2) -Hil2 #Hil2 /3 width=3 by lift_lref_lt, lift_lref_ge, ex2_intro/
  | -Hil1 >yplus_comm_23 in Hil2; #H lapply ( yle_inv_monotonic_plus_dx … H) -H #H
    elim (yle_inv_plus_inj2 … H) -H >yminus_inj #Hl2im2 #H
    lapply (yle_inv_inj … H) -H #Hm2i 
    lapply (yle_trans … Hl12 … Hl2im2) -Hl12 #Hl1im2
    >le_plus_minus_comm // >(plus_minus_m_m i m2) in ⊢ (? ? ? %);
    /3 width=3 by lift_lref_ge, ex2_intro/
  ]
| #p #l1 #m1 #l2 #m2 #T2 #Hk #Hl12
  lapply (lift_inv_gref2 … Hk) -Hk #Hk destruct /3 width=3 by lift_gref, ex2_intro/
| #a #I #W1 #W #U1 #U #l1 #m1 #_ #_ #IHW #IHU #l2 #m2 #T2 #H #Hl12
  lapply (lift_inv_bind2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct
  elim (IHW … HW2) // -IHW -HW2 #W0 #HW2 #HW1
  <yplus_succ1 in HU2; #HU2 elim (IHU … HU2) /3 width=5 by yle_succ, lift_bind, ex2_intro/
| #I #W1 #W #U1 #U #l1 #m1 #_ #_ #IHW #IHU #l2 #m2 #T2 #H #Hl12
  lapply (lift_inv_flat2 … H) -H * #W2 #U2 #HW2 #HU2 #H destruct
  elim (IHW … HW2) // -IHW -HW2 #W0 #HW2 #HW1
  elim (IHU … HU2) /3 width=5 by lift_flat, ex2_intro/
]
qed.

(* Note: apparently this was missing in basic_1 *)
theorem lift_div_be: ∀l1,m1,T1,T. ⬆[l1, m1] T1 ≡ T →
                     ∀m,m2,T2. ⬆[l1 + yinj m, m2] T2 ≡ T →
                     m ≤ m1 → m1 ≤ m + m2 →
                     ∃∃T0. ⬆[l1, m] T0 ≡ T2 & ⬆[l1, m + m2 - m1] T0 ≡ T1.
#l1 #m1 #T1 #T #H elim H -l1 -m1 -T1 -T
[ #k #l1 #m1 #m #m2 #T2 #H >(lift_inv_sort2 … H) -H /2 width=3 by lift_sort, ex2_intro/
| #i #l1 #m1 #Hil1 #m #m2 #T2 #H #Hm1 #Hm1m2
  >(lift_inv_lref2_lt … H) -H /3 width=3 by ylt_plus_dx1_trans, lift_lref_lt, ex2_intro/
| #i #l1 #m1 #Hil1 #m #m2 #T2 #H #Hm1 #Hm1m2
  elim (ylt_split (i+m1) (l1+m+m2)) #H0
  [ elim (lift_inv_lref2_be … H) -H /3 width=2 by monotonic_yle_plus, yle_inj/
  | >(lift_inv_lref2_ge … H ?) -H //
    lapply (yle_plus2_to_minus_inj2 … H0) #Hl1m21i
    elim (yle_inv_plus_inj2 … H0) -H0 #Hl1m12 #Hm2im1
    @ex2_intro [2: /2 width=1 by lift_lref_ge_minus/ | skip ]
    @lift_lref_ge_minus_eq
    [ <yminus_inj <yplus_inj >yplus_minus_assoc_inj /2 width=1 by yle_inj/
    | /2 width=1 by minus_le_minus_minus_comm/
    ]
  ]
| #p #l1 #m1 #m #m2 #T2 #H >(lift_inv_gref2 … H) -H /2 width=3 by lift_gref, ex2_intro/
| #a #I #V1 #V #T1 #T #l1 #m1 #_ #_ #IHV1 #IHT1 #m #m2 #X #H #Hm1 #Hm1m2
  elim (lift_inv_bind2 … H) -H #V2 #T2 #HV2 <yplus_succ1 #HT2 #H destruct
  elim (IHV1 … HV2) -V //
  elim (IHT1 … HT2) -T /3 width=5 by lift_bind, ex2_intro/
| #I #V1 #V #T1 #T #l1 #m1 #_ #_ #IHV1 #IHT1 #m #m2 #X #H #Hm1 #Hm1m2
  elim (lift_inv_flat2 … H) -H #V2 #T2 #HV2 #HT2 #H destruct
  elim (IHV1 … HV2) -V //
  elim (IHT1 … HT2) -T /3 width=5 by lift_flat, ex2_intro/
]
qed.

theorem lift_mono: ∀l,m,T,U1. ⬆[l,m] T ≡ U1 → ∀U2. ⬆[l,m] T ≡ U2 → U1 = U2.
#l #m #T #U1 #H elim H -l -m -T -U1
[ #k #l #m #X #HX
  lapply (lift_inv_sort1 … HX) -HX //
| #i #l #m #Hil #X #HX
  lapply (lift_inv_lref1_lt … HX ?) -HX //
| #i #l #m #Hli #X #HX
  lapply (lift_inv_lref1_ge … HX ?) -HX //
| #p #l #m #X #HX
  lapply (lift_inv_gref1 … HX) -HX //
| #a #I #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind1 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
| #I #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat1 … HX) -HX #V #T #HV1 #HT1 #HX destruct /3 width=1 by eq_f2/
]
qed-.

(* Basic_1: was: lift_free (left to right) *)
theorem lift_trans_be: ∀l1,m1,T1,T. ⬆[l1, m1] T1 ≡ T →
                       ∀l2,m2,T2. ⬆[l2, m2] T ≡ T2 →
                       l1 ≤ l2 → l2 ≤ l1 + m1 → ⬆[l1, m1 + m2] T1 ≡ T2.
#l1 #m1 #T1 #T #H elim H -l1 -m1 -T1 -T
[ #k #l1 #m1 #l2 #m2 #T2 #HT2 #_ #_
  >(lift_inv_sort1 … HT2) -HT2 //
| #i #l1 #m1 #Hil1 #l2 #m2 #T2 #HT2 #Hl12 #_
  lapply (ylt_yle_trans … Hl12 Hil1) -Hl12 #Hil2
  lapply (lift_inv_lref1_lt … HT2 Hil2) /2 width=1 by lift_lref_lt/
| #i #l1 #m1 #Hil1 #l2 #m2 #T2 #HT2 #_ #Hl21
  lapply (lift_inv_lref1_ge … HT2 ?) -HT2
  [ @(yle_trans … Hl21) -Hl21 /2 width=1 by monotonic_yle_plus_dx/
  | -Hl21 /2 width=1 by lift_lref_ge/
  ]
| #p #l1 #m1 #l2 #m2 #T2 #HT2 #_ #_
  >(lift_inv_gref1 … HT2) -HT2 //
| #a #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hl12 #Hl21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  lapply (IHV12 … HV20 ? ?) // -IHV12 -HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2 width=1 by lift_bind, yle_succ/ (**) (* full auto a bit slow *)
| #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hl12 #Hl21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  lapply (IHV12 … HV20 ? ?) // -IHV12 -HV20 #HV10
  lapply (IHT12 … HT20 ? ?) /2 width=1 by lift_flat/ (**) (* full auto a bit slow *)
]
qed.

(* Basic_1: was: lift_d (right to left) *)
theorem lift_trans_le: ∀l1,m1,T1,T. ⬆[l1, m1] T1 ≡ T →
                       ∀l2,m2,T2. ⬆[l2, m2] T ≡ T2 → l2 ≤ l1 →
                       ∃∃T0. ⬆[l2, m2] T1 ≡ T0 & ⬆[l1 + m2, m1] T0 ≡ T2.
#l1 #m1 #T1 #T #H elim H -l1 -m1 -T1 -T
[ #k #l1 #m1 #l2 #m2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2 width=3 by lift_sort, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #X #HX #_
  lapply (ylt_yle_trans … (l1+m2) ? Hil1) // #Him2
  elim (lift_inv_lref1 … HX) -HX * #Hil2 #HX destruct
  /4 width=3 by monotonic_ylt_plus_dx, monotonic_yle_plus_dx, lift_lref_ge_minus, lift_lref_lt, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #X #HX #Hl21
  lapply (yle_trans … Hl21 … Hil1) -Hl21 #Hil2
  lapply (lift_inv_lref1_ge … HX ?) -HX /2 width=3 by yle_plus_dx1_trans/ #HX destruct
  >plus_plus_comm_23 /4 width=3 by monotonic_yle_plus_dx, lift_lref_ge_minus, lift_lref_ge, ex2_intro/
| #p #l1 #m1 #l2 #m2 #X #HX #_
  >(lift_inv_gref1 … HX) -HX /2 width=3 by lift_gref, ex2_intro/
| #a #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hl21
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20) -IHV12 -HV20 //
  elim (IHT12 … HT20) -IHT12 -HT20 /3 width=5 by lift_bind, yle_succ, ex2_intro/
| #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hl21
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20) -IHV12 -HV20 //
  elim (IHT12 … HT20) -IHT12 -HT20 /3 width=5 by lift_flat, ex2_intro/
]
qed.

(* Basic_1: was: lift_d (left to right) *)
theorem lift_trans_ge: ∀l1,m1,T1,T. ⬆[l1, m1] T1 ≡ T →
                       ∀l2,m2,T2. ⬆[l2, m2] T ≡ T2 → l1 + m1 ≤ l2 →
                       ∃∃T0. ⬆[l2 - m1, m2] T1 ≡ T0 & ⬆[l1, m1] T0 ≡ T2.
#l1 #m1 #T1 #T #H elim H -l1 -m1 -T1 -T
[ #k #l1 #m1 #l2 #m2 #X #HX #_
  >(lift_inv_sort1 … HX) -HX /2 width=3 by lift_sort, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #X #HX #Hlml
  lapply (ylt_yle_trans … (l1+m1) ? Hil1) // #Hil1m
  lapply (ylt_yle_trans … (l2-m1) ? Hil1) /2 width=1 by yle_plus1_to_minus_inj2/ #Hil2m
  lapply (ylt_yle_trans … Hlml Hil1m) -Hil1m -Hlml #Hil2
  lapply (lift_inv_lref1_lt … HX ?) -HX // #HX destruct /3 width=3 by lift_lref_lt, ex2_intro/
| #i #l1 #m1 #Hil1 #l2 #m2 #X #HX #_
  elim (lift_inv_lref1 … HX) -HX * <yplus_inj #Himl #HX destruct
  [ /4 width=3 by lift_lref_lt, lift_lref_ge, ylt_plus1_to_minus_inj2, ex2_intro/
  | /4 width=3 by lift_lref_ge, yle_plus_dx1_trans, monotonic_yle_minus_dx, ex2_intro/
  ]
| #p #l1 #m1 #l2 #m2 #X #HX #_
  >(lift_inv_gref1 … HX) -HX /2 width=3 by lift_gref, ex2_intro/
| #a #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hlml
  elim (yle_inv_plus_inj2 … Hlml) #Hlm #Hml
  elim (lift_inv_bind1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20) -IHV12 -HV20 //
  elim (IHT12 … HT20) -IHT12 -HT20 /2 width=1 by yle_succ/ -Hlml
  #T >yminus_succ1_inj /3 width=5 by lift_bind, ex2_intro/
| #I #V1 #V2 #T1 #T2 #l1 #m1 #_ #_ #IHV12 #IHT12 #l2 #m2 #X #HX #Hlml
  elim (lift_inv_flat1 … HX) -HX #V0 #T0 #HV20 #HT20 #HX destruct
  elim (IHV12 … HV20) -IHV12 -HV20 //
  elim (IHT12 … HT20) -IHT12 -HT20 /3 width=5 by lift_flat, ex2_intro/
]
qed.

(* Advanced properties ******************************************************)

lemma lift_conf_O1: ∀T,T1,l1,m1. ⬆[l1, m1] T ≡ T1 → ∀T2,m2. ⬆[0, m2] T ≡ T2 →
                    ∃∃T0. ⬆[0, m2] T1 ≡ T0 & ⬆[l1 + m2, m1] T2 ≡ T0.
#T #T1 #l1 #m1 #HT1 #T2 #m2 #HT2
elim (lift_total T1 0 m2) #T0 #HT10
elim (lift_trans_le … HT1 … HT10) -HT1 // #X #HTX #HT20
lapply (lift_mono … HTX … HT2) -T #H destruct /2 width=3 by ex2_intro/
qed.

lemma lift_conf_be: ∀T,T1,l,m1. ⬆[l, m1] T ≡ T1 → ∀T2,m2. ⬆[l, m2] T ≡ T2 →
                    m1 ≤ m2 → ⬆[l + yinj m1, m2 - m1] T1 ≡ T2.
#T #T1 #l #m1 #HT1 #T2 #m2 #HT2 #Hm12
elim (lift_split … HT2 (l+m1) m1) -HT2 // #X #H
>(lift_mono … H … HT1) -T //
qed.
