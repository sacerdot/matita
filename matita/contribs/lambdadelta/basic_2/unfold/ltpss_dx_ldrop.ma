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

include "basic_2/substitution/fsup.ma".
include "basic_2/unfold/tpss_lift.ma".
include "basic_2/unfold/ltpss_dx.ma".

(* DX PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

(* Properies on local environment slicing ***********************************)

lemma ltpss_dx_ldrop_conf_ge: ∀L0,L1,d1,e1. L0 ▶* [d1, e1] L1 →
                              ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                              d1 + e1 ≤ e2 → ⇩[0, e2] L1 ≡ L2.
#L0 #L1 #d1 #e1 #H elim H -L0 -L1 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H //
| //
| normalize #K0 #K1 #I #V0 #V1 #e1 #_ #_ #IHK01 #L2 #e2 #H #He12
  elim (le_inv_plus_l … He12) #_ #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  lapply (IHK01 … HK0L2 ?) -K0 /2 width=1/
| #K0 #K1 #I #V0 #V1 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK01 #L2 #e2 #H #Hd1e2
  elim (le_inv_plus_l … Hd1e2) #_ #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  lapply (IHK01 … HK0L2 ?) -K0 /2 width=1/
]
qed.

lemma ltpss_dx_ldrop_trans_ge: ∀L1,L0,d1,e1. L1 ▶* [d1, e1] L0 →
                               ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                               d1 + e1 ≤ e2 → ⇩[0, e2] L1 ≡ L2.
#L1 #L0 #d1 #e1 #H elim H -L1 -L0 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H //
| //
| normalize #K1 #K0 #I #V1 #V0 #e1 #_ #_ #IHK10 #L2 #e2 #H #He12
  elim (le_inv_plus_l … He12) #_ #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  lapply (IHK10 … HK0L2 ?) -K0 /2 width=1/
| #K0 #K1 #I #V1 #V0 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK10 #L2 #e2 #H #Hd1e2
  elim (le_inv_plus_l … Hd1e2) #_ #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  lapply (IHK10 … HK0L2 ?) -IHK10 -HK0L2 /2 width=1/
]
qed.

lemma ltpss_dx_ldrop_conf_be: ∀L0,L1,d1,e1. L0 ▶* [d1, e1] L1 →
                              ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                              ∃∃L. L2 ▶* [0, d1 + e1 - e2] L & ⇩[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H elim H -L0 -L1 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H /2 width=3/
| normalize #L #I #V #L2 #e2 #HL2 #_ #He2
  lapply (le_n_O_to_eq … He2) -He2 #H destruct
  lapply (ldrop_inv_refl … HL2) -HL2 #H destruct /2 width=3/
| normalize #K0 #K1 #I #V0 #V1 #e1 #HK01 #HV01 #IHK01 #L2 #e2 #H #_ #He21
  lapply (ldrop_inv_O1 … H) -H * * #He2 #HK0L2
  [ -IHK01 -He21 destruct <minus_n_O /3 width=3/
  | -HK01 -HV01 <minus_le_minus_minus_comm //
    elim (IHK01 … HK0L2 ? ?) -K0 // /2 width=1/ /3 width=3/
  ]
| #K0 #K1 #I #V0 #V1 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK01 #L2 #e2 #H #Hd1e2 #He2de1
  elim (le_inv_plus_l … Hd1e2) #_ #He2
  <minus_le_minus_minus_comm //
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  elim (IHK01 … HK0L2 ? ?) -K0 /2 width=1/ /3 width=3/
]
qed.

lemma ltpss_dx_ldrop_trans_be: ∀L1,L0,d1,e1. L1 ▶* [d1, e1] L0 →
                               ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                               ∃∃L. L ▶* [0, d1 + e1 - e2] L2 & ⇩[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H elim H -L1 -L0 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H /2 width=3/
| normalize #L #I #V #L2 #e2 #HL2 #_ #He2
  lapply (le_n_O_to_eq … He2) -He2 #H destruct
  lapply (ldrop_inv_refl … HL2) -HL2 #H destruct /2 width=3/
| normalize #K1 #K0 #I #V1 #V0 #e1 #HK10 #HV10 #IHK10 #L2 #e2 #H #_ #He21
  lapply (ldrop_inv_O1 … H) -H * * #He2 #HK0L2
  [ -IHK10 -He21 destruct <minus_n_O /3 width=3/
  | -HK10 -HV10 <minus_le_minus_minus_comm //
    elim (IHK10 … HK0L2 ? ?) -K0 // /2 width=1/ /3 width=3/
  ]
| #K1 #K0 #I #V1 #V0 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK10 #L2 #e2 #H #Hd1e2 #He2de1
  elim (le_inv_plus_l … Hd1e2) #_ #He2
  <minus_le_minus_minus_comm //
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HK0L2
  elim (IHK10 … HK0L2 ? ?) -K0 /2 width=1/ /3 width=3/
]
qed.

lemma ltpss_dx_ldrop_conf_le: ∀L0,L1,d1,e1. L0 ▶* [d1, e1] L1 →
                              ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                              ∃∃L. L2 ▶* [d1 - e2, e1] L & ⇩[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H elim H -L0 -L1 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H /2 width=3/
| /2 width=3/
| normalize #K0 #K1 #I #V0 #V1 #e1 #HK01 #HV01 #_ #L2 #e2 #H #He2
  lapply (le_n_O_to_eq … He2) -He2 #He2 destruct
  lapply (ldrop_inv_refl … H) -H #H destruct /3 width=3/
| #K0 #K1 #I #V0 #V1 #d1 #e1 #HK01 #HV01 #IHK01 #L2 #e2 #H #He2d1
  lapply (ldrop_inv_O1 … H) -H * * #He2 #HK0L2
  [ -IHK01 -He2d1 destruct <minus_n_O /3 width=3/
  | -HK01 -HV01 <minus_le_minus_minus_comm //
    elim (IHK01 … HK0L2 ?) -K0 /2 width=1/ /3 width=3/
  ]
]
qed.

lemma ltpss_dx_ldrop_trans_le: ∀L1,L0,d1,e1. L1 ▶* [d1, e1] L0 →
                               ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                               ∃∃L. L ▶* [d1 - e2, e1] L2 & ⇩[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H elim H -L1 -L0 -d1 -e1
[ #d1 #e1 #L2 #e2 #H >(ldrop_inv_atom1 … H) -H /2 width=3/
| /2 width=3/
| normalize #K1 #K0 #I #V1 #V0 #e1 #HK10 #HV10 #_ #L2 #e2 #H #He2
  lapply (le_n_O_to_eq … He2) -He2 #He2 destruct
  lapply (ldrop_inv_refl … H) -H #H destruct /3 width=3/
| #K1 #K0 #I #V1 #V0 #d1 #e1 #HK10 #HV10 #IHK10 #L2 #e2 #H #He2d1
  lapply (ldrop_inv_O1 … H) -H * * #He2 #HK0L2
  [ -IHK10 -He2d1 destruct <minus_n_O /3 width=3/
  | -HK10 -HV10 <minus_le_minus_minus_comm //
    elim (IHK10 … HK0L2 ?) -K0 /2 width=1/ /3 width=3/
  ]
]
qed.

lemma ldrop_ltpss_dx_trans_le: ∀L1,K1,d1,e1. ⇩[d1, e1] L1 ≡ K1 →
                               ∀K2,d2,e2. K1 ▶* [d2, e2] K2 → d1 ≤ d2 →
                               ∃∃L2. L1 ▶* [d2 + e1, e2] L2 & ⇩[d1, e1] L2 ≡ K2.
#L1 #K1 #d1 #e1 #H elim H -L1 -K1 -d1 -e1
[ #d1 #e1 #K2 #d2 #e2 #H #_
  >(ltpss_dx_inv_atom1 … H) -H /2 width=3/
| /2 width=3/
| #L1 #K1 #I #V #e1 #_ #IHLK1 #K2 #d2 #e2 #HK12 #Hd
  elim (IHLK1 … HK12 Hd) -K1 -Hd /3 width=5/
| #L1 #K1 #I #V1 #W1 #d1 #e1 #_ #HWV1 #IHLK1 #X #d2 #e2 #H #Hd12
  elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hd2
  elim (ltpss_dx_inv_tpss11 … H Hd2) -H #K2 #W2 #HK12 #HW12 #H destruct
  elim (IHLK1 … HK12 … Hd12) -IHLK1 -HK12 <le_plus_minus_comm // #L2 #HL12 #HLK2
  elim (lift_total W2 d1 e1) #V2 #HWV2
  lapply (tpss_lift_ge … HW12 … HLK2 HWV1 … HWV2) -W1 // -Hd12
  <le_plus_minus_comm // /4 width=5/
]
qed-.

lemma ldrop_ltpss_dx_trans_be: ∀L1,K1,d1,e1. ⇩[d1, e1] L1 ≡ K1 →
                               ∀K2,d2,e2. K1 ▶* [d2, e2] K2 →
                               d2 ≤ d1 → d1 ≤ d2 + e2 →
                               ∃∃L2. L1 ▶* [d2, e1 + e2] L2 &
                                     ⇩[d1, e1] L2 ≡ K2.
#L1 #K1 #d1 #e1 #H elim H -L1 -K1 -d1 -e1
[ #d1 #e1 #K2 #d2 #e2 #H #_ #_
  >(ltpss_dx_inv_atom1 … H) -H /2 width=3/
| #K1 #I #V1 #K2 #d2 #e2 #HK12 #H #_
  lapply (le_n_O_to_eq … H) -H #H destruct /2 width=3/
| #L1 #K1 #I #V #e1 #_ #IHLK1 #K2 #d2 #e2 #HK12 #H1 #H2
  elim (IHLK1 … HK12 H1 H2) -K1 -H2
  lapply (le_n_O_to_eq … H1) -H1 #H destruct /3 width=5/
| #L1 #K1 #I #V1 #W1 #d1 #e1 #_ #HWV1 #IHLK1 #X #d2 #e2 #H #Hd21 #Hd12
  elim (eq_or_gt d2) #Hd2 [ -Hd21 elim (eq_or_gt e2) #He2 ] destruct
  [ lapply (le_n_O_to_eq … Hd12) -Hd12 <plus_n_Sm #H destruct
  | elim (ltpss_dx_inv_tpss21 … H He2) -H #K2 #W2 #HK12 #HW12 #H destruct
    elim (IHLK1 … HK12 …) -IHLK1 // /2 width=1/ >plus_minus_commutative // #L2 #HL12 #HLK2
    elim (lift_total W2 d1 e1) #V2 #HWV2
    lapply (tpss_lift_be … HW12 … HLK2 HWV1 … HWV2) -W1 // /2 width=1/
    >plus_minus // >commutative_plus /4 width=5/
  | elim (ltpss_dx_inv_tpss11 … H Hd2) -H #K2 #W2 #HK12 #HW12 #H destruct
    elim (IHLK1 … HK12 …) -IHLK1 [2: >plus_minus // ] /2 width=1/ #L2 #HL12 #HLK2
    elim (lift_total W2 d1 e1) #V2 #HWV2
    lapply (tpss_lift_be … HW12 … HLK2 HWV1 … HWV2) -W1 [ >plus_minus // ] /2 width=1/
    >commutative_plus /3 width=5/
  ]
]
qed-.

lemma ldrop_ltpss_dx_trans_ge: ∀L1,K1,d1,e1. ⇩[d1, e1] L1 ≡ K1 →
                               ∀K2,d2,e2. K1 ▶* [d2, e2] K2 → d2 + e2 ≤ d1 →
                               ∃∃L2. L1 ▶* [d2, e2] L2 & ⇩[d1, e1] L2 ≡ K2.
#L1 #K1 #d1 #e1 #H elim H -L1 -K1 -d1 -e1
[ #d1 #e1 #K2 #d2 #e2 #H #_
  >(ltpss_dx_inv_atom1 … H) -H /2 width=3/
| #K1 #I #V1 #K2 #d2 #e2 #HK12 #H
  elim (plus_le_0 … H) -H #H1 #H2 destruct /2 width=3/
| #L1 #K1 #I #V #e1 #_ #IHLK1 #K2 #d2 #e2 #HK12 #H
  elim (IHLK1 … HK12 H) -K1
  elim (plus_le_0 … H) -H #H1 #H2 destruct #L2 #HL12
  >(ltpss_dx_inv_refl_O2 … HL12) -L1 /3 width=5/
| #L1 #K1 #I #V1 #W1 #d1 #e1 #HLK1 #HWV1 #IHLK1 #X #d2 #e2 #H #Hd21
  elim (eq_or_gt d2) #Hd2 [ elim (eq_or_gt e2) #He2 ] destruct
  [ -IHLK1 -Hd21 <(ltpss_dx_inv_refl_O2 … H) -X /3 width=5/
  | elim (ltpss_dx_inv_tpss21 … H He2) -H #K2 #W2 #HK12 #HW12 #H destruct
    elim (IHLK1 … HK12 …) -IHLK1 /2 width=1/ #L2 #HL12 #HLK2
    elim (lift_total W2 d1 e1) #V2 #HWV2
    lapply (tpss_lift_le … HW12 … HLK2 HWV1 … HWV2) -W1 /2 width=1/ /3 width=5/
  | elim (ltpss_dx_inv_tpss11 … H Hd2) -H #K2 #W2 #HK12 #HW12 #H destruct
    elim (IHLK1 … HK12 …) -IHLK1 [2: >plus_minus // /2 width=1/ ] #L2 #HL12 #HLK2
    elim (lift_total W2 d1 e1) #V2 #HWV2
    lapply (tpss_lift_le … HW12 … HLK2 HWV1 … HWV2) -W1 [ >plus_minus // /2 width=1/ ] /3 width=5/
  ]
]
qed-.

(* Properties on supclosure *************************************************)

lemma fsup_tps_trans_full: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀U2. L2 ⊢ T2 ▶[0,|L2|] U2 →
                           ∃∃L,U1. L1 ▶*[0,|L|] L & L ⊢ T1 ▶[0,|L|] U1 & ⦃L, U1⦄ ⊃ ⦃L2, T2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 [1,2,3,4,5: /3 width=5/ ]
#L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
elim (IHT12 … HTU2) -IHT12 -HTU2 #K #T #HK1 #HT1 #HT2
elim (lift_total T d e) #U #HTU
elim (le_or_ge d (|K|)) #Hd
[ elim (ldrop_ltpss_dx_trans_be … HLK1 … HK1 … Hd) // -HLK1 -HK1 #L2 #HL12 #HL2K
  lapply (tps_lift_be … HT1 … HL2K … HTU1 HTU … Hd) // -HT1 -HTU1 #HU1
| elim (ldrop_ltpss_dx_trans_ge … HLK1 … HK1 Hd) -HLK1 -HK1 #L2 #HL12 #HL2K
  lapply (tps_lift_le … HT1 … HL2K … HTU1 HTU Hd) -HT1 -HTU1 #HU1
]
lapply (ltpss_dx_weak_full … HL12) -HL12 #HL12
lapply (tps_weak_full … HU1) -HU1 #HU1
@(ex3_2_intro … L2 U) // /2 width=7/ (**) (* explicit constructor: auto /3 width=14/ too slow *)
qed-.
