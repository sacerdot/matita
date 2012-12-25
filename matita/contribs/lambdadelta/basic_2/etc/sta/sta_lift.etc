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

include "basic_2/substitution/ldrop_ldrop.ma".
include "basic_2/static/sta.ma".

(* STATIC TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties on relocation *************************************************)

(* Basic_1: was: sty0_lift *)
lemma sta_lift: ∀h,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 • U1 → ∀L2,d,e. ⇩[d, e] L2 ≡ L1 →
                ∀T2. ⇧[d, e] T1 ≡ T2 → ∀U2. ⇧[d, e] U1 ≡ U2 → ⦃h, L2⦄ ⊢ T2 • U2.
#h #L1 #T1 #U1 #H elim H -L1 -T1 -U1
[ #L1 #k #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  >(lift_inv_sort1 … H1) -X1
  >(lift_inv_sort1 … H2) -X2 //
| #L1 #K1 #V1 #W1 #W #i #HLK1 #_ #HW1 #IHVW1 #L2 #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2 ?) -W // #W2 #HW12 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1 ?) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=8/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #L1 #K1 #W1 #V1 #W #i #HLK1 #_ #HW1 #IHWV1 #L2 #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2 ?) -W // <minus_plus #W #HW1 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1 ?) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    lapply (lift_mono … HW1 … HW12) -HW1 #H destruct
    elim (lift_total V1 (d-i-1) e) /3 width=8/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #I #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_bind1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=5/
| #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=5/
| #L1 #W1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #W2 #T2 #_ #HT12 #H destruct /3 width=5/
]
qed.

(* Note: apparently this was missing in basic_1 *)
lemma sta_inv_lift1: ∀h,L2,T2,U2. ⦃h, L2⦄ ⊢ T2 • U2 → ∀L1,d,e. ⇩[d, e] L2 ≡ L1 →
                     ∀T1. ⇧[d, e] T1 ≡ T2 →
                     ∃∃U1. ⦃h, L1⦄ ⊢ T1 • U1 & ⇧[d, e] U1 ≡ U2.
#h #L2 #T2 #U2 #H elim H -L2 -T2 -U2
[ #L2 #k #L1 #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=3/
| #L2 #K2 #V2 #W2 #W #i #HLK2 #HVW2 #HW2 #IHVW2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HVW2 | -IHVW2 ]
  [ elim (ldrop_conf_lt … HL21 … HLK2 ?) -L2 // #K1 #V1 #HLK1 #HK21 #HV12
    elim (IHVW2 … HK21 … HV12) -K2 -V2 #W1 #HVW1 #HW12
    elim (lift_trans_le … HW12 … HW2 ?) -W2 // >minus_plus <plus_minus_m_m // -Hid /3 width=6/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1) ? ? ?) -HW2 // [3: /2 width=1/ ]
    [ #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /2 width=1/ /3 width=6/
    | <le_plus_minus_comm // /2 width=1/
    ]
  ]
| #L2 #K2 #W2 #V2 #W #i #HLK2 #HWV2 #HW2 #IHWV2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HWV2 | -IHWV2 ]
  [ elim (ldrop_conf_lt … HL21 … HLK2 ?) -L2 // #K1 #W1 #HLK1 #HK21 #HW12
    elim (IHWV2 … HK21 … HW12) -K2 #V1 #HWV1 #_
    elim (lift_trans_le … HW12 … HW2 ?) -W2 // >minus_plus <plus_minus_m_m // -Hid /3 width=6/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1) ? ? ?) -HW2 // [3: /2 width=1/ ]
    [ #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /2 width=1/ /3 width=6/
    | <le_plus_minus_comm // /2 width=1/
    ]
  ]
| #I #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 (L1.ⓑ{I}V1) … HT12) -IHTU2 -HT12 /2 width=1/ -HL21 /3 width=5/
| #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=5/
| #L2 #W2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #_ #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=3/
]
qed.  

(* Advanced forvard lemmas **************************************************)

(* Basic_1: was: sty0_correct *)
lemma sta_fwd_correct: ∀h,L,T,U. ⦃h, L⦄ ⊢ T • U → ∃T0. ⦃h, L⦄ ⊢ U • T0.
#h #L #T #U #H elim H -L -T -U
[ /2 width=2/
| #L #K #V #W #W0 #i #HLK #_ #HW0 * #V0 #HWV0
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V0 0 (i+1)) /3 width=10/
| #L #K #W #V #V0 #i #HLK #HWV #HWV0 #_
  lapply (ldrop_fwd_ldrop2 … HLK) -HLK #HLK
  elim (lift_total V 0 (i+1)) /3 width=10/
| #I #L #V #T #U #_ * /3 width=2/
| #L #V #T #U #_ * #T0 #HUT0 /3 width=2/
| #L #W #T #U #_ * /2 width=2/
]
qed-.
