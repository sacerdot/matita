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

include "basic_2/static/da_lift.ma".
include "basic_2/static/ssta.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS ******************************)

(* Properties on relocation *************************************************)

lemma ssta_lift: ∀h,g,G. l_liftable (ssta h g G).
#h #g #G #L1 #T1 #U1 #H elim H -G -L1 -T1 -U1
[ #G #L1 #k #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  >(lift_inv_sort1 … H1) -X1
  >(lift_inv_sort1 … H2) -X2 //
| #G #L1 #K1 #V1 #U1 #W1 #i #HLK1 #_ #HWU1 #IHVW1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HWU1 … HU12) -U1 // #W2 #HW12 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=8/
  | lapply (lift_trans_be … HWU1 … HU12 ? ?) -U1 // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #G #L1 #K1 #W1 #U1 #l #i #HLK1 #HW1l #HWU1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HWU1 … HU12) -U1 // <minus_plus #W2 #HW12 #HWU2
    elim (ldrop_trans_le … HL21 … HLK1) -L1 /2 width=2/ #X #HLK2 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K2 #W #HK21 #HW1 #H destruct
    lapply (lift_mono … HW1 … HW12) -HW1 #H destruct
    /3 width=10 by da_lift, ssta_ldec/
  | lapply (lift_trans_be … HWU1 … HU12 ? ?) -U1 // /2 width=1/ #HW1U2
    lapply (ldrop_trans_ge … HL21 … HLK1 ?) -L1 // -Hid /3 width=8/
  ]
| #a #I #G #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_bind1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=5/
| #G #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=5/
| #G #L1 #W1 #T1 #U1 #_ #IHTU1 #L2 #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #W2 #T2 #_ #HT12 #H destruct /3 width=5/
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma ssta_inv_lift1: ∀h,g,G. l_deliftable_sn (ssta h g G).
#h #g #G #L2 #T2 #U2 #H elim H -G -L2 -T2 -U2
[ #G #L2 #k #L1 #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=3/
| #G #L2 #K2 #V2 #U2 #W2 #i #HLK2 #HVW2 #HWU2 #IHVW2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HVW2 | -IHVW2 ]
  [ elim (ldrop_conf_lt … HL21 … HLK2) -L2 // #K1 #V1 #HLK1 #HK21 #HV12
    elim (IHVW2 … HK21 … HV12) -K2 -V2 #W1 #HW12 #HVW1
    elim (lift_trans_le … HW12 … HWU2) -W2 // >minus_plus <plus_minus_m_m // -Hid /3 width=8/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HWU2 d (i-e+1)) -HWU2 // [3: /2 width=1/ ]
    [ #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /2 width=1/ /3 width=8/
    | <le_plus_minus_comm //
    ]
  ]
| #G #L2 #K2 #W2 #U2 #l #i #HLK2 #HW2l #HWU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct
  [ elim (ldrop_conf_lt … HL21 … HLK2) -L2 // #K1 #W1 #HLK1 #HK21 #HW12
    lapply (da_inv_lift … HW2l … HK21 … HW12) -K2
    elim (lift_trans_le … HW12 … HWU2) -W2 // >minus_plus <plus_minus_m_m // -Hid /3 width=8/
  | lapply (ldrop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HWU2 d (i-e+1)) -HWU2 // [3: /2 width=1/ ]
    [ #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /2 width=1/ /3 width=8/
    | <le_plus_minus_comm //
    ]
  ]
| #a #I #G #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 (L1.ⓑ{I}V1) … HT12) -IHTU2 -HT12 /2 width=1/ -HL21 /3 width=5/
| #G #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=5/
| #G #L2 #W2 #T2 #U2 #_ #IHTU2 #L1 #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #_ #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=3/
]
qed-.

(* Advanced properties ******************************************************)

lemma ssta_da_conf: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U →
                    ∀l. ⦃G, L⦄ ⊢ T ▪[h, g] l → ⦃G, L⦄ ⊢ U ▪[h, g] l-1.
#h #g #G #L #T #U #H elim H -G -L -T -U
[ #G #L #k #l #H
  lapply (da_inv_sort … H) -H /3 width=1/
| #G #L #K #V #U #W #i #HLK #_ #HWU #IHVW #l #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0] #HLK0 #HV0
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct
  lapply (ldrop_fwd_drop2 … HLK) -HLK /3 width=7/
| #G #L #K #W #U #l0 #i #HLK #_ #HWU #l #H -l0
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l1] #HLK0 #HV0 [| #H0 ]
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct
  lapply (ldrop_fwd_drop2 … HLK) -HLK /3 width=7/
| #a #I #G #L #V #T #U #_ #IHTU #l #H
  lapply (da_inv_bind … H) -H /3 width=1/
| #G #L #V #T #U #_ #IHTU #l #H
  lapply (da_inv_flat … H) -H /3 width=1/
| #G #L #W #T #U #_ #IHTU #l #H
  lapply (da_inv_flat … H) -H /2 width=1/
]
qed-.

(* Advanced forvard lemmas **************************************************)

lemma ssta_fwd_correct: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U →
                        ∃T0. ⦃G, L⦄ ⊢ U •[h, g] T0.
#h #g #G #L #T #U #H elim H -G -L -T -U
[ /2 width=2/
| #G #L #K #V #U #W #i #HLK #_ #HWU * #T #HWT
  lapply (ldrop_fwd_drop2 … HLK) -HLK #HLK
  elim (lift_total T 0 (i+1)) /3 width=10/
| #G #L #K #W #U #l #i #HLK #HWl #HWU
  elim (da_ssta … HWl) -HWl #T #HWT
  lapply (ldrop_fwd_drop2 … HLK) -HLK #HLK
  elim (lift_total T 0 (i+1)) /3 width=10/
| #a #I #G #L #V #T #U #_ * /3 width=2/
| #G #L #V #T #U #_ * #T0 #HUT0 /3 width=2/
| #G #L #W #T #U #_ * /2 width=2/
]
qed-.
