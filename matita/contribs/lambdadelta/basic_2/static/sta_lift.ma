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

include "basic_2/substitution/drop_drop.ma".
include "basic_2/static/sta.ma".

(* STATIC TYPE ASSIGNMENT ON TERMS ******************************************)

(* Properties on relocation *************************************************)

(* Basic_1: was: sty0_lift *)
lemma sta_lift: ∀h,G. l_liftable (sta h G).
#h #G #L1 #T1 #U1 #H elim H -G -L1 -T1 -U1
[ #G #L1 #k #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  >(lift_inv_sort1 … H1) -X1
  >(lift_inv_sort1 … H2) -X2 //
| #G #L1 #K1 #V1 #W1 #W #i #HLK1 #_ #HW1 #IHVW1 #L2 #s #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2) -W // #W2 #HW12 #HWU2
    elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=9 by sta_ldef/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W /2 width=1 by le_S/ #HW1U2
    lapply (drop_trans_ge … HL21 … HLK1 ?) -L1 /3 width=9 by sta_ldef, drop_inv_gen/
  ]
| #G #L1 #K1 #W1 #V1 #W #i #HLK1 #_ #HW1 #IHWV1 #L2 #s #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2) -W // <minus_plus #W #HW1 #HWU2
    elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    lapply (lift_mono … HW1 … HW12) -HW1 #H destruct
    elim (lift_total V1 (d-i-1) e) /3 width=9 by sta_ldec/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W /2 width=1 by le_S/ #HW1U2
    lapply (drop_trans_ge … HL21 … HLK1 ?) -L1 /3 width=9 by sta_ldec, drop_inv_gen/
  ]
| #a #I #G #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_bind1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=6 by sta_bind, drop_skip/
| #G #L1 #V1 #T1 #U1 #_ #IHTU1 #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=6 by sta_appl/
| #G #L1 #W1 #T1 #U1 #_ #IHTU1 #L2 #s #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #W2 #T2 #_ #HT12 #H destruct /3 width=6 by sta_cast/
]
qed.

(* Note: apparently this was missing in basic_1 *)
lemma sta_inv_lift1: ∀h,G. l_deliftable_sn (sta h G).
#h #G #L2 #T2 #U2 #H elim H -G -L2 -T2 -U2
[ #G #L2 #k #L1 #s #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=3 by sta_sort, lift_sort, ex2_intro/
| #G #L2 #K2 #V2 #W2 #W #i #HLK2 #HVW2 #HW2 #IHVW2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HVW2 | -IHVW2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 // #K1 #V1 #HLK1 #HK21 #HV12
    elim (IHVW2 … HK21 … HV12) -K2 -V2 #W1 #HW12 #HVW1
    elim (lift_trans_le … HW12 … HW2) -W2 // >minus_plus <plus_minus_m_m /3 width=8 by sta_ldef, ex2_intro/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1)) -HW2 /2 width=1 by le_S_S, le_S/
    #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /3 width=8 by sta_ldef, le_S, ex2_intro/
  ]
| #G #L2 #K2 #W2 #V2 #W #i #HLK2 #HWV2 #HW2 #IHWV2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HWV2 | -IHWV2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 // #K1 #W1 #HLK1 #HK21 #HW12
    elim (IHWV2 … HK21 … HW12) -K2 #V1 #_ #HWV1
    elim (lift_trans_le … HW12 … HW2) -W2 // >minus_plus <plus_minus_m_m /3 width=8 by sta_ldec, ex2_intro/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1)) -HW2 /2 width=1 by le_S_S, le_S/
    #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /3 width=8 by sta_ldec, le_S, ex2_intro/
  ]
| #a #I #G #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 (L1.ⓑ{I}V1) … HT12) -IHTU2 -HT12 /3 width=5 by sta_bind, drop_skip, lift_bind, ex2_intro/
| #G #L2 #V2 #T2 #U2 #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=5 by sta_appl, lift_flat, ex2_intro/
| #G #L2 #W2 #T2 #U2 #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #_ #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=3 by sta_cast, ex2_intro/
]
qed-.

(* Advanced forward lemmas **************************************************)

(* Basic_1: was: sty0_correct *)
lemma sta_fwd_correct: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U → ∃T0. ⦃G, L⦄ ⊢ U •[h] T0.
#h #G #L #T #U #H elim H -G -L -T -U
[ /2 width=2/
| #G #L #K #V #W #W0 #i #HLK #_ #HW0 * #V0 #HWV0
  lapply (drop_fwd_drop2 … HLK) -HLK #HLK
  elim (lift_total V0 0 (i+1)) /3 width=11 by ex_intro, sta_lift/
| #G #L #K #W #V #V0 #i #HLK #HWV #HWV0 #_
  lapply (drop_fwd_drop2 … HLK) -HLK #HLK
  elim (lift_total V 0 (i+1)) /3 width=11 by ex_intro, sta_lift/
| #a #I #G #L #V #T #U #_ * /3 width=2 by sta_bind, ex_intro/
| #G #L #V #T #U #_ * #T0 #HUT0 /3 width=2 by sta_appl, ex_intro/
| #G #L #W #T #U #_ * /2 width=2 by ex_intro/
]
qed-.
