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
include "basic_2/unfold/lstas.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on relocation *************************************************)

(* Basic_1: was just: sty0_lift *)
lemma lstas_lift: ∀h,G,l. l_liftable (lstas h G l).
#h #G #l #L1 #T1 #U1 #H elim H -G -L1 -T1 -U1 -l
[ #G #L1 #l #k #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  >(lift_inv_sort1 … H1) -X1
  >(lift_inv_sort1 … H2) -X2 //
| #G #L1 #K1 #V1 #W1 #W #i #l #HLK1 #_ #HW1 #IHVW1 #L2 #s #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2) -W // #W2 #HW12 #HWU2
    elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=9 by lstas_ldef/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W /2 width=1 by le_S/ #HW1U2
    lapply (drop_trans_ge … HL21 … HLK1 ?) -L1 /3 width=9 by lstas_ldef, drop_inv_gen/
  ]
| #G #L1 #K1 #V1 #W1 #i #HLK1 #_ #IHVW1 #L2 #s #d #e #HL21 #X #H #U2 #HWU2
  >(lift_mono … HWU2 … H) -U2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_total W1 (d-i-1) e) #W2 #HW12
    elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #V2 #HK21 #HV12 #H destruct
    /3 width=10 by lstas_zero/
  | lapply (drop_trans_ge … HL21 … HLK1 ?) -L1
    /3 width=10 by lstas_zero, drop_inv_gen/
  ]
| #G #L1 #K1 #W1 #V1 #W #i #l #HLK1 #_ #HW1 #IHWV1 #L2 #s #d #e #HL21 #X #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HW1 … HWU2) -W // <minus_plus #W #HW1 #HWU2
    elim (drop_trans_le … HL21 … HLK1) -L1 /2 width=2 by lt_to_le/ #X #HLK2 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K2 #W2 #HK21 #HW12 #H destruct
    /3 width=9 by lstas_succ/
  | lapply (lift_trans_be … HW1 … HWU2 ? ?) -W /2 width=1 by le_S/ #HW1U2
    lapply (drop_trans_ge … HL21 … HLK1 ?) -L1 /3 width=9 by lstas_succ, drop_inv_gen/
  ]
| #a #I #G #L1 #V1 #T1 #U1 #l #_ #IHTU1 #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_bind1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_bind1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=6 by lstas_bind, drop_skip/
| #G #L1 #V1 #T1 #U1 #l #_ #IHTU1 #L2 #s #d #e #HL21 #X1 #H1 #X2 #H2
  elim (lift_inv_flat1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H destruct
  elim (lift_inv_flat1 … H2) -H2 #X #U2 #H1 #HU12 #H2 destruct
  lapply (lift_mono … H1 … HV12) -H1 #H destruct /4 width=6 by lstas_appl/
| #G #L1 #W1 #T1 #U1 #l #_ #IHTU1 #L2 #s #d #e #HL21 #X #H #U2 #HU12
  elim (lift_inv_flat1 … H) -H #W2 #T2 #_ #HT12 #H destruct /3 width=6 by lstas_cast/
]
qed.

(* Inversion lemmas on relocation *******************************************)

(* Note: apparently this was missing in basic_1 *)
lemma lstas_inv_lift1: ∀h,G,l. l_deliftable_sn (lstas h G l).
#h #G #l #L2 #T2 #U2 #H elim H -G -L2 -T2 -U2 -l
[ #G #L2 #l #k #L1 #s #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=3 by lstas_sort, lift_sort, ex2_intro/
| #G #L2 #K2 #V2 #W2 #W #i #l #HLK2 #HVW2 #HW2 #IHVW2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HVW2 | -IHVW2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 // #K1 #V1 #HLK1 #HK21 #HV12
    elim (IHVW2 … HK21 … HV12) -K2 -V2 #W1 #HW12 #HVW1
    elim (lift_trans_le … HW12 … HW2) -W2 // >minus_plus <plus_minus_m_m /3 width=8 by lstas_ldef, ex2_intro/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1)) -HW2 /2 width=1 by le_S_S, le_S/
    #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /3 width=8 by lstas_ldef, le_S, ex2_intro/
  ]
| #G #L2 #K2 #W2 #V2 #i #HLK2 #HWV2 #IHWV2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HWV2 | -IHWV2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 // #K1 #W1 #HLK1 #HK21 #HW12
    elim (IHWV2 … HK21 … HW12) -K2
    /3 width=5 by lstas_zero, lift_lref_lt, ex2_intro/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2
    /3 width=5 by lstas_zero, lift_lref_ge_minus, ex2_intro/
  ]
| #G #L2 #K2 #W2 #V2 #W #i #l #HLK2 #HWV2 #HW2 #IHWV2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct [ -HWV2 | -IHWV2 ]
  [ elim (drop_conf_lt … HL21 … HLK2) -L2 // #K1 #W1 #HLK1 #HK21 #HW12
    elim (IHWV2 … HK21 … HW12) -K2 #V1 #HV12 #HWV1
    elim (lift_trans_le … HV12 … HW2) -W2 // >minus_plus <plus_minus_m_m /3 width=8 by lstas_succ, ex2_intro/
  | lapply (drop_conf_ge … HL21 … HLK2 ?) -L2 // #HL1K2
    elim (le_inv_plus_l … Hid) -Hid #Hdie #ei
    elim (lift_split … HW2 d (i-e+1)) -HW2 /2 width=1 by le_S_S, le_S/
    #W0 #HW20 <le_plus_minus_comm // >minus_minus_m_m /3 width=8 by lstas_succ, le_S, ex2_intro/
  ]
| #a #I #G #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 (L1.ⓑ{I}V1) … HT12) -IHTU2 -HT12 /3 width=5 by lstas_bind, drop_skip, lift_bind, ex2_intro/
| #G #L2 #V2 #T2 #U2 #l #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HV12 #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=5 by lstas_appl, lift_flat, ex2_intro/
| #G #L2 #W2 #T2 #U2 #l #_ #IHTU2 #L1 #s #d #e #HL21 #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #_ #HT12 #H destruct
  elim (IHTU2 … HL21 … HT12) -L2 -HT12 /3 width=3 by lstas_cast, ex2_intro/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma zero_eq_plus: ∀x,y. 0 = x + y → 0 = x ∧ 0 = y.
* /2 width=1 by conj/ #x #y normalize #H destruct
qed-.

lemma lstas_split_aux: ∀h,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*[h, l] T2 → ∀l1,l2. l = l1 + l2 →
                       ∃∃T. ⦃G, L⦄ ⊢ T1 •*[h, l1] T & ⦃G, L⦄ ⊢ T •*[h, l2] T2.
#h #G #L #T1 #T2 #l #H elim H -G -L -T1 -T2 -l
[ #G #L #l #k #l1 #l2 #H destruct
  >commutative_plus >iter_plus /2 width=3 by lstas_sort, ex2_intro/
| #G #L #K #V1 #V2 #U2 #i #l #HLK #_ #VU2 #IHV12 #l1 #l2 #H destruct
  elim (IHV12 l1 l2) -IHV12 // #V
  elim (lift_total V 0 (i+1))
  lapply (drop_fwd_drop2 … HLK)
  /3 width=12 by lstas_lift, lstas_ldef, ex2_intro/
| #G #L #K #W1 #W2 #i #HLK #HW12 #_ #l1 #l2 #H
  elim (zero_eq_plus … H) -H #H1 #H2 destruct
  /3 width=5 by lstas_zero, ex2_intro/
| #G #L #K #W1 #W2 #U2 #i #l #HLK #HW12 #HWU2 #IHW12 #l1 @(nat_ind_plus … l1) -l1
  [ #l2 normalize #H destruct
    elim (IHW12 0 l) -IHW12 //
    lapply (drop_fwd_drop2 … HLK)
    /3 width=8 by lstas_succ, lstas_zero, ex2_intro/
  | #l1 #_ #l2 <plus_plus_comm_23 #H lapply (injective_plus_l … H) -H #H
    elim (IHW12 … H) -l #W
    elim (lift_total W 0 (i+1))
    lapply (drop_fwd_drop2 … HLK)
    /3 width=12 by lstas_lift, lstas_succ, ex2_intro/
  ]
| #a #I #G #L #V #T #U #l #_ #IHTU #l1 #l2 #H
  elim (IHTU … H) -l /3 width=3 by lstas_bind, ex2_intro/
| #G #L #V #T #U #l #_ #IHTU #l1 #l2 #H
  elim (IHTU … H) -l /3 width=3 by lstas_appl, ex2_intro/
| #G #L #W #T #U #l #_ #IHTU #l1 #l2 #H
  elim (IHTU … H) -l /3 width=3 by lstas_cast, ex2_intro/
]
qed-.

lemma lstas_split: ∀h,G,L,T1,T2,l1,l2. ⦃G, L⦄ ⊢ T1 •*[h, l1 + l2] T2 →
                   ∃∃T. ⦃G, L⦄ ⊢ T1 •*[h, l1] T & ⦃G, L⦄ ⊢ T •*[h, l2] T2.
/2 width=3 by lstas_split_aux/ qed-.

(* Advanced properties ******************************************************)

lemma lstas_lstas: ∀h,G,L,T,T1,l1. ⦃G, L⦄ ⊢ T •*[h, l1] T1 →
                   ∀l2. ∃T2. ⦃G, L⦄ ⊢ T •*[h, l2] T2.
#h #G #L #T #T1 #l1 #H elim H -G -L -T -T1 -l1
[ /2 width=2 by lstas_sort, ex_intro/
| #G #L #K #V #V1 #U1 #i #l1 #HLK #_ #HVU1 #IHV1 #l2
  elim (IHV1 l2) -IHV1 #V2
  elim (lift_total V2 0 (i+1))
  /3 width=7 by ex_intro, lstas_ldef/
| #G #L #K #W #W1 #i #HLK #HW1 #IHW1 #l2
  @(nat_ind_plus … l2) -l2 /3 width=5 by lstas_zero, ex_intro/
  #l2 #_ elim (IHW1 l2) -IHW1 #W2
  elim (lift_total W2 0 (i+1))
  /3 width=7 by lstas_succ, ex_intro/
| #G #L #K #W #W1 #U1 #i #l #HLK #_ #_ #IHW1 #l2
  @(nat_ind_plus … l2) -l2
  [ elim (IHW1 0) -IHW1 /3 width=5 by lstas_zero, ex_intro/
  | #l2 #_ elim (IHW1 l2) -IHW1
    #W2 elim (lift_total W2 0 (i+1)) /3 width=7 by ex_intro, lstas_succ/
  ]
| #a #I #G #L #V #T #U #l #_ #IHTU #l2
  elim (IHTU l2) -IHTU /3 width=2 by lstas_bind, ex_intro/
| #G #L #V #T #U #l #_ #IHTU #l2
  elim (IHTU l2) -IHTU /3 width=2 by lstas_appl, ex_intro/
| #G #L #W #T #U #l #_ #IHTU #l2
  elim (IHTU l2) -IHTU /3 width=2 by lstas_cast, ex_intro/
]
qed-.
