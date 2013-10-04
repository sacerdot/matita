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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/relocation/fsupq.ma".
include "basic_2/static/ssta.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Advanced properties ******************************************************)

lemma ssta_cpx: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •[h, g] T2 →
                ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L #T1 #T2 #l #H elim H -G -L -T1 -T2
[ #G #L #k #H lapply (da_inv_sort … H) -H /2 width=2/
| #G #L #K #V #U #W #i #HLK #_ #HWU #IHVW #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0 ] #HLK0
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct /3 width=7/
| #G #L #K #W #U #l0 #i #HLK #_ #HWU #H
  elim (da_inv_lref … H) -H * #K0 #W0 [| #l1 ] #HLK0
  lapply (ldrop_mono … HLK0 … HLK) -HLK0 #H destruct /2 width=7/
| #a #I #G #L #V #T #U #_ #IHTU #H lapply (da_inv_bind … H) -H /3 width=1/
| #G #L #V #T #U #_ #IHTU #H lapply (da_inv_flat … H) -H /3 width=1/
| #G #L #W #T #U #_ #IHTU #H lapply (da_inv_flat … H) -H /3 width=1/
]
qed.

(* Relocation properties ****************************************************)

lemma cpx_lift: ∀h,g,G. l_liftable (cpx h g G).
#h #g #G #K #T1 #T2 #H elim H -G -K -T1 -T2
[ #I #G #K #L #d #e #_ #U1 #H1 #U2 #H2
  >(lift_mono … H1 … H2) -H1 -H2 //
| #G #K #k #l #Hkl #L #d #e #_ #U1 #H1 #U2 #H2
  >(lift_inv_sort1 … H1) -U1
  >(lift_inv_sort1 … H2) -U2 /2 width=2/
| #I #G #K #KV #V #V2 #W2 #i #HKV #HV2 #HVW2 #IHV2 #L #d #e #HLK #U1 #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HVW2 … HWU2) -W2 // <minus_plus #W2 #HVW2 #HWU2
    elim (ldrop_trans_le … HLK … HKV) -K /2 width=2/ #X #HLK #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #K #Y #HKV #HVY #H destruct /3 width=9/
  | lapply (lift_trans_be … HVW2 … HWU2 ? ?) -W2 // /2 width=1/ >plus_plus_comm_23 #HVU2
    lapply (ldrop_trans_ge_comm … HLK … HKV ?) -K // -Hid /3 width=7/
  ]
| #a #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /4 width=5/
| #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /3 width=6/
| #G #K #V #T1 #T #T2 #_ #HT2 #IHT1 #L #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_bind1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (lift_conf_O1 … HTU2 … HT2) -T2 /4 width=5/
| #G #K #V #T1 #T2 #_ #IHT12 #L #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct /3 width=5/
| #G #K #V1 #V2 #T #_ #IHV12 #L #d #e #HLK #U1 #H #U2 #HVU2
  elim (lift_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct /3 width=5/
| #a #G #K #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #X #T3 #HX #HT23 #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #W3 #V3 #HW23 #HV23 #HX destruct /4 width=5/
| #a #G #K #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct
  elim (lift_trans_ge … HV2 … HV3) -V2 // /4 width=5/
]
qed.

lemma cpx_inv_lift1: ∀h,g,G. l_deliftable_sn (cpx h g G).
#h #g #G #L #U1 #U2 #H elim H -G -L -U1 -U2
[ * #G #L #i #K #d #e #_ #T1 #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3/
  ]
| #G #L #k #l #Hkl #K #d #e #_ #T1 #H
  lapply (lift_inv_sort2 … H) -H #H destruct /3 width=3/
| #I #G #L #LV #V #V2 #W2 #i #HLV #HV2 #HVW2 #IHV2 #K #d #e #HLK #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (ldrop_conf_lt … HLK … HLV) -L // #L #U #HKL #HLV #HUV
    elim (IHV2 … HLV … HUV) -V #U2 #HUV2 #HU2
    elim (lift_trans_le … HUV2 … HVW2) -V2 // >minus_plus <plus_minus_m_m // -Hid /3 width=9/
  | elim (le_inv_plus_l … Hid) #Hdie #Hei
    lapply (ldrop_conf_ge … HLK … HLV ?) -L // #HKLV
    elim (lift_split … HVW2 d (i - e + 1)) -HVW2 [4: // |3: /2 width=1/ |2: /3 width=1/ ] -Hid -Hdie
    #V1 #HV1 >plus_minus // <minus_minus // /2 width=1/ <minus_n_n <plus_n_O /3 width=9/
  ]
| #a #I #G #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -IHV12 #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -IHU12 -HTU1 /3 width=5/
| #I #G #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1
  elim (IHU12 … HLK … HTU1) -U1 -HLK /3 width=5/
| #G #L #V #U1 #U #U2 #_ #HU2 #IHU1 #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU1 (K.ⓓW1) … HTU1) /2 width=1/ -L -U1 #T #HTU #HT1
  elim (lift_div_le … HU2 … HTU) -U // /3 width=5/
| #G #L #V #U1 #U2 #_ #IHU12 #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU12 … HLK … HTU1) -L -U1 /3 width=3/
| #G #L #V1 #V2 #U1 #_ #IHV12 #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -L -V1 /3 width=3/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #K #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV12 … HLK … HV01) -V1 #V3 #HV32 #HV03
  elim (IHT12 (K.ⓛW0) … HT01) -T1 /2 width=1/ #T3 #HT32 #HT03
  elim (IHW12 … HLK … HW01) -W1 #W3 #HW32 #HW03
  @ex2_intro [2: /3 width=2/ | skip |3: /2 width=1/ ] (**) (* /4 width=6/ is slow *)
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #K #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV1 … HLK … HV01) -V1 #V3 #HV3 #HV03
  elim (IHT12 (K.ⓓW0) … HT01) -T1 /2 width=1/ #T3 #HT32 #HT03
  elim (IHW12 … HLK … HW01) -W1 #W3 #HW32 #HW03
  elim (lift_trans_le … HV3 … HV2) -V // #V #HV3 #HV2
  @ex2_intro [2: /3 width=2/ | skip |3: /2 width=3/ ] (**) (* /4 width=5/ is slow *)
]
qed-.

(* Properties on supclosure *************************************************)

lemma fsupq_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                       ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 [1: /2 width=3/ |3,4,5: /3 width=3/ ]
[ #I #G #L1 #V2 #U2 #HVU2
  elim (lift_total U2 0 1) /4 width=9/
| #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
  elim (IHT12 … HTU2) -IHT12 -HTU2 #T #HT1 #HT2
  elim (lift_total T d e) #U #HTU
  lapply (cpx_lift … HT1 … HLK1 … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
]
qed-.

lemma fsupq_ssta_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                        ∀U2. ⦃G2, L2⦄ ⊢ T2 •[h, g] U2 →
                        ∀l. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] l+1 →
                        ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
/3 width=5 by fsupq_cpx_trans, ssta_cpx/ qed-.

lemma fsup_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
/3 width=3 by fsupq_cpx_trans, fsup_fsupq/ qed-.

lemma fsup_ssta_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                       ∀U2. ⦃G2, L2⦄ ⊢ T2 •[h, g] U2 →
                       ∀l. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] l+1 →
                       ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊃⸮ ⦃G2, L2, U2⦄.
/3 width=5 by fsupq_ssta_trans, fsup_fsupq/ qed-.
