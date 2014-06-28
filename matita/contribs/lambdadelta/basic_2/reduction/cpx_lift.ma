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
include "basic_2/multiple/fqus_alt.ma".
include "basic_2/static/sta.ma".
include "basic_2/static/da.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Advanced properties ******************************************************)

lemma sta_cpx: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •[h] T2 →
               ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L #T1 #T2 #l #H elim H -G -L -T1 -T2
[ /3 width=4 by cpx_st, da_inv_sort/
| #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 #IHV12 #H
  elim (da_inv_lref … H) -H * #K0 #V0 [| #l0 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct /3 width=7 by cpx_delta/
| #G #L #K #W1 #W2 #V1 #i #HLK #_ #HWV1 #IHW12 #H
  elim (da_inv_lref … H) -H * #K0 #W0 [| #l1 ] #HLK0
  lapply (drop_mono … HLK0 … HLK) -HLK0 #H destruct /3 width=7 by cpx_delta/
| /4 width=2 by cpx_bind, da_inv_bind/
| /4 width=3 by cpx_flat, da_inv_flat/
| /4 width=3 by cpx_eps, da_inv_flat/
]
qed.

(* Relocation properties ****************************************************)

lemma cpx_lift: ∀h,g,G. l_liftable (cpx h g G).
#h #g #G #K #T1 #T2 #H elim H -G -K -T1 -T2
[ #I #G #K #L #s #d #e #_ #U1 #H1 #U2 #H2
  >(lift_mono … H1 … H2) -H1 -H2 //
| #G #K #k #l #Hkl #L #s #d #e #_ #U1 #H1 #U2 #H2
  >(lift_inv_sort1 … H1) -U1
  >(lift_inv_sort1 … H2) -U2 /2 width=2 by cpx_st/
| #I #G #K #KV #V #V2 #W2 #i #HKV #HV2 #HVW2 #IHV2 #L #s #d #e #HLK #U1 #H #U2 #HWU2
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (lift_trans_ge … HVW2 … HWU2) -W2 // <minus_plus #W2 #HVW2 #HWU2
    elim (drop_trans_le … HLK … HKV) -K /2 width=2 by lt_to_le/ #X #HLK #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid
    #K #Y #HKV #HVY #H destruct /3 width=10 by cpx_delta/
  | lapply (lift_trans_be … HVW2 … HWU2 ? ?) -W2 /2 width=1 by le_S/ >plus_plus_comm_23 #HVU2
    lapply (drop_trans_ge_comm … HLK … HKV ?) -K /3 width=7 by cpx_delta, drop_inv_gen/
  ]
| #a #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #s #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /4 width=6 by cpx_bind, drop_skip/
| #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L #s #d #e #HLK #U1 #H1 #U2 #H2
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1 destruct
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct /3 width=6 by cpx_flat/
| #G #K #V #T1 #T #T2 #_ #HT2 #IHT1 #L #s #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_bind1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct
  elim (lift_conf_O1 … HTU2 … HT2) -T2 /4 width=6 by cpx_zeta, drop_skip/
| #G #K #V #T1 #T2 #_ #IHT12 #L #s #d #e #HLK #U1 #H #U2 #HTU2
  elim (lift_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct /3 width=6 by cpx_eps/
| #G #K #V1 #V2 #T #_ #IHV12 #L #s #d #e #HLK #U1 #H #U2 #HVU2
  elim (lift_inv_flat1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct /3 width=6 by cpx_ct/
| #a #G #K #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L #s #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #X #T3 #HX #HT23 #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #W3 #V3 #HW23 #HV23 #HX destruct /4 width=6 by cpx_beta, drop_skip/
| #a #G #K #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L #s #d #e #HLK #X1 #HX1 #X2 #HX2
  elim (lift_inv_flat1 … HX1) -HX1 #V0 #X #HV10 #HX #HX1 destruct
  elim (lift_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT10 #HX destruct
  elim (lift_inv_bind1 … HX2) -HX2 #W3 #X #HW23 #HX #HX2 destruct
  elim (lift_inv_flat1 … HX) -HX #V3 #T3 #HV3 #HT23 #HX destruct
  elim (lift_trans_ge … HV2 … HV3) -V2 /4 width=6 by cpx_theta, drop_skip/
]
qed.

lemma cpx_inv_lift1: ∀h,g,G. l_deliftable_sn (cpx h g G).
#h #g #G #L #U1 #U2 #H elim H -G -L -U1 -U2
[ * #i #G #L #K #s #d #e #_ #T1 #H
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by cpx_atom, lift_sort, ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3 by cpx_atom, lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by cpx_atom, lift_gref, ex2_intro/
  ]
| #G #L #k #l #Hkl #K #s #d #e #_ #T1 #H
  lapply (lift_inv_sort2 … H) -H #H destruct /3 width=3 by cpx_st, lift_sort, ex2_intro/
| #I #G #L #LV #V #V2 #W2 #i #HLV #HV2 #HVW2 #IHV2 #K #s #d #e #HLK #T1 #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (drop_conf_lt … HLK … HLV) -L // #L #U #HKL #HLV #HUV
    elim (IHV2 … HLV … HUV) -V #U2 #HUV2 #HU2
    elim (lift_trans_le … HUV2 … HVW2) -V2 // >minus_plus <plus_minus_m_m /3 width=9 by cpx_delta, ex2_intro/
  | elim (le_inv_plus_l … Hid) #Hdie #Hei
    lapply (drop_conf_ge … HLK … HLV ?) -L // #HKLV
    elim (lift_split … HVW2 d (i - e + 1)) -HVW2 /3 width=1 by le_S, le_S_S/ -Hid -Hdie
    #V1 #HV1 >plus_minus // <minus_minus /2 width=1 by le_S/ <minus_n_n <plus_n_O /3 width=9 by cpx_delta, ex2_intro/
  ]
| #a #I #G #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #s #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -IHV12 #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -IHU12 -HTU1 /3 width=6 by cpx_bind, drop_skip, lift_bind, ex2_intro/
| #I #G #L #V1 #V2 #U1 #U2 #_ #_ #IHV12 #IHU12 #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1
  elim (IHU12 … HLK … HTU1) -U1 -HLK /3 width=5 by cpx_flat, lift_flat, ex2_intro/
| #G #L #V #U1 #U #U2 #_ #HU2 #IHU1 #K #s #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU1 (K.ⓓW1) s … HTU1) /2 width=1/ -L -U1 #T #HTU #HT1
  elim (lift_div_le … HU2 … HTU) -U /3 width=5 by cpx_zeta, ex2_intro/
| #G #L #V #U1 #U2 #_ #IHU12 #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHU12 … HLK … HTU1) -L -U1 /3 width=3 by cpx_eps, ex2_intro/
| #G #L #V1 #V2 #U1 #_ #IHV12 #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -L -V1 /3 width=3 by cpx_ct, ex2_intro/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #K #s #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV12 … HLK … HV01) -V1 #V3 #HV32 #HV03
  elim (IHT12 (K.ⓛW0) s … HT01) -T1 /2 width=1 by drop_skip/ #T3 #HT32 #HT03
  elim (IHW12 … HLK … HW01) -W1
  /4 width=7 by cpx_beta, lift_bind, lift_flat, ex2_intro/
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #K #s #d #e #HLK #X #HX
  elim (lift_inv_flat2 … HX) -HX #V0 #Y #HV01 #HY #HX destruct
  elim (lift_inv_bind2 … HY) -HY #W0 #T0 #HW01 #HT01 #HY destruct
  elim (IHV1 … HLK … HV01) -V1 #V3 #HV3 #HV03
  elim (IHT12 (K.ⓓW0) s … HT01) -T1 /2 width=1 by drop_skip/ #T3 #HT32 #HT03
  elim (IHW12 … HLK … HW01) -W1 #W3 #HW32 #HW03
  elim (lift_trans_le … HV3 … HV2) -V
  /4 width=9 by cpx_theta, lift_bind, lift_flat, ex2_intro/
]
qed-.

(* Properties on supclosure *************************************************)

lemma fqu_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                     ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 
/3 width=3 by fqu_pair_sn, fqu_bind_dx, fqu_flat_dx, cpx_pair_sn, cpx_bind, cpx_flat, ex2_intro/
[ #I #G #L #V2 #U2 #HVU2
  elim (lift_total U2 0 1)
  /4 width=7 by fqu_drop, cpx_delta, drop_pair, drop_drop, ex2_intro/
| #G #L #K #T1 #U1 #e #HLK1 #HTU1 #T2 #HTU2
  elim (lift_total T2 0 (e+1))
  /3 width=11 by cpx_lift, fqu_drop, ex2_intro/
]
qed-.

lemma fqu_sta_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∀U2. ⦃G2, L2⦄ ⊢ T2 •[h] U2 →
                     ∀l. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] l+1 →
                     ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
/3 width=5 by fqu_cpx_trans, sta_cpx/ qed-.

lemma fquq_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fquq_inv_gen … H) -H
[ #HT12 elim (fqu_cpx_trans … HT12 … HTU2) /3 width=3 by fqu_fquq, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fquq_sta_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 •[h] U2 →
                      ∀l. ⦃G2, L2⦄ ⊢ T2 ▪[h, g] l+1 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
/3 width=5 by fquq_cpx_trans, sta_cpx/ qed-.

lemma fqup_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #U2 #HTU2 elim (fqu_cpx_trans … H12 … HTU2) -T2
  /3 width=3 by fqu_fqup, ex2_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #U2 #HTU2
  elim (fqu_cpx_trans … HT2 … HTU2) -T2 #T2 #HT2 #HTU2
  elim (IHT1 … HT2) -T /3 width=7 by fqup_strap1, ex2_intro/
]
qed-.

lemma fqus_cpx_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                      ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                      ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 elim (fqus_inv_gen … H) -H
[ #HT12 elim (fqup_cpx_trans … HT12 … HTU2) /3 width=3 by fqup_fqus, ex2_intro/
| * #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma fqu_cpx_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                         ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 → (T2 = U2 → ⊥) →
                         ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lift_total V2 0 1)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by fqu_drop, cpx_delta, drop_pair, drop_drop/
  | #H destruct /2 width=7 by lift_inv_lref2_be/
  ]
| #I #G #L #V1 #T #V2 #HV12 #H @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpx_pair_sn/
  | #H0 destruct /2 width=1 by/
  ]
| #a #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓑ{a,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpx_bind/
  | #H0 destruct /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpx_flat/
  | #H0 destruct /2 width=1 by/
  ]
| #G #L #K #T1 #U1 #e #HLK #HTU1 #T2 #HT12 #H elim (lift_total T2 0 (e+1))
  #U2 #HTU2 @(ex3_intro … U2)
  [1,3: /2 width=10 by cpx_lift, fqu_drop/
  | #H0 destruct /3 width=5 by lift_inj/
]
qed-.

lemma fquq_cpx_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fquq_inv_gen … H12) -H12
[ #H12 elim (fqu_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpx_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpx_trans_neq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpx_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_gen … H12) -H12
[ #H12 elim (fqup_cpx_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.
