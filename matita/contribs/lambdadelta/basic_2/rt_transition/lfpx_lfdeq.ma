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

include "basic_2/relocation/lifts_tdeq.ma".
include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/static/lfdeq_fqup.ma".
include "basic_2/rt_transition/lfpx_frees.ma".
include "basic_2/rt_transition/lfpx.ma". (**) (* should be in lfpx_frees.ma *)

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with degree-based equivalence for local environments **********)

lemma lfpx_pair_sn_split: ∀h,o,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, V] L2 →
                          ∃∃L. ⦃G, L1⦄ ⊢ ⬈[h, ②{I}V.T] L & L ≡[h, o, V] L2.
/3 width=5 by lfpx_frees_conf, lfxs_pair_sn_split/ qed-.

lemma lfpx_flat_dx_split: ∀h,o,I,G,L1,L2,V,T. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 →
                          ∃∃L. ⦃G, L1⦄ ⊢ ⬈[h, ⓕ{I}V.T] L & L ≡[h, o, T] L2.
/3 width=5 by lfpx_frees_conf, lfxs_flat_dx_split/ qed-.

lemma cpx_tdeq_conf_lexs: ∀h,o,G. R_confluent2_lfxs … (cpx h G) (cdeq h o) (cpx h G) (cdeq h o).
#h #o #G #L0 #T0 #T1 #H @(cpx_ind … H) -G -L0 -T0 -T1 /2 width=3 by ex2_intro/
[ #G #L0 #s0 #X0 #H0 #L1 #HL01 #L2 #HL02
  elim (tdeq_inv_sort1 … H0) -H0 #s1 #d1 #Hs0 #Hs1 #H destruct
  /4 width=3 by tdeq_sort, deg_next, ex2_intro/
| #I #G #K0 #V0 #V1 #W1 #_ #IH #HVW1 #T2 #H0 #L1 #H1 #L2 #H2
  >(tdeq_inv_lref1 … H0) -H0
  elim (lfpx_inv_zero_pair_sn … H1) -H1 #K1 #X1 #HK01 #HX1 #H destruct
  elim (lfdeq_inv_zero_pair_sn … H2) -H2 #K2 #X2 #HK02 #HX2 #H destruct
  elim (IH X2 … HK01 … HK02) // -K0 -V0 #V #HV1 #HV2
  elim (tdeq_lifts_sn … HV1 … HVW1) -V1 /3 width=5 by cpx_delta, ex2_intro/
| #I #G #K0 #V0 #V1 #W1 #i #_ #IH #HVW1 #T2 #H0 #L1 #H1 #L2 #H2
  >(tdeq_inv_lref1 … H0) -H0
  elim (lfpx_inv_lref_pair_sn … H1) -H1 #K1 #X1 #HK01 #H destruct
  elim (lfdeq_inv_lref_pair_sn … H2) -H2 #K2 #X2 #HK02 #H destruct
  elim (IH … HK01 … HK02) [|*: //] -K0 -V0 #V #HV1 #HV2
  elim (tdeq_lifts_sn … HV1 … HVW1) -V1 /3 width=5 by cpx_lref, ex2_intro/
| #p #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #T2 #HV02 #HT02 #H destruct
  elim (lfpx_inv_bind … H1) -H1 #HL01 #H1
  elim (lfdeq_inv_bind … H2) -H2 #HL02 #H2
  lapply (lfdeq_pair_repl_dx … H2 … HV02) -H2 #H2
  elim (IHV … HV02 … HL01 … HL02) -IHV -HV02 -HL01 -HL02
  elim (IHT … HT02 … H1 … H2) -L0 -T0
  /3 width=5 by cpx_bind, tdeq_pair, ex2_intro/
| #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #T2 #HV02 #HT02 #H destruct
  elim (lfpx_inv_flat … H1) -H1 #HL01 #H1
  elim (lfdeq_inv_flat … H2) -H2 #HL02 #H2
  elim (IHV … HV02 … HL01 … HL02) -IHV -HV02 -HL01 -HL02
  elim (IHT … HT02 … H1 … H2) -L0 -V0 -T0
  /3 width=5 by cpx_flat, tdeq_pair, ex2_intro/
| #G #L0 #V0 #T0 #T1 #U1 #_ #IH #HUT1 #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #T2 #HV02 #HT02 #H destruct
  elim (lfpx_inv_bind … H1) -H1 #HL01 #H1
  elim (lfdeq_inv_bind … H2) -H2 #HL02 #H2
  lapply (lfdeq_pair_repl_dx … H2 … HV02) -H2 -HV02 #H2
  elim (IH … HT02 … H1 … H2) -L0 -T0 #T #HT1
  elim (tdeq_inv_lifts_sn … HT1 … HUT1) -T1
  /3 width=5 by cpx_zeta, ex2_intro/
| #G #L0 #V0 #T0 #T1 #_ #IH #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #T2 #_ #HT02 #H destruct
  elim (lfpx_inv_flat … H1) -H1 #HL01 #H1
  elim (lfdeq_inv_flat … H2) -H2 #HL02 #H2
  elim (IH … HT02 … H1 … H2) -L0 -V0 -T0
  /3 width=3 by cpx_eps, ex2_intro/
| #G #L0 #V0 #T0 #T1 #_ #IH #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #T2 #HV02 #_ #H destruct
  elim (lfpx_inv_flat … H1) -H1 #HL01 #H1
  elim (lfdeq_inv_flat … H2) -H2 #HL02 #H2
  elim (IH … HV02 … HL01 … HL02) -L0 -V0 -T1
  /3 width=3 by cpx_ee, ex2_intro/
| #p #G #L0 #V0 #V1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #X #HV02 #H0 #H destruct
  elim (tdeq_inv_pair1 … H0) -H0 #W2 #T2 #HW02 #HT02 #H destruct
  elim (lfpx_inv_flat … H1) -H1 #H1LV0 #H1
  elim (lfpx_inv_bind … H1) -H1 #H1LW0 #H1LT0
  elim (lfdeq_inv_flat … H2) -H2 #H2LV0 #H2
  elim (lfdeq_inv_bind … H2) -H2 #H2LW0 #H2LT0
  lapply (lfdeq_pair_repl_dx … H2LT0 … HW02) -H2LT0 #H2LT0
  elim (IHV … HV02 … H1LV0 … H2LV0) -IHV -HV02 -H1LV0 -H2LV0
  elim (IHW … HW02 … H1LW0 … H2LW0) -IHW -HW02 -H1LW0 -H2LW0
  elim (IHT … HT02 … H1LT0 … H2LT0) -L0 -V0 -T0
  /4 width=7 by cpx_beta, tdeq_pair, ex2_intro/ (* note: 2 tdeq_pair *)
| #p #G #L0 #V0 #V1 #U1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #HVU1 #X0 #H0 #L1 #H1 #L2 #H2
  elim (tdeq_inv_pair1 … H0) -H0 #V2 #X #HV02 #H0 #H destruct
  elim (tdeq_inv_pair1 … H0) -H0 #W2 #T2 #HW02 #HT02 #H destruct
  elim (lfpx_inv_flat … H1) -H1 #H1LV0 #H1
  elim (lfpx_inv_bind … H1) -H1 #H1LW0 #H1LT0
  elim (lfdeq_inv_flat … H2) -H2 #H2LV0 #H2
  elim (lfdeq_inv_bind … H2) -H2 #H2LW0 #H2LT0
  lapply (lfdeq_pair_repl_dx … H2LT0 … HW02) -H2LT0 #H2LT0
  elim (IHV … HV02 … H1LV0 … H2LV0) -IHV -HV02 -H1LV0 -H2LV0 #V #HV1
  elim (IHW … HW02 … H1LW0 … H2LW0) -IHW -HW02 -H1LW0 -H2LW0
  elim (IHT … HT02 … H1LT0 … H2LT0) -L0 -V0 -T0
  elim (tdeq_lifts_sn … HV1 … HVU1) -V1
  /4 width=9 by cpx_theta, tdeq_pair, ex2_intro/ (* note: 2 tdeq_pair *)
]
qed-.

lemma cpx_tdeq_conf: ∀h,o,G,L,T0,T1. ⦃G, L⦄ ⊢ T0 ⬈[h] T1 →
                     ∀T2. T0 ≡[h, o] T2 →
                     ∃∃T. T1 ≡[h, o] T & ⦃G, L⦄ ⊢ T2 ⬈[h] T.
#h #o #G #L #T0 #T1 #HT01 #T2 #HT02
elim (cpx_tdeq_conf_lexs … HT01 … HT02 L … L) -HT01 -HT02
/2 width=3 by lfxs_refl, ex2_intro/
qed-.

lemma tdeq_cpx_trans: ∀h,o,G,L,T2,T0. T2 ≡[h, o] T0 →
                      ∀T1. ⦃G, L⦄ ⊢ T0 ⬈[h] T1 → 
                      ∃∃T. ⦃G, L⦄ ⊢ T2 ⬈[h] T & T ≡[h, o] T1.
#h #o #G #L #T2 #T0 #HT20 #T1 #HT01
elim (cpx_tdeq_conf … HT01 T2) -HT01 /3 width=3 by tdeq_sym, ex2_intro/
qed-.

(* Basic_2A1: was just: cpx_lleq_conf *)
lemma cpx_lfdeq_conf: ∀h,o,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                      ∀L2. L0 ≡[h, o, T0] L2 →
                      ∃∃T. ⦃G, L2⦄ ⊢ T0 ⬈[h] T & T1 ≡[h, o] T.
#h #o #G #L0 #T0 #T1 #HT01 #L2 #HL02
elim (cpx_tdeq_conf_lexs … HT01 T0 … L0 … HL02) -HT01 -HL02
/2 width=3 by lfxs_refl, ex2_intro/
qed-.

(* Basic_2A1: was just: lleq_cpx_trans *)
lemma lfdeq_cpx_trans: ∀h,o,G,L2,L0,T0. L2 ≡[h, o, T0] L0 →
                       ∀T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                       ∃∃T. ⦃G, L2⦄ ⊢ T0 ⬈[h] T & T ≡[h, o] T1.
#h #o #G #L2 #L0 #T0 #HL20 #T1 #HT01
elim (cpx_lfdeq_conf … o … HT01 L2) -HT01
/3 width=3 by lfdeq_sym, tdeq_sym, ex2_intro/
qed-.

lemma lfpx_lfdeq_conf: ∀h,o,G,T. confluent2 … (lfpx h G T) (lfdeq h o T).
/3 width=6 by lfpx_frees_conf, cpx_tdeq_conf_lexs, frees_lfdeq_conf_lexs, lfxs_conf/ qed-.

(* Basic_2A1: was just: lleq_lpx_trans *)
lemma lfdeq_lfpx_trans: ∀h,o,G,T,L2,K2. ⦃G, L2⦄ ⊢ ⬈[h, T] K2 →
                        ∀L1. L1 ≡[h, o, T] L2 →
                        ∃∃K1. ⦃G, L1⦄ ⊢ ⬈[h, T] K1 & K1 ≡[h, o, T] K2.
#h #o #G #T #L2 #K2 #HLK2 #L1 #HL12
elim (lfpx_lfdeq_conf … o … HLK2 L1)
/3 width=3 by lfdeq_sym, ex2_intro/
qed-.
