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

include "static_2/syntax/teqx.ma".
include "basic_2/rt_transition/rpx_reqg.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS **********)
(*
(* Properties with sort-irrelevant equivalence for local environments *******)

lemma rpx_pair_sn_split (G):
      ∀L1,L2,V. ❨G,L1❩ ⊢ ⬈[V] L2 → ∀I,T.
      ∃∃L. ❨G,L1❩ ⊢ ⬈[②[I]V.T] L & L ≛[V] L2.
/3 width=5 by rpx_fsge_comp, rex_pair_sn_split/ qed-.

lemma rpx_flat_dx_split (G):
      ∀L1,L2,T. ❨G,L1❩ ⊢ ⬈[T] L2 → ∀I,V.
      ∃∃L. ❨G,L1❩ ⊢ ⬈[ⓕ[I]V.T] L & L ≛[T] L2.
/3 width=5 by rpx_fsge_comp, rex_flat_dx_split/ qed-.

lemma rpx_bind_dx_split (G):
      ∀I,L1,L2,V1,T. ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈[T] L2 → ∀p.
      ∃∃L,V. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V1.T] L & L.ⓑ[I]V ≛[T] L2 & ❨G,L1❩ ⊢ V1 ⬈ V.
/3 width=5 by rpx_fsge_comp, rex_bind_dx_split/ qed-.

lemma rpx_bind_dx_split_void (G):
      ∀K1,L2,T. ❨G,K1.ⓧ❩ ⊢ ⬈[T] L2 → ∀p,I,V.
      ∃∃K2. ❨G,K1❩ ⊢ ⬈[ⓑ[p,I]V.T] K2 & K2.ⓧ ≛[T] L2.
/3 width=5 by rpx_fsge_comp, rex_bind_dx_split_void/ qed-.

lemma rpx_teqx_conf_sn (G): s_r_confluent1 … cdeq (rpx G).
/2 width=5 by teqx_rex_conf_sn/ qed-.

lemma rpx_teqx_div (G):
      ∀T1,T2. T1 ≛ T2 → ∀L1,L2. ❨G,L1❩ ⊢ ⬈[T2] L2 → ❨G,L1❩ ⊢ ⬈[T1] L2.
/2 width=5 by teqx_rex_div/ qed-.

lemma cpx_teqx_repl_reqx (G) (L0) (T0):
      ∀T1. ❨G,L0❩ ⊢ T0 ⬈ T1 → ∀T2. T0 ≛ T2 → ∀T3. T1 ≛ T3 →
      ∀L2. L0 ≛[T0] L2 → ❨G,L2❩ ⊢ T2 ⬈ T3.
#G #L0 #T0 #T1 #H @(cpx_ind … H) -G -L0 -T0 -T1
[ * #x0 #G #L0 #X2 #HX2 #X3 #HX3 #L2 #_
  [ elim (teqx_inv_sort1 … HX2) -HX2 #x2 #H destruct
    elim (teqx_inv_sort1 … HX3) -HX3 #x3 #H destruct //
  | lapply (teqx_inv_lref1 … HX2) -HX2 #H destruct
    lapply (teqx_inv_lref1 … HX3) -HX3 #H destruct //
  | lapply (teqx_inv_gref1 … HX2) -HX2 #H destruct
    lapply (teqx_inv_gref1 … HX3) -HX3 #H destruct //
  ]
| #G #L0 #s0 #s1 #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_sort1 … HX2) -HX2 #s2 #H destruct
  elim (teqx_inv_sort1 … HX3) -HX3 #s3 #H destruct //
| #I #G #K0 #V0 #V1 #W1 #_ #IH #HVW1 #X2 #HX2 #X3 #HX3 #L2 #HL2
  lapply (teqx_inv_lref1 … HX2) -HX2 #H destruct
  elim (reqx_inv_zero_pair_sn … HL2) -HL2 #K2 #V2 #HK02 #HV02 #H destruct
  elim (teqx_inv_lifts_sn … HX3 … HVW1) -W1 #V3 #HVX3 #HV13
  /3 width=3 by cpx_delta/
| #I0 #G #K0 #V1 #W1 #i #_ #IH #HVW1 #X2 #HX2 #X3 #HX3 #L2 #HL2
  lapply (teqx_inv_lref1 … HX2) -HX2 #H destruct
  elim (reqx_inv_lref_bind_sn … HL2) -HL2 #I2 #K2 #HK02 #H destruct
  elim (teqx_inv_lifts_sn … HX3 … HVW1) -W1 #V3 #HVX3 #HV13
  /3 width=3 by cpx_lref/
| #p #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #HT02 #H destruct
  elim (teqx_inv_pair1 … HX3) -HX3 #V3 #T3 #HV13 #HT13 #H destruct
  elim (reqx_inv_bind … HL02) -HL02 #HV0 #HT0
  lapply (reqx_bind_repl_dx … HT0 (BPair I V2) ?) -HT0
  /2 width=1 by ext2_pair/ #HT0
  /3 width=1 by cpx_bind/
| #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #HT02 #H destruct
  elim (teqx_inv_pair1 … HX3) -HX3 #V3 #T3 #HV13 #HT13 #H destruct
  elim (reqx_inv_flat … HL02) -HL02 #HV0 #HT0
  /3 width=1 by cpx_flat/
| #G #L0 #V0 #U0 #T0 #T1 #HTU0 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #U2 #HV02 #HU02 #H destruct
  elim (reqx_inv_bind … HL02) -HL02 #HV0 #HU0
  lapply (reqx_inv_lifts_bi … HU0 (Ⓣ) … HTU0) -HU0
  [6:|*: /3 width=2 by drops_refl, drops_drop/ ] #HT0
  elim (teqx_inv_lifts_sn … HU02 … HTU0) -U0 #T2 #HTU2 #HT02
  /3 width=3 by cpx_zeta/
| #G #L0 #V0 #T0 #T1 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #T2 #_ #HT02 #H destruct
  elim (reqx_inv_flat … HL02) -HL02 #HV0 #HT0
  /3 width=1 by cpx_eps/
| #G #L0 #V0 #T0 #T1 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #_ #H destruct
  elim (reqx_inv_flat … HL02) -HL02 #HV0 #HT1
  /3 width=1 by cpx_ee/
| #p #G #L0 #V0 #V1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #X #HV02 #HX #H destruct
  elim (teqx_inv_pair1 … HX) -HX #W2 #T2 #HW02 #HT02 #H destruct
  elim (teqx_inv_pair1 … HX3) -HX3 #X #T3 #HX #HT13 #H destruct
  elim (teqx_inv_pair1 … HX) -HX #W3 #V3 #HW13 #HV13 #H destruct
  elim (reqx_inv_flat … HL02) -HL02 #HV0 #HL02
  elim (reqx_inv_bind … HL02) -HL02 #HW0 #HT0
  lapply (reqx_bind_repl_dx … HT0 (BPair Abst W2) ?) -HT0
  /2 width=1 by ext2_pair/ #H2T0
  /3 width=1 by cpx_beta/
| #p #G #L0 #V0 #V1 #U1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #HVU1 #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqx_inv_pair1 … HX2) -HX2 #V2 #X #HV02 #HX #H destruct
  elim (teqx_inv_pair1 … HX) -HX #W2 #T2 #HW02 #HT02 #H destruct
  elim (teqx_inv_pair1 … HX3) -HX3 #W3 #X #HW13 #HX #H destruct
  elim (teqx_inv_pair1 … HX) -HX #U3 #T3 #HU13 #HT13 #H destruct
  elim (reqx_inv_flat … HL02) -HL02 #HV0 #HL02
  elim (reqx_inv_bind … HL02) -HL02 #HW0 #HT0
  lapply (reqx_bind_repl_dx … HT0 (BPair Abbr W2) ?) -HT0
  /2 width=1 by ext2_pair/ #HT0
  elim (teqx_inv_lifts_sn … HU13 … HVU1) -U1 #V3 #HVU3 #HV13
  /3 width=3 by cpx_theta/
]
qed-.

lemma cpx_teqx_conf (G) (L):
      ∀T0:term. ∀T1. ❨G,L❩ ⊢ T0 ⬈ T1 → ∀T2. T0 ≛ T2 → ❨G,L❩ ⊢ T2 ⬈ T1.
/2 width=7 by cpx_teqx_repl_reqx/ qed-.
*)
lemma teqx_cpx_trans (G) (L):
      ∀T2. ∀T0:term. T2 ≅ T0 → ∀T1. ❨G,L❩ ⊢ T0 ⬈ T1 → ❨G,L❩ ⊢ T2 ⬈ T1.
/2 width=6 by teqg_cpx_trans/ qed-.
(*
lemma teqx_cpx (G) (L):
      ∀T1,T2:term. T1 ≛ T2 → ❨G,L❩ ⊢ T1 ⬈ T2.
/2 width=3 by teqx_cpx_trans/ qed.

(* Basic_2A1: uses: cpx_lleq_conf *)
lemma cpx_reqx_conf (G):
      ∀L0,T0,T1. ❨G,L0❩ ⊢ T0 ⬈ T1 → ∀L2. L0 ≛[T0] L2 → ❨G,L2❩ ⊢ T0 ⬈ T1.
/2 width=7 by cpx_teqx_repl_reqx/ qed-.

(* Basic_2A1: uses: lleq_cpx_trans *)
lemma reqx_cpx_trans (G):
      ∀L2,L0,T0. L2 ≛[T0] L0 → ∀T1. ❨G,L0❩ ⊢ T0 ⬈ T1 → ❨G,L2❩ ⊢ T0 ⬈ T1.
/3 width=3 by cpx_reqx_conf, reqx_sym/
qed-.

lemma rpx_reqx_conf (G) (T):
      confluent1 … (rpx G T) (reqx T).
/3 width=7 by reqx_fsge_comp, cpx_teqx_repl_reqx, rex_conf1/ qed-.

lemma reqx_rpx_trans (G) (T) (L):
      ∀L1. L1 ≛[T] L → ∀L2. ❨G,L❩ ⊢ ⬈[T] L2 → ❨G,L1❩ ⊢ ⬈[T] L2.
/3 width=3 by rpx_reqx_conf, reqx_sym/ qed-.

lemma reqx_rpx (G) (T):
      ∀L1,L2. L1 ≛[T] L2 → ❨G,L1❩ ⊢ ⬈[T] L2.
/2 width=3 by reqx_rpx_trans/ qed.
*)
