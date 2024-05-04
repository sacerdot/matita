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

include "static_2/static/reqg_drops.ma".
include "static_2/static/reqg_fqup.ma".
include "static_2/static/reqg_reqg.ma".
include "basic_2/rt_transition/rpx_fsle.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS **********)

(* Properties with generic equivalence for local environments ***************)

lemma rpx_pair_sn_split (S) (G):
      reflexive … S →
      ∀L1,L2,V. ❨G,L1❩ ⊢ ⬈[V] L2 → ∀I,T.
      ∃∃L. ❨G,L1❩ ⊢ ⬈[②[I]V.T] L & L ≛[S,V] L2.
/3 width=5 by rpx_fsge_comp, rex_pair_sn_split, teqg_refl/ qed-.

lemma rpx_flat_dx_split (S) (G):
      reflexive … S →
      ∀L1,L2,T. ❨G,L1❩ ⊢ ⬈[T] L2 → ∀I,V.
      ∃∃L. ❨G,L1❩ ⊢ ⬈[ⓕ[I]V.T] L & L ≛[S,T] L2.
/3 width=5 by rpx_fsge_comp, rex_flat_dx_split, teqg_refl/ qed-.

lemma rpx_bind_dx_split (S) (G):
      reflexive … S →
      ∀I,L1,L2,V1,T. ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈[T] L2 → ∀p.
      ∃∃L,V. ❨G,L1❩ ⊢ ⬈[ⓑ[p,I]V1.T] L & L.ⓑ[I]V ≛[S,T] L2 & ❨G,L1❩ ⊢ V1 ⬈ V.
/3 width=5 by rpx_fsge_comp, rex_bind_dx_split, teqg_refl/ qed-.

lemma rpx_bind_dx_split_void (S) (G):
      reflexive … S →
      ∀K1,L2,T. ❨G,K1.ⓧ❩ ⊢ ⬈[T] L2 → ∀p,I,V.
      ∃∃K2. ❨G,K1❩ ⊢ ⬈[ⓑ[p,I]V.T] K2 & K2.ⓧ ≛[S,T] L2.
/3 width=5 by rpx_fsge_comp, rex_bind_dx_split_void, teqg_refl/ qed-.

lemma rpx_teqg_conf_sn (S) (G):
      reflexive … S →
      s_r_confluent1 … (ceqg S) (rpx G).
/2 width=5 by teqg_rex_conf_sn/ qed-.

lemma rpx_teqg_div (S) (G):
      reflexive … S → symmetric … S →
      ∀T1,T2. T1 ≛[S] T2 → ∀L1,L2. ❨G,L1❩ ⊢ ⬈[T2] L2 → ❨G,L1❩ ⊢ ⬈[T1] L2.
/2 width=6 by teqg_rex_div/ qed-.

lemma cpx_teqg_repl_reqg (S) (G) (L0) (T0):
      reflexive … S →
      ∀T1. ❨G,L0❩ ⊢ T0 ⬈ T1 → ∀T2. T0 ≛[S] T2 → ∀T3. T1 ≛[S] T3 →
      ∀L2. L0 ≛[S,T0] L2 → ❨G,L2❩ ⊢ T2 ⬈ T3.
#S #G #L0 #T0 #HS #T1 #H @(cpx_ind … H) -G -L0 -T0 -T1
[ * #x0 #G #L0 #X2 #HX2 #X3 #HX3 #L2 #_
  [ elim (teqg_inv_sort1 … HX2) -HX2 #x2 #Hx02 #H destruct
    elim (teqg_inv_sort1 … HX3) -HX3 #x3 #Hx03 #H destruct //
  | lapply (teqg_inv_lref1 … HX2) -HX2 #H destruct
    lapply (teqg_inv_lref1 … HX3) -HX3 #H destruct //
  | lapply (teqg_inv_gref1 … HX2) -HX2 #H destruct
    lapply (teqg_inv_gref1 … HX3) -HX3 #H destruct //
  ]
| #G #L0 #s0 #s1 #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_sort1 … HX2) -HX2 #s2 #H destruct
  elim (teqg_inv_sort1 … HX3) -HX3 #s3 #H destruct //
| #I #G #K0 #V0 #V1 #W1 #_ #IH #HVW1 #X2 #HX2 #X3 #HX3 #L2 #HL2
  lapply (teqg_inv_lref1 … HX2) -HX2 #H destruct
  elim (reqg_inv_zero_pair_sn … HL2) -HL2 #K2 #V2 #HK02 #HV02 #H destruct
  elim (teqg_inv_lifts_sn … HX3 … HVW1) -W1 #V3 #HVX3 #HV13
  /3 width=3 by cpx_delta/
| #I0 #G #K0 #V1 #W1 #i #_ #IH #HVW1 #X2 #HX2 #X3 #HX3 #L2 #HL2
  lapply (teqg_inv_lref1 … HX2) -HX2 #H destruct
  elim (reqg_inv_lref_bind_sn … HL2) -HL2 #I2 #K2 #HK02 #H destruct
  elim (teqg_inv_lifts_sn … HX3 … HVW1) -W1 #V3 #HVX3 #HV13
  /3 width=3 by cpx_lref/
| #p #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #HT02 #H destruct
  elim (teqg_inv_pair1 … HX3) -HX3 #V3 #T3 #HV13 #HT13 #H destruct
  elim (reqg_inv_bind_refl … HL02) -HL02 // #HV0 #HT0
  lapply (reqg_bind_repl_dx … HT0 (BPair I V2) ?) -HT0
  /2 width=1 by ext2_pair/ #HT0
  /3 width=1 by cpx_bind/
| #I #G #L0 #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #HT02 #H destruct
  elim (teqg_inv_pair1 … HX3) -HX3 #V3 #T3 #HV13 #HT13 #H destruct
  elim (reqg_inv_flat … HL02) -HL02 #HV0 #HT0
  /3 width=1 by cpx_flat/
| #G #L0 #V0 #U0 #T0 #T1 #HTU0 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #U2 #HV02 #HU02 #H destruct
  elim (reqg_inv_bind_refl … HL02) -HL02 // #HV0 #HU0
  lapply (reqg_inv_lifts_bi … HU0 (ⓣ) … HTU0) -HU0
  [6:|*: /3 width=2 by drops_refl, drops_drop/ ] #HT0
  elim (teqg_inv_lifts_sn … HU02 … HTU0) -U0 #T2 #HTU2 #HT02
  /3 width=3 by cpx_zeta/
| #G #L0 #V0 #T0 #T1 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #T2 #_ #HT02 #H destruct
  elim (reqg_inv_flat … HL02) -HL02 #HV0 #HT0
  /3 width=1 by cpx_eps/
| #G #L0 #V0 #T0 #T1 #_ #IH #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #T2 #HV02 #_ #H destruct
  elim (reqg_inv_flat … HL02) -HL02 #HV0 #HT1
  /3 width=1 by cpx_ee/
| #p #G #L0 #V0 #V1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #X #HV02 #HX #H destruct
  elim (teqg_inv_pair1 … HX) -HX #W2 #T2 #HW02 #HT02 #H destruct
  elim (teqg_inv_pair1 … HX3) -HX3 #X #T3 #HX #HT13 #H destruct
  elim (teqg_inv_pair1 … HX) -HX #W3 #V3 #HW13 #HV13 #H destruct
  elim (reqg_inv_flat … HL02) -HL02 #HV0 #HL02
  elim (reqg_inv_bind_refl … HL02) -HL02 // #HW0 #HT0
  lapply (reqg_bind_repl_dx … HT0 (BPair Abst W2) ?) -HT0
  /2 width=1 by ext2_pair/ #H2T0
  /3 width=1 by cpx_beta/
| #p #G #L0 #V0 #V1 #U1 #W0 #W1 #T0 #T1 #_ #_ #_ #IHV #IHW #IHT #HVU1 #X2 #HX2 #X3 #HX3 #L2 #HL02
  elim (teqg_inv_pair1 … HX2) -HX2 #V2 #X #HV02 #HX #H destruct
  elim (teqg_inv_pair1 … HX) -HX #W2 #T2 #HW02 #HT02 #H destruct
  elim (teqg_inv_pair1 … HX3) -HX3 #W3 #X #HW13 #HX #H destruct
  elim (teqg_inv_pair1 … HX) -HX #U3 #T3 #HU13 #HT13 #H destruct
  elim (reqg_inv_flat … HL02) -HL02 #HV0 #HL02
  elim (reqg_inv_bind_refl … HL02) -HL02 // #HW0 #HT0
  lapply (reqg_bind_repl_dx … HT0 (BPair Abbr W2) ?) -HT0
  /2 width=1 by ext2_pair/ #HT0
  elim (teqg_inv_lifts_sn … HU13 … HVU1) -U1 #V3 #HVU3 #HV13
  /3 width=3 by cpx_theta/
]
qed-.

lemma cpx_teqg_conf (S) (G) (L):
      reflexive … S →
      ∀T0:term. ∀T1. ❨G,L❩ ⊢ T0 ⬈ T1 → ∀T2. T0 ≛[S] T2 → ❨G,L❩ ⊢ T2 ⬈ T1.
/3 width=9 by cpx_teqg_repl_reqg, reqg_refl, teqg_refl/ qed-.

lemma teqg_cpx_trans (S) (G) (L):
      reflexive … S → symmetric … S →
      ∀T2. ∀T0:term. T2 ≛[S] T0 → ∀T1. ❨G,L❩ ⊢ T0 ⬈ T1 → ❨G,L❩ ⊢ T2 ⬈ T1.
/3 width=6 by cpx_teqg_conf, teqg_sym/
qed-.

lemma teqg_cpx (S) (G) (L):
      reflexive … S → symmetric … S →
      ∀T1,T2:term. T1 ≛[S] T2 → ❨G,L❩ ⊢ T1 ⬈ T2.
/2 width=6 by teqg_cpx_trans/ qed.

(* Basic_2A1: uses: cpx_lleq_conf *)
lemma cpx_reqg_conf (S) (G):
      reflexive … S →
      R_confluent1_rex (cpx G) (ceqg S).
/3 width=9 by cpx_teqg_repl_reqg, teqg_refl/ qed-.

(* Basic_2A1: uses: lleq_cpx_trans *)
lemma reqg_cpx_trans (S) (G):
      reflexive … S → symmetric … S →
      ∀L2,L0,T0. L2 ≛[S,T0] L0 → ∀T1. ❨G,L0❩ ⊢ T0 ⬈ T1 → ❨G,L2❩ ⊢ T0 ⬈ T1.
/3 width=7 by cpx_reqg_conf, reqg_sym/
qed-.

lemma rpx_reqg_conf (S) (G) (T):
      reflexive … S →
      confluent1 … (rpx G T) (reqg S T).
/3 width=9 by reqg_fsge_comp, cpx_teqg_repl_reqg, rex_conf1, teqg_refl/ qed-.

lemma reqg_rpx_trans (S) (G) (T) (L):
      reflexive … S → symmetric … S →
      ∀L1. L1 ≛[S,T] L → ∀L2. ❨G,L❩ ⊢ ⬈[T] L2 → ❨G,L1❩ ⊢ ⬈[T] L2.
/3 width=7 by rpx_reqg_conf, reqg_sym/ qed-.

lemma reqg_rpx (S) (G) (T):
      reflexive … S → symmetric … S →
      ∀L1,L2. L1 ≛[S,T] L2 → ❨G,L1❩ ⊢ ⬈[T] L2.
/2 width=6 by reqg_rpx_trans/ qed.
