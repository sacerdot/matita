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

include "basic_2/rt_computation/cpxs_fqus.ma".
include "basic_2/rt_computation/cpxs_reqg.ma".
include "basic_2/rt_computation/lpxs_feqg.ma".
include "basic_2/rt_computation/fpbs_lpx.ma".
include "basic_2/rt_computation/fpbs_cpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with extended rt-computation on full local environments  ******)

lemma lpxs_fpbs:
      ∀G,L1,L2,T. ❨G,L1❩ ⊢ ⬈* L2 → ❨G,L1,T❩ ≥ ❨G,L2,T❩.
#G #L1 #L2 #T #H @(lpxs_ind_dx … H) -L2
/3 width=5 by lpx_fpb, fpbs_strap1/
qed.

lemma fpbs_lpxs_trans:
      ∀G1,G2,L1,L,T1,T2. ❨G1,L1,T1❩ ≥ ❨G2,L,T2❩ →
      ∀L2. ❨G2,L❩ ⊢ ⬈* L2 → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L #T1 #T2 #H1 #L2 #H @(lpxs_ind_dx … H) -L2
/3 width=5 by fpbs_strap1, lpx_fpb/
qed-.

lemma lpxs_fpbs_trans:
      ∀G1,G2,L,L2,T1,T2. ❨G1,L,T1❩ ≥ ❨G2,L2,T2❩ →
      ∀L1. ❨G1,L1❩ ⊢ ⬈* L → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L #L2 #T1 #T2 #H1 #L1 #H @(lpxs_ind_sn … H) -L1
/3 width=5 by fpbs_strap2, lpx_fpb/
qed-.

(* Basic_2A1: uses: lpxs_lleq_fpbs *)
lemma lpxs_feqg_fpbs (S) (L):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1❩ ⊢ ⬈* L →
      ∀G2,L2,T2. ❨G1,L,T1❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=4 by lpxs_fpbs_trans, feqg_fpbs/ qed.

(* Properties with star-iterated structural successor for closures **********)

lemma fqus_lpxs_fpbs:
      ∀G1,G2,L1,L,T1,T2. ❨G1,L1,T1❩ ⬂* ❨G2,L,T2❩ →
      ∀L2. ❨G2,L❩ ⊢ ⬈* L2 → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=3 by fpbs_lpxs_trans, fqus_fpbs/ qed.

(* Properties with extended context-sensitive parallel rt-computation *******)

lemma cpxs_fqus_lpxs_fpbs:
      ∀G1,L1,T1,T. ❨G1,L1❩ ⊢ T1 ⬈* T →
      ∀G2,L,T2. ❨G1,L1,T❩ ⬂* ❨G2,L,T2❩ →
      ∀L2.❨G2,L❩ ⊢ ⬈* L2 → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=5 by cpxs_fqus_fpbs, fpbs_lpxs_trans/ qed.

lemma fpbs_cpxs_teqg_fqup_lpx_trans (S):
      reflexive … S → symmetric … S →
      ∀G1,G3,L1,L3,T1,T3. ❨G1,L1,T1❩ ≥  ❨G3,L3,T3❩ →
      ∀T4. ❨G3,L3❩ ⊢ T3 ⬈* T4 → ∀T5. T4 ≛[S] T5 →
      ∀G2,L4,T2. ❨G3,L3,T5❩ ⬂+ ❨G2,L4,T2❩ →
      ∀L2. ❨G2,L4❩ ⊢ ⬈ L2 → ❨G1,L1,T1❩ ≥  ❨G2,L2,T2❩.
#S #H1S #H2S #G1 #G3 #L1 #L3 #T1 #T3 #H13 #T4 #HT34 #T5 #HT45 #G2 #L4 #T2 #H34 #L2 #HL42
@(fpbs_lpx_trans … HL42) -L2 (**) (* full auto too slow *)
@(fpbs_fqup_trans … H34) -G2 -L4 -T2
/3 width=6 by fpbs_cpxs_trans, fpbs_teqg_trans/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: fpbs_intro_alt *)
lemma fpbs_intro_star (S) (G) (T) (T0) (L) (L0):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1. ❨G1,L1❩ ⊢ T1 ⬈* T →
      ❨G1,L1,T❩ ⬂* ❨G,L,T0❩ → ❨G,L❩ ⊢ ⬈* L0 →
      ∀G2,L2,T2. ❨G,L0,T0❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=8 by cpxs_fqus_lpxs_fpbs, fpbs_strap1, feqg_fpb/ qed.

(* Advanced inversion lemmas *************************************************)

(* Basic_2A1: uses: fpbs_inv_alt *)
lemma fpbs_inv_star (S):
      reflexive … S → symmetric … S → Transitive  … S →
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ →
      ∃∃G,L,L0,T,T0. ❨G1,L1❩ ⊢ T1 ⬈* T & ❨G1,L1,T❩ ⬂* ❨G,L,T0❩ & ❨G,L❩ ⊢ ⬈* L0 & ❨G,L0,T0❩ ≛[S] ❨G2,L2,T2❩.
#S #H1S #H2S #H3S #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
[ /3 width=9 by feqg_refl, ex4_5_intro/
| #G1 #G0 #L1 #L0 #T1 #T0 *
  #L3 #T3 #H13 #HT30 #HL30 #_ *
  #G4 #L4 #L5 #T4 #T5 #HT04 #H45 #HL45 #H52
  lapply (rpx_cpx_conf_sn … HT30 … HL30) -HL30 #HL30
  elim (fquq_cpx_trans … H13 … HT30) -T3 #T3 #HT13 #H30
  elim (rpx_fwd_lpx_reqg S … HL30) -HL30 // #L #HL3 #HL0
  lapply (reqg_cpxs_trans … HT04 … HL0) -HT04 // #HT04
  lapply (cpxs_reqg_conf_sn … HT04 … HL0) -HL0 #HL0
  lapply (lpx_cpxs_trans … HT04 … HL3) -HT04 #HT04
  elim (fquq_cpxs_trans … HT04 … H30) -T0 #T0 #HT30 #H04
  lapply (cpxs_strap2 … HT13 … HT30) -T3 #HT10
  elim (reqg_fqus_trans … H45 … HL0) -L0 // #L0 #T3 #H43 #HT35 #HL04
  lapply (feqg_intro_dx … G4 … HL04 … HT35) -HL04 -HT35 // #H35
  elim (lpx_fqus_trans … H43 … HL3) -L #L #T #HT4 #H3 #HL0
  elim (fquq_cpxs_trans … HT4 … H04) -T4 #T4 #HT04 #H4
  lapply (cpxs_trans … HT10 … HT04) -T0 #HT14
  lapply (fqus_strap2 … H4 … H3) -G0 -L3 -T #H43
  elim (feqg_lpxs_trans … H35 … HL45) -L4 // #L4 #HL04 #H35
  lapply (lpxs_step_sn … HL0 … HL04) -L0 #HL4
  lapply (feqg_trans … H35 … H52) -L5 -T5 // #H32
  /2 width=9 by ex4_5_intro/
]
qed-.
