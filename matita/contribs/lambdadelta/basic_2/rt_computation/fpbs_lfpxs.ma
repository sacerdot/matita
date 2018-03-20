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

include "basic_2/static/ffdeq_fqus.ma".
include "basic_2/static/ffdeq_ffdeq.ma".
include "basic_2/rt_computation/cpxs_fqus.ma".
include "basic_2/rt_computation/cpxs_ffdeq.ma".
include "basic_2/rt_computation/cpxs_lfpx.ma".
include "basic_2/rt_computation/lfpxs_ffdeq.ma".
include "basic_2/rt_computation/fpbs_cpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with uncounted parallel rt-computation on referred entries ****)

(* Basic_2A1: uses: lpxs_fpbs *)
lemma lfpxs_fpbs: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
#h #o #G #L1 #L2 #T #H @(lfpxs_ind_sn … H) -L2
/3 width=5 by fpbq_lfpx, fpbs_strap1/
qed.

(* Basic_2A1: uses: fpbs_lpxs_trans *)
lemma fpbs_lfpxs_trans: ∀h,o,G1,G2,L1,L,T1,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L, T2⦄ →
                        ∀L2. ⦃G2, L⦄ ⊢ ⬈*[h, T2] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L #T1 #T2 #H1 #L2 #H @(lfpxs_ind_sn … H) -L2
/3 width=5 by fpbs_strap1, fpbq_lfpx/
qed-.

(* Basic_2A1: uses: lpxs_fpbs_trans *)
lemma lfpxs_fpbs_trans: ∀h,o,G1,G2,L,L2,T1,T2. ⦃G1, L, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                        ∀L1. ⦃G1, L1⦄ ⊢ ⬈*[h, T1] L → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L #L2 #T1 #T2 #H1 #L1 #H @(lfpxs_ind_dx … H) -L1
/3 width=5 by fpbs_strap2, fpbq_lfpx/
qed-.

(* Basic_2A1: uses: lpxs_lleq_fpbs *)
lemma lfpxs_ffdeq_fpbs: ∀h,o,G1,L1,L,T1. ⦃G1, L1⦄ ⊢ ⬈*[h, T1] L →
                        ∀G2,L2,T2. ⦃G1, L, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=3 by lfpxs_fpbs_trans, ffdeq_fpbs/ qed.

(* Properties with star-iterated structural successor for closures **********)

(* Basic_2A1: uses: fqus_lpxs_fpbs *)
lemma fqus_lfpxs_fpbs: ∀h,o,G1,G2,L1,L,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L, T2⦄ →
                       ∀L2. ⦃G2, L⦄ ⊢ ⬈*[h, T2] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=3 by fpbs_lfpxs_trans, fqus_fpbs/ qed.

(* Properties with uncounted context-sensitive parallel rt-computation ******)

(* Basic_2A1: uses: cpxs_fqus_lpxs_fpbs *)
lemma cpxs_fqus_lfpxs_fpbs: ∀h,o,G1,L1,T1,T. ⦃G1, L1⦄ ⊢ T1 ⬈*[h] T →
                            ∀G2,L,T2. ⦃G1, L1, T⦄ ⊐* ⦃G2, L, T2⦄ →
                            ∀L2.⦃G2, L⦄ ⊢ ⬈*[h, T2] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by cpxs_fqus_fpbs, fpbs_lfpxs_trans/ qed.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: fpbs_intro_alt *) 
lemma fpbs_intro_star: ∀h,o,G1,L1,T1,T. ⦃G1, L1⦄ ⊢ T1 ⬈*[h] T →
                       ∀G,L,T0. ⦃G1, L1, T⦄ ⊐* ⦃G, L, T0⦄ →
                       ∀L0. ⦃G, L⦄ ⊢ ⬈*[h, T0] L0 →
                       ∀G2,L2,T2. ⦃G, L0, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ .
/3 width=5 by cpxs_fqus_lfpxs_fpbs, fpbs_strap1, fpbq_ffdeq/ qed.

(* Advanced inversion lemmas *************************************************)

(* Basic_2A1: uses: fpbs_inv_alt *) 
lemma fpbs_inv_star: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                     ∃∃G,L,L0,T,T0. ⦃G1, L1⦄ ⊢ T1 ⬈*[h] T & ⦃G1, L1, T⦄ ⊐* ⦃G, L, T0⦄
                                  & ⦃G, L⦄ ⊢ ⬈*[h, T0] L0 & ⦃G, L0, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
[ /2 width=9 by ex4_5_intro/
| #G1 #G0 #L1 #L0 #T1 #T0 * -G0 -L0 -T0
  [ #G0 #L0 #T0 #H10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    elim (fquq_cpxs_trans … HT03 … H10) -T0
    /3 width=9 by fqus_strap2, ex4_5_intro/
  | #T0 #HT10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    /3 width=9 by cpxs_strap2, ex4_5_intro/
  | #L0 #HL10 #_ * #G3 #L3 #L4 #T3 #T4 #HT13 #H34 #HL34 #H42
    lapply (lfpx_cpxs_trans … HT13 … HL10) -HT13 #HT13
    lapply (lfpx_cpxs_conf … HT13 … HL10) -HL10 #HL10
    elim (lfpx_fqus_trans … H34 … HL10) -L0
    /3 width=9 by lfpxs_step_sn, cpxs_trans, ex4_5_intro/
  | #G0 #L0 #T0 #H10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    elim (ffdeq_cpxs_trans … H10 … HT03) -T0 #T0 #HT10 #H03
    elim (ffdeq_fqus_trans … H03 … H34) -G0 -L0 -T3 #G0 #L0 #T3 #H03 #H34
    elim (ffdeq_lfpxs_trans … H34 … HL34) -L3 #L3 #HL03 #H34
    /3 width=13 by ffdeq_trans, ex4_5_intro/
  ]
]
qed-.
