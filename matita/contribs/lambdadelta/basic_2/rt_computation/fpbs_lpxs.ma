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

include "static_2/static/fdeq_fqus.ma".
include "static_2/static/fdeq_fdeq.ma".
include "basic_2/rt_computation/cpxs_fqus.ma".
include "basic_2/rt_computation/cpxs_fdeq.ma".
include "basic_2/rt_computation/lpxs_fdeq.ma".
include "basic_2/rt_computation/fpbs_cpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with unbound rt-computation on full local environments  *******)

lemma lpxs_fpbs: ∀h,G,L1,L2,T. ⦃G,L1⦄ ⊢ ⬈*[h] L2 → ⦃G,L1,T⦄ ≥[h] ⦃G,L2,T⦄.
#h #G #L1 #L2 #T #H @(lpxs_ind_dx … H) -L2
/3 width=5 by fpbq_lpx, fpbs_strap1/
qed.

lemma fpbs_lpxs_trans: ∀h,G1,G2,L1,L,T1,T2. ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L,T2⦄ →
                       ∀L2. ⦃G2,L⦄ ⊢ ⬈*[h] L2 → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
#h #G1 #G2 #L1 #L #T1 #T2 #H1 #L2 #H @(lpxs_ind_dx … H) -L2
/3 width=5 by fpbs_strap1, fpbq_lpx/
qed-.

lemma lpxs_fpbs_trans: ∀h,G1,G2,L,L2,T1,T2. ⦃G1,L,T1⦄ ≥[h] ⦃G2,L2,T2⦄ →
                       ∀L1. ⦃G1,L1⦄ ⊢ ⬈*[h] L → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
#h #G1 #G2 #L #L2 #T1 #T2 #H1 #L1 #H @(lpxs_ind_sn … H) -L1
/3 width=5 by fpbs_strap2, fpbq_lpx/
qed-.

(* Basic_2A1: uses: lpxs_lleq_fpbs *)
lemma lpxs_fdeq_fpbs: ∀h,G1,L1,L,T1. ⦃G1,L1⦄ ⊢ ⬈*[h] L →
                      ∀G2,L2,T2. ⦃G1,L,T1⦄ ≛ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=3 by lpxs_fpbs_trans, fdeq_fpbs/ qed.

lemma fpbs_lpx_trans: ∀h,G1,G2,L1,L,T1,T2. ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L,T2⦄ →
                      ∀L2. ⦃G2,L⦄ ⊢ ⬈[h] L2 → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=3 by fpbs_lpxs_trans, lpx_lpxs/ qed-.

(* Properties with star-iterated structural successor for closures **********)

lemma fqus_lpxs_fpbs: ∀h,G1,G2,L1,L,T1,T2. ⦃G1,L1,T1⦄ ⬂* ⦃G2,L,T2⦄ →
                      ∀L2. ⦃G2,L⦄ ⊢ ⬈*[h] L2 → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=3 by fpbs_lpxs_trans, fqus_fpbs/ qed.

(* Properties with unbound context-sensitive parallel rt-computation ********)

lemma cpxs_fqus_lpxs_fpbs: ∀h,G1,L1,T1,T. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T →
                           ∀G2,L,T2. ⦃G1,L1,T⦄ ⬂* ⦃G2,L,T2⦄ →
                           ∀L2.⦃G2,L⦄ ⊢ ⬈*[h] L2 → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=5 by cpxs_fqus_fpbs, fpbs_lpxs_trans/ qed.

lemma fpbs_cpxs_tdeq_fqup_lpx_trans: ∀h,G1,G3,L1,L3,T1,T3. ⦃G1,L1,T1⦄ ≥ [h] ⦃G3,L3,T3⦄ →
                                     ∀T4. ⦃G3,L3⦄ ⊢ T3 ⬈*[h] T4 → ∀T5. T4 ≛ T5 →
                                     ∀G2,L4,T2. ⦃G3,L3,T5⦄ ⬂+ ⦃G2,L4,T2⦄ →
                                     ∀L2. ⦃G2,L4⦄ ⊢ ⬈[h] L2 → ⦃G1,L1,T1⦄ ≥ [h] ⦃G2,L2,T2⦄.
#h #G1 #G3 #L1 #L3 #T1 #T3 #H13 #T4 #HT34 #T5 #HT45 #G2 #L4 #T2 #H34 #L2 #HL42  
@(fpbs_lpx_trans … HL42) -L2 (**) (* full auto too slow *)
@(fpbs_fqup_trans … H34) -G2 -L4 -T2
/3 width=3 by fpbs_cpxs_trans, fpbs_tdeq_trans/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: fpbs_intro_alt *)
lemma fpbs_intro_star: ∀h,G1,L1,T1,T. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T →
                       ∀G,L,T0. ⦃G1,L1,T⦄ ⬂* ⦃G,L,T0⦄ →
                       ∀L0. ⦃G,L⦄ ⊢ ⬈*[h] L0 →
                       ∀G2,L2,T2. ⦃G,L0,T0⦄ ≛ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄ .
/3 width=5 by cpxs_fqus_lpxs_fpbs, fpbs_strap1, fpbq_fdeq/ qed.

(* Advanced inversion lemmas *************************************************)

(* Basic_2A1: uses: fpbs_inv_alt *)
lemma fpbs_inv_star: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄ →
                     ∃∃G,L,L0,T,T0. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T & ⦃G1,L1,T⦄ ⬂* ⦃G,L,T0⦄
                                  & ⦃G,L⦄ ⊢ ⬈*[h] L0 & ⦃G,L0,T0⦄ ≛ ⦃G2,L2,T2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind_dx … H) -G1 -L1 -T1
[ /2 width=9 by ex4_5_intro/
| #G1 #G0 #L1 #L0 #T1 #T0 * -G0 -L0 -T0
  [ #G0 #L0 #T0 #H10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    elim (fquq_cpxs_trans … HT03 … H10) -T0
    /3 width=9 by fqus_strap2, ex4_5_intro/
  | #T0 #HT10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    /3 width=9 by cpxs_strap2, ex4_5_intro/
  | #L0 #HL10 #_ * #G3 #L3 #L4 #T3 #T4 #HT13 #H34 #HL34 #H42
    lapply (lpx_cpxs_trans … HT13 … HL10) -HT13 #HT13
    elim (lpx_fqus_trans … H34 … HL10) -L0
    /3 width=9 by lpxs_step_sn, cpxs_trans, ex4_5_intro/
  | #G0 #L0 #T0 #H10 #_ * #G3 #L3 #L4 #T3 #T4 #HT03 #H34 #HL34 #H42
    elim (fdeq_cpxs_trans … H10 … HT03) -T0 #T0 #HT10 #H03
    elim (fdeq_fqus_trans … H03 … H34) -G0 -L0 -T3 #G0 #L0 #T3 #H03 #H34
    elim (fdeq_lpxs_trans … H34 … HL34) -L3 #L3 #HL03 #H34
    /3 width=13 by fdeq_trans, ex4_5_intro/
  ]
]
qed-.
