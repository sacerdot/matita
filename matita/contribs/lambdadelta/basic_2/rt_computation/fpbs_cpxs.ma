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

include "basic_2/rt_computation/cpxs.ma".
include "basic_2/rt_computation/fpbs_fqup.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with unbound context-sensitive parallel rt-computation ********)

lemma cpxs_fpbs: ∀h,G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ⬈*[h] T2 → ⦃G,L,T1⦄ ≥[h] ⦃G,L,T2⦄.
#h #G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by fpbq_cpx, fpbs_strap1/
qed.

lemma fpbs_cpxs_trans: ∀h,G1,G,L1,L,T1,T. ⦃G1,L1,T1⦄ ≥[h] ⦃G,L,T⦄ →
                       ∀T2. ⦃G,L⦄ ⊢ T ⬈*[h] T2 → ⦃G1,L1,T1⦄ ≥[h] ⦃G,L,T2⦄.
#h #G1 #G #L1 #L #T1 #T #H1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by fpbs_strap1, fpbq_cpx/
qed-.

lemma cpxs_fpbs_trans: ∀h,G1,G2,L1,L2,T,T2. ⦃G1,L1,T⦄ ≥[h] ⦃G2,L2,T2⦄ →
                       ∀T1. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
#h #G1 #G2 #L1 #L2 #T #T2 #H1 #T1 #H @(cpxs_ind_dx … H) -T1
/3 width=5 by fpbs_strap2, fpbq_cpx/
qed-.

lemma cpxs_tdeq_fpbs_trans: ∀h,G1,L1,T1,T. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T →
                            ∀T0. T ≛ T0 →
                            ∀G2,L2,T2. ⦃G1,L1,T0⦄ ≥[h] ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=3 by cpxs_fpbs_trans, tdeq_fpbs_trans/ qed-.

lemma cpxs_tdeq_fpbs: ∀h,G,L,T1,T. ⦃G,L⦄ ⊢ T1 ⬈*[h] T →
                      ∀T2. T ≛ T2 → ⦃G,L,T1⦄ ≥[h] ⦃G,L,T2⦄.
/4 width=3 by cpxs_fpbs_trans, fdeq_fpbs, tdeq_fdeq/ qed.

(* Properties with star-iterated structural successor for closures **********)

lemma cpxs_fqus_fpbs: ∀h,G1,L1,T1,T. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T →
                      ∀G2,L2,T2. ⦃G1,L1,T⦄ ⊐* ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=5 by fpbs_fqus_trans, cpxs_fpbs/ qed.

(* Properties with plus-iterated structural successor for closures **********)

lemma cpxs_fqup_fpbs: ∀h,G1,L1,T1,T. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T →
                      ∀G2,L2,T2. ⦃G1,L1,T⦄ ⊐+ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=5 by fpbs_fqup_trans, cpxs_fpbs/ qed.
