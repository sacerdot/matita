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

include "basic_2/rt_computation/cpms_lpr.ma".
include "basic_2/rt_computation/cprs_cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Properties concerning sn parallel reduction on local environments ********)

(* Basic_1: uses: pr3_pr2_pr2_t *)
(* Basic_1: includes: pr3_pr0_pr2_t *)
lemma lpr_cpr_trans (h) (G): s_r_transitive … (λL. cpm h G L 0) (λ_. lpr h G).
/3 width=4 by cprs_inv_CTC, lpr_cpm_trans, ltc_inv_CTC/
qed-.

(* Basic_1: uses: pr3_pr2_pr3_t pr3_wcpr0_t *)
lemma lpr_cprs_trans (h) (G): s_rs_transitive … (λL. cpm h G L 0) (λ_. lpr h G).
#h #G @s_r_trans_CTC1 /2 width=3 by lpr_cpr_trans/ (**) (* full auto fails *)
qed-.

lemma cprs_lpr_conf_dx (h) (G):
                       ∀L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡*[h] T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 →
                       ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[h] T & ⦃G, L1⦄ ⊢ T0 ➡*[h] T.
#h #G #L0 #T0 #T1 #H
@(cprs_ind_dx … H) -T1 /2 width=3 by ex2_intro/
#T #T1 #_ #HT1 #IHT0 #L1 #HL01
elim (IHT0 … HL01) #T2 #HT2 #HT02
elim (lpr_cpr_conf_dx … HT1 … HL01) -L0 #T3 #HT3 #HT13
elim (cprs_strip … HT2 … HT3) -T
/3 width=5 by cprs_step_dx, cprs_step_sn, ex2_intro/
qed-.

lemma cprs_lpr_conf_sn (h) (G):
                       ∀L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡*[h] T1 →
                       ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 →
                       ∃∃T. ⦃G, L0⦄ ⊢ T1 ➡*[h] T & ⦃G, L1⦄ ⊢ T0 ➡*[h] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (cprs_lpr_conf_dx … HT01 … HL01) -HT01 #T #HT1 #HT0
/3 width=3 by lpr_cpms_trans, ex2_intro/
qed-.
