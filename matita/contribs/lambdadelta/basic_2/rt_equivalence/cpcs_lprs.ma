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

include "basic_2/rt_computation/lprs_cprs.ma".
include "basic_2/rt_equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Properties with parallel r-computation for full local environments *******)

lemma lpr_cpcs_trans (h) (G): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡[h] L2 →
                              ∀T1,T2. ⦃G,L2⦄ ⊢ T1 ⬌*[h] T2 → ⦃G,L1⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
 /4 width=5 by cprs_div, lpr_cpms_trans/
qed-.

lemma lprs_cpcs_trans (h) (G): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡*[h] L2 →
                               ∀T1,T2. ⦃G,L2⦄ ⊢ T1 ⬌*[h] T2 → ⦃G,L1⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
/4 width=5 by cprs_div, lprs_cpms_trans/
qed-.

lemma lprs_cprs_conf (h) (G): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡*[h] L2 →
                              ∀T1,T2. ⦃G,L1⦄ ⊢ T1 ➡*[h] T2 → ⦃G,L2⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L1 #L2 #HL12 #T1 #T2 #HT12 elim (lprs_cprs_conf_dx … HT12 … HL12) -L1
/2 width=3 by cprs_div/
qed-.

(* Basic_1: was: pc3_wcpr0_t *)
(* Basic_1: note: pc3_wcpr0_t should be renamed *)
(* Note: alternative proof /3 width=5 by lprs_cprs_conf, lpr_lprs/ *)
lemma lpr_cprs_conf (h) (G): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡[h] L2 →
                             ∀T1,T2. ⦃G,L1⦄ ⊢ T1 ➡*[h] T2 → ⦃G,L2⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L1 #L2 #HL12 #T1 #T2 #HT12 elim (cprs_lpr_conf_dx … HT12 … HL12) -L1
/2 width=3 by cprs_div/
qed-.

(* Basic_1: was only: pc3_pr0_pr2_t *)
(* Basic_1: note: pc3_pr0_pr2_t should be renamed *)
lemma lpr_cpr_conf (h) (G): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡[h] L2 →
                            ∀T1,T2. ⦃G,L1⦄ ⊢ T1 ➡[h] T2 → ⦃G,L2⦄ ⊢ T1 ⬌*[h] T2.
/3 width=5 by lpr_cprs_conf, cpm_cpms/ qed-.

(* Advanced inversion lemmas ************************************************)

(* Note: there must be a proof suitable for lfpr *)
lemma cpcs_inv_abst_sn (h) (G) (L): ∀p1,p2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ ⓛ{p1}W1.T1 ⬌*[h] ⓛ{p2}W2.T2 →
                                    ∧∧ ⦃G,L⦄ ⊢ W1 ⬌*[h] W2 & ⦃G,L.ⓛW1⦄ ⊢ T1 ⬌*[h] T2 & p1 = p2.
#h #G #L #p1 #p2 #W1 #W2 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (cpms_inv_abst_sn … H1) -H1 #W0 #T0 #HW10 #HT10 #H destruct
elim (cpms_inv_abst_sn … H2) -H2 #W #T #HW2 #HT2 #H destruct
lapply (lprs_cprs_conf … (L.ⓛW) … HT2) /2 width=1 by lprs_pair/ -HT2 #HT2
lapply (lprs_cpcs_trans … (L.ⓛW1) … HT2) /2 width=1 by lprs_pair/ -HT2 #HT2
/4 width=3 by and3_intro, cprs_div, cpcs_cprs_div, cpcs_sym/
qed-.

lemma cpcs_inv_abst_dx (h) (G) (L): ∀p1,p2,W1,W2,T1,T2. ⦃G,L⦄ ⊢ ⓛ{p1}W1.T1 ⬌*[h] ⓛ{p2}W2.T2 →
                                   ∧∧ ⦃G,L⦄ ⊢ W1 ⬌*[h] W2 & ⦃G,L.ⓛW2⦄ ⊢ T1 ⬌*[h] T2 & p1 = p2.
#h #G #L #p1 #p2 #W1 #W2 #T1 #T2 #HT12 lapply (cpcs_sym … HT12) -HT12
#HT12 elim (cpcs_inv_abst_sn … HT12) -HT12 /3 width=1 by cpcs_sym, and3_intro/
qed-.
