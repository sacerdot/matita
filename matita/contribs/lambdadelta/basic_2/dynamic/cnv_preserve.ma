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

include "basic_2/dynamic/cnv_cpms_conf.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Main preservation properties *********************************************)

(* Basic_2A1: uses: snv_preserve *)
lemma cnv_preserve (a) (h): ∀G,L,T. ⦃G,L⦄ ⊢ T ![a,h] →
      ∧∧ IH_cnv_cpms_conf_lpr a h G L T
       & IH_cnv_cpm_trans_lpr a h G L T.
#a #h #G #L #T #HT
lapply (cnv_fwd_fsb … HT) -HT #H
@(fsb_ind_fpbg … H) -G -L -T #G #L #T #_ #IH
@conj [ letin aux ≝ cnv_cpms_conf_lpr_aux | letin aux ≝ cnv_cpm_trans_lpr_aux ]
@(aux … G L T) // #G0 #L0 #T0 #H
elim (IH … H) -IH -H //
qed-.

theorem cnv_cpms_conf_lpr (a) (h) (G) (L) (T): IH_cnv_cpms_conf_lpr a h G L T.
#a #h #G #L #T #HT elim (cnv_preserve … HT) /2 width=1 by/
qed-.

(* Basic_2A1: uses: snv_cpr_lpr *)
theorem cnv_cpm_trans_lpr (a) (h) (G) (L) (T): IH_cnv_cpm_trans_lpr a h G L T.
#a #h #G #L #T #HT elim (cnv_preserve … HT) /2 width=2 by/
qed-.

(* Advanced preservation properties *****************************************)

lemma cnv_cpms_conf (a) (h) (G) (L):
      ∀T0. ⦃G,L⦄ ⊢ T0 ![a,h] →
      ∀n1,T1. ⦃G,L⦄ ⊢ T0 ➡*[n1,h] T1 → ∀n2,T2. ⦃G,L⦄ ⊢ T0 ➡*[n2,h] T2 →
      ∃∃T. ⦃G,L⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G,L⦄ ⊢ T2 ➡*[n1-n2,h] T.
/2 width=8 by cnv_cpms_conf_lpr/ qed-.

(* Basic_2A1: uses: snv_cprs_lpr *)
lemma cnv_cpms_trans_lpr (a) (h) (G) (L) (T): IH_cnv_cpms_trans_lpr a h G L T.
#a #h #G #L1 #T1 #HT1 #n #T2 #H
@(cpms_ind_dx … H) -n -T2 /3 width=6 by cnv_cpm_trans_lpr/
qed-.

lemma cnv_cpm_trans (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
      ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → ⦃G,L⦄ ⊢ T2 ![a,h].
/2 width=6 by cnv_cpm_trans_lpr/ qed-.

(* Note: this is the preservation property *)
lemma cnv_cpms_trans (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
      ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G,L⦄ ⊢ T2 ![a,h].
/2 width=6 by cnv_cpms_trans_lpr/ qed-.

lemma cnv_lpr_trans (a) (h) (G):
      ∀L1,T. ⦃G,L1⦄ ⊢ T ![a,h] → ∀L2. ⦃G,L1⦄ ⊢ ➡[h] L2 → ⦃G,L2⦄ ⊢ T ![a,h].
/2 width=6 by cnv_cpm_trans_lpr/ qed-.

lemma cnv_lprs_trans (a) (h) (G):
      ∀L1,T. ⦃G,L1⦄ ⊢ T ![a,h] → ∀L2. ⦃G,L1⦄ ⊢ ➡*[h] L2 → ⦃G,L2⦄ ⊢ T ![a,h].
#a #h #G #L1 #T #HT #L2 #H
@(lprs_ind_dx … H) -L2 /2 width=3 by cnv_lpr_trans/
qed-.
