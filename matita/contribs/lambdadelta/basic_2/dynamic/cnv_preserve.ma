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

(* Advanced inversion lemmas ************************************************)

lemma cnv_inv_appl_SO (a) (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ⓐV.T ![a, h] →
      ∃∃n,p,W0,U0. a = Ⓣ → n = 1 & ⦃G, L⦄ ⊢ V ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                   ⦃G, L⦄ ⊢ V ➡*[1, h] W0 & ⦃G, L⦄ ⊢ T ➡*[n, h] ⓛ{p}W0.U0.
* #h #G #L #V #T #H
elim (cnv_inv_appl … H) -H [ * [| #n ] | #n ] #p #W #U #Ha #HV #HT #HVW #HTU
[ elim (cnv_fwd_cpm_SO … (ⓛ{p}W.U))
  [|*: /2 width=8 by cnv_cpms_trans/ ] #X #HU0
  elim (cpm_inv_abst1 … HU0) #W0 #U0 #HW0 #_ #H0 destruct
  lapply (cpms_step_dx … HVW … HW0) -HVW -HW0 #HVW0
  lapply (cpms_step_dx … HTU … HU0) -HTU -HU0 #HTU0
  /2 width=7 by ex5_4_intro/
| lapply (Ha ?) -Ha [ // ] #Ha
  lapply (le_n_O_to_eq n ?) [ /3 width=1 by le_S_S_to_le/ ] -Ha #H destruct
  /2 width=7 by ex5_4_intro/
| @(ex5_4_intro … HV HT HVW HTU) #H destruct
]
qed-.
