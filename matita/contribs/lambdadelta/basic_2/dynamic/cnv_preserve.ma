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
letin o ≝ (sd_O h)
lapply (cnv_fwd_fsb … o … HT) -HT #H
@(fsb_ind_fpbg … H) -G -L -T #G #L #T #_ #IH
@conj [ letin aux ≝ cnv_cpms_conf_lpr_aux | letin aux ≝ cnv_cpm_trans_lpr_aux ]
@(aux … o … G L T) // #G0 #L0 #T0 #H
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

(* Basic_2A1: uses: snv_cprs_lpr *)
lemma cnv_cpms_trans_lpr (a) (h) (G) (L) (T): IH_cnv_cpms_trans_lpr a h G L T.
#a #h #G #L1 #T1 #HT1 #n #T2 #H
@(cpms_ind_dx … H) -n -T2 /3 width=6 by cnv_cpm_trans_lpr/
qed-.
