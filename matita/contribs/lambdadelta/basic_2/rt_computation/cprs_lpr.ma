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
include "basic_2/rt_computation/cprs_ctc.ma".

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
