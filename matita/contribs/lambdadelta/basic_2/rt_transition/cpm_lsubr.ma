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

include "basic_2/rt_transition/cpg_lsubr.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with restricted refinement for local environments *************)

(* Basic_2A1: includes: lsubr_cpr_trans *)
lemma lsubr_cpm_trans: ∀n,h,G. lsub_trans … (cpm n h G) lsubr.
#n #h #G #L1 #T1 #T2 * /3 width=5 by lsubr_cpg_trans, ex2_intro/
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: was by definition: pr2_free *)
(* Basic_2A1: includes: tpr_cpr *)
lemma tpm_cpm: ∀n,h,G,T1,T2. ⦃G, ⋆⦄ ⊢ T1 ➡[n, h] T2 → ∀L. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2.
#n #h #G #T1 #T2 #HT12 #L lapply (lsubr_cpm_trans … HT12 L ?) //
qed.
