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

include "basic_2/reducibility/cpr_ltpr.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties about context-free parallel reduction on local environments ***)

(* Basic_1: was only: pc3_pr0_pr2_t *)
(* Basic_1: note: pc3_pr0_pr2_t should be renamed *)
lemma ltpr_cpr_conf: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L1 ⊢ T1 ➡ T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #HL12 #T1 #T2 #HT12
elim (cpr_ltpr_conf_eq … HT12 … HL12) -L1 #T #HT1 #HT2
@(cprs_div … T) /2 width=1/ /3 width=1/ (**) (* /4 width=3/ is too long *)
qed.

(* Basic_1: was: pc3_wcpr0_t *)
(* Basic_1: note: pc3_wcpr0_t should be renamed *)
lemma ltpr_cprs_conf: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L1 ⊢ T1 ➡* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #HL12 #T1 #T2 #H @(cprs_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1
@(cpcs_trans … IHT1) -T1 /2 width=3/
qed.

(* Basic_1: was: pc3_wcpr0 *)
lemma ltpr_cpcs_conf: ∀L1,L2. L1 ➡ L2 → ∀T1,T2. L1 ⊢ T1 ⬌* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #HL12 #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H #T #HT1 #HT2
@(cpcs_canc_dx … T) /2 width=3/
qed.
