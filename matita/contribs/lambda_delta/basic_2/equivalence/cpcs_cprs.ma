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

include "basic_2/computation/cprs.ma".
include "basic_2/equivalence/cpcs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties about context sensitive computation on terms ******************)

(* Basic_1: was: pc3_pr3_r *)
lemma cpcs_cprs_dx: ∀L,T1,T2. L ⊢ T1 ➡* T2 → L ⊢ T1 ⬌* T2.
#L #T1 #T2 #H @(cprs_ind … H) -T2 /width=1/ /3 width=3/
qed.

lemma cpcs_tpr_dx: ∀L,T1,T2. T1 ➡ T2 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

(* Basic_1: was: pc3_pr3_x *)
lemma cpcs_cprs_sn: ∀L,T1,T2. L ⊢ T2 ➡* T1 → L ⊢ T1 ⬌* T2.
#L #T1 #T2 #H @(cprs_ind_dx … H) -T2 /width=1/ /3 width=3/
qed.

lemma cpcs_tpr_sn: ∀L,T1,T2. T2 ➡ T1 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

lemma cpcs_cprs_strap1: ∀L,T1,T. L ⊢ T1 ⬌* T → ∀T2. L ⊢ T ➡* T2 → L ⊢ T1 ⬌* T2.
#L #T1 #T #HT1 #T2 #H @(cprs_ind … H) -T2 /width=1/ /2 width=3/
qed.

lemma cpcs_cprs_strap2: ∀L,T1,T. L ⊢ T1 ➡* T → ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
#L #T1 #T #H #T2 #HT2 @(cprs_ind_dx … H) -T1 /width=1/ /2 width=3/
qed.

lemma cpcs_cprs_div: ∀L,T1,T. L ⊢ T1 ⬌* T → ∀T2. L ⊢ T2 ➡* T → L ⊢ T1 ⬌* T2.
#L #T1 #T #HT1 #T2 #H @(cprs_ind_dx … H) -T2 /width=1/ /2 width=3/
qed.

(* Basic_1: was: pc3_pr3_conf *)
lemma cpcs_cprs_conf: ∀L,T1,T. L ⊢ T ➡* T1 → ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
#L #T1 #T #H #T2 #HT2 @(cprs_ind … H) -T1 /width=1/ /2 width=3/
qed.

(* Basic_1: was: pc3_pr3_t *)
(* Basic_1: note: pc3_pr3_t should be renamed *)
lemma cprs_div: ∀L,T1,T. L ⊢ T1 ➡* T → ∀T2. L ⊢ T2 ➡* T → L ⊢ T1 ⬌* T2.
#L #T1 #T #HT1 #T2 #H @(cprs_ind_dx … H) -T2 /2 width=1/ /2 width=3/
qed.
