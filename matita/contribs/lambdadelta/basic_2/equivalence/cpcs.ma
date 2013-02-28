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

include "basic_2/conversion/cpc.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

definition cpcs: lenv → relation term ≝
                 λL. TC … (cpc L).

interpretation "context-sensitive parallel equivalence (term)"
   'PConvStar L T1 T2 = (cpcs L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpcs_ind: ∀L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. L ⊢ T1 ⬌* T → L ⊢ T ⬌ T2 → R T → R T2) →
                ∀T2. L ⊢ T1 ⬌* T2 → R T2.
#L #T1 #R #HT1 #IHT1 #T2 #HT12 @(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpcs_ind_dx: ∀L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. L ⊢ T1 ⬌ T → L ⊢ T ⬌* T2 → R T → R T1) →
                   ∀T1. L ⊢ T1 ⬌* T2 → R T1.
#L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: pc3_refl *)
lemma cpcs_refl: ∀L. reflexive … (cpcs L).
/2 width=1/ qed.

(* Basic_1: was: pc3_s *)
lemma cpcs_sym: ∀L. symmetric … (cpcs L).
/3 width=1/ qed.

lemma cpc_cpcs: ∀L,T1,T2. L ⊢ T1 ⬌ T2 → L ⊢ T2 ⬌* T2.
/2 width=1/ qed.

lemma cpcs_strap1: ∀L,T1,T,T2. L ⊢ T1 ⬌* T → L ⊢ T ⬌ T2 → L ⊢ T1 ⬌* T2.
/2 width=3/ qed.

lemma cpcs_strap2: ∀L,T1,T,T2. L ⊢ T1 ⬌ T → L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/2 width=3/ qed.

(* Basic_1: was: pc3_pr2_r *)
lemma cpcs_cpr_dx: ∀L,T1,T2. L ⊢ T1 ➡ T2 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

lemma cpcs_tpr_dx: ∀L,T1,T2. T1 ➡ T2 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

(* Basic_1: was: pc3_pr2_x *)
lemma cpcs_cpr_sn: ∀L,T1,T2. L ⊢ T2 ➡ T1 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

lemma cpcs_tpr_sn: ∀L,T1,T2. T2 ➡ T1 → L ⊢ T1 ⬌* T2.
/3 width=1/ qed.

lemma cpcs_cpr_strap1: ∀L,T1,T. L ⊢ T1 ⬌* T → ∀T2. L ⊢ T ➡ T2 → L ⊢ T1 ⬌* T2.
/3 width=3/ qed.

(* Basic_1: was: pc3_pr2_u *)
lemma cpcs_cpr_strap2: ∀L,T1,T. L ⊢ T1 ➡ T → ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/3 width=3/ qed.

lemma cpcs_cpr_div: ∀L,T1,T. L ⊢ T1 ⬌* T → ∀T2. L ⊢ T2 ➡ T → L ⊢ T1 ⬌* T2.
/3 width=3/ qed.

lemma cpr_div: ∀L,T1,T. L ⊢ T1 ➡ T → ∀T2. L ⊢ T2 ➡ T → L ⊢ T1 ⬌* T2.
/3 width=3/ qed-.

(* Basic_1: was: pc3_pr2_u2 *)
lemma cpcs_cpr_conf: ∀L,T1,T. L ⊢ T ➡ T1 → ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/3 width=3/ qed.

lemma cpcs_tpss_strap1: ∀L,T1,T. L ⊢ T1 ⬌* T → 
                        ∀T2,d,e. L ⊢ T ▶* [d, e] T2 → L ⊢ T1 ⬌* T2.
#L #T1 #T #HT1 #T2 #d #e #HT2
@(cpcs_cpr_strap1 … HT1) -T1 /2 width=3/
qed-.

lemma cpcs_tpss_conf: ∀L,T,T1,d,e. L ⊢ T ▶* [d, e] T1 →
                      ∀T2. L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
#L #T #T1 #d #e #HT1 #T2 #HT2
@(cpcs_cpr_conf … HT2) -T2 /2 width=3/
qed-.

(* Basic_1: removed theorems 9:
            clear_pc3_trans pc3_ind_left
            pc3_head_1 pc3_head_2 pc3_head_12 pc3_head_21
            pc3_pr2_fsubst0 pc3_pr2_fsubst0_back pc3_fsubst0
*)   
(* Basic_1: removed local theorems 6:
            pc3_left_pr3 pc3_left_trans pc3_left_sym pc3_left_pc3 pc3_pc3_left
            pc3_wcpr0_t_aux
*)
