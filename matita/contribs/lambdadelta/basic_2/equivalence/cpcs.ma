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

include "basic_2/notation/relations/pconvstar_4.ma".
include "basic_2/conversion/cpc.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

definition cpcs: relation4 genv lenv term term ≝
           λG. LTC … (cpc G).

interpretation "context-sensitive parallel equivalence (term)"
   'PConvStar G L T1 T2 = (cpcs G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpcs_ind: ∀G,L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. ⦃G, L⦄ ⊢ T1 ⬌* T → ⦃G, L⦄ ⊢ T ⬌ T2 → R T → R T2) →
                ∀T2. ⦃G, L⦄ ⊢ T1 ⬌* T2 → R T2.
#G #L #T1 #R #HT1 #IHT1 #T2 #HT12 @(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpcs_ind_dx: ∀G,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃G, L⦄ ⊢ T1 ⬌ T → ⦃G, L⦄ ⊢ T ⬌* T2 → R T → R T1) →
                   ∀T1. ⦃G, L⦄ ⊢ T1 ⬌* T2 → R T1.
#G #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: pc3_refl *)
lemma cpcs_refl: ∀G,L. reflexive … (cpcs G L).
/2 width=1/ qed.

(* Basic_1: was: pc3_s *)
lemma cpcs_sym: ∀G,L. symmetric … (cpcs G L).
#G #L @TC_symmetric // qed.

lemma cpc_cpcs: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌ T2 → ⦃G, L⦄ ⊢ T2 ⬌* T2.
/2 width=1/ qed.

lemma cpcs_strap1: ∀G,L,T1,T,T2. ⦃G, L⦄ ⊢ T1 ⬌* T → ⦃G, L⦄ ⊢ T ⬌ T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
#G #L @step qed.

lemma cpcs_strap2: ∀G,L,T1,T,T2. ⦃G, L⦄ ⊢ T1 ⬌ T → ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
#G #L @TC_strap qed.

(* Basic_1: was: pc3_pr2_r *)
lemma cpr_cpcs_dx: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=1/ qed.

(* Basic_1: was: pc3_pr2_x *)
lemma cpr_cpcs_sn: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T2 ➡ T1 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=1/ qed.

lemma cpcs_cpr_strap1: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬌* T → ∀T2. ⦃G, L⦄ ⊢ T ➡ T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3/ qed.

(* Basic_1: was: pc3_pr2_u *)
lemma cpcs_cpr_strap2: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡ T → ∀T2. ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3/ qed.

lemma cpcs_cpr_div: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬌* T → ∀T2. ⦃G, L⦄ ⊢ T2 ➡ T → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3/ qed.

lemma cpr_div: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡ T → ∀T2. ⦃G, L⦄ ⊢ T2 ➡ T → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3/ qed-.

(* Basic_1: was: pc3_pr2_u2 *)
lemma cpcs_cpr_conf: ∀G,L,T1,T. ⦃G, L⦄ ⊢ T ➡ T1 → ∀T2. ⦃G, L⦄ ⊢ T ⬌* T2 → ⦃G, L⦄ ⊢ T1 ⬌* T2.
/3 width=3/ qed.

(* Basic_1: removed theorems 9:
            clear_pc3_trans pc3_ind_left
            pc3_head_1 pc3_head_2 pc3_head_12 pc3_head_21
            pc3_pr2_fqubst0 pc3_pr2_fqubst0_back pc3_fqubst0
            pc3_gen_abst pc3_gen_abst_shift
*)
(* Basic_1: removed local theorems 6:
            pc3_left_pr3 pc3_left_trans pc3_left_sym pc3_left_pc3 pc3_pc3_left
            pc3_wcpr0_t_aux
*)
