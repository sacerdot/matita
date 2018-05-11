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

include "ground_2/lib/star.ma".
include "basic_2/notation/relations/pconvstar_5.ma".
include "basic_2/rt_conversion/cpc.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

definition cpcs: sh → relation4 genv lenv term term ≝
           λh,G. CTC … (cpc h G).

interpretation "context-sensitive parallel r-equivalence (term)"
   'PConvStar h G L T1 T2 = (cpcs h G L T1 T2).

(* Basic eliminators ********************************************************)

(* Basic_2A1: was: cpcs_ind_dx *)
lemma cpcs_ind_sn (h): ∀G,L,T2. ∀R:predicate term. R T2 →
                       (∀T1,T. ⦃G, L⦄ ⊢ T1 ⬌[h] T → ⦃G, L⦄ ⊢ T ⬌*[h] T2 → R T → R T1) →
                       ∀T1. ⦃G, L⦄ ⊢ T1 ⬌*[h] T2 → R T1.
normalize /3 width=6 by TC_star_ind_dx/
qed-.

(* Basic_2A1: was: cpcs_ind *)
lemma cpcs_ind_dx (h): ∀G,L,T1. ∀R:predicate term. R T1 →
                       (∀T,T2. ⦃G, L⦄ ⊢ T1 ⬌*[h] T → ⦃G, L⦄ ⊢ T ⬌[h] T2 → R T → R T2) →
                       ∀T2. ⦃G, L⦄ ⊢ T1 ⬌*[h] T2 → R T2.
normalize /3 width=6 by TC_star_ind/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: pc3_refl *)
lemma cpcs_refl (h): ∀G. c_reflexive … (cpcs h G).
/2 width=1 by inj/ qed.

(* Basic_1: was: pc3_s *)
lemma cpcs_sym (h): ∀G,L. symmetric … (cpcs h G L).
#h #G #L @TC_symmetric
/2 width=1 by cpc_sym/
qed-.

lemma cpc_cpcs (h): ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/2 width=1 by inj/ qed.

(* Basic_2A1: was: cpcs_strap2 *)
lemma cpcs_step_sn (h): ∀G,L,T1,T,T2. ⦃G, L⦄ ⊢ T1 ⬌[h] T → ⦃G, L⦄ ⊢ T ⬌*[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
normalize /2 width=3 by TC_strap/
qed-.

(* Basic_2A1: was: cpcs_strap1 *)
lemma cpcs_step_dx (h): ∀G,L,T1,T,T2. ⦃G, L⦄ ⊢ T1 ⬌*[h] T → ⦃G, L⦄ ⊢ T ⬌[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
normalize /2 width=3 by step/
qed-.

(* Basic_1: was: pc3_pr2_r *)
lemma cpr_cpcs_dx (h): ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=1 by cpc_cpcs, or_introl/ qed.

(* Basic_1: was: pc3_pr2_x *)
lemma cpr_cpcs_sn (h): ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T2 ➡[h] T1 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=1 by cpc_cpcs, or_intror/ qed.

(* Basic_1: was: pc3_pr2_u *)
(* Basic_2A1: was: cpcs_cpr_strap2 *)
lemma cpcs_cpr_step_sn (h): ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡[h] T → ∀T2. ⦃G, L⦄ ⊢ T ⬌*[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpcs_step_sn, or_introl/ qed-.

(* Basic_2A1: was: cpcs_cpr_strap1 *)
lemma cpcs_cpr_step_dx (h): ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬌*[h] T → ∀T2. ⦃G, L⦄ ⊢ T ➡[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpcs_step_dx, or_introl/ qed-.

lemma cpcs_cpr_div (h): ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ⬌*[h] T → ∀T2. ⦃G, L⦄ ⊢ T2 ➡[h] T → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpcs_step_dx, or_intror/ qed-.

lemma cpr_div (h): ∀G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡[h] T → ∀T2. ⦃G, L⦄ ⊢ T2 ➡[h] T → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpr_cpcs_dx, cpcs_step_dx, or_intror/ qed-.

(* Basic_1: was: pc3_pr2_u2 *)
lemma cpcs_cpr_conf (h): ∀G,L,T1,T. ⦃G, L⦄ ⊢ T ➡[h] T1 → ∀T2. ⦃G, L⦄ ⊢ T ⬌*[h] T2 → ⦃G, L⦄ ⊢ T1 ⬌*[h] T2.
/3 width=3 by cpcs_step_sn, or_intror/ qed-.

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
