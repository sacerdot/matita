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

include "basic_2/relocation/lex_tc.ma".
include "basic_2/rt_computation/cprs_lpr.ma".
include "basic_2/rt_computation/lprs.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Eliminators with r-transition for full local environments ****************)

(* Basic_2A1: was: lprs_ind_dx *)
lemma lprs_ind_sn (h) (G) (L2): ∀R:predicate lenv. R L2 →
                                (∀L1,L. ⦃G, L1⦄ ⊢ ➡[h] L → ⦃G, L⦄ ⊢ ➡*[h] L2 → R L → R L1) →
                                ∀L1. ⦃G, L1⦄ ⊢ ➡*[h] L2 → R L1.
/3 width=7 by lpr_cprs_trans, cpr_refl, lex_CTC_ind_sn/ qed-.

(* Basic_2A1: was: lprs_ind *)
lemma lprs_ind_dx (h) (G) (L1): ∀R:predicate lenv. R L1 →
                                (∀L,L2. ⦃G, L1⦄ ⊢ ➡*[h] L → ⦃G, L⦄ ⊢ ➡[h] L2 → R L → R L2) →
                                ∀L2. ⦃G, L1⦄ ⊢ ➡*[h] L2 → R L2.
/3 width=7 by lpr_cprs_trans, cpr_refl, lex_CTC_ind_dx/ qed-.

(* Properties with unbound rt-transition for full local environments ********)

lemma lpr_lprs (h) (G): ∀L1,L2. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L1⦄ ⊢ ➡*[h] L2.
/3 width=3 by lpr_cprs_trans, lex_CTC_inj/ qed.

(* Basic_2A1: was: lprs_strap2 *)
lemma lprs_step_sn (h) (G): ∀L1,L. ⦃G, L1⦄ ⊢ ➡[h] L →
                            ∀L2.⦃G, L⦄ ⊢ ➡*[h] L2 → ⦃G, L1⦄ ⊢ ➡*[h] L2.
/3 width=3 by lpr_cprs_trans, lex_CTC_step_sn/ qed-.

(* Basic_2A1: was: lpxs_strap1 *)
lemma lprs_step_dx (h) (G): ∀L1,L. ⦃G, L1⦄ ⊢ ➡*[h] L →
                            ∀L2. ⦃G, L⦄ ⊢ ➡[h] L2 → ⦃G, L1⦄ ⊢ ➡*[h] L2.
/3 width=3 by lpr_cprs_trans, lex_CTC_step_dx/ qed-.
