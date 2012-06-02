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

include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/lsubn.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE TYPE ASSIGNMENT ******************)

(* Properties on context-sensitive parallel equivalence for terms ***********)

(* Basic_1: was: csubt_pr2 *)
lemma cpr_lsubn_trans: ∀h,L1,L2. h ⊢ L1 :⊑ L2 →
                       ∀T1,T2. L2 ⊢ T1 ➡ T2 → L1 ⊢ T1 ➡ T2.
/3 width=4 by lsubn_fwd_lsubs2, cpr_lsubs_trans/ qed.

lemma cprs_lsubn_trans: ∀h,L1,L2. h ⊢ L1 :⊑ L2 →
                        ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
/3 width=4 by lsubn_fwd_lsubs2, cprs_lsubs_trans/ qed.

(* Basic_1: was: csubt_pc3 *)
lemma cpcs_lsubn_trans: ∀h,L1,L2. h ⊢ L1 :⊑ L2 →
                        ∀T1,T2. L2 ⊢ T1 ⬌* T2 → L1 ⊢ T1 ⬌* T2.
/3 width=4 by lsubn_fwd_lsubs2, cpcs_lsubs_trans/ qed.
