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
include "basic_2/equivalence/lsubss.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED STATIC TYPE ASSIGNMENT *******)

(* Properties on context-sensitive parallel equivalence for terms ***********)

lemma lsubss_cpcs_trans: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                         ∀T1,T2. L2 ⊢ T1 ⬌* T2 → L1 ⊢ T1 ⬌* T2.
/3 width=5 by lsubss_fwd_lsubr2, cpcs_lsubr_trans/
qed-.
