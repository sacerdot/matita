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
include "basic_2/equivalence/lsubse.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR CONTEXT-SENSITIVE PARALLEL EQUIVALENCE **)

(* Properties on context-sensitive parallel equivalence for terms ***********)

lemma lsubse_cpcs_trans: ∀h,g,L1,L2. h ⊢ L1 ⊢•⊑[g] L2 →
                         ∀T1,T2. L2 ⊢ T1 ⬌* T2 → L1 ⊢ T1 ⬌* T2.
/3 width=5 by lsubse_fwd_lsubs2, cpcs_lsubs_trans/
qed-.
