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
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on context-sensitive parallel equivalence for terms ***********)

lemma lsubsv_cpcs_trans: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 →
                         ∀T1,T2. ⦃G, L2⦄ ⊢ T1 ⬌* T2 → ⦃G, L1⦄ ⊢ T1 ⬌* T2.
/3 width=6 by lsubsv_fwd_lsubr, lsubr_cpcs_trans/
qed-.
