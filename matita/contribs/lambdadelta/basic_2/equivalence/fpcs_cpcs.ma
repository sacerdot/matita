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

include "basic_2/computation/fprs_cprs.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/equivalence/fpcs_fprs.ma".

(* CONTEXT-FREE PARALLEL EQUIVALENCE ON CLOSURES ****************************)

(* Properties on context-sensitive parallel equivalence for terms ***********)

lemma cpcs_fpcs: ∀L,T1,T2. L ⊢ T1 ⬌* T2 → ⦃L, T1⦄ ⬌* ⦃L, T2⦄.
#L #T1 #T2 #H
elim (cpcs_inv_cprs … H) -H /3 width=4 by fprs_div, cprs_fprs/ (**) (* too slow without trace *)
qed.
