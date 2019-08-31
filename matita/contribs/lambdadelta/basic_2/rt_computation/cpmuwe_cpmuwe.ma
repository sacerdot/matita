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

include "basic_2/rt_computation/cnuw_cnuw.ma".
include "basic_2/rt_computation/cpmuwe.ma".

(* T-UNBOUND WHD EVALUATION FOR T-BOUND RT-TRANSITION ON TERMS **************)

(* Advanced properties ******************************************************)

lemma cpmuwe_abbr_neg (h) (n) (G) (L) (T):
      ∀V,U. ⦃G,L⦄ ⊢ T ➡*[n,h] -ⓓV.U → ⦃G,L⦄ ⊢ T ➡*𝐍𝐖*[h,n] -ⓓV.U.
/3 width=5 by cnuw_abbr_neg, cpmuwe_intro/ qed.

lemma cpmuwe_abst (h) (n) (p) (G) (L) (T):
      ∀W,U. ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W.U → ⦃G,L⦄ ⊢ T ➡*𝐍𝐖*[h,n] ⓛ{p}W.U.
/3 width=5 by cnuw_abst, cpmuwe_intro/ qed.
