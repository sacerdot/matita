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

(* Basic properties *********************************************************)

(* Basic_1: was: pc3_refl *)
lemma cpcs_refl: ∀L,T. L ⊢ T ⬌* T.
/2 width=1/ qed.

lemma cpcs_strap1: ∀L,T1,T,T2.
                   L ⊢ T1 ⬌* T → L ⊢ T ⬌ T2 → L ⊢ T1 ⬌* T2.
/2 width=3/ qed.

lemma cpcs_strap2: ∀L,T1,T,T2.
                   L ⊢ T1 ⬌ T → L ⊢ T ⬌* T2 → L ⊢ T1 ⬌* T2.
/2 width=3/ qed.

(* Basic_1: removed theorems 1: clear_pc3_trans *)
