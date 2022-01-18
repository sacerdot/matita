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

include "ground/lib/subset.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

definition subset_ext_f1 (A1) (A0) (f:A1→A0): 𝒫❨A1❩ → 𝒫❨A0❩ ≝
           λu1,a0. ∃∃a1. a1 ϵ u1 & f a1 = a0.

definition subset_ext_p1 (A1) (Q:predicate A1): predicate (𝒫❨A1❩) ≝
           λu1. ∀a1. a1 ϵ u1 → Q a1.

(* Basic constructions ******************************************************)

lemma subset_in_ext_f1_dx (A1) (A0) (f) (u1) (a1):
      a1 ϵ u1 → f a1 ϵ subset_ext_f1 A1 A0 f u1.
/2 width=3 by ex2_intro/ qed.

(* Basic inversions *********************************************************)

lemma subset_in_inv_ext_p1_dx (A1) (Q) (u1) (a1):
      a1 ϵ u1 → subset_ext_p1 A1 Q u1 → Q a1.
/2 width=1 by/ qed-.
