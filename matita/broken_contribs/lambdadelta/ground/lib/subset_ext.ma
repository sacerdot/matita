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
include "ground/lib/functions.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

definition subset_ext_f1 (A1) (A0) (f:A1→A0): 𝒫❨A1❩ → 𝒫❨A0❩ ≝
           λu1. ❴a0 ❘ ∃∃a1. a1 ϵ u1 & f a1 = a0❵.

definition subset_ext_f1_1 (A11) (A21) (A0) (f1:A11→A0) (f2:A21→A0): 𝒫❨A11❩ → 𝒫❨A21❩ → 𝒫❨A0❩ ≝
           λu11,u21. ❴a0 ❘
           ∨∨ subset_ext_f1 A11 A0 f1 u11 a0
            | subset_ext_f1 A21 A0 f2 u21 a0❵.

definition subset_ext_p1 (A1) (Q:predicate A1): predicate (𝒫❨A1❩) ≝
           λu1. ∀a1. a1 ϵ u1 → Q a1.

(* Basic constructions ******************************************************)

lemma subset_in_ext_f1_dx (A1) (A0) (f) (u1) (a1):
      a1 ϵ u1 → f a1 ϵ subset_ext_f1 A1 A0 f u1.
/2 width=3 by ex2_intro/ qed.

lemma subset_in_ext_f1_1_dx_1 (A11) (A21) (A0) (f1) (f2) (u11) (u21) (a11):
      a11 ϵ u11 → f1 a11 ϵ subset_ext_f1_1 A11 A21 A0 f1 f2 u11 u21.
/3 width=3 by subset_in_ext_f1_dx, or_introl/ qed.

lemma subset_in_ext_f1_1_dx_2 (A11) (A21) (A0) (f1) (f2) (u11) (u21) (a21):
      a21 ϵ u21 → f2 a21 ϵ subset_ext_f1_1 A11 A21 A0 f1 f2 u11 u21.
/3 width=3 by subset_in_ext_f1_dx, or_intror/ qed.

(* Basic inversions *********************************************************)

lemma subset_in_inv_ext_f1_dx (A1) (A0) (f) (u1) (a1):
      injective_2_fwd … (eq …) (eq …) f → 
      f a1 ϵ subset_ext_f1 A1 A0 f u1 → a1 ϵ u1.
#A1 #A0 #f #u1 #a1 #Hf * #a0 #Ha0 #H0
lapply (Hf … H0) -f #H0 destruct //
qed-.

lemma subset_in_inv_ext_p1_dx (A1) (Q) (u1) (a1):
      a1 ϵ u1 → subset_ext_p1 A1 Q u1 → Q a1.
/2 width=1 by/ qed-.
