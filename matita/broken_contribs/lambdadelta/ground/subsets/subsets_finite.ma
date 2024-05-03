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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_listed.ma".
include "ground/notation/functions/subset_omega_1.ma".

(* FINITE SUBSETS ***********************************************************)

definition subsets_finite (A): 𝒫❨𝒫❨A❩❩ ≝
           {u | ∃l. u ⊆ 𝐗❨l❩}.

interpretation
  "finite (subset of subsets)"
  'SubsetOmega A = (subsets_finite A).

(* Basic constructions ******************************************************)

lemma subsets_finite_in (A) (u) (l):
      u ⊆ 𝐗❨l❩ → u ϵ 𝛀{A}.
/2 width=2 by ex_intro/
qed.

(* Advanced constructions ***************************************************)

lemma subsets_finite_listed (A) (l):
      (𝐗❨l❩) ϵ 𝛀{A}.
/2 width=2 by subsets_finite_in/
qed.

lemma subsets_finite_le_trans (A) (u) (v):
      u ⊆ v → v ϵ 𝛀 → u ϵ 𝛀{A}.
#A #u #v #Huv * #l #Hv
/3 width=6 by subsets_finite_in, subset_le_trans/
qed-.
