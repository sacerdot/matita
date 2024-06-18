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
include "ground/notation/functions/subset_womega_1.ma".

(* WEAKLY FINITE SUBSETS ****************************************************)

definition subsets_wfinite (A): 𝒫❨𝒫❨A❩❩ ≝
           {u | ∃l. u ⊆ 𝐗❨l❩}.

interpretation
  "weakly finite (subset of subsets)"
  'SubsetWOmega A = (subsets_wfinite A).

(* Basic constructions ******************************************************)

lemma subsets_wfinite_in (A) (u) (l):
      u ⊆ 𝐗❨l❩ → u ϵ 𝐖𝛀{A}.
/2 width=2 by ex_intro/
qed.

(* Advanced constructions ***************************************************)

lemma subsets_wfinite_listed (A) (l):
      (𝐗❨l❩) ϵ 𝐖𝛀{A}.
/2 width=2 by subsets_wfinite_in/
qed.

lemma subsets_wfinite_le_trans (A) (u) (v):
      u ⊆ v → v ϵ 𝐖𝛀 → u ϵ 𝐖𝛀{A}.
#A #u #v #Huv * #l #Hv
/3 width=6 by subsets_wfinite_in, subset_le_trans/
qed-.
