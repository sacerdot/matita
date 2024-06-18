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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed.ma".
include "ground/notation/functions/subset_somega_1.ma".

(* STRONGLY FINITE SUBSETS **************************************************)

definition subsets_sfinite (A): 𝒫❨𝒫❨A❩❩ ≝
           {u | ∃l. u ⇔ 𝐗❨l❩}.

interpretation
  "strongly finite (subset of subsets)"
  'SubsetSOmega A = (subsets_sfinite A).

(* Basic constructions ******************************************************)

lemma subsets_sfinite_in (A) (u) (l):
      u ⇔ 𝐗❨l❩ → u ϵ 𝐒𝛀{A}.
/2 width=2 by ex_intro/
qed.

(* Advanced constructions ***************************************************)

lemma subsets_sfinite_listed (A) (l):
      (𝐗❨l❩) ϵ 𝐒𝛀{A}.
/2 width=2 by subsets_sfinite_in/
qed.

lemma subsets_sfinite_eq_trans (A) (u) (v):
      u ⇔ v → v ϵ 𝐒𝛀 → u ϵ 𝐒𝛀{A}.
#A #u #v #Huv * #l #Hv
/3 width=6 by subsets_sfinite_in, subset_eq_trans/
qed-.
