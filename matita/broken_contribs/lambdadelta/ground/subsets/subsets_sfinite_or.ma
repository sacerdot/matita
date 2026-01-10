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

include "ground/subsets/subset_or_eq.ma".
include "ground/subsets/subset_listed_or_eq.ma".
include "ground/subsets/subsets_sfinite.ma".

(* STRONGLY FINITE SUBSETS **************************************************)

(* Constructions with subset_or *********************************************)

lemma subsets_sfinite_or (A) (u1) (u2):
      u1 ϵ 𝐒𝛀 → u2 ϵ 𝐒𝛀 → u1 ∪ u2 ϵ 𝐒𝛀❪A❫.
#A #u1 #u2 * #l1 #Hl1 * #l2 #Hl2
lapply (subset_or_eq_repl … Hl1 … Hl2) -Hl1 -Hl2 #Hl12
lapply (subset_eq_trans … Hl12 … (subset_eq_or_listed_append …)) -Hl12 #Hl12
/2 width=2 by subsets_sfinite_in/
qed.
