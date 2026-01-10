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

include "ground/subsets/subset_listed_or_le.ma".
include "ground/subsets/subsets_wfinite.ma".

(* WEAKLY FINITE SUBSETS ****************************************************)

(* Constructions with subset_or *********************************************)

lemma subsets_wfinite_or (A) (u1) (u2):
      u1 ϵ 𝐖𝛀 → u2 ϵ 𝐖𝛀 → u1 ∪ u2 ϵ 𝐖𝛀❪A❫.
#A #u1 #u2 * #l1 #Hl1 * #l2 #Hl2
/4 width=7 by subset_le_or_listed_append, subsets_wfinite_in, subset_or_le_repl/
qed.
