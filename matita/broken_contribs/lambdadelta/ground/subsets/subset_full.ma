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

include "ground/subsets/subset.ma".
include "ground/notation/functions/circled_collection_t_1.ma".

(* FULL SUBSET FOR SUBSETS **************************************************)

definition subset_full (A): 𝒫❨A❩ ≝
           {p | ⊤}.

interpretation
  "full (subset)"
  'CircledCollectionT A = (subset_full A).

(* Basic constructions ******************************************************)

lemma subset_full_in (A) (p):
      p ϵ{A} Ⓣ.
//
qed.
