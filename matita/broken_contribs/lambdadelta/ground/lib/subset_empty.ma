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

include "ground/notation/functions/circled_collection_f_1.ma".
include "ground/lib/subset.ma".

(* EMPTY SUBSET FOR SUBSETS *************************************************)

definition subset_empty (A): 𝒫❨A❩ ≝
           {p | ⊥}.

interpretation
  "empty (subset)"
  'CircledCollectionF A = (subset_empty A).

(* Basic inversions *********************************************************)

lemma subset_empty_inv_in (A) (p):
      p ϵ{A} Ⓕ → ⊥.
//
qed-.
