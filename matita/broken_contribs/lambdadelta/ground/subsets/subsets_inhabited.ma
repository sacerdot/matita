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

include "ground/subsets/subset_ol.ma".
include "ground/notation/functions/odot_1.ma".

(* INHABITED SUBSETS ********************************************************)

definition subsets_inh (A): 𝒫❨𝒫❨A❩❩ ≝
           {u | u ≬❪A❫ u}.

interpretation
  "inhabited (subset of subsets)"
  'ODot A = (subsets_inh A).

(* Basic constructions ******************************************************)

lemma subsets_inh_in (A) (u) (a):
      a ϵ❪A❫ u → u ϵ ⊙.
/2 width=3 by ex2_intro/
qed.

(* Basic inversions *********************************************************)

lemma subsets_inh_inv_in (A) (u):
      u ϵ ⊙ → ∃a. a ϵ❪A❫ u.
#A #u * #a #Ha #_
/2 width=2 by ex_intro/
qed-.
