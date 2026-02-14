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

include "ground/subsets/subset_and.ma".
include "ground/notation/functions/parenthesis_3.ma".

(* RESTRICTION FOR SUBSETS **************************************************)

definition subset_rest (A) (R) (u): 𝒫❨A❩ ≝
           {a | R} ∩ u.

interpretation
  "restriction (subset)"
  'Parenthesis A R u = (subset_rest A R u).

(* Basic constructions ******************************************************)

lemma subset_rest_unfold (A) (R) (u):
      {a:A | R} ∩ u = ❨R❩u.
//
qed.
