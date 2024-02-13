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

include "ground/notation/functions/curly_2.ma".
include "ground/lib/subset.ma".

(* SINGLETON FOR SUBSETS ****************************************************)

definition subset_singleton (A) (a): 𝒫❨A❩ ≝
           {p | a = p}.

interpretation
  "singleton (subset)"
  'Curly A a = (subset_singleton A a).

(* Basic constructions ******************************************************)

lemma subset_singleton_in (A) (a):
      a ϵ ❴a:A❵.
//
qed.

(* Basic inversions *********************************************************)

lemma subset_singleton_inv_in (A) (a) (p):
      p ϵ ❴a:A❵ → a = p.
//
qed-.
