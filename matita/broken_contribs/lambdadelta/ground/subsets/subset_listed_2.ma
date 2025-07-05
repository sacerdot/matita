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

include "ground/subsets/subset_listed.ma".
include "ground/notation/functions/curly_3.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

interpretation
  "pair (subset)"
  'Curly A a1 a2 = (subset_listed A (list_lcons A a2 (list_lcons A a1 (list_empty A)))).

(* Basic constructions ******************************************************)

lemma subset_in_pair_sx (A) (a1) (a2):
      a1 ϵ ❴a1,a2:A❵.
//
qed.

lemma subset_in_pair_dx (A) (a1) (a2):
      a2 ϵ ❴a1,a2:A❵.
//
qed.

(* Basic inversion **********************************************************)

lemma subset_in_inv_pair (A) (a1) (a2) (b):
      b ϵ ❴a1,a2:A❵ → ∨∨ b = a1 | b = a2.
#A #a1 #a2 #b #H0
elim (subset_in_inv_listed_lcons ???? H0) -H0
[ /2 width=1 by or_intror/ ] #H0
elim (subset_in_inv_listed_lcons ???? H0) -H0
[ /2 width=1 by or_introl/ ] #H0
elim (subset_nin_inv_empty ?? H0)
qed-.
