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
include "ground/notation/functions/curly_2.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

interpretation
  "singleton (subset)"
  'Curly A a1 = (subset_listed A (list_lcons A a1 (list_empty A))).

(* Basic constructions ******************************************************)

lemma subset_in_single (A) (a1):
      a1 ϵ ❴a1:A❵.
//
qed.

(* Basic inversions *********************************************************)

lemma subset_in_inv_single (A) (a1) (b):
      b ϵ ❴a1:A❵ → b = a1.
#A #a1 #b #H0
elim (subset_in_inv_listed_lcons ???? H0) -H0 //
#H0 elim (subset_nin_inv_empty ?? H0)
qed-.

lemma subset_nin_inv_single (A) (a1) (b):
      b ⧸ϵ ❴a1:A❵ → b ⧸= a1.
/2 width=1 by/
qed-.
