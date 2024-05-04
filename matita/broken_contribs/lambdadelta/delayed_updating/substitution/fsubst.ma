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
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/square_sw_black_3.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

definition fsubst (u) (v) (t): 𝕋 ≝
           λr.
           ∨∨ ∧∧ t ≬ u & r ϵ v
            | ∧∧ r ϵ t & r ⧸ϵ u
.

interpretation
  "focalized substitution (prototerm)"
  'SquareSWBlack u v t = (fsubst u v t).

(* Basic constructions ******************************************************)

lemma fsubst_in_comp_true (t) (u) (v) (r):
      t ≬ u → r ϵ v → r ϵ ⬕[u←v]t.
/3 width=1 by or_introl, conj/
qed.

lemma fsubst_in_comp_false (t) (u) (v) (r):
      r ϵ t → r ⧸ϵ u → r ϵ ⬕[u←v]t.
/3 width=1 by or_intror, conj/
qed.
