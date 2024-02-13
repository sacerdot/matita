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

include "delayed_updating/notation/relations/sqsubseteq_2.ma".
include "delayed_updating/notation/relations/not_sqsubseteq_2.ma".
include "delayed_updating/syntax/prototerm.ma".

(* ROOT ORDER FOR PATH ******************************************************)

definition path_le: relation2 (ℙ) (ℙ) ≝
           λp1,p2. p2 ϵ ↑p1
.

interpretation
  "cleared order (path)"
  'SqSubsetEq p1 p2 = (path_le p1 p2).

interpretation
  "negated cleared order (path)"
  'NotSqSubsetEq p1 p2 = (negation (path_le p1 p2)).

(* Basic constructions ******************************************************)

lemma path_le_mk (p1) (p2) (q):
      p2 = p1●q → p1 ⊑ p2.
/3 width=3 by subset_full_in, ex2_intro/
qed.

lemma path_le_refl:
      reflexive … path_le.
//
qed.

(* Main constructions *******************************************************)

theorem path_le_trans:
        Transitive … path_le.
#p #p1 * #r1 #_ #Hr1 #p2 * #r2 #_ #Hr2
>Hr1 in Hr2; -p1 <list_append_assoc #H0
/2 width=2 by path_le_mk/
qed-.

(* Basic inversions *********************************************************)

lemma path_le_inv_lcons_bi (p1) (p2) (l1) (l2):
      l1◗p1 ⊑ l2◗p2 →
      ∧∧ l1 = l2 & p1 ⊑ p2.
#p1 #p2 #l1 #l2 #H0
elim (term_slice_inv_lcons_bi … H0) -H0
/2 width=1 by conj/
qed-.

lemma path_le_antisym (p1) (p2):
      p1 ⊑ p2 → p2 ⊑ p1 → p1 = p2.
/2 width=1 by term_slice_antisym/
qed-.
