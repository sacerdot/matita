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
include "delayed_updating/notation/relations/neg_sqsubseteq_2.ma".
include "delayed_updating/syntax/prototerm.ma".

(* ROOT ORDER FOR PATH ******************************************************)

definition path_rle: relation2 (ℙ) (ℙ) ≝
           λp1,p2. p2 ϵ ↑p1
.

interpretation
  "root order (path)"
  'SqSubsetEq p1 p2 = (path_rle p1 p2).

interpretation
  "negated root order (path)"
  'NegSqSubsetEq p1 p2 = (negation (path_rle p1 p2)).

(* Basic constructions ******************************************************)

lemma path_rle_mk (p1) (p2) (q):
      p2 = p1●q → p1 ⊑ p2.
/3 width=3 by subset_full_in, ex2_intro/
qed.

lemma path_rle_refl:
      reflexive … path_rle.
//
qed.

(* Main constructions *******************************************************)

theorem path_rle_trans:
        Transitive … path_rle.
#p #p1 * #r1 #_ #Hr1 #p2 * #r2 #_ #Hr2
>Hr1 in Hr2; -p1 <list_append_assoc #H0
/2 width=2 by path_rle_mk/
qed-.

theorem path_rle_dec (p1) (p2):
        Decidable (p1 ⊑ p2).
/2 width=1 by term_in_slice_dec/
qed-.

(* Basic inversions *********************************************************)

lemma path_rle_inv_lcons_bi (p1) (p2) (l1) (l2):
      l1◗p1 ⊑ l2◗p2 →
      ∧∧ l1 = l2 & p1 ⊑ p2.
#p1 #p2 #l1 #l2 #H0
elim (term_slice_inv_lcons_bi … H0) -H0
/2 width=1 by conj/
qed-.

(* Advanced inversions ******************************************************)

lemma path_rle_inv_in_comp_dx (t) (p1) (p2):
      p1 ϵ t → p2 ⊑ p1 →
      ∃∃q2. q2 ϵ ⋔[p2]t & p2●q2 = p1.
#t #p1 #p2 #Hp1 #Hp
elim (term_in_slice_inv_gen … Hp) -Hp #q2 #H0 destruct
/2 width=3 by ex2_intro/
qed-.

(* Advanced destructions with path_root_le **********************************)

lemma path_rle_in_comp_trans (t) (p1) (p2):
      p1 ⊑ p2 → p2 ϵ t → p1 ϵ ▵t.
#t #p1 #p2 #Hp #Hp2
elim (term_in_slice_inv_gen … Hp) -Hp #q1 #H0 destruct
/2 width=2 by term_in_root/
qed-.

(* Main inversions **********************************************************)

theorem path_rle_antisym (p1) (p2):
        p1 ⊑ p2 → p2 ⊑ p1 → p1 = p2.
/2 width=1 by term_slice_antisym/
qed-.
