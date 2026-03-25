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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_or.ma".
include "delayed_updating/syntax/prototerm_clear.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subset_or and subset_le *******************************)

lemma clear_or_ge (t1) (t2):
      (⓪t1) ∪ (⓪t2) ⊆ ⓪(t1 ∪ t2).
#t1 #t2 #p0 * * #p #Hp #H0 destruct
/3 width=1 by in_comp_term_clear, subset_or_in_dx, subset_or_in_sx/
qed.

lemma clear_or_le (t1) (t2):
      (⓪(t1 ∪ t2)) ⊆ (⓪t1) ∪ (⓪t2).
#t1 #t2 #p0 * #p * #Hp #H0 destruct
/3 width=1 by in_comp_term_clear, subset_or_in_dx, subset_or_in_sx/
qed.

(* Constructions with subset_or and subset_eq *******************************)

lemma clear_or_eq (t1) (t2):
      (⓪t1) ∪ (⓪t2) ⇔ ⓪(t1 ∪ t2).
/3 width=1 by conj, clear_or_le, clear_or_ge/
qed.
