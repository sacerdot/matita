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

include "ground/lib/bool.ma".

(* CONJUNCTION FOR BOOLEANS *************************************************)

(* Advanced constructions ***************************************************)

lemma commutative_andb:
      commutative … andb.
* * // qed.

lemma andb_false_dx (b):
      ⓕ = (b ∧ ⓕ).
* // qed.

lemma andb_false_sn (b):
      ⓕ = (ⓕ ∧ b).
// qed.

lemma andb_true_dx (b):
      b = (b ∧ ⓣ).
* // qed.

lemma andb_true_sn (b):
      b = (ⓣ ∧ b).
// qed.

(* Advanced inversions ******************************************************)

lemma andb_inv_true_sn (b1) (b2):
      ⓣ = (b1 ∧ b2) → ∧∧ ⓣ = b1 & ⓣ = b2.
* normalize
[ /2 width=1 by conj/
| #b2 #H destruct
]
qed-.
