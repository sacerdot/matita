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

(* DISJUNCTION FOR BOOLEANS *************************************************)

(* Advanced constructions ***************************************************)

lemma commutative_orb:
      commutative … orb.
* * // qed.

lemma orb_true_dx (b):
      (b ∨ ⓣ) = ⓣ.
* // qed.

lemma orb_true_sn (b):
      (ⓣ ∨ b) = ⓣ.
// qed.

(* Advanced inversions ******************************************************)

lemma orb_inv_false_dx (b1) (b2):
      (b1 ∨ b2) = ⓕ → ∧∧ b1 = ⓕ & b2 = ⓕ.
* normalize /2 width=1 by conj/ #b2 #H destruct
qed-.
