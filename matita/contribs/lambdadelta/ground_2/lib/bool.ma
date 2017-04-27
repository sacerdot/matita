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

include "basics/bool.ma".
include "ground_2/lib/relations.ma".
include "ground_2/notation/constructors/no_0.ma".
include "ground_2/notation/constructors/yes_0.ma".

(* BOOLEAN PROPERTIES *******************************************************)

interpretation "boolean false" 'no = false.

interpretation "boolean true" 'yes = true.

(* Basic properties *********************************************************)

lemma commutative_orb: commutative … orb.
* * // qed.

lemma orb_true_dx: ∀b. (b ∨ Ⓣ) = Ⓣ.
* // qed.

lemma orb_true_sn: ∀b. (Ⓣ ∨ b) = Ⓣ.
// qed.

lemma commutative_andb: commutative … andb.
* * // qed.

lemma andb_false_dx: ∀b. (b ∧ Ⓕ) = Ⓕ.
* // qed.

lemma andb_false_sn: ∀b. (Ⓕ ∧ b) = Ⓕ.
// qed.

lemma eq_bool_dec: ∀b1,b2:bool. Decidable (b1 = b2).
* * /2 width=1 by or_introl/
@or_intror #H destruct
qed-.

(* Basic inversion lemmas ***************************************************)

lemma orb_inv_false_dx: ∀b1,b2:bool. (b1 ∨ b2) = Ⓕ → b1 = Ⓕ ∧ b2 = Ⓕ.
* normalize /2 width=1 by conj/ #b2 #H destruct
qed-.

lemma andb_inv_true_dx: ∀b1,b2:bool. (b1 ∧ b2) = Ⓣ → b1 = Ⓣ ∧ b2 = Ⓣ.
* normalize /2 width=1 by conj/ #b2 #H destruct
qed-.
