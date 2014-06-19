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
include "ground_2/lib/star.ma".
include "ground_2/notation/constructors/no_0.ma".
include "ground_2/notation/constructors/yes_0.ma".

(* BOOLEAN PROPERTIES *******************************************************)

interpretation "boolean false" 'no = false.

interpretation "boolean true" 'yes = true.

(* Basic properties *********************************************************)

lemma orb_false_r: ∀b1,b2:bool. (b1 ∨ b2) = false → b1 = false ∧ b2 = false.
* normalize /2 width=1 by conj/ #b2 #H destruct
qed-.

lemma commutative_orb: commutative … orb.
* * // qed.

lemma eq_bool_dec: ∀b1,b2:bool. Decidable (b1 = b2).
* * /2 width=1 by or_introl/
@or_intror #H destruct
qed-.
