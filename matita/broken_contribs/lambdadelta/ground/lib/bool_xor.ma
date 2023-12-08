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

include "ground/notation/functions/xor_2.ma".
include "ground/lib/bool.ma".

(* EXCLUSIVE DISJUNCTION FOR BOOLEANS ***************************************)

interpretation
  "exclusive disjunction (booleans)"
  'Xor b1 b2 = (xorb b1 b2).

(* Advanced constructions ***************************************************)

lemma commutative_xorb:
      commutative … xorb.
* * // qed.

lemma xorb_false_dx (b):
      b = b ⊻ ⓕ.
* // qed.

lemma xorb_false_sn (b):
      b = ⓕ ⊻ b.
// qed.

lemma xorb_true_bi:
      ⓕ = ⓣ ⊻ ⓣ.
// qed.
