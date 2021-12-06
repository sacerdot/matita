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

include "ground/notation/functions/oplusleft_3.ma".
include "ground/lib/list_append.ma".

(* RIGHT CONS FOR LISTS *****************************************************)

interpretation
  "right cons (lists)"
  'OPlusLeft A hd tl = (list_append A hd (list_lcons A tl (list_empty A))).

(* Basic constructions ******************************************************)

lemma list_cons_comm (A):
      ∀a. a ⨮ ⓔ = ⓔ ⨭{A} a.
// qed.

lemma list_cons_shift (A):
      ∀a1,l,a2. a1 ⨮{A} l ⨭ a2 = (a1 ⨮ l) ⨭ a2.
// qed.

(* Advanced constructions ***************************************************)

(* Note: this is list_append_lcons_dx *)
lemma list_append_rcons_sn (A):
      ∀l1,l2,a. l1 ⨁ (a ⨮ l2) = (l1 ⨭ a) ⨁{A} l2.
// qed.

lemma list_append_rcons_dx (A):
      ∀l1,l2,a. l1 ⨁ l2 ⨭ a = l1 ⨁{A} (l2 ⨭ a).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_list_empty_rcons (A):
      ∀l,a. ⓔ = l⨭{A}a → ⊥.
#A #l #a #H
elim (eq_inv_list_empty_append … H) -H #_ #H destruct
qed-.
