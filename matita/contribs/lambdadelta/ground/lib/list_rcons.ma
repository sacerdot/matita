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
include "ground/generated/pull_2.ma". 

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
      ∀l1,l2,a. (l1 ⨁ l2) ⨭ a = l1 ⨁{A} (l2 ⨭ a).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_list_empty_rcons (A):
      ∀l,a. ⓔ = l⨭{A}a → ⊥.
#A #l #a #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
qed-.

lemma eq_inv_list_rcons_empty (A):
      ∀l,a. l⨭{A}a = ⓔ → ⊥.
#A #l #a #H0
elim (eq_inv_list_append_empty … H0) -H0 #_ #H0 destruct
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_list_rcons_bi (A):
      ∀a1,a2,l1,l2. l1 ⨭{A} a1 = l2 ⨭ a2 →
      ∧∧ l1 = l2 & a1 = a2.
#A #a1 #a2 #l1 elim l1 -l1 [| #b1 #l1 #IH ] *
[ <list_append_empty_sn <list_append_empty_sn #H destruct
  /2 width=1 by conj/
| #b2 #l2 <list_append_empty_sn <list_append_lcons_sn #H destruct -H
  elim (eq_inv_list_empty_rcons ??? e0)
| <list_append_lcons_sn <list_append_empty_sn #H destruct -H
  elim (eq_inv_list_empty_rcons ??? (sym_eq … e0))
| #b2 #l2 <list_append_lcons_sn <list_append_lcons_sn #H destruct -H
  elim (IH … e0) -IH -e0 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

(* Advanced eliminations ****************************************************)

lemma list_ind_rcons (A) (Q:predicate …):
      Q (ⓔ{A}) →
      (∀l,a. Q l -> Q (l⨭a)) →
      ∀l. Q l.
#A #Q #IH1 #IH2 #l
@(list_ind_append_dx … l) -l //
@pull_2 #l2 elim l2 -l2 //
#a2 #l2 #IH0 #l1 #IH /3 width=1 by/
qed-.
