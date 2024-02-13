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

include "ground/notation/functions/circled_element_e_1.ma".
include "ground/notation/functions/oplusright_3.ma".
include "ground/lib/relations.ma".

(* LISTS ********************************************************************)

inductive list (A:Type[0]): Type[0] :=
| list_empty: list A
| list_lcons: A → list A → list A
.

interpretation
  "empty (lists)"
  'CircledElementE A = (list_empty A).

interpretation
  "left cons (lists)"
  'OPlusRight A hd tl = (list_lcons A hd tl).

rec definition list_all A (R:predicate A) (l:list A) on l ≝ match l with
[ list_empty       ⇒ ⊤
| list_lcons hd tl ⇒ ∧∧ R hd & list_all A R tl
].

(* Basic inversions *********************************************************)

lemma eq_inv_list_lcons_bi (A) (a1) (a2) (l1) (l2):
      a1⨮l1 = a2⨮{A}l2 →
      ∧∧ a1 = a2 & l1 = l2.
#A #a1 #a2 #l1 #l2 #H0 destruct
/2 width=1 by conj/
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_list_lcons_refl (A) (a) (l):
      a⨮{A}l ⧸= l.
#A #a #l elim l -l
[ #H0 destruct
| #a0 #l #IH #H0
  elim (eq_inv_list_lcons_bi ????? H0) -H0 * -a0
  /2 width=1 by/
]
qed-.

lemma eq_inv_refl_list_lcons (A) (a) (l):
      l ⧸= a⨮{A}l.
/2 width=4 by eq_inv_list_lcons_refl/
qed-.
