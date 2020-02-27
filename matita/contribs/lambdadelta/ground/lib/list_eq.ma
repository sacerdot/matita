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

include "ground/notation/relations/ringeq_3.ma".
include "ground/lib/list.ma".

(* EXTENSIONAL EQUIVALENCE OF LISTS *****************************************)

rec definition eq_list A (l1,l2:list A) on l1 ≝
match l1 with
[ nil        ⇒
  match l2 with
  [ nil      ⇒ ⊤
  | cons _ _ ⇒ ⊥
  ]
| cons a1 l1 ⇒
  match l2 with
  [ nil        ⇒ ⊥
  | cons a2 l2 ⇒ a1 = a2 ∧ eq_list A l1 l2
  ]
].

interpretation "extensional equivalence (list)"
   'RingEq A l1 l2 = (eq_list A l1 l2).

(* Basic properties *********************************************************)

lemma eq_list_refl (A): reflexive … (eq_list A).
#A #l elim l -l /2 width=1 by conj/
qed.

(* Main properties **********************************************************)

theorem eq_eq_list (A,l1,l2): l1 = l2 → l1 ≗{A} l2.
// qed.

(* Main inversion propertiess ***********************************************)

theorem eq_list_inv_eq (A,l1,l2): l1 ≗{A} l2 → l1 = l2.
#A #l1 elim l1 -l1 [| #a1 #l1 #IH ] *
[ //
| #a2 #l2 #H elim H
| #H elim H
| #a2 #l2 * #Ha #Hl /3 width=1 by eq_f2/
]
qed-.
