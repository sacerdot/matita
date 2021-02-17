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

rec definition list_eq A (l1,l2:list A) on l1 ≝
match l1 with
[ list_nil        ⇒
  match l2 with
  [ list_nil      ⇒ ⊤
  | list_cons _ _ ⇒ ⊥
  ]
| list_cons a1 l1 ⇒
  match l2 with
  [ list_nil        ⇒ ⊥
  | list_cons a2 l2 ⇒ a1 = a2 ∧ list_eq A l1 l2
  ]
].

interpretation
  "extensional equivalence (lists)"
  'RingEq A l1 l2 = (list_eq A l1 l2).

(* Basic constructions ******************************************************)

lemma list_eq_refl (A): reflexive … (list_eq A).
#A #l elim l -l /2 width=1 by conj/
qed.

(* Main constructions *******************************************************)

theorem eq_list_eq (A,l1,l2): l1 = l2 → l1 ≗{A} l2.
// qed.

(* Main inversions **********************************************************)

theorem list_eq_inv_eq (A,l1,l2): l1 ≗{A} l2 → l1 = l2.
#A #l1 elim l1 -l1 [| #a1 #l1 #IH ] *
[ //
| #a2 #l2 #H elim H
| #H elim H
| #a2 #l2 * #Ha #Hl /3 width=1 by eq_f2/
]
qed-.
