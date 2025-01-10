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

include "ground/notation/functions/oplus_3.ma".
include "ground/lib/list.ma".

(* APPEND FOR LISTS *********************************************************)

rec definition list_append A (l1:list A) (l2:list A) on l1 ≝ match l1 with
[ list_empty       ⇒ l2
| list_lcons hd tl ⇒ hd ⨮ (list_append A tl l2)
].

interpretation
  "append (lists)"
  'OPlus A l1 l2 = (list_append A l1 l2).

(* Basic constructions ******************************************************)

lemma list_append_empty_sn (A):
      ∀l2. l2 = ⓔ ⨁{A} l2.
// qed.

lemma list_append_lcons_sn (A):
      ∀a,l1,l2. a ⨮ l1 ⨁ l2 = (a⨮l1) ⨁{A} l2.
// qed.

(* Helper constructions *****************************************************)

lemma list_append_lcons_empty_sn (A):
      ∀a,l. a ⨮ l = (a⨮ⓔ) ⨁{A} l.
// qed-.

(* Advanced constructions ***************************************************)

lemma list_append_empty_dx (A):
      ∀l1. l1 = l1 ⨁{A} ⓔ.
#A #l1 elim l1 -l1
[ <list_append_empty_sn //
| #hd #tl #IH <list_append_lcons_sn <IH //
]
qed.

lemma list_append_assoc (A):
      associative … (list_append A).
#A #l1 elim l1 -l1
[ <list_append_empty_sn //
| #a1 #l1 #IH *
  [ #l3 <list_append_empty_dx <list_append_empty_sn //
  | #a2 #l2 #l3 <list_append_lcons_sn <list_append_lcons_sn <IH //
  ]
]
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_list_empty_append (A):
      ∀l1,l2. ⓔ = l1⨁{A}l2 →
      ∧∧ ⓔ = l1 & ⓔ = l2.
#A *
[ #l2 /2 width=1 by conj/
| #a1 #l1 #l2 <list_append_lcons_sn #H destruct
]
qed-.

lemma eq_inv_list_append_empty (A):
      ∀l1,l2. l1⨁{A}l2 = ⓔ →
      ∧∧ l1 = ⓔ & l2 = ⓔ.
#A *
[ #l2 /2 width=1 by conj/
| #a1 #l1 #l2 <list_append_lcons_sn #H destruct
]
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_list_lcons_append (A) (l2) (l1) (l) (a):
      a⨮l = l1 ⨁{A} l2 →
      ∨∨ ∧∧ ⓔ = l1 & a⨮l = l2
       | ∃∃ m. a⨮m = l1 & l = m ⨁ l2.
#A #l2 #l1 #l #a cases l1 -l1
[ <list_append_empty_sn #H0 destruct
  /3 width=1 by or_introl, conj/
| #b #m <list_append_lcons_sn #H0 destruct
  /3 width=3 by ex2_intro, or_intror/
]
qed-.

lemma eq_inv_list_append_bi (A) (l1) (l2) (n1) (n2):
      l1 ⨁ l2 = n1 ⨁{A} n2 →
      ∨∨ ∃∃m. l1 = n1 ⨁ m & n2 = m ⨁ l2
       | ∃∃m. l2 = m ⨁ n2 & n1 = l1 ⨁ m.
#A #l1 elim l1 -l1
[ #l2 #n1 #n2 <list_append_empty_sn #H destruct
  /3 width=3 by ex2_intro, or_intror/
| #a1 #l1 #IH #l2 #n1 #n2 #H0
  elim (eq_inv_list_lcons_append ????? H0) -H0 * [| #c ] #H1 #H2 destruct
  [ -IH /3 width=3 by ex2_intro, or_introl/
  | elim (IH … H2) -IH -H2 * #m #H1 #H2 destruct
    /3 width=3 by ex2_intro, or_introl, or_intror/
  ]
]
qed-.

lemma eq_inv_list_append_dx_sn_refl (A) (l1) (l2):
      l1 = l1⨁{A}l2 → ⓔ = l2.
#A #l1 elim l1 -l1 [ // ]
#a1 #l1 #IH #l2 <list_append_lcons_sn #H0 destruct -H0
/2 width=1 by/
qed-.

lemma eq_inv_list_append_sn_bi (A) (l1) (l2) (l):
      l ⨁ l1 = l ⨁{A} l2 → l1 = l2.
#A #l1 #l2 #l #H0
elim (eq_inv_list_append_bi … H0) -H0 * #m #H1 #H2
[ lapply (eq_inv_list_append_dx_sn_refl … H1) -H1
| lapply (eq_inv_list_append_dx_sn_refl … H2) -H2
]
#H0 destruct //
qed-.

(* Advanced eliminations ****************************************************)

lemma list_ind_append_dx (A) (Q:predicate …):
      Q (ⓔ{A}) →
      (∀l1,l2. Q l1 -> Q (l1⨁l2)) →
      ∀l. Q l.
#A #Q #IH1 #IH2 * //
#a #l >(list_append_empty_sn … (a⨮l))
/2 width=1 by/
qed-.

lemma list_ind_append_sn (A) (Q:predicate …):
      Q (ⓔ{A}) →
      (∀l1,l2. Q l2 -> Q (l1⨁l2)) →
      ∀l. Q l.
#A #Q #IH1 #IH2 * //
#a #l >(list_append_empty_dx … (a⨮l))
/2 width=1 by/
qed-.
