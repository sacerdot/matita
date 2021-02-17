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

include "ground/lib/list.ma".
include "ground/arith/nat_succ.ma".

(* LENGTH FOR LISTS *********************************************************)

rec definition list_length A (l:list A) on l ≝
match l with
[ list_nil      ⇒ 𝟎
| list_cons _ l ⇒ ↑(list_length A l)
].

interpretation
  "length (lists)"
  'card l = (list_length ? l).

(* Basic constructions ******************************************************)

lemma list_length_nil (A:Type[0]): |list_nil A| = 𝟎.
// qed.

lemma list_length_cons (A:Type[0]) (l:list A) (a:A): |a⨮l| = ↑|l|.
// qed.

(* Basic inversions *********************************************************)

lemma list_length_inv_zero_dx (A:Type[0]) (l:list A):
      |l| = 𝟎 → l = Ⓔ.
#A * // #a #l >list_length_cons #H
elim (eq_inv_nsucc_zero … H)
qed-.

lemma list_length_inv_zero_sn (A:Type[0]) (l:list A):
      (𝟎) = |l| → l = Ⓔ.
/2 width=1 by list_length_inv_zero_dx/ qed-.

lemma list_length_inv_succ_dx (A:Type[0]) (l:list A) (x):
      |l| = ↑x →
      ∃∃tl,a. x = |tl| & l = a ⨮ tl.
#A *
[ #x >list_length_nil #H
  elim (eq_inv_zero_nsucc … H)
| #a #l #x >list_length_cons #H
  /3 width=4 by eq_inv_nsucc_bi, ex2_2_intro/
]
qed-.

lemma list_length_inv_succ_sn (A:Type[0]) (l:list A) (x):
      ↑x = |l| →
      ∃∃tl,a. x = |tl| & l = a ⨮ tl.
/2 width=1 by list_length_inv_succ_dx/ qed-.
