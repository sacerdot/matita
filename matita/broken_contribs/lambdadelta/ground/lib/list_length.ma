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

include "ground/notation/functions/verticalbars_2.ma".
include "ground/arith/nat_succ.ma".
include "ground/lib/list.ma".

(* LENGTH FOR LISTS *********************************************************)

rec definition list_length A (l:list A) on l : ℕ ≝ match l with
[ list_empty     ⇒ 𝟎
| list_lcons _ l ⇒ (⁤↑(list_length A l):ℕ)
].

interpretation
  "length (lists)"
  'VerticalBars A l = (list_length A l).

(* Basic constructions ******************************************************)

lemma list_length_empty (A):
      (𝟎) = ❘ⓔ❪A❫❘.
// qed.

lemma list_length_lcons (A) (l) (a):
      (⁤↑❘l❘) =❪ℕ❫ ❘a⨮❪A❫l❘.
// qed.

(* Basic inversions *********************************************************)

lemma list_length_inv_zero_dx (A) (l):
      ❘l❘ = 𝟎 → ⓔ❪A❫ = l.
#A * // #a #l <list_length_lcons #H
elim (eq_inv_npos_zero … H)
qed-.

lemma list_length_inv_zero_sx (A) (l):
      (𝟎) = ❘l❘ → ⓔ❪A❫ = l.
/2 width=1 by list_length_inv_zero_dx/ qed-.

lemma list_length_inv_succ_dx (A) (l) (x):
      ❘l❘❪A❫ = (⁤↑x) →
      ∃∃tl,a. ❘tl❘ = x & a⨮tl = l.
#A *
[ #x <list_length_empty #H
  elim (eq_inv_zero_npos … H)
| #a #l #x <list_length_lcons #H
  /3 width=4 by eq_inv_nsucc_bi, ex2_2_intro/
]
qed-.

lemma list_length_inv_succ_sx (A) (l) (x):
      (⁤↑x) =❪ℕ❫ ❘l❘❪A❫ →
      ∃∃tl,a. ❘tl❘ = x & a⨮tl = l.
/2 width=1 by list_length_inv_succ_dx/ qed-.
