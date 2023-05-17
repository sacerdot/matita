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

include "ground/notation/functions/verticalbars_1.ma". 
include "ground/lib/list.ma".
include "ground/arith/nat_succ.ma".

(* LENGTH FOR LISTS *********************************************************)

rec definition list_length A (l:list A) on l : ℕ ≝ match l with
[ list_empty     ⇒ 𝟎
| list_lcons _ l ⇒ (↑(list_length A l):ℕ)
].

interpretation
  "length (lists)"
  'VerticalBars l = (list_length ? l).

(* Basic constructions ******************************************************)

lemma list_length_empty (A:Type[0]):
      ❘list_empty A❘ = 𝟎.
// qed.

lemma list_length_lcons (A:Type[0]) (l:list A) (a:A):
      ❘a⨮l❘ = ↑❘l❘.
// qed.

(* Basic inversions *********************************************************)

lemma list_length_inv_zero_dx (A:Type[0]) (l:list A):
      ❘l❘ = 𝟎 → l = ⓔ.
#A * // #a #l >list_length_lcons #H
elim (eq_inv_npos_zero … H)
qed-.

lemma list_length_inv_zero_sn (A:Type[0]) (l:list A):
      (𝟎) = ❘l❘ → l = ⓔ.
/2 width=1 by list_length_inv_zero_dx/ qed-.

lemma list_length_inv_succ_dx (A:Type[0]) (l:list A) (x):
      ❘l❘ = ↑x →
      ∃∃tl,a. x = ❘tl❘ & l = a ⨮ tl.
#A *
[ #x >list_length_empty #H
  elim (eq_inv_zero_npos … H)
| #a #l #x >list_length_lcons #H
  /3 width=4 by eq_inv_nsucc_bi, ex2_2_intro/
]
qed-.

lemma list_length_inv_succ_sn (A:Type[0]) (l:list A) (x):
      ↑x ={ℕ} ❘l❘ →
      ∃∃tl,a. x = ❘tl❘ & l = a ⨮ tl.
/2 width=1 by list_length_inv_succ_dx/ qed-.
