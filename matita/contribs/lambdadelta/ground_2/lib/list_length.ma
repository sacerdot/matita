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

include "ground_2/lib/arith.ma".
include "ground_2/lib/list.ma".

(* LENGTH OF A LIST *********************************************************)

rec definition length A (l:list A) on l ≝ match l with
[ nil      ⇒ 0
| cons _ l ⇒ ↑(length A l)
].

interpretation "length (list)"
   'card l = (length ? l).

(* Basic properties *********************************************************)

lemma length_nil (A:Type[0]): |nil A| = 0.
// qed.

lemma length_cons (A:Type[0]) (l:list A) (a:A): |a⨮l| = ↑|l|.
// qed.

(* Basic inversion lemmas ***************************************************)

lemma length_inv_zero_dx (A:Type[0]) (l:list A): |l| = 0 → l = Ⓔ.
#A * // #a #l >length_cons #H destruct
qed-.

lemma length_inv_zero_sn (A:Type[0]) (l:list A): 0 = |l| → l = Ⓔ.
/2 width=1 by length_inv_zero_dx/ qed-.

lemma length_inv_succ_dx (A:Type[0]) (l:list A) (x): |l| = ↑x →
                         ∃∃tl,a. x = |tl| & l = a ⨮ tl.
#A * /2 width=4 by ex2_2_intro/
>length_nil #x #H destruct
qed-.

lemma length_inv_succ_sn (A:Type[0]) (l:list A) (x): ↑x = |l| →
                         ∃∃tl,a. x = |tl| & l = a ⨮ tl.
/2 width=1 by length_inv_succ_dx/ qed.
