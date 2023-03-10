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

rec definition list_length A (l:list A) on l โ match l with
[ list_empty     โ ๐
| list_lcons _ l โ โ(list_length A l)
].

interpretation
  "length (lists)"
  'VerticalBars l = (list_length ? l).

(* Basic constructions ******************************************************)

lemma list_length_empty (A:Type[0]):
      โlist_empty Aโ = ๐.
// qed.

lemma list_length_lcons (A:Type[0]) (l:list A) (a:A):
      โaโจฎlโ = โโlโ.
// qed.

(* Basic inversions *********************************************************)

lemma list_length_inv_zero_dx (A:Type[0]) (l:list A):
      โlโ = ๐ โ l = โ.
#A * // #a #l >list_length_lcons #H
elim (eq_inv_nsucc_zero โฆ H)
qed-.

lemma list_length_inv_zero_sn (A:Type[0]) (l:list A):
      (๐) = โlโ โ l = โ.
/2 width=1 by list_length_inv_zero_dx/ qed-.

lemma list_length_inv_succ_dx (A:Type[0]) (l:list A) (x):
      โlโ = โx โ
      โโtl,a. x = โtlโ & l = a โจฎ tl.
#A *
[ #x >list_length_empty #H
  elim (eq_inv_zero_nsucc โฆ H)
| #a #l #x >list_length_lcons #H
  /3 width=4 by eq_inv_nsucc_bi, ex2_2_intro/
]
qed-.

lemma list_length_inv_succ_sn (A:Type[0]) (l:list A) (x):
      โx = โlโ โ
      โโtl,a. x = โtlโ & l = a โจฎ tl.
/2 width=1 by list_length_inv_succ_dx/ qed-.
