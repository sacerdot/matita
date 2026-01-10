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

include "ground/notation/functions/times2_3.ma".
include "ground/arith/nat_succ_iter.ma".
include "ground/lib/list.ma".

(* PRODUCT FOR LIST ELEMENTS ************************************************)

definition list_times (n) (A) (a): list A ≝
           ((list_lcons A a)^n) (ⓔ).

interpretation
  "product (list elements)"
  'Times2 A a n = (list_times n A a).

(* Basic constructions ******************************************************)

lemma list_times_unfold (A) (a) (n):
      ((list_lcons ? a)^n) (ⓔ) = a×❪A❫n.
// qed.

lemma list_times_zero (A) (a):
      ⓔ = a×❪A❫𝟎.
// qed.

lemma list_times_succ_lcons (A) (a) (n):
      a ⨮ (a×n) = a×❪A❫(⁤↑n).
#A #a #n
<list_times_unfold <list_times_unfold <niter_succ //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_list_empty_times (A) (a) (n):
      ⓔ = a×❪A❫n → 𝟎 = n.
#A #a #n @(nat_ind_succ … n) -n //
#n #_ <list_times_succ_lcons #H0 destruct
qed-.
