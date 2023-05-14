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

include "ground/arith/nat_pred_succ.ma".
include "ground/arith/nat_plus.ma".

(* ADDITION FOR NON-NEGATIVE INTEGERS ***************************************)

(* Inversions with npred ****************************************************)

(*** plus_inv_S3_sn *)
lemma eq_inv_succ_nplus_sn (o) (m) (n):
      ↑o ={ℕ} m + n →
      ∨∨ ∧∧ 𝟎 = m & n = ↑o
       | ∧∧ m = ↑⫰m & o = ⫰m + n.
#o #m @(nat_ind_succ … m) -m
[ /3 width=1 by or_introl, conj/
| #m #_ #n <nplus_succ_sn <npred_succ
  /4 width=1 by eq_inv_nsucc_bi, or_intror, conj/
]
qed-.

(*** plus_inv_S3_dx *)
lemma eq_inv_succ_nplus_dx (o) (m) (n):
      ↑o ={ℕ} m + n →
      ∨∨ ∧∧ 𝟎 = n & m = ↑o
       | ∧∧ n = ↑⫰n & o = m + ⫰n.
#o #m #n @(nat_ind_succ … n) -n
[ /3 width=1 by or_introl, conj/
| #n #_ <nplus_succ_sn <npred_succ
  /4 width=1 by eq_inv_nsucc_bi, or_intror, conj/
]
qed-.
