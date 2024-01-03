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

(* Constructions with npred *************************************************) 

lemma nplus_pred_sn (m) (n):
      m ϵ 𝐏 → ⫰(m+n) = (⫰m)+n.
#m #n #Hm @(nat_ind_succ … n) -n //
#n #IH
<nplus_succ_dx <nplus_succ_shift <Hm -Hm
<npred_succ //
qed.

lemma nispos_plus_dx (m) (n):
      m ϵ 𝐏 → m+n ϵ 𝐏.
#m #n #Hm
@nispos_intro
>nplus_pred_sn //
qed.

(* Inversions with npred ****************************************************)

(*** plus_inv_S3_sn *)
lemma eq_inv_succ_nplus_sn (o) (m) (n):
      (⁤↑o) = m + n →
      ∨∨ ∧∧ 𝟎 = m & n = (⁤↑o)
       | ∧∧ m ϵ 𝐏 & o = ⫰m + n.
#o #m @(nat_ind_succ … m) -m
[ /3 width=1 by or_introl, conj/
| #m #_ #n <nplus_succ_sn <npred_succ
  /4 width=1 by eq_inv_nsucc_bi, or_intror, conj/
]
qed-.

(*** plus_inv_S3_dx *)
lemma eq_inv_succ_nplus_dx (o) (m) (n):
      (⁤↑o) = m + n →
      ∨∨ ∧∧ 𝟎 = n & m = (⁤↑o)
       | ∧∧ n ϵ 𝐏 & o = m + ⫰n.
#o #m #n @(nat_ind_succ … n) -n
[ /3 width=1 by or_introl, conj/
| #n #_ <nplus_succ_sn <npred_succ
  /4 width=1 by eq_inv_nsucc_bi, or_intror, conj/
]
qed-.
