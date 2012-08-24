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

include "character/class.ma".

(* CHARACTER CLASSES ********************************************************)

(* Arithmetics of classes P and T *******************************************)

lemma pt_inv_gen: ∀i.
                  (P i → ∃h. i = h * 3 + 1) ∧
                  (T i → ∃∃h,k. i = (h * 3 + 1) * 3 ^ (k + 1)).
#i @(nat_elim1 … i) -i #i #IH
@conj #H
[ inversion H -H
  [ #H destruct /2 width=2/
  | #i0 #j0 #Hi0 #Hj0 #H destruct
    elim (t_pos … Hi0) #i #H destruct
    elim (p_pos … Hj0) #j #H destruct
    elim (IH (i+1) ?) // #_ #H
    elim (H Hi0) -H -Hi0 #hi #ki #H >H -H
    elim (IH (j+1) ?) -IH // #H #_ -i
    elim (H Hj0) -H -Hj0 #hj #H >H -j
    <associative_plus >exp_n_m_plus_1 /2 width=2/
  ]
| @(T_inv_ind … H) -H #i0 #Hi0 #H destruct
  [ elim (p_pos … Hi0) #i #H destruct
    elim (IH (i+1) ?) -IH /2 width=1 by monotonic_le_plus_r/ #H #_
    elim (H Hi0) -H -Hi0 #hi #H >H -i
    @(ex1_2_intro … hi 0) //
  | elim (t_pos … Hi0) #i #H destruct
    elim (IH (i+1) ?) -IH /2 width=1 by monotonic_le_plus_r/ #_ #H
    elim (H Hi0) -H -Hi0 #hi #ki #H >H -i
    >associative_times <exp_n_m_plus_1 /2 width=3/
  ]
]
qed-.

theorem p_inv_gen: ∀i. P i → ∃h. i = h * 3 + 1.
#i #Hi elim (pt_inv_gen i) /2 width=1/
qed-.

theorem t_inv_gen: ∀i. T i → ∃∃h,k. i = (h * 3 + 1) * 3 ^ (k + 1).
#i #Hi elim (pt_inv_gen i) /2 width=1/
qed-.

theorem p_gen: ∀i. P (i * 3 + 1).
#i @(nat_ind_plus … i) -i //
#i #IHi >times_n_plus_1_m >associative_plus /2 width=1/
qed.

theorem t_gen: ∀i,j. T ((i * 3 + 1) * 3 ^ (j + 1)).
#i #j @(nat_ind_plus … j) -j /2 width=1/
#j #IH >exp_n_m_plus_1 <associative_times /2 width=1/
qed.

lemma pt_discr: ∀i. P i → T i → False.
#i #Hp #Ht
elim (p_inv_gen … Hp) -Hp #hp #Hp
elim (t_inv_gen … Ht) -Ht #ht #kt #Ht destruct
>exp_n_m_plus_1 in Ht; <associative_times #H
elim (not_b_divides_nbr … H) -H //
qed-.
