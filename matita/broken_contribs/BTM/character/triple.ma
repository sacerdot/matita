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

include "character/class_pt.ma".

(* TRIPLES OF CHARACTER CLASSES *********************************************)

lemma not_p_pS: ∀i. P i → P (i + 1) → False.
#i #Hi #HSi
elim (p_inv_gen … Hi) -Hi #hi #Hi
elim (p_inv_gen … HSi) -HSi #hSi #HSi destruct
lapply (injective_plus_l … HSi) -HSi #H
elim (not_b_divides_nbr … H) -H //
qed-.

lemma not_p_pSS: ∀i. P i → P (i + 2) → False.
#i #Hi #HSi
elim (p_inv_gen … Hi) -Hi #hi #Hi
elim (p_inv_gen … HSi) -HSi #hSi #HSi destruct
>plus_plus_comm_23 in HSi; #H
lapply (injective_plus_l … H) -H #H
elim (not_b_divides_nbr … H) -H //
qed-.

lemma not_p_tS: ∀i. P i → T (i + 1) → False.
#i #Hp #Ht
elim (p_inv_gen … Hp) -Hp #hp #Hp
elim (t_inv_gen … Ht) -Ht #ht #kt #Ht destruct
>exp_n_m_plus_1 in Ht; <associative_times >associative_plus #H
elim (not_b_divides_nbr … H) -H //
qed-.
