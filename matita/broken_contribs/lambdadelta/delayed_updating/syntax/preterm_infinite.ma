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

include "delayed_updating/syntax/preterm.ma".
include "ground/arith/nat_succ_iter.ma".

(* PRETERM ******************************************************************)

(* An infinite preterm ******************************************************)

definition path_As (n:ℕ): ℙ → ℙ ≝
           (λp.𝗔◗p)^n
.

definition path_y (n:ℕ): ℙ ≝
           path_As n (𝗦◗𝗱(⁤𝟏)◗𝐞)
.

definition term_y: 𝕋 ≝
           {r | ∃n. r = path_y n}
.

(* Basic constructions ******************************************************)

lemma path_y_unfold (n):
      (λp.𝗔◗p)^n (𝗦◗𝗱(⁤𝟏)◗𝐞) = path_y n
.
// qed.

lemma path_y_zero:
      (𝗦◗𝗱(⁤𝟏)◗𝐞) = path_y (𝟎).
// qed.

lemma path_y_succ (n):
      (𝗔)◗(path_y n) = path_y (⁤↑n).
#n <path_y_unfold <path_y_unfold
@(niter_succ … (λp.𝗔◗p))
qed.

(* Basic destructions *******************************************************)

lemma eq_inv_append_bi_path_y_sn (q1:ℙ) (q2:ℙ) (n1) (n2):
      (path_y n1)●q1 = (path_y n2)●q2 → n1 = n2.
#q1 #q2 @nat_ind_succ [| #n1 #IH ]
@nat_ind_succ [2,4: #n2 #_ ]
[ <path_y_zero <path_y_succ
  <list_append_assoc <list_append_assoc <list_append_assoc #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| <path_y_succ <path_y_succ
  <list_append_assoc <list_append_assoc #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
  <(IH … H0) -IH -n2 //
| //
| <path_y_zero <path_y_succ
  <list_append_assoc <list_append_assoc <list_append_assoc #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
]
qed-.

(* Main constructions *******************************************************)

theorem preterm_y:
        term_y ϵ 𝐓.
@mk_preterm_posts
[ #p1 #p2 * #n1 #H1 * #n2 #H2 * #q2 #_
  >(list_append_empty_sn … p1) in ⊢ (%→?); #H0 destruct 
  <(eq_inv_append_bi_path_y_sn … H0) -n2 //
| #p #l1 #k2 * #q1 * #n1 #H1 * #q2 * #n2 #H2 
  
  
  
  