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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/element_r_4.ma".
include "delayed_updating/notation/functions/element_r_3.ma".
include "delayed_updating/notation/functions/element_r_2.ma".

(* PATHS FOR b-REDUCTION ****************************************************)

definition path_beta (p) (b) (q) (n): ℙ ≝
           ((((p◖𝗔)●b)◖𝗟)●q)◖𝗱n.

interpretation
  "for beta (path)"
  'ElementR p b q n = (path_beta p b q n).

definition path_pbeta (p) (b) (q): ℙ ≝
           (((p◖𝗔)●b)◖𝗟)●q.

interpretation
  "left part for beta (path)"
  'ElementR p b q = (path_pbeta p b q).

definition path_qbeta (q) (n): ℙ ≝
           q◖𝗱n.

interpretation
  "right part for beta (path)"
  'ElementR q n = (path_qbeta q n).

(* Basic constructions ******************************************************)

lemma path_beta_unfold_sx (p) (b) (q) (n):
      ((((p◖𝗔)●b)◖𝗟)●q)◖𝗱n = 𝐫❨p,b,q,n❩.
//
qed.

lemma path_beta_unfold_dx (p) (b) (q) (n):
      p●𝗔◗(b●(𝗟◗(q◖𝗱n))) = 𝐫❨p,b,q,n❩.
#p #b #q #n
<list_append_rcons_sn //
qed.

lemma path_beta_unfold_b (p) (b) (q) (n):
      ((p◖𝗔)●b)●(𝗟◗(q◖𝗱n)) = 𝐫❨p,b,q,n❩.
//
qed-.

lemma path_pbeta_unfold_sx (p) (b) (q):
      (((p◖𝗔)●b)◖𝗟)●q = 𝐫❨p,b,q❩.
//
qed.

lemma path_pbeta_unfold_dx (p) (b) (q):
      p●𝗔◗(b●(𝗟◗q)) = 𝐫❨p,b,q❩.
#p #b #q
<list_append_rcons_sn //
qed.

lemma path_pbeta_unfold_b (p) (b) (q):
      ((p◖𝗔)●b)●(𝗟◗q) = 𝐫❨p,b,q❩.
//
qed.

lemma path_qbeta_unfold (q) (n):
      q◖𝗱n = 𝐫❨q,n❩.
//
qed.

(* Advanced constructions ***************************************************)

lemma path_beta_append_p (p1) (p2) (b) (q) (n):
      p1●𝐫❨p2,b,q,n❩ = 𝐫❨p1●p2,b,q,n❩.
//
qed.

lemma path_beta_append_q (p) (b) (q1) (q2) (n):
      (𝐫❨p,b,q1❩)●𝐫❨q2,n❩ = 𝐫❨p,b,q1●q2,n❩.
#p #b #q1 #q2 #n
<path_beta_unfold_dx <path_pbeta_unfold_dx //
qed.

lemma path_pbeta_append_p (p1) (p2) (b) (q):
      p1●𝐫❨p2,b,q❩ = 𝐫❨p1●p2,b,q❩.
//
qed.

lemma path_pbeta_rcons (p) (b) (q) (l):
      (𝐫❨p,b,q❩)◖l = 𝐫❨p,b,q◖l❩.
//
qed.

lemma path_pbeta_append_q (p) (b) (q1) (q2):
      (𝐫❨p,b,q1❩)●q2 = 𝐫❨p,b,q1●q2❩.
//
qed.

lemma path_qbeta_append (q1) (q2) (n):
      q1●𝐫❨q2,n❩ = 𝐫❨q1●q2,n❩.
//
qed.

lemma path_beta_swap_pq (p) (b1) (x) (b2) (q) (n):
      (𝐫❨p,b1,𝐫❨x,b2,q,n❩❩) = 𝐫❨𝐫❨p,b1,x❩,b2,q,n❩.
//
qed.

lemma path_pbeta_qbeta (p) (b) (q) (n):
      (𝐫❨p,b,q❩)◖𝗱n = 𝐫❨p,b,𝐫❨q,n❩❩.
//
qed.

lemma path_pbeta_rcons_d (p) (b) (q) (n):
      (𝐫❨p,b,q,n❩) = 𝐫❨p,b,q❩◖𝗱n.
//
qed.

(* Basic inversions *********************************************************)

lemma path_eq_inv_beta_append_dx_bi_q (x1) (x2) (p) (b) (q1) (q2) (n1) (n2):
      (𝐫❨p,b,q1,n1❩)●x1 = 𝐫❨p,b,q2,n2❩●x2 →
      (𝐫❨q1,n1❩)●x1 = 𝐫❨q2,n2❩●x2.
#x1 #x2 #p #b #q1 #q2 #n1 #n2
<path_beta_unfold_b <list_append_assoc
<path_beta_unfold_b <list_append_assoc in ⊢ ((???%)→?); #H0
lapply (eq_inv_list_append_dx_bi … H0) -H0
<list_append_rcons_dx <list_append_rcons_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_ //
qed-.

lemma path_neq_p_beta (p) (b) (q) (q1) (q2) (n):
      (p◖𝗦)●q1 ⧸= 𝐫❨p,b,q,n❩●q2.
#p #b #q #q1 #q2 #n
<path_beta_unfold_dx <list_append_rcons_sn <list_append_assoc #H0
@(path_neq_prefix … H0) -p -b -q -q1 -q2 -n #H0 destruct
qed-.

lemma path_neq_p_pbeta (p) (b) (q) (q1) (q2):
      (p◖𝗦)●q1 ⧸= 𝐫❨p,b,q❩●q2.
#p #b #q #q1 #q2
<path_pbeta_unfold_dx <list_append_rcons_sn <list_append_assoc #H0
@(path_neq_prefix … H0) -p -b -q -q1 -q2 #H0 destruct
qed-.
