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

include "ground/xoa/ex_1_2.ma".
include "ground/notation/xoa/ex_1_2_typed.ma".
include "ground/subsets/subset_ol_eq.ma".
include "delayed_updating/syntax/path_help.ma".
include "delayed_updating/syntax/prototerm_eq.ma".

(* PROTOTERM ****************************************************************)

(* Constructionswith subset_ol **********************************************)

lemma term_ol_append_bi (u1) (u2) (p):
      u1 ≬ u2 → (p●u1) ≬ (p●u2).
#u1 #u2 #p * #r #H1r #H2r
/3 width=3 by pt_append_in, subset_ol_i/
qed.

lemma term_ol_slice_append_dx (u1) (u2) (p):
      u1 ≬ (p●↑u2) → u1 ≬ ↑(p●u2).
/2 width=5 by subset_ol_eq_repl/
qed.

(* Note: the name refers to the case t = ↑… *)
lemma term_ol_slice_bi (t) (p):
      p ϵ ▵t → ↑p ≬ t.
#t #p * #q #H0
lapply (term_grafted_inv_gen … H0) -H0 #H0
/2 width=3 by subset_ol_i/
qed.

(* Inversions with subset_ol ************************************************)

lemma term_ol_inv_append_bi (u1) (u2) (p):
      (p●u1) ≬ (p●u2) → u1 ≬ u2.
#u1 #u2 #p * #r * #s1 #Hs1 #H1 * #s2 #Hs2 #H2 destruct
lapply (eq_inv_list_append_dx_bi … H2) -p #H0 destruct
/2 width=3 by subset_ol_i/
qed-.

lemma term_ol_inv_slice_append_dx (u1) (u2) (p):
      u1 ≬ ↑(p●u2) → u1 ≬ (p●↑u2).
/3 width=5 by subset_ol_eq_repl, subset_eq_sym/ (**) (* slow symmetry *)
qed-.

lemma term_ol_inv_slice_sx (t) (p):
      ↑p ≬ t → p ϵ ▵t.
#t #p * #r * #q #_ #H0 #Hr destruct
/2 width=2 by term_in_root/
qed-.

lemma term_ol_inv_slice_bi (p1) (p2):
      ↑p1 ≬ ↑p2 →
      ∃∃q1:ℙ,q2:ℙ. p1●q1 = p2●q2.
#p1 #p2 * #r * #q1 #_ #H1 * #q2 #_ #H2 destruct
/2 width=3 by ex1_2_intro/
qed.

(* Destructions with subset_ol **********************************************)

lemma term_ol_des_lcons_bi (t1) (t2) (l1) (l2):
      (l1◗t1) ≬ (l2◗t2) → l1 = l2.
#t1 #t2 #l1 #l2
* #p * #r1 #_ #H1 * #r2 #_ #H2 destruct
elim (eq_inv_list_rcons_bi ????? H2) -H2 #_ //
qed-.

lemma term_ol_des_grafted_bi (t1) (t2) (p):
      (⋔[p]t1) ≬ ⋔[p]t2 → t1 ≬ t2.
#t1 #t2 #p * #r #H1r #H2r
/2 width=3 by subset_ol_i/
qed-.

(* Main destructions with subset_ol *****************************************)

theorem term_ol_des_slice_rcons_bi (p1) (p2) (l1) (l2):
        ↑(p1◖l1) ≬ ↑(p2◖l2) → ↑(p2◖l1) ≬ ↑(p1◖l2) →
        l1 = l2.
#p1 #p2 #l1 #l2 #H1 #H2
elim (term_ol_inv_slice_bi … H1) -H1 #q1 #q2 #H1
elim (term_ol_inv_slice_bi … H2) -H2 #q3 #q4 #H2
elim (eq_inv_list_append_bi … H1) -H1 * #r1 #H1r #H2r
elim (eq_inv_list_append_bi … H2) -H2 * #r2 #H3r #H4r
-q1 -q2 -q3 -q4
[ lapply (path_des_append_help_1 … H2r H4r) -r1 -r2 //
| lapply (path_des_append_help_2 … H2r H3r) -r1 -r2 //
| lapply (path_des_append_help_2 … H1r H4r) -r1 -r2 //
| lapply (path_des_append_help_1 … H1r H3r) -r1 -r2 //
]
qed-.
