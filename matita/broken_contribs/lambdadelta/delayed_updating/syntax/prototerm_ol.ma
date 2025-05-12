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

include "ground/subsets/subset_ol_eq.ma".
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

(* Note: the name refers to the case t = ↑… *)
lemma term_ol_inv_slice_bi (t) (p):
      ↑p ≬ t → p ϵ ▵t.
#t #p * #r * #q #_ #H0 #Hr destruct
/2 width=2 by term_in_root/
qed-.

(* Destructions with subset_ol **********************************************)

lemma term_ol_des_lcons_bi (t1) (t2) (l1) (l2):
      (l1◗t1) ≬ (l2◗t2) → l1 = l2.
#t1 #t2 #l1 #l2
* #p * #r1 #_ #H1 * #r2 #_ #H2 destruct
elim (eq_inv_list_rcons_bi ????? H2) -H2 #_ //
qed-.
