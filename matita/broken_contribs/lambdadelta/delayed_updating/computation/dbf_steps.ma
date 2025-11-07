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

include "delayed_updating/reduction/dbf_step_eq.ma".
include "delayed_updating/computation/frs.ma".
include "delayed_updating/notation/relations/black_rightarrow_star_dbf_3.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

interpretation
  "balanced focused computation with delayed updating (prototerm)"
  'BlackRightArrowStarDBF t1 rs t2 = (frs dbfs rs t1 t2).

(* Basic inversions *********************************************************)

lemma dbfss_inv_step (t1) (t2) (r):
      t1 ➡*𝐝𝐛𝐟[r◗𝐞] t2 → t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #t2 #r
@frs_inv_step -t1 -t2 -r #t #t1 #t2 #r
[ /3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
| /2 width=3 by dbfs_eq_trans/
]
qed-.

(* Advanced inversions ******************************************************)

lemma dbfss_inv_step_sx (t1) (t2) (ss) (r):
      t1 ➡*𝐝𝐛𝐟[r◗ss] t2 →
      ∃∃t. t1 ➡𝐝𝐛𝐟[r] t & t ➡*𝐝𝐛𝐟[ss] t2.
#t1 #t2 #ss #r
@frs_inv_step_sx -t1 -t2 -ss -r #t #t1 #t2 #r
[ /3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
| /2 width=3 by dbfs_eq_trans/
]
qed-.

lemma dbfss_inv_step_dx (t1) (t2) (rs) (s):
      t1 ➡*𝐝𝐛𝐟[rs◖s] t2 →
      ∃∃t. t1 ➡*𝐝𝐛𝐟[rs] t & t ➡𝐝𝐛𝐟[s] t2.
#t1 #t2 #rs #s
@frs_inv_step_dx -t1 -t2 -rs -s #t #t1 #t2 #r
[ /3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
| /2 width=3 by dbfs_eq_trans/
]
qed-.

(* Advanced eliminators *****************************************************)

lemma dbfss_ind_sx (t2) (Q:relation2 …):
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      Q t2 (𝐞) →
      (∀t,t1,ss,r. t1 ➡𝐝𝐛𝐟[r] t → t ➡*𝐝𝐛𝐟[ss] t2 → Q t ss → Q t1 (r◗ss)) →
      ∀t1,rs. t1 ➡*𝐝𝐛𝐟[rs] t2 → Q t1 rs.
#t2 #Q
@frs_ind_sx -Q -t2 #t #t1 #t2 #r
[ /3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
| /2 width=3 by dbfs_eq_trans/
]
qed-.

lemma dbfss_ind_dx (t1) (Q:relation2 …):
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      Q t1 (𝐞) →
      (∀t,t2,rs,s. t1 ➡*𝐝𝐛𝐟[rs] t → t ➡𝐝𝐛𝐟[s] t2 → Q t rs → Q t2 (rs◖s)) →
      ∀t2,rs. t1 ➡*𝐝𝐛𝐟[rs] t2 → Q t2 rs.
#t1 #Q
@frs_ind_dx -Q -t1 #t #t1 #t2 #r
[ /3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
| /2 width=3 by dbfs_eq_trans/
]
qed-.

(* Constructions with subset_eq *********************************************)

lemma dbfss_eq_trans (t):
      ∀t1,rs. t1 ➡*𝐝𝐛𝐟[rs] t →
      ∀t2. t ⇔ t2 → t1 ➡*𝐝𝐛𝐟[rs] t2.
#t #t1 #rs #H0
@(dbfss_ind_dx … H0) -t -rs
[ #t #t0 #rs #Ht0 #IH #t2 #Ht2
  /3 width=3 by subset_eq_canc_sx/
| /2 width=1 by frs_refl/
| #u1 #u2 #ss #s #Htu #Hu #_ #t2 #Hut
  /3 width=5 by frs_step_dx, dbfs_eq_trans/
]
qed-.

lemma dbfss_eq_canc_dx (t) (t1) (t2) (rs):
      t1 ➡*𝐝𝐛𝐟[rs] t → t2 ⇔ t → t1 ➡*𝐝𝐛𝐟[rs] t2.
/3 width=3 by dbfss_eq_trans, subset_eq_sym/
qed-.

lemma dbfss_eq_canc_sx (t) (t1) (t2) (rs):
      t ⇔ t1 → t ➡*𝐝𝐛𝐟[rs] t2 → t1 ➡*𝐝𝐛𝐟[rs] t2.
#t #t1 #t2 #rs #Ht1 #H0 @(dbfss_ind_dx … H0) -t2 -rs
[ #t0 #t2 #rs #Ht02 #Ht12
  /2 width=3 by dbfss_eq_canc_dx/
| /3 width=1 by frs_refl, subset_eq_sym/
| #t0 #t2 #rs #s #_ #Ht02 #Ht10
  /2 width=3 by frs_step_dx/
]
qed-.

lemma eq_dbfss_trans (t) (t1) (t2) (rs):
      t1 ⇔ t → t ➡*𝐝𝐛𝐟[rs] t2 → t1 ➡*𝐝𝐛𝐟[rs] t2.
/3 width=3 by dbfss_eq_canc_sx, subset_eq_sym/
qed-.

lemma dbfss_eq_repl (t1) (t2) (u1) (u2) (rs):
      t1 ⇔ u1 → t2 ⇔ u2 → t1 ➡*𝐝𝐛𝐟[rs] t2 → u1 ➡*𝐝𝐛𝐟[rs] u2.
/3 width=3 by dbfss_eq_canc_sx, dbfss_eq_trans/
qed-.
