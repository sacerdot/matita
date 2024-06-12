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

include "delayed_updating/reduction/dbfr_eq.ma".
include "delayed_updating/computation/frs.ma".
include "delayed_updating/notation/relations/black_rightarrow_star_dbf_3.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

interpretation
  "balanced focused computation with delayed updating (prototerm)"
  'BlackRightArrowStarDBF t1 rs t2 = (frs dbfr rs t1 t2).

(* Basic inversions *********************************************************)

lemma dbfrs_inv_step (t1) (t2) (r):
      t1 ➡*𝐝𝐛𝐟[r◗𝐞] t2 → t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #t2 #r
@frs_inv_step -t1 -t2 -r #t #t1 #t2 #r
[ /3 width=3 by dbfr_eq_canc_sn, subset_eq_sym/
| /2 width=3 by dbfr_eq_trans/
]
qed-.

(* Advanced inversions ******************************************************)

lemma dbfrs_inv_step_sn (t1) (t2) (ss) (r):
      t1 ➡*𝐝𝐛𝐟[r◗ss] t2 →
      ∃∃t. t1 ➡𝐝𝐛𝐟[r] t & t ➡*𝐝𝐛𝐟[ss] t2.
#t1 #t2 #ss #r
@frs_inv_step_sn -t1 -t2 -ss -r #t #t1 #t2 #r
[ /3 width=3 by dbfr_eq_canc_sn, subset_eq_sym/
| /2 width=3 by dbfr_eq_trans/
]
qed-.

lemma dbfrs_inv_step_dx (t1) (t2) (rs) (s):
      t1 ➡*𝐝𝐛𝐟[rs◖s] t2 →
      ∃∃t. t1 ➡*𝐝𝐛𝐟[rs] t & t ➡𝐝𝐛𝐟[s] t2.
#t1 #t2 #rs #s
@frs_inv_step_dx -t1 -t2 -rs -s #t #t1 #t2 #r
[ /3 width=3 by dbfr_eq_canc_sn, subset_eq_sym/
| /2 width=3 by dbfr_eq_trans/
]
qed-.

(* Advanced eliminators *****************************************************)

lemma dbfrs_ind_sn (t2) (Q:relation2 …):
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      Q t2 (𝐞) →
      (∀t,t1,ss,r. t1 ➡𝐝𝐛𝐟[r] t → t ➡*𝐝𝐛𝐟[ss] t2 → Q t ss → Q t1 (r◗ss)) →
      ∀t1,rs. t1 ➡*𝐝𝐛𝐟[rs] t2 → Q t1 rs.
#t2 #Q
@frs_ind_sn -Q -t2 #t #t1 #t2 #r
[ /3 width=3 by dbfr_eq_canc_sn, subset_eq_sym/
| /2 width=3 by dbfr_eq_trans/
]
qed-.

lemma dbfrs_ind_dx (t1) (Q:relation2 …):
      (∀t1,t2,rs. t1 ⇔ t2 → Q t2 rs → Q t1 rs) →
      Q t1 (𝐞) →
      (∀t,t2,rs,s. t1 ➡*𝐝𝐛𝐟[rs] t → t ➡𝐝𝐛𝐟[s] t2 → Q t rs → Q t2 (rs◖s)) →
      ∀t2,rs. t1 ➡*𝐝𝐛𝐟[rs] t2 → Q t2 rs.
#t1 #Q
@frs_ind_dx -Q -t1 #t #t1 #t2 #r
[ /3 width=3 by dbfr_eq_canc_sn, subset_eq_sym/
| /2 width=3 by dbfr_eq_trans/
]
qed-.

(* Constructions with subset_eq *********************************************)

lemma dbfrs_eq_trans (t):
      ∀t1,rs. t1 ➡*𝐝𝐛𝐟[rs] t →
      ∀t2. t ⇔ t2 → t1 ➡*𝐝𝐛𝐟[rs] t2.
#t #t1 #rs #H0
@(dbfrs_ind_dx … H0) -t -rs
[ #t #t0 #rs #Ht0 #IH #t2 #Ht2
  /3 width=3 by subset_eq_canc_sn/
| /2 width=1 by frs_refl/
| #u1 #u2 #ss #s #Htu #Hu #_ #t2 #Hut
  /3 width=5 by frs_step_dx, dbfr_eq_trans/
]
qed-.

lemma dbfrs_eq_canc_dx (t) (t1) (t2) (rs):
      t1 ➡*𝐝𝐛𝐟[rs] t → t2 ⇔ t → t1 ➡*𝐝𝐛𝐟[rs] t2.
/3 width=3 by dbfrs_eq_trans, subset_eq_sym/
qed-.
