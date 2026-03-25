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

include "ground/xoa/ex_3_1.ma".
include "delayed_updating/reduction/dbf_step.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals.ma".
include "delayed_updating/notation/relations/d_stroke_black_rightarrow_dbf_4.ma".

(* DELAYED BALANCED FOCUSED REDUCTION IN A DEVELOPMENT **********************)

definition dbfds: relation4 (𝕋) (𝒫❨ℙ❩) (𝕋) (𝒫❨ℙ❩) ≝
           λt1,u1,t2,u2.
           ∃∃r. r ϵ u1 & t1 ➡𝐝𝐛𝐟[r] t2 & u1 /𝐝𝐛𝐟 r ⇔ u2
.

interpretation
  "balanced focused reduction with delayed updating in a development (prototerm)"
  'DStrokeBlackRightArrowDBF t1 u1 u2 t2 = (dbfds t1 u1 t2 u2).

(* Basic constructions ******************************************************)

lemma dbfds_mk (t1) (t2) (u1) (u2) (r):
      r ϵ u1 → t1 ➡𝐝𝐛𝐟[r] t2 → u1 /𝐝𝐛𝐟 r ⇔ u2 →
      t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2.
/2 width=4 by ex3_intro/
qed.

(* Constructions with subset_eq *********************************************)

lemma dbfds_eq_trans (t) (t1) (t2) (u) (u1) (u2):
      t1 Ꟈ➡𝐝𝐛𝐟[u1,u] t → t ⇔ t2 → u ⇔ u2 → t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2.
#t #t1 #t2 #u #u1 #u2
* #r #Hr #Ht1 #Hu1 #Ht2 #Hu2
@(dbfds_mk … Hr) -Hr
[ @(dbfs_eq_trans … Ht1) -Ht1 //
| @(subset_eq_trans … Hu1) -Hu1 //
]
qed-.

lemma dbfds_eq_canc_dx (t) (t1) (t2) (u) (u1) (u2):
      t1 Ꟈ➡𝐝𝐛𝐟[u1,u] t → t2 ⇔ t → u2 ⇔ u → t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2.
/3 width=5 by dbfds_eq_trans, subset_eq_sym/
qed-.
