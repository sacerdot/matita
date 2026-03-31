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

include "delayed_updating/reduction/prototerm_dbf_residuals_eq.ma".
include "delayed_updating/reduction/dbf_step_eq.ma".
include "delayed_updating/reduction/dbf_dstep.ma".

(* DELAYED BALANCED FOCUSED REDUCTION IN A DEVELOPMENT **********************)

(* Constructions with subset_eq *********************************************)

lemma dbfds_eq_canc_sx (t) (t1) (t2) (u) (u1) (u2):
      t ⇔ t1 → u ⇔ u1 → t Ꟈ➡𝐝𝐛𝐟[u,u2] t2 → t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2.
#t #t1 #t2 #u #u1 #u2 #Ht1 #Hu1
* #r #Hr #Ht2 #Hu2
@(dbfds_mk … r)
[ /2 width=3 by subset_in_eq_repl_fwd/
| /2 width=3 by dbfs_eq_canc_sx/
| /3 width=3 by subset_eq_canc_sx, term_dbfr_eq_repl_fwd/
]
qed-.

lemma eq_dbfds_trans (t) (t1) (t2) (u) (u1) (u2):
      t1 ⇔ t → u1 ⇔ u → t Ꟈ➡𝐝𝐛𝐟[u,u2] t2 → t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2.
/3 width=5 by dbfds_eq_canc_sx, subset_eq_sym/
qed-.

lemma dbfds_eq_repl (t1) (t2) (u1) (u2) (v1) (v2) (w1) (w2):
      t1 ⇔ u1 → t2 ⇔ u2 → v1 ⇔ w1 → v2 ⇔ w2 →
      t1 Ꟈ➡𝐝𝐛𝐟[v1,v2] t2 → u1 Ꟈ➡𝐝𝐛𝐟[w1,w2] u2.
/3 width=5 by dbfds_eq_canc_sx, dbfds_eq_trans/
qed-.

(* Advanced constructions ***************************************************)

lemma dbfds_single (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → t1 Ꟈ➡𝐝𝐛𝐟[❴r❵, Ⓕ] t2.
#t1 #t2 #r #Ht12
@(dbfds_mk … Ht12) -Ht12
/2 width=1 by subset_eq_sym/
qed.

(* Advanced inversions ******************************************************)

lemma dbfds_inv_dbfr_dx (t1) (t2) (u) (r):
      t1 Ꟈ➡𝐝𝐛𝐟[u, u /𝐝𝐛𝐟 r] t2 →
      ∧∧ r ϵ u & t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #t2 #u #r * #r0 #Hr0 #Ht12 #Hu
>(term_eq_des_dbfr_bi_neq … Hu) -Hu
/2 width=1 by or_intror, conj/
qed-.
