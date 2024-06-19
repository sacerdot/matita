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

(* DELAYED BALANCED FOCUSED PARALLEL REDUCTION ******************************)

include "ground/subsets/subset_nimply_eq.ma".
include "delayed_updating/reduction/dbfpr.ma".

(* Advanced constructions with subset_eq ************************************)

lemma dbfpr_eq_repl_rc (t1) (t2) (u):
      t1 ∥➡𝐝𝐛𝐟[u] t2 → ∀v. u ⇔ v → t1 ∥➡𝐝𝐛𝐟[v] t2.
#t1 #t2 #u #H0 elim H0 -t1 -t2 -u
[ #t1 #t2 #u #Ht12 #Hu #v * #_ #Hvu
  /3 width=5 by dbfpr_refl, subset_le_trans/
| #t0 #t1 #t2 #u #p #b #q #n #Hb #Hq #Ht1 #Hu #Ht2 #_ #IH #v #Huv
  lapply (subset_in_eq_repl_fwd ??? Hu … Huv) -Hu #Hv
  @(dbfpr_step … Hb Hq Ht1 Hv Ht2) -t2 -n -Hb -Hv
  /3 width=1 by subset_nimp_eq_repl/
]
qed-.

lemma dbfpr_eq_repl (t1) (t2) (u1) (u2) (u) (v):
      t1 ⇔ u1 → t2 ⇔ u2 → u ⇔ v → t1 ∥➡𝐝𝐛𝐟[u] t2 → u1 ∥➡𝐝𝐛𝐟[v] u2.
/4 width=3 by dbfpr_eq_repl_rc, dbfpr_eq_canc_sn, dbfpr_eq_trans/
qed-.
