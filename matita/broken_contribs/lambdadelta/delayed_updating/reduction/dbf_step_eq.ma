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

include "delayed_updating/reduction/dbf_step.ma".
include "delayed_updating/reduction/prototerm_delayed_eq.ma".
include "delayed_updating/reduction/prototerm_cx_redex_eq.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with subset_eq *********************************************)

lemma dbfs_eq_canc_sx (t) (t1) (t2) (r):
      t ⇔ t1 → t ➡𝐝𝐛𝐟[r] t2 → t1 ➡𝐝𝐛𝐟[r] t2.
#t #t1 #t2 #r #Ht1
* #p #b #q #n #Hr #Ht2
@(dbfs_mk … p b q n)
[ /3 width=3 by pcxr_eq_repl, subset_in_eq_repl_fwd/
| /4 width=3 by subset_eq_canc_sx, fsubst_eq_repl, brd_eq_repl_fwd/
]
qed-.

lemma eq_dbfs_trans (t) (t1) (t2) (r):
      t1 ⇔ t → t ➡𝐝𝐛𝐟[r] t2 → t1 ➡𝐝𝐛𝐟[r] t2.
/3 width=3 by dbfs_eq_canc_sx, subset_eq_sym/
qed-.

lemma dbfs_eq_repl (t1) (t2) (u1) (u2) (r):
      t1 ⇔ u1 → t2 ⇔ u2 → t1 ➡𝐝𝐛𝐟[r] t2 → u1 ➡𝐝𝐛𝐟[r] u2.
/3 width=3 by dbfs_eq_canc_sx, dbfs_eq_trans/
qed-.
