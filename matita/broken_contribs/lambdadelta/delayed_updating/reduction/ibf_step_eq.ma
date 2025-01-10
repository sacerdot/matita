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

include "delayed_updating/reduction/ibf_step.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with subset_eq *********************************************)

lemma ibfs_eq_canc_sn (t) (t1) (t2) (r):
      t ⇔ t1 → t ➡𝐢𝐛𝐟[r] t2 → t1 ➡𝐢𝐛𝐟[r] t2.
#t #t1 #t2 #r #Ht1
* #p #b #q #n #Hr #Hb #Hn #Ht #Ht2 destruct
@(ex5_4_intro … p … Hb Hn) [ // ] -Hb -Hn
[ /2 width=3 by subset_in_eq_repl_fwd/
| /6 width=3 by subset_eq_canc_sn, fsubst_eq_repl, pt_append_eq_repl_bi, lift_term_eq_repl_dx, term_grafted_eq_repl/
]
qed-.

lemma ibfs_eq_repl (t1) (t2) (u1) (u2) (r):
      t1 ⇔ u1 → t2 ⇔ u2 → t1 ➡𝐢𝐛𝐟[r] t2 → u1 ➡𝐢𝐛𝐟[r] u2.
/3 width=3 by ibfs_eq_canc_sn, ibfs_eq_trans/
qed-.
