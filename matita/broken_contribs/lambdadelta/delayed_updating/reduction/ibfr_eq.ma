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

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

include "delayed_updating/reduction/ibfr.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

(* Constructions with subset_equivalence ************************************)

lemma ibfr_eq_canc_sn (t) (t1) (t2) (r):
      t ⇔ t1 → t ➡𝐢𝐛𝐟[r] t2 → t1 ➡𝐢𝐛𝐟[r] t2.
#t #t1 #t2 #r #Ht1
* #p #b #q #m #n #Hr #Hb #Hm #Hn #Ht #Ht2 destruct
@(ex6_5_intro … p … Hb Hm Hn) [ // ] -Hb -Hm -Hn
[ /2 width=3 by subset_in_eq_repl_back/
| /5 width=3 by subset_eq_canc_sn, fsubst_eq_repl, lift_term_eq_repl_dx, grafted_eq_repl/
]
qed-.

lemma ibfr_eq_repl (t1) (t2) (u1) (u2) (r):
      t1 ⇔ u1 → t2 ⇔ u2 → t1 ➡𝐢𝐛𝐟[r] t2 → u1 ➡𝐢𝐛𝐟[r] u2.
/3 width=3 by ibfr_eq_canc_sn, ibfr_eq_trans/
qed-.
