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

include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "ground/subsets/subset_or_eq.ma".

(* CONSTRUCTORS FOR PROTOTERM ***********************************************)

(* Constructions with equivalence for prototerm *****************************)

lemma iref_eq_repl_bi (t1) (t2) (k1) (k2):
      k1 = k2 → t1 ⇔ t2 → 𝛕k1.t1 ⇔ 𝛕k2.t2.
/3 width=2 by pt_append_eq_repl_bi/
qed.

lemma abst_eq_repl (t1) (t2):
      t1 ⇔ t2 → 𝛌.t1 ⇔ 𝛌.t2.
/2 width=2 by pt_append_eq_repl_bi/
qed.

lemma appl_eq_repl (u1) (u2) (t1) (t2):
      u1 ⇔ u2 → t1 ⇔ t2 → ＠u1.t1 ⇔ ＠u2.t2.
/3 width=2 by pt_append_eq_repl_bi, subset_or_eq_repl/
qed.

(* Constructions with term_grafted ******************************************)

lemma term_grafted_abst_hd (t) (p):
      (⋔[p]t) ⇔ ⋔[𝗟◗p]𝛌.t.
#t #p @conj #r #Hr
[ /2 width=3 by ex2_intro/
| lapply (term_grafted_inv_gen … Hr) -Hr
  /2 width=1 by in_comp_inv_abst_hd/
]
qed.

lemma term_grafted_appl_sd (v) (t) (p):
      (⋔[p]v) ⇔ ⋔[𝗦◗p]＠v.t.
#v #t #p @conj #r #Hr
[ /3 width=3 by ex2_intro, or_introl/
| lapply (term_grafted_inv_gen … Hr) -Hr
  /2 width=2 by in_comp_inv_appl_sd/
]
qed.

lemma term_grafted_appl_hd (v) (t) (p):
      (⋔[p]t) ⇔ ⋔[𝗔◗p]＠v.t.
#v #t #p @conj #r #Hr
[ /3 width=3 by ex2_intro, or_intror/
| lapply (term_grafted_inv_gen … Hr) -Hr
  /2 width=2 by in_comp_inv_appl_hd/
]
qed.
