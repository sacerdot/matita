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
include "ground/lib/subset_ext_equivalence.ma".

(* CONSTRUCTORS FOR PROTOTERM ***********************************************)

(* Constructions with equivalence for prototerm *****************************)

lemma iref_eq_repl (t1) (t2) (k):
      t1 â t2 â ğk.t1 â ğk.t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.

lemma abst_eq_repl (t1) (t2):
      t1 â t2 â ğ.t1 â ğ.t2.
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.

lemma appl_eq_repl (u1) (u2) (t1) (t2):
      u1 â u2 â t1 â t2 â ï¼ u1.t1 â ï¼ u2.t2.
/2 width=1 by subset_equivalence_ext_f1_1_bi/
qed.

(* Constructions with prototerm_grafted *************************************)

lemma grafted_abst_hd (t) (p):
      tâp â (ğ.t)â(ğâp).
#t #p @conj #r #Hr
[ /2 width=3 by ex2_intro/
| lapply (prototerm_grafted_inv_gen â¦ Hr) -Hr
  /2 width=1 by in_comp_inv_abst_hd/
]
qed.

lemma grafted_appl_sd (v) (t) (p):
      vâp â (ï¼ v.t)â(ğ¦âp).
#v #t #p @conj #r #Hr
[ /3 width=3 by ex2_intro, or_introl/
| lapply (prototerm_grafted_inv_gen â¦ Hr) -Hr
  /2 width=2 by in_comp_inv_appl_sd/
]
qed.

lemma grafted_appl_hd (v) (t) (p):
      tâp â (ï¼ v.t)â(ğâp).
#v #t #p @conj #r #Hr
[ /3 width=3 by ex2_intro, or_intror/
| lapply (prototerm_grafted_inv_gen â¦ Hr) -Hr
  /2 width=2 by in_comp_inv_appl_hd/
]
qed.
