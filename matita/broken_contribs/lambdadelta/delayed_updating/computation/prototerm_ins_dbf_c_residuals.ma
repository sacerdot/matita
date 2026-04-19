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

include "delayed_updating/computation/prototerm_dbf_c_residuals.ma".
include "delayed_updating/computation/prototerm_ins_dbf_residuals.ma".

(* MEMBERSHIP OF A TRACE TO A SUBSET OF DBF-REDEX POINTERS ******************)

(* Constructions with term_dbfrs ********************************************)

lemma term_ins_dbfr_append (rs) (ss) (u):
      rs ϵ* u → ss ϵ* u /𝐝𝐛𝐟 rs → rs⨁ss ϵ* u.
#rs elim rs -rs [ // ]
#r #rs #IH #ss #u * #Hr #Hrs #Hss
/3 width=1 by term_ins_dbfr_cons_sx/
qed.

lemma term_ins_dbfr_cons_dx (rs) (r) (u):
      rs ϵ* u → r ϵ u /𝐝𝐛𝐟 rs → rs⨭r ϵ* u.
/3 width=1 by term_ins_dbfr_cons_sx, term_ins_dbfr_append/
qed.

(* Inversions with term_dbfrs ***********************************************)

lemma term_ins_dbfr_inv_append (rs) (ss) (u):
      rs⨁ss ϵ* u → ∧∧ rs ϵ* u & ss ϵ* u /𝐝𝐛𝐟 rs.
#rs elim rs -rs
[ /2 width=1 by conj/
| #r #rs #IH #ss #u * #Hr #Hrss
  elim (IH … Hrss) -IH -Hrss #Hrs #Hss
  /3 width=1 by term_ins_dbfr_cons_sx, conj/
]
qed-.

lemma term_ins_dbfr_inv_cons_dx (rs) (r) (u):
      rs⨭r ϵ* u → ∧∧ rs ϵ* u & r ϵ u /𝐝𝐛𝐟 rs.
#rs #r #u #H0
elim (term_ins_dbfr_inv_append … H0) -H0 #Hrs * #Hr #_
/2 width=1 by conj/
qed-.
