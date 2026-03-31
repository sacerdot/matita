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
/3 width=1 by term_ins_dbfr_lcons/
qed.

lemma term_ins_dbfr_rcons (rs) (r) (u):
      rs ϵ* u → r ϵ u /𝐝𝐛𝐟 rs → rs⨭r ϵ* u.
/3 width=1 by term_ins_dbfr_lcons, term_ins_dbfr_append/
qed.
