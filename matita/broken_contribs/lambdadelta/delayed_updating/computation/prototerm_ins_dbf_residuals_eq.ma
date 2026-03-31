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
include "delayed_updating/computation/prototerm_ins_dbf_residuals.ma".

(* MEMBERSHIP OF A TRACE TO A SUBSET OF DBF-REDEX POINTERS ******************)

(* Constructions with term_eq ***********************************************)

lemma term_ins_dbfr_eq_repl_fwd (rs) (u1) (u2):
      rs ϵ* u1 → u1 ⇔ u2 → rs ϵ* u2.
#rs elim rs -rs [ // ]
#r #rs #IH #u1 #u2 * #Hr #Hrs #Hu12
/4 width=3 by term_ins_dbfr_lcons, term_dbfr_eq_repl_fwd, subset_in_eq_repl_fwd/
qed-.
