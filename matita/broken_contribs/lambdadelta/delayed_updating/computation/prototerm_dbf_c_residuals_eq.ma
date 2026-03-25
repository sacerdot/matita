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
include "delayed_updating/computation/prototerm_dbf_c_residuals.ma".

(* CUMULATED RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ********************)

(* Constructions with subset_eq *********************************************)

lemma term_dbfrs_eq_repl (rs) (u1) (u2):
      u1 ⇔ u2 → (u1 /𝐝𝐛𝐟 rs) ⇔ (u2 /𝐝𝐛𝐟 rs).
#rs elim rs -rs [ // ]
#r #rs #IH #u1 #u2 #Hu12
/3 width=1 by term_dbfr_eq_repl/
qed.
