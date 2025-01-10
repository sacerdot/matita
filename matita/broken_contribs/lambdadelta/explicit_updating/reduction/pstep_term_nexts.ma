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

include "explicit_updating/syntax/term_nexts.ma".
include "explicit_updating/reduction/pstep_term_next.ma".

(* Constructions with term_nexts ********************************************)

lemma pstep_term_nexts_bi (R2) (n) (t1) (t2):
      t1 ⫽➡[R2] t2 → ↑*[n]t1 ⫽➡[R2] ↑*[n]t2.
#R2 @nat_ind_succ //
#n #IH #t1 #t2 #Ht12
<term_nexts_succ_swap <term_nexts_succ_swap
/3 width=1 by pstep_term_next_bi/
qed.
