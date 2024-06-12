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

include "delayed_updating/syntax/preterm_eq.ma".
include "delayed_updating/reduction/dbfr_preterm.ma".
include "delayed_updating/computation/dbfrs.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Destructions with preterm ************************************************)

lemma dbfrs_preterm_trans (t1) (t2) (rs):
      t1 ϵ 𝐓 → t1 ➡*𝐝𝐛𝐟[rs] t2 → t2 ϵ 𝐓.
#t1 #t2 #rs #Ht1 #H0
@(dbfrs_ind_dx … H0) -t2 -rs //
[ /2 width=3 by term_eq_repl_back/
| #t #t2 #rs #r #_ #Ht2 #IH -Ht1
  /2 width=4 by dbfr_preterm_trans/
]
qed. 
