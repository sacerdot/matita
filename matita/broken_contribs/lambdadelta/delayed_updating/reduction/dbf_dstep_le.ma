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

include "delayed_updating/reduction/prototerm_dbf_residuals_le.ma".
include "delayed_updating/reduction/dbf_dstep.ma".

(* DELAYED BALANCED FOCUSED REDUCTION IN A DEVELOPMENT **********************)

(* Constructions with subset_le *********************************************)

lemma dbfds_subset_le_sx_conf (t1) (t2) (u1) (u2) (v1):
      t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2 → u1 ⊆ v1 →
      ∃∃v2. t1 Ꟈ➡𝐝𝐛𝐟[v1,v2] t2 & u2 ⊆ v2.
#t1 #t2 #u1 #u2 #v1 * #r #Hr #Ht12 #Hu12 #Huv1
@(ex2_intro … (v1 /𝐝𝐛𝐟{t1} r))
[ /3 width=4 by dbfds_mk/
| @(subset_le_eq_repl … Hu12) -Hu12 [1,3: // ]
  @(term_dbfr_le_repl … Huv1) -Huv1 //
]
qed-.
