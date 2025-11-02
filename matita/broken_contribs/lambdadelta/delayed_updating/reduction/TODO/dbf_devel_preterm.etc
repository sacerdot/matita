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

include "delayed_updating/reduction/path_dbf_residuals_preterm.ma".
include "delayed_updating/reduction/dbf_devel_eq.ma".

(* COMPLETE DEVELOPMENT FOR DELAYED BALANCED FOCUSED REDUCTION **************)

(* Constructions with preterm ***********************************************)

lemma dbfs_neq_dbfd (t1) (t2) (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      s ⧸= r → s ⧸ϵ ⓪▵↑(p◖𝗦) →
      t1 ➡𝐝𝐛𝐟[s] t2 → t1 ⫽➡𝐝𝐛𝐟[s /𝐝𝐛𝐟{t} r] t2.
#t1 #t2 #t #s #r #p #b #q #n #Ht #Hr #Hnsr #Hns #Ht12
lapply (dbfs_des_clear_r … Ht12) #Hs
@(dbfd_step … Ht12) -Ht12
[ /2 width=1 by path_dbfr_neq/
| @(dbfd_eq_repl … (Ⓕ) … t2 … t2) [2:|*: // ]
  @(subset_eq_trans … (path_dbfr_refl t1 s))
  @(subset_eq_trans … (term_dbfr_single …))
  @term_dbfr_eq_repl [ // ]
  /2 width=6 by path_dbfr_neq_eq/
]
qed.
