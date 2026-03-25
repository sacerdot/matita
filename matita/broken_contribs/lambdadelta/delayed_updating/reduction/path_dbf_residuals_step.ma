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

include "delayed_updating/reduction/dbf_step_c_redex.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with dbfs **************************************************)

lemma path_dbfr_step (t1) (t2) (s) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      s ϵ 𝐑❨t1❩ → (s /𝐝𝐛𝐟 r) ⊆ 𝐑❨t2❩.
#t1 #t2 #s #r #Ht1 #Ht12 #Hs #y * *
[ #Hnrs #H0 destruct
  /2 width=6 by dbfs_des_pcr_neq/
| #p #b #q #q0 #n #Hr #Hq0 #H1 #H2 destruct
  /4 width=5 by dbfs_des_pcr_side, dbfs_des_r, subset_and_in/
]
qed.
