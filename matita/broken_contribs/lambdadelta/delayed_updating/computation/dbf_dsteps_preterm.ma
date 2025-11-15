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
include "delayed_updating/reduction//dbf_dstep_preterm.ma".
include "delayed_updating/computation/dbf_dsteps_eq.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with preterm ***********************************************)

lemma dbfs_neq_dbfdss (t1) (t2) (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      s ⧸= r → s ⧸ϵ ⓪▵↑(p◖𝗦) →
      t1 ➡𝐝𝐛𝐟[s] t2 → t1 Ꟈ➡*𝐝𝐛𝐟[s /𝐝𝐛𝐟{t} r, Ⓕ] t2.
#t1 #t2 #t #s #r #p #b #q #n #Ht #Hr #Hnsr #Hns #Ht12
lapply (dbfs_des_clear_r … Ht12) #Hs
@(dbfdss_eq_canc_sx t1)
[3: // |4: @(path_dbfr_neq_eq … Hr) // | skip ]
/3 width=1 by dbfdss_step, dbfds_single/
qed.

lemma dbfs_side_dbfdss (t0) (t) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x):
      t1 ϵ 𝐓 → t2 ϵ 𝐓 → x ϵ 𝐏 →
      r1 ϵ 𝐑❨t1,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t2,p2,b2,q2,n2❩ →
      r2 ⧸ϵ ⓪▵↑(p1◖𝗦) → ⓪(p2◖𝗦)●⓪x = r1 →
      t1 ➡𝐝𝐛𝐟[r1] t → t ➡𝐝𝐛𝐟[r2●⓪x] t0 →
      t1 Ꟈ➡*𝐝𝐛𝐟[r1 /𝐝𝐛𝐟{t2} r2, Ⓕ] t0.
#t0 #t #t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x #Ht1 #Ht2 #Hx #Hr1 #Hr2 #Hnr2 #H0 #Htr1 #Htr2
lapply (xprc_des_r … Hr2) #H0r2
@(dbfdss_eq_canc_sx t1)
[3: // |4: @(path_dbfr_side … Hr2) // | skip ]
@(dbfdss_trans … t … (❴r2●⓪x❵))
[ /3 width=14 by dbfdss_step, dbfds_side_sx/
| /3 width=1 by dbfdss_step, dbfds_single/
]
qed-.
