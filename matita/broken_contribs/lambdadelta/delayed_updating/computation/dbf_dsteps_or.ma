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

include "delayed_updating/reduction/prototerm_x_redex_proper.ma".
include "delayed_updating/reduction/dbf_dstep_or.ma".
include "delayed_updating/computation/dbf_dsteps_eq.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Advanced constructions ***************************************************)

lemma dbfs_side_dbfdss (t0) (t) (t1) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2) (x):
      r1 ϵ 𝐑❨p1,b1,q1,n1❩ → r2 ϵ 𝐑❨p2,b2,q2,n2❩ →
      p1◖𝗦 ⧸≚ 𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩ → p2◖𝗦●x = r1 →
      t1 ➡𝐝𝐛𝐟[r1] t → t ➡𝐝𝐛𝐟[𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●x] t0 →
      t1 Ꟈ➡*𝐝𝐛𝐟[r1 /𝐝𝐛𝐟 r2, Ⓕ] t0.
#t0 #t #t1 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x #Hr1 #Hr2 #Hnr2 #H0 #Htr1 #Htr2
@(dbfdss_trans … t)
[3: /3 width=2 by dbfdss_step, dbfds_single/ | skip ]
@(dbfdss_eq_canc_sx t1)
[3: //
|4: @(path_dbfr_side_eq … Hr2) /2 width=8 by pxr_S_des_ppc/
|1: skip
|2: /3 width=6 by dbfdss_step, dbfds_side_sx/
]
qed-.

lemma dbfs_side_dbfdss_cx (u1) (u2) (t0) (t) (t1) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2) (x):
      r1 ϵ 𝐑❨u1,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨u2,p2,b2,q2,n2❩ →
      p1◖𝗦 ⧸≚ 𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩ → p2◖𝗦●x = r1 →
      t1 ➡𝐝𝐛𝐟[r1] t → t ➡𝐝𝐛𝐟[𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●x] t0 →
      t1 Ꟈ➡*𝐝𝐛𝐟[r1 /𝐝𝐛𝐟 r2, Ⓕ] t0.
/3 width=16 by pcxr_des_x, dbfs_side_dbfdss/
qed.
