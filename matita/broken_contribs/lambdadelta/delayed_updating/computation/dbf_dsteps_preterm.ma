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

include "delayed_updating/reduction/preterm_cx_redex_clear.ma".
include "delayed_updating/computation/dbf_dsteps_or.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with preterm ***********************************************)

lemma dbfs_side_dbfdss_preterm (t) (t0) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2) (x):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      p1◖𝗦 ⧸≚ r2 → p2◖𝗦●x = r1 →
      t1 ➡𝐝𝐛𝐟[r1] t0 → t0 ➡𝐝𝐛𝐟[𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●x] t2 →
      t1 Ꟈ➡*𝐝𝐛𝐟[r1 /𝐝𝐛𝐟 r2, Ⓕ] t2.
/3 width=18 by dbfs_side_dbfdss_cx, nreq_des_side_pcxr/
qed.
