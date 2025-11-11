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

include "delayed_updating/reduction/dbf_dstep_preterm.ma".
include "delayed_updating/computation/dbf_dsteps.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with preterm ***********************************************)

lemma dbfs_neq_dbfdss (t1) (t2) (t) (s) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      s ⧸= r → s ⧸ϵ ⓪▵↑(p◖𝗦) →
      t1 ➡𝐝𝐛𝐟[s] t2 → t1 Ꟈ➡*𝐝𝐛𝐟[s /𝐝𝐛𝐟{t} r, Ⓕ] t2.
/3 width=6 by dbfs_neq_dbfds, dbfdss_step/
qed.
