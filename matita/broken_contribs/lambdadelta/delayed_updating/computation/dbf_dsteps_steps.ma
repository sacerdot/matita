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

include "delayed_updating/computation/dbf_steps.ma".
include "delayed_updating/computation/dbf_dsteps.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Destructions with delayed balanced focused computation *******************)

lemma dbfdss_des_dbfss (t1) (t2) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 →
      ∃rs. t1 ➡*𝐝𝐛𝐟[rs] t2.
#t1 #t2 #u1 #u2 #H12 elim H12 -t1 -t2 -u1 -u2
[ #t1 #t2 #u1 #u2 #Ht12 #Hu12
  /3 width=2 by frs_refl, ex_intro/
| #t1 #t2 #u1 #u2 * #r #Hr #Ht12 #Hu12
  /3 width=2 by frs_step, ex_intro/
| #t #t1 #t2 #u #u1 #u2 #_ #_ * #rs1 #Ht1 * #rs2 #Ht2
  /3 width=5 by frs_trans, ex_intro/
]
qed-.
