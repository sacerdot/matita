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

include "delayed_updating/syntax/preterm_root_eq.ma".
include "delayed_updating/reduction/ibf_step_root_le.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Destructions with preterm ************************************************)

lemma ibfs_des_in_comp_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐢𝐛𝐟[r] t2 → s ⧸= r →
      s ϵ t1 → s ϵ t2.
#t1 #t2 #r #s #Ht1 #Ht12 #Hnrs #Hs
/5 width=5 by ibfs_des_in_comp_nrle, ibfs_des_r, path_rle_inv_complete/
qed-.

lemma ibfs_des_pcxr_neq (t1) (t2) (r) (s) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐢𝐛𝐟[r] t2 → s ⧸= r →
      s ϵ 𝐑❨t1,p,b,q,n❩ → s ϵ 𝐑❨t2,p,b,q,n❩.
#t1 #t2 #r #s #p #b #q #n #Ht1 #Ht12 #Hnrs * #H1s #H2s
/3 width=6 by ibfs_des_in_comp_neq, subset_and_in/
qed-.
