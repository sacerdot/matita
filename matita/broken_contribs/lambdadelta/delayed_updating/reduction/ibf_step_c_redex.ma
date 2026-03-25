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

include "delayed_updating/reduction/prototerm_c_redex.ma".
include "delayed_updating/reduction/ibf_step_preterm.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with pcr ***************************************************)

lemma ibfs_pcr (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr
/2 width=5 by pcxr_ibfs/
qed-.

(* Inversions with pcr ******************************************************)

lemma ibfs_inv_pcr (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #_
/2 width=5 by pcr_mk/
qed-.

(* Destructions with pcr ****************************************************)

lemma ibfs_des_pcr_nrle (t1) (t2) (r) (s):
      t1 ➡𝐢𝐛𝐟[r] t2 →
      r ⧸⊑ s → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht12 #Hnrs * #p #b #q #n #Hs
/3 width=9 by pcr_mk, ibfs_des_pcxr_nrle/
qed-.

lemma ibfs_des_pcr_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐢𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht12 #Hnrs * #p #b #q #n #Hs
/3 width=10 by pcr_mk, ibfs_des_pcxr_neq/
qed-.
