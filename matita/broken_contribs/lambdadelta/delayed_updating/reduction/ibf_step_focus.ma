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

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/reduction/prototerm_focus.ma".
include "delayed_updating/reduction/ibf_step.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with brf ***************************************************)

lemma ibfs_mk_brf (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨t1,p,b,q,n❩←𝐈❨t1,p,b,q,n❩]t1 ⇔ t2 →
      t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #t2 #r #p #b #q #n #Hr #Ht12
lapply (subset_eq_canc_sx … (fsubst_and_rc_sx …) … Ht12) -Ht12 #Ht12
/2 width=6 by ibfs_mk/
qed.

(* Inversions with brf ******************************************************)

lemma ibfs_inv_brf (t1) (t2) (r):
      t1 ➡ 𝐢𝐛𝐟[r] t2 →
      ∃∃p,b,q,n. r ϵ 𝐑❨t1,p,b,q,n❩ & ⬕[𝐅❨t1,p,b,q,n❩←𝐈❨t1,p,b,q,n❩]t1 ⇔ t2.
#t1 #t2 #r * #p #b #q #n #Hr #Ht12
lapply (subset_eq_trans … (fsubst_and_rc_sx …) … Ht12) -Ht12 #Ht12
/2 width=6 by ex2_4_intro/
qed-.
