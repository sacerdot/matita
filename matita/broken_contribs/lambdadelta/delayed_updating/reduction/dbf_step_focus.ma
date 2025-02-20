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
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with brf ***************************************************)

lemma dbfs_mk_brf (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨t1,p,b,q❩←𝐃❨t1,p,b,q,n❩]t1 ⇔ t2 →
      t1 ➡𝐝𝐛𝐟[r] t2.
#t1 #t2 #r #p #b #q #n #Hr #Ht12
lapply (subset_eq_canc_sn … (fsubst_and_rc_sn …) … Ht12) -Ht12 #Ht12 
/2 width=6 by dbfs_mk/
qed.

(* Inversions with brf ******************************************************)

lemma dbfs_inv_brf (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 →
      ∃∃p,b,q,n. r ϵ 𝐑❨t1,p,b,q,n❩ & ⬕[𝐅❨t1,p,b,q❩←𝐃❨t1,p,b,q,n❩]t1 ⇔ t2.
#t1 #t2 #r * #p #b #q #n #Hr #Ht12
lapply (subset_eq_trans … (fsubst_and_rc_sn …) … Ht12) -Ht12 #Ht12 
/2 width=6 by ex2_4_intro/
qed-.
