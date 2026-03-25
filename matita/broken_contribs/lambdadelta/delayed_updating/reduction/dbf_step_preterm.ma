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

include "delayed_updating/syntax/preterm_eq.ma".
include "delayed_updating/syntax/preterm_root_eq.ma".
include "delayed_updating/reduction/dbf_step_root_le.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions with preterm ************************************************)

axiom dbfs_preterm_trans_aux (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      ⬕[𝐅❨p,b,q,n❩←𝐃❨t,p,b,q,n❩]t ϵ 𝐓.

lemma dbfs_preterm_trans (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐓.
#t1 #t2 #r #Ht1 * #p #b #q #n #Hr #Ht12
/3 width=3 by term_eq_repl_fwd, dbfs_preterm_trans_aux/
qed.

(* Note: was: dbfs_des_pcxr_neq *)
lemma dbfs_des_in_comp_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → s ⧸= r →
      s ϵ t1 → s ϵ t2.
#t1 #t2 #r #s #Ht1 #Ht12 #Hnrs #Hs
/5 width=5 by dbfs_des_in_comp_nrle, dbfs_des_r, path_rle_inv_complete/
qed-.

lemma dbfs_des_pcxr_neq (t1) (t2) (r) (s) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → s ⧸= r →
      s ϵ 𝐑❨t1,p,b,q,n❩ → s ϵ 𝐑❨t2,p,b,q,n❩.
#t1 #t2 #r #s #p #b #q #n #Ht1 #Ht12 #Hnrs * #H1s #H2s
/3 width=6 by dbfs_des_in_comp_neq, subset_and_in/
qed-.
