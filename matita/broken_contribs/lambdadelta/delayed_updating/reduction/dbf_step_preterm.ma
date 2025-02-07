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

include "delayed_updating/reduction/prototerm_reducible_preterm.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions with preterm ************************************************)

axiom dbfs_preterm_trans (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐓.

(* Inversions with preterm **************************************************)

lemma dbfs_preterm_inv_sn (t1) (t2) (r) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[↑(p●𝗔◗b●𝗟◗q)←(p●𝗔◗(⓪b)●𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t1]t1 ⇔ t2.
#t1 #t2 #r #p1 #b1 #q1 #n1 #Ht1
* #p2 #b2 #q2 #n2 #H2r #Ht12 #H1r
lapply (subset_ol_i ???? H1r H2r) -H1r -H2r #H0
elim (xprc_des_ol … Ht1 H0) -H0 #H1 #H2 #H3 #H4 destruct //
qed-.

(* Main inversions with preterm *********************************************)

theorem dbfs_preterm_mono (t0) (t1) (t2) (r):
        t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r] t1 → t0 ➡𝐝𝐛𝐟[r] t2 → t1 ⇔ t2.
#t0 #t1 #t2 #r #Ht0 #Ht01
* #p #b #q #n #Hr #Ht02
lapply (dbfs_preterm_inv_sn … Ht0 Ht01 Hr) -Ht0 -Ht01 -Hr #Ht01
@(subset_eq_canc_sn … Ht01 … Ht02)
qed-.
