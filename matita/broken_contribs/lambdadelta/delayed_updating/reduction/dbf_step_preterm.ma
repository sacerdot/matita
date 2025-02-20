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

include "delayed_updating/reduction/preterm_reducible.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions with preterm ************************************************)

axiom dbfs_preterm_trans (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐓.

lemma dbfs_des_xprc_neq (t1) (t2) (r) (s) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → s ⧸= r →
      s ϵ 𝐑❨t1,p,b,q,n❩ → s ϵ 𝐑❨t2,p,b,q,n❩.
#t1 #t2 #r #s #p #b #q #n #Ht1 #Ht12
#Hnsr * #Hs #Hb #Hq #Hn destruct
@(xprc_mk … Hb Hq) -Hb -Hq
@(dbfs_des_in_comp_neq … Ht12) // #H0
cases Ht12 -Ht12 #p0 #b0 #q0 #n0 * #Hr #_ #_ #Hn0 #Ht12 destruct
lapply (term_slice_des_clear_bi … (𝐞) … Ht1 … H0) -H0
[ /2 width=2 by term_in_root_rcons/
| /2 width=1 by term_in_comp_root/
]
* #s #_ #Hs >Hs in Hn; #Hn
lapply (term_comp_append … Ht1 Hn0 Hn) -t1 #H0 destruct
<(list_append_lcons_sn) in Hs; <list_append_empty_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #Hs -n -n0
/2 width=1 by/
qed-.

(* Inversions with preterm **************************************************)

lemma dbfs_preterm_inv_sn (t1) (t2) (r) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨p,b,q❩←𝐃❨t1,p,b,q,n❩]t1 ⇔ t2.
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
