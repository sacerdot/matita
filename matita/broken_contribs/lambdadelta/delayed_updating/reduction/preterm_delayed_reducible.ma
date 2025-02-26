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

include "ground/subsets/subset_and_ol.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_clear_ol.ma".
include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible_clear.ma".
include "delayed_updating/reduction/prototerm_delayed_reducible.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Destructions with xprc and preterm ***************************************)

lemma and_clear_brd_dx_xprc (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ →
      ⓪t ∩ ⓪𝐃❨t,p,b,q,n❩ ⊆ Ⓕ.
#t #r #p #b #q #n #H1t #Hr #s1 * #H1s1 #H2s1
lapply (clear_brd_xprc_sx … Hr … H2s1) -H2s1
* #s2 * #s3 #Hs3 #H2 #H1 destruct
lapply (xprc_des_r_clear … Hr) -b -q -n #Hr
lapply (preterm_clear … H1t) #H2t
lapply (term_comp_append … H2t Hr H1s1) -H2t -Hr -H1s1
>list_cons_comm in ⊢ (??%?→?); #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_ destruct
lapply (in_comp_inv_term_empty_clear … Hs3) -Hs3 #H0
lapply (term_grafted_inv_gen … H0) -H0 #H0
elim (term_proper_S_post … H1t … H0)
qed-.

lemma nol_brd_dx_xprc (t) (t1) (r2) (p2) (b2) (q2) (n2):
      t ϵ 𝐓 → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (t ∩ t1) ⧸≬ 𝐃❨t,p2,b2,q2,n2❩.
#t #t1 #r2 #p2 #b2 #q2 #n2 #Ht #Hr2 #H0
lapply (subset_ol_and_sx … H0) -H0 #H0
lapply (clear_ol … H0) -H0 * #s #_ -t1 #Hs
lapply (clear_and_dx … Hs) -Hs #Hs
lapply (and_clear_brd_dx_xprc … Ht Hr2 … Hs) -t -r2 -p2 -b2 -q2 -n2
/2 width=3 by subset_nin_inv_empty/
qed-.
