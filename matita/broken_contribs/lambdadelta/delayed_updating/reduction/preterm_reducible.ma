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

include "ground/subsets/subset_ol.ma".
include "delayed_updating/syntax/path_balanced_structure.ma".
include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Main destructions with preterm *******************************************)

theorem xprc_des_ol (t) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 → 𝐑❨t,p1,b1,q1,n1❩ ≬ 𝐑❨t,p2,b2,q2,n2❩ →
        ∧∧ p1 = p2 & b1 = b2 & q1 = q2 & n1 = n2.
#t #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht * #r
* #Hr #Hb1 #Hq1 #Hn1 * #H0 #Hb2 #Hq2 #Hn2 destruct
lapply (term_clear_inj … Ht … H0) -H0
[1,2: /2 width=2 by term_in_root/ ] #H0
lapply (term_root_post … Ht (p1●𝗔◗b1●𝗟◗q1) (𝗱(⁤↑n1)) (⁤↑n2) ??)
[ <H0 ] [1,2: /2 width=2 by term_in_root/ ] -Ht -Hn1 -Hn2 #Hn
lapply (eq_inv_d_bi … Hn) -Hn #Hn
lapply (eq_inv_nsucc_bi … Hn) -Hn #Hn destruct
>path_append_pAbLq_5 in H0; >path_append_pAbLq_5 in ⊢ (%→?); #H0
lapply (pcc_inj_L_sn … Hq1 … Hq2 ?) -Hq1 -Hq2 [ // |2,3: skip ] #Hq destruct
lapply (eq_inv_list_append_sn_bi … H0) -H0 #H0
lapply (path_eq_des_pAb_bi_pbc … Hb2 Hb1 H0) -Hb2 -Hb1 #H1 destruct
lapply (eq_inv_list_append_sn_bi … H0) -H0 #H0 destruct
/2 width=1 by and4_intro/
qed-.
