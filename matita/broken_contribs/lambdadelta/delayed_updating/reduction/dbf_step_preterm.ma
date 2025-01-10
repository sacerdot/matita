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

include "delayed_updating/syntax/path_balanced_structure.ma".
include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions with preterm ************************************************)

axiom dbfs_preterm_trans (t1) (t2) (r):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐓.

(* Inversions with preterm **************************************************)

lemma dbfs_preterm_inv_sn (t1) (t2) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[⓪(p●𝗔◗b●𝗟◗q)] t2 →
      ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → (p●𝗔◗b●𝗟◗q)◖𝗱(⁤↑n) ϵ t1 →
      ⬕[↑(p●𝗔◗b●𝗟◗q)←(p●𝗔◗(⓪b)●𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t1]t1 ⇔ t2.
#t1 #t2 #p1 #b1 #q1 #n1 #Ht1
* #p2 #b2 #q2 #n2 #H0 #Hb2 #Hq2 #Hn2 #Ht2
#Hb1 #Hq1 #Hn1
lapply (term_clear_inj … Ht1 … H0) -H0
[1,2: /2 width=2 by term_in_root/ ] #H0
lapply (term_root_post … Ht1 (p1●𝗔◗b1●𝗟◗q1) (𝗱(⁤↑n1)) (⁤↑n2) ??)
[ <H0 ] [1,2: /2 width=2 by term_in_root/ ] -Ht1 -Hn1 -Hn2 #Hn
lapply (eq_inv_d_bi … Hn) -Hn #Hn
lapply (eq_inv_nsucc_bi … Hn) -Hn #Hn destruct
>path_append_pAbLq_5 in H0; >path_append_pAbLq_5 in ⊢ (%→?); #H0
lapply (pcc_inj_L_sn … Hq1 … Hq2 ?) -Hq1 -Hq2 [ // |2,3: skip ] #Hq destruct 
lapply (eq_inv_list_append_sn_bi … H0) -H0 #H0
lapply (path_eq_des_pAb_bi_pbc … Hb2 Hb1 H0) -Hb2 -Hb1 #H1 destruct
lapply (eq_inv_list_append_sn_bi … H0) -H0 #H0 destruct //
qed-.
