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

include "delayed_updating/unwind/preterm_balanced_structure.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Destructions by term_root_L_post *****************************************)

(* Note: this holds but is not necessary
axiom dbfs_xprc_chain_p (t1) (t2) (r1) (r2) (p) (b1) (b2) (q1) (q) (q2) (n1) (n2):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r1] t2 → r1 ϵ 𝐑❨t1,p,b1,q1,n1❩ →
      r2 ϵ 𝐑❨t2,p●𝗔◗b1●𝗟◗q,b2,q2,n2❩ → r2 ϵ 𝐑❨t2,p●𝗔◗⓪b1●𝗟◗q,b2,q2,n2❩.
*)

lemma dbfs_des_xprc_chain_b (t1) (t2) (r1) (r2) (p) (b1) (b2) (q1) (q2) (n1) (n2):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r1] t2 → r1 ϵ 𝐑❨t1,p,b1,q1,n1❩ →
      r2 ϵ 𝐑❨t2,p,b2,q2,n2❩ → ⓪b1 = b2.
#t1 #t2 #r1 #r2 #p #b1 #b2 #q1 #q2 #n1 #n2 #Ht1 #Ht12 #Hr1 #Hr2
lapply (xprc_des_b … Hr1) >path_structure_clear #Hb1
lapply (xprc_des_n … Hr1) #Hn1
elim (term_full_A_post … Ht1 p) [| /2 width=2 by term_in_root/ ] #x #Hx
lapply (dbfs_preterm_trans … Ht1 … Ht12) #Ht2
lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr1) -Ht1 -Ht12 -Hr1 #Ht12
lapply (in_comp_brd t1 p x b1 q1 n1 Hx) -Hx #Hx
lapply (subset_in_eq_repl_fwd ????? Ht12) -Ht12
[ @(fsubst_in_comp_true … Hx) /2 width=3 by subset_ol_i/ | skip ] -t1
<(list_append_rcons_sn … (𝗔)) #Hx
lapply (xprc_des_b … Hr2) #Hb2
lapply (xprc_des_n … Hr2) -Hr2 #Hn2
@(term_in_comp_structure_pbc_L_inj … Ht2 Hb1 Hb2) -Ht2 -Hb1 -Hb2
[4,5: // |*: skip ]
qed-.
