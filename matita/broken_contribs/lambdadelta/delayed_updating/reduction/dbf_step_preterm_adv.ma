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

include "ground/subsets/subset_or_eq.ma".
include "ground/subsets/subset_nimply_eq.ma".
include "ground/subsets/subset_listed_or_eq.ma".
include "ground/subsets/subset_listed_nimply_eq.ma".
include "delayed_updating/syntax/prototerm_or.ma".
include "delayed_updating/syntax/prototerm_nimply.ma".
include "delayed_updating/reduction/prototerm_xfocus_ol.ma".
include "delayed_updating/reduction/prototerm_delayed_eq.ma".
include "delayed_updating/reduction/prototerm_delayed_ol.ma".
include "delayed_updating/reduction/preterm_xfocus_reducible.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Advanced destructions with preterm ***************************************)

lemma dbfs_des_grafted_nol (t1) (t2) (r) (p1) (p2) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p1,b,q,n❩ →
      ↑(p1◖𝗔) ⧸≬ ↑p2 → ⋔[p2]t1 ⇔ ⋔[p2]t2.
#t1 #t2 #r #p1 #p2 #b #q #n #Ht1 #Ht12 #Hr #Hp12
lapply (xprc_des_n … Hr) #Hn
lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr) -r -Ht1 #Ht12
lapply (subset_eq_trans … (fsubst_eq …) … Ht12) -Ht12
[ /2 width=3 by subset_ol_i/ ] -Hn #Ht12
@(subset_eq_trans … (term_grafted_eq_repl … Ht12)) -t2
@(subset_eq_trans … (term_grafted_or …))
@(subset_eq_trans … (subset_or_eq_repl …))
[2: @subset_eq_refl |4: @grafted_brd_nol // |3,5: skip ]
@(subset_eq_trans ????? (subset_eq_or_dx_empty_refl …))
@(subset_eq_trans … (term_grafted_nimp …))
@(subset_eq_trans … (subset_nimp_eq_repl …))
[ @subset_eq_nimp_dx_refl_empty | @grafted_brxf_nol // | // |*: skip ]
qed-.

lemma dbfs_des_grafted_full (t1) (t2) (r) (p) (b) (q) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p,b,q,n❩ →
      (⋔[p◖𝗦]t1) ⇔ ⋔[𝐫❨p,⓪b,q,⁤↑(♭b+n)❩]t2.
#t1 #t2 #r #p #b #q #n #Ht1 #Ht12 #Hr
lapply (xprc_des_b … Hr) #Hb
lapply (xprc_des_n … Hr) #Hn
lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr) #Ht12
lapply (subset_eq_trans … (fsubst_eq …) … Ht12) -Ht12
[ /2 width=3 by subset_ol_i/ ] -Hn #Ht12
@(subset_eq_trans … (term_grafted_eq_repl … Ht12)) -t2
@(subset_eq_trans … (term_grafted_or …))
@(subset_eq_trans … (subset_or_eq_repl …))
[ @subset_eq_or_dx_refl_empty |4: @term_grafted_pt_append |3,5: skip ]
@(subset_eq_trans … (term_grafted_nimp …))
@subset_eq_empty_nimp
@(le_grafted_full_bi_brxf_dx … Ht1 Hr) -t1 -r -p -q -n //
qed-.
