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

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/preterm_root_eq_clear.ma".
include "delayed_updating/reduction/prototerm_x_focus_root_le.ma".
include "delayed_updating/reduction/prototerm_x_focus_cx_redex_clear.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Destructions with pcxr and preterm and clear *****************************)

lemma ol_des_clear_brxf_preterm_pcxr_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      (⓪𝐅❨p1,b1,q1,n1❩ ≬ ⓪𝐅❨p2,b2,q2,n2❩) → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #H0
lapply (ol_des_clear_brxf_pcxr_bi … Hr1 Hr2 H0) -H0 #Hr
@(path_req_in_comp_inv_clear_bi … Ht … Hr) -Ht -Hr
/2 width=5 by pcxr_des_r/
qed-.

(* Inversions with pcxr and preterm and clear *******************************)

lemma neq_inv_preterm_pcxr_bi_clear_brxf (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (⓪𝐅❨p1,b1,q1,n1❩ ⧸≬ ⓪𝐅❨p2,b2,q2,n2❩).
/3 width=13 by ol_des_clear_brxf_preterm_pcxr_bi/
qed-.

lemma preterm_nol_brxf (t1) (t2) (r) (x) (p1) (p2) (b1) (b2) (q1) (q2) (l) (n1) (n2):
      t1 ϵ 𝐓 →
      r ϵ 𝐑❨t1, p1, b1, q1, n1❩ →
      (𝐫❨p1,⓪b1,q1,⁤↑(♭b1+n1)❩●(x◖l) ϵ 𝐑❨t2, p2, b2, q2, n2❩) →
      t1 ⧸≬ 𝐅❨p2, b2, q2, n2❩.
#t1 #t2 #r #x #p1 #p2 #b1 #b2 #q1 #q2 #l #n1 #n2 #Ht1 #Hr #Hx
* #y #H1y #H2y
lapply (in_comp_brxf_inv_rle … H2y) -H2y #H2y
lapply (path_rle_in_comp_trans … H2y H1y) -y #H0
lapply (pcxr_des_n … Hr) -r #Hn1
lapply (pcxr_des_eq … Hx) -t2 #Hx
>Hx in H0; #H0 -p2 -b2 -q2 -n2
lapply (preterm_clear … Ht1) -Ht1 #Ht1
lapply (in_comp_term_clear … Hn1) -Hn1 #Hn1
lapply (in_comp_term_clear … H0) -H0
<path_clear_append <path_clear_rcons <(path_clear_beta_b … (⁤↑n1)) #H0
lapply (term_le_root_clear … H0) -H0 #H0
(* Note: the next may go in preterm_root_eq *)
lapply (path_rle_inv_complete_head_dx … Ht1 Hn1 H0 ?) -t1 [ // ] #H0
lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0 destruct
qed-.
