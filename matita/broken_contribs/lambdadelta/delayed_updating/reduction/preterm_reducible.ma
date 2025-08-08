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

include "delayed_updating/syntax/path_le.ma".
include "delayed_updating/syntax/path_balanced_structure.ma".
include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible_clear.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Inversions with preterm **************************************************)

lemma term_in_comp_inv_xprc_append_dx (t) (r) (x) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → r●x ϵ ⓪t → 𝐞 = x.
#t #r #x #p #b #q #n #Ht #Hr #Hx
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #H0 destruct
/3 width=5 by preterm_clear, in_comp_term_clear, term_complete_append/
qed-.

lemma term_in_root_inv_xprc_append_dx (t) (r) (x) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → r●x ϵ ▵⓪t → 𝐞 = x.
#t #r #x #p #b #q #n #Ht #Hr * #y #Hy
lapply (term_grafted_inv_gen … Hy) -Hy <list_append_assoc #Hy
lapply (term_in_comp_inv_xprc_append_dx … Ht Hr Hy) -t #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 //
qed-.

lemma term_in_comp_clear_root_slice_inv_xprc (t) (r) (p1) (p2) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p1,b,q,n❩ → p2◖𝗦 ϵ ▵t →
      r ϵ ⓪▵↑(p2◖𝗦) → r ϵ ⓪↑(p2◖𝗦).
#t #r #p1 #p2 #b #q #n #Ht #Hr #Hp2
<(xprc_des_clear … Hr) #H0
lapply (term_ol_clear_slice_bi … H0) -H0 #H0
elim (term_ol_clear_slice_bi_inv_gen … H0) -H0 #s #q2 #H0
elim (eq_inv_list_append_bi … H0) -H0 * #x #H1x #H2x
[ -s -q2
  >(xprc_des_clear … Hr) in H2x; #H2x
  lapply (in_comp_term_clear … Hp2) -Hp2 #Hp2
  lapply (term_le_root_clear … Hp2) -Hp2 >H2x #Hp2
  lapply (term_in_root_inv_xprc_append_dx … Ht Hr Hp2) -Ht -Hr -Hp2 #H0 destruct
  <list_append_empty_sn in H2x; #H0 destruct
  /2 width=1 by in_comp_term_clear/
| /2 width=1 by in_comp_slice_clear_inv_clear_sx/
]
qed-.

(* Destructions with preterm ************************************************)

lemma xprc_des_side (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → p◖𝗦 ϵ ▵t.
#t #r #p #b #q #n #Ht #Hr
lapply (xprc_des_n … Hr) -Hr #Hn
/3 width=4 by term_full_A_post, path_beta_pA_in_root/
qed-.

lemma xprc_des_clear_slice (t) (r) (p1) (p2) (b1) (q1) (n1):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p1,b1,q1,n1❩ → r ϵ ⓪↑p2 → p2 ϵ ▵t →
      ∃∃q2. q2 ϵ ⋔[p2]t & ⓪p2●⓪q2 = r.
#t #r #p1 #p2 #b1 #q1 #n1 #Ht #H1r #H2r #Hp2
elim (in_comp_inv_term_clear_slice … H2r) -H2r #q0 #H0 #_ destruct
lapply (xprc_des_n … H1r) #Hn1
lapply (xprc_des_r … H1r) -H1r #Hr
lapply (sym_eq ??? Hr) -Hr #H0
elim (eq_inv_path_append_clear … H0) -H0 #y2 #y0 #Hy2 #Hy0 #Hy
lapply (term_clear_inj … Ht Hp2 … Hy2) -Ht -Hp2 -Hy2
[ /2 width=2 by term_in_root/ ] #H0 destruct
>Hy0 <Hy in Hn1; -p1 -b1 -q1 -q0 #Hy
/2 width=3 by ex2_intro/
qed-.

(* Advanced inversions with preterm *****************************************)

lemma rp_nin_root_side (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → r ⧸ϵ ⓪▵↑(p◖𝗦).
#t #r #p #b #q #n #Ht #Hr #Hnr
lapply (term_in_comp_clear_root_slice_inv_xprc … Ht Hr … Hnr) -Hnr
[ /2 width=5 by xprc_des_side/ ] #Hnr
lapply (xprc_des_ol_pA_sn … Hr Hnr) -t -r -b -q -n #H0
elim (term_ol_clear_slice_bi_inv_gen … H0) -H0 #q1 #q2
<path_clear_A_dx <path_clear_S_dx
>list_append_rcons_sn >list_append_rcons_sn in ⊢ ((???%)→?); #H0
lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed-.

(* Main destructions with preterm *******************************************)

theorem ol_des_xprc_bi (t) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 → 𝐑❨t,p1,b1,q1,n1❩ ≬ 𝐑❨t,p2,b2,q2,n2❩ →
        ∧∧ p1 = p2 & b1 = b2 & q1 = q2 & n1 = n2.
#t #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht * #r
* #Hr #Hb1 #Hq1 #Hn1 * #H0 #Hb2 #Hq2 #Hn2 destruct
lapply (term_clear_inj … Ht … H0) -H0
[1,2: /2 width=2 by term_in_root/ ] #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #H2 #H1
lapply (eq_inv_d_bi … H2) -H2 #H2
lapply (eq_inv_nsucc_bi … H2) -H2 #H2 destruct
lapply (pcc_inj_L_sn … Hq2 … Hq1 H1) -Hq1 -Hq2 #H0 destruct
lapply (eq_inv_list_append_sn_bi … H1) -H1 #H1
elim (eq_inv_list_lcons_bi ????? H1) -H1 #_ #H1
lapply (path_eq_des_pAb_bi_pbc … Hb2 Hb1 H1) -Hb2 -Hb1 #H0 destruct
lapply (eq_inv_list_append_sn_bi … H1) -H1 #H destruct
/2 width=1 by and4_intro/
qed-.

theorem path_le_des_xprc_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ⊑ r2 → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 * #s #_ #H0 destruct
lapply (xprc_des_r_clear … Hr1) -p1 -b1 -q1 -n1 #Hr1
lapply (xprc_des_r_clear … Hr2) -p2 -b2 -q2 -n2 #Hr2
lapply (preterm_clear … Ht) -Ht #Ht
lapply (term_complete_append … Ht Hr1 ?) -Hr1
[ /2 width=2 by term_in_root/ | skip ] -t #H0 destruct //
qed-.

theorem term_in_comp_clear_root_slice_inv_xprc_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ϵ ⓪▵↑(p2◖𝗦) → r1 ϵ ⓪↑(p2◖𝗦).
/3 width=13 by term_in_comp_clear_root_slice_inv_xprc, xprc_des_side/
qed-.
