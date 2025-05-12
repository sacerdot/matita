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
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → r●x ϵ ⓪t → 𝐞◖𝗱𝟎 = x.
#t #r #x #p #b #q #n #Ht #Hr #Hx
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #H0 destruct
/4 width=5 by preterm_clear, term_comp_append, in_comp_term_clear_d_dx/
qed-.

lemma term_in_root_inv_xprc_append_dx (t) (r) (x) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → r●x ϵ ▵⓪t →
      ∨∨ 𝐞 = x | 𝐞◖𝗱𝟎 = x.
#t #r #x #p #b #q #n #Ht #Hr * #y #Hy
lapply (term_grafted_inv_gen … Hy) -Hy <list_append_assoc #Hy
lapply (term_in_comp_inv_xprc_append_dx … Ht Hr Hy) #H0 -t -r -p -b -q -n
elim (eq_inv_list_lcons_append ????? H0) -H0 *
[ #_ #H0 /2 width=1 by or_intror/
| #z #_ #H0
  elim (eq_inv_list_empty_append … H0) -H0 #_ #H0
  /2 width=1 by or_introl/
]
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
  elim (term_in_root_inv_xprc_append_dx … Ht Hr Hp2) -Ht -Hr -Hp2 #H0 destruct
  [ <list_append_empty_sn in H2x; #H0 destruct
    /2 width=1 by in_comp_term_clear/
  | <list_append_lcons_sn in H2x; <list_append_empty_sn <path_clear_S_dx #H0 destruct
  ]
| /2 width=1 by in_comp_slice_clear_inv_clear_sx/
]
qed-.

(* Destructions with preterm ************************************************)

lemma xprc_des_S (t) (r) (p) (b) (q) (n):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b,q,n❩ → p◖𝗦 ϵ ▵t.
#t #r #p #b #q #n #Ht #Hr
lapply (xprc_des_n … Hr) -Hr #Hn
/3 width=2 by term_full_A_post, term_in_root/
qed-.

(* Main destructions with preterm *******************************************)

theorem ol_des_xprc_bi (t) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
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

theorem path_le_des_xprc_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ⊑ r2 → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 * #s #_ #H0 destruct
lapply (xprc_des_r_clear … Hr1) -p1 -b1 -q1 -n1 #Hr1
lapply (xprc_des_r_clear … Hr2) -p2 -b2 -q2 -n2 #Hr2
lapply (preterm_clear … Ht) -Ht #Ht
lapply (term_comp_append … Ht Hr1 ?) -Hr1
[ /2 width=2 by term_in_root/ | skip ] -t #H0 destruct //
qed-.

theorem term_in_comp_clear_root_slice_inv_xprc_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
        t ϵ 𝐓 →
        r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
        r1 ϵ ⓪▵↑(p2◖𝗦) → r1 ϵ ⓪↑(p2◖𝗦).
/3 width=13 by term_in_comp_clear_root_slice_inv_xprc, xprc_des_S/
qed-.
