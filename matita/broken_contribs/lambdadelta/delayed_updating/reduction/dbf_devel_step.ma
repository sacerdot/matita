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

include "ground/xoa/ex_4_1.ma".
include "delayed_updating/substitution/fsubst_fsubst.ma".
include "delayed_updating/reduction/prototerm_xfocus_ol.ma".
include "delayed_updating/reduction/prototerm_delayed_ol.ma".
include "delayed_updating/reduction/prototerm_delayed_reducible.ma".
include "delayed_updating/reduction/preterm_delayed_xfocus_reducible.ma".
include "delayed_updating/reduction/dbf_step_preterm_main.ma".
include "delayed_updating/reduction/dbf_devel_preterm.ma".

(* COMPLETE DEVELOPMENT FOR DELAYED BALANCED FOCUSED REDUCTION **************)

(* Constructions with dbfs **************************************************)

(* UPDATE *)

lemma dbf_step_conf_local_ol (t0) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      r1 ϵ ⓪▵↑(p2◖𝗦) → r2 ϵ ⓪▵↑(p1◖𝗦) → ⊥.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hp21 #Hp12
lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr01 Hr02 Hp21) [ // ] -Hp21 #Hp21
lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr02 Hr01 Hp12) [ // ] -Hp12 #Hp12
lapply (xprc_des_ol_pA_sn … Hr01 Hp21) -Hp21 #Hp21
lapply (xprc_des_ol_pA_sn … Hr02 Hp12) -Hp12 #Hp12
lapply (term_ol_des_clear_slice_bi … Hp21) -Hp21 #Hp21
lapply (term_ol_des_clear_slice_bi … Hp12) -Hp12 #Hp12
lapply (term_ol_des_slice_rcons_bi … Hp12 Hp21) -p1 -p2 #H0 destruct
qed-.

lemma dbf_step_conf_local_nol (t0) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      (r2 = r1 → ⊥) → (r1 ϵ ⓪▵↑(p2◖𝗦) → ⊥) → (r2 ϵ ⓪▵↑(p1◖𝗦) → ⊥) →
      ∃∃t. t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] t &
           r1 ϵ 𝐑❨t2,p1,b1,q1,n1❩ & r2 ϵ 𝐑❨t1,p2,b2,q2,n2❩.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hnr21 #Hp21 #Hp12
lapply (dbfs_preterm_trans … Ht0 Ht01) #Ht1
lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
lapply (dbfs_des_xprc_neq … Ht0 Ht01 Hnr21 Hr02) #Hr12
lapply (dbfs_des_xprc_neq … Ht0 Ht02 … Hr01) [ /2 width=1 by/ ] #Hr21
lapply (dbfs_preterm_inv_sn … Ht0 Ht01 Hr01) -Ht01 #Ht01
lapply (dbfs_preterm_inv_sn … Ht0 Ht02 Hr02) -Ht02 #Ht02
elim (xprc_dbfs … Hr12) #t3 #Ht13
elim (xprc_dbfs … Hr21) #t4 #Ht24
cut (t3 ⇔ t4)
[ lapply (dbfs_preterm_inv_sn … Ht1 Ht13 Hr12) -Ht13 -Hr12 #Ht13
  lapply (dbfs_preterm_inv_sn … Ht2 Ht24 Hr21) -Ht24 -Hr21 #Ht24
  @(fsubst_fsubst_inv_eq ?????????????????? Ht01 Ht02 Ht13 Ht24) -t3 -t4
  [ @fsubst_fsubst_nol_eq
    [ /2 width=3 by brxf_ol_sn/
    | /2 width=3 by brxf_ol_sn/
    | /3 width=16 by neq_inv_xprc_bi_brxf/
    | /3 width=17 by neq_inv_xprc_bi_brxf_brd/
    | /4 width=17 by neq_inv_xprc_bi_brxf_brd, sym_eq/
    ]
  |2,3: @subset_eq_refl
  | @(brd_fsubst_false_eq_repl_fwd … Ht01)
    [ /3 width=7 by term_in_root_brxf_des_xprc/ | /3 width=7 by term_in_root_brd_des_xprc/ ]
  | @(brd_fsubst_false_eq_repl_fwd … Ht02)
    [ /3 width=7 by term_in_root_brxf_des_xprc/ | /3 width=7 by term_in_root_brd_des_xprc/ ]
  ]
| #Ht34
  @(ex4_intro … Ht13 … Hr21 Hr12)
  /2 width=5 by dbfs_eq_canc_dx/
]
qed-.

lemma dbf_step_conf_local_le (t0) (t1) (t2) (r1) (r2) (p1) (p2) (x) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      (r2 = r1 → ⊥) → (r2 ϵ ⓪▵↑(p1◖𝗦) → ⊥) →
      x◖𝗱⁤↑n1 ϵ ⋔[p2◖𝗦]t0 → ⓪(p2◖𝗦)●⓪x=r1 →
      ∃∃u,t. t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] u & u ➡𝐝𝐛𝐟[r2◖𝗱𝟎●⓪x] t.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #x #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hnr21 #Hp12 #Hx #H0 destruct
lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
lapply (dbfs_des_xprc_neq … Ht0 Ht01 Hnr21 Hr02) #Hr12
elim (xprc_dbfs … Hr12) #t3 #Ht13
lapply (dbfs_des_xprc_neq … Ht0 Ht02 … Hr01) [ /2 width=1 by/ ] #Hr21
elim (xprc_dbfs … Hr21) #t4 #Ht24
elim (dbfs_inv_reducible_side … Ht0 Ht02 Hr02 Hx Hr01)
* #y #H1 #H2 destruct #Hy
elim (xprc_dbfs … Hy) #t6 #Ht26
elim (dbf_step_conf_local_nol … Ht2 Ht24 Ht26 Hr21 Hy) (* -Ht24 -Ht26 *)
[1,5: |*: #H0 ]
[|
| -Ht0 -Ht02 -Ht2 -Hx -Ht01 -Hnr21 -Hr01 -Hr21
  elim (term_in_comp_clear_root_slice_inv_xprc_gen … Hy H0) -Hy -H0 #x1 #x2
  >list_append_rcons_sn <list_append_assoc #H0
  /3 width=6 by term_in_comp_clear_root_slice_xprc_dx/
| -Ht0 -Ht02 -Hp12 -Ht2 -Hr02 -Hx -Ht01 -Hnr21 -Hr01 -Hr21 -Hy
  >path_clear_append in H0; #H0
  lapply (term_ol_clear_slice_bi … H0) -H0 #H0
  elim (term_ol_clear_slice_bi_inv_gen … H0) -H0 #x1 #x2
  <path_clear_append <list_append_assoc <path_clear_S_dx >list_append_rcons_sn
  <path_append_pAbLq_1 <list_append_assoc <path_clear_S_dx
  >list_append_rcons_sn in ⊢ ((???%)→?);
  <path_clear_append in ⊢ ((???%)→?); <list_append_assoc in ⊢ ((???%)→?);
  <path_clear_A_dx >list_append_rcons_sn in ⊢ ((???%)→?); #H0
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| -Ht02 -Hp12 -Ht2 -Hx -Ht01 -Hnr21 -Hr01 -Hr21 -Hy
  >list_append_rcons_sn in H0; #H0
  lapply (term_in_comp_clear_root_slice_xprc_dx … Hr02 H0) -H0 #H0
  /2 width=9 by rp_nin_root_side/
| -Ht0 -Ht02 -Hp12 -Hr02 -Hx -Ht01 -Hnr21 -Hr01 -Hr21
  /2 width=9 by rp_nin_root_side/
| -Ht0 -Ht02 -Hp12 -Ht2 -Hr02 -Hx -Ht01 -Hnr21 -Hr01 -Hr21 -Hy
  >path_clear_append in H0; #H0
  lapply (term_ol_clear_slice_bi … H0) -H0 #H0
  elim (term_ol_clear_slice_bi_inv_gen … H0) -H0 #x1 #x2
  <path_append_pAbLq_1 <path_clear_append <list_append_assoc
  <path_clear_S_dx >list_append_rcons_sn <path_clear_append <list_append_assoc
  <path_clear_A_dx <path_clear_S_dx
  >list_append_rcons_sn >list_append_rcons_sn in ⊢ ((???%)→?); #H0
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| -Ht0 -Ht02 -Hp12 -Ht2 -Hr02 -Hx -Ht01 -Hnr21 -Hr01 -Hr21 -Hy
  lapply (eq_inv_list_append_sn_bi … H0) -H0
  <path_clear_S_dx #H0 destruct
]
#t5 #Ht45 #_ #_ #Hr45
cut (t3 ⇔ t5)
[2,4: #Ht35
  @(ex3_2_intro … Ht13 Ht24) /2 width=4 by dbfs_eq_canc_dx/
|*: -Hy -Ht26
  lapply (dbfs_preterm_trans … Ht0 Ht01) #Ht1
  lapply (dbfs_preterm_trans … Ht2 Ht24) #Ht4
  lapply (dbfs_preterm_inv_sn … Ht0 Ht01 Hr01) -Ht01 -Hr01 #Ht01
  lapply (dbfs_preterm_inv_sn … Ht0 Ht02 Hr02) -Ht02 -Hr02 #Ht02
  lapply (dbfs_preterm_inv_sn … Ht1 Ht13 Hr12) -Ht13 -Hr12 #Ht13
  lapply (dbfs_preterm_inv_sn … Ht2 Ht24 Hr21) -Ht24 -Hr21 #Ht24
  lapply (dbfs_preterm_inv_sn … Ht4 Ht45 Hr45) -Ht45 -Hr45 #Ht45
  @(fsubst_fsubst_fsubst_inv_eq ????????????????????? ???? Ht01 Ht02 Ht13 Ht24 Ht45) -t3 -t5
  [4,5,13,14: @subset_eq_refl
  |6,15: @(brd_fsubst_true_eq_repl_fwd … Ht01)

  |1,2,10,11: skip
  |7,16: @(brd_fsubst_false_eq_repl_fwd … Ht02)
    [ /2 width=5 by nin_root_brxf_side/
    | /2 width=7 by nin_root_brd_side/
    | /2 width=5 by nin_root_brxf_side_trunk/
    | /2 width=7 by nin_root_brd_side_trunk/
    ]
  |8: @brd_brxf_append_p |17: @brd_brxf_append_q
  |9: @brd_brd_append_p
  |18:

  |3: (* argument moved *)
  |12: (* argument not moved *)
  ]
]

(*
lemma dbf_step_conf_local (t0) (t1) (t2) (r1) (r2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      ∃∃t. t1 ⫽➡𝐝𝐛𝐟[r2 /𝐝𝐛𝐟{t0} r1] t & t2 ⫽➡𝐝𝐛𝐟[r1 /𝐝𝐛𝐟{t0} r2] t.
#t0 #t1 #t2 #r1 #r2 #Ht0 #Ht01 #Ht02
elim (eq_path_dec r2 r1) #Hnr21 destruct
[ lapply (dbfs_preterm_mono … Ht0 Ht01 Ht02) -Ht0 -Ht01 -Ht02 #Ht12
  /3 width=3 by dbfd_self, ex2_intro/
| cases Ht01 #p1 #b1 #q1 #n1 #Hr01 #_
  cases Ht02 #p2 #b2 #q2 #n2 #Hr02 #_
  elim (term_in_comp_clear_root_slice_dec_xprc … (p2◖𝗦) … Hr01) #Hp21
  elim (term_in_comp_clear_root_slice_dec_xprc … (p1◖𝗦) … Hr02) #Hp12
  [ elim (dbf_step_conf_local_ol … Ht0 Ht01 Ht02 Hr01 Hr02 Hp21 Hp12)
  | lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr01 Hr02 Hp21) [ // ] -Hp21 #Hp21
    elim (xprc_des_clear_slice … Hr01 Hp21) -Hp21
    [ #x #Hx #H0 | /2 width=5 by xprc_des_side/ | // ]
    elim (dbf_step_conf_local_le … Ht0 Ht01 Ht02 Hr01 Hr02 … Hx H0)
    [ -Ht0 -Ht01 -Ht02 -Hr01 -Hr02 -Hnr21 -Hp12 -Hx -H0 #u #t #Ht10 #Ht2u0 #Hut0 |*: /2 width=1 by/ ]

  | lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr02 Hr01 Hp12) [ // ] -Hp12 #Hp12
    elim (xprc_des_clear_slice … Hr02 Hp12) -Hp12
    [ #x #Hx #H0 | /2 width=5 by xprc_des_side/ | // ]
    elim (dbf_step_conf_local_le … Ht0 Ht02 Ht01 Hr02 Hr01 … Hx H0)
    [ -Ht0 -Ht01 -Ht02 -Hr01 -Hr02 -Hnr21 -Hp21 -Hx -H0 #u #t #Ht20 #Ht1u0 #Hut0 |*: /2 width=1 by/ ]

  | elim (dbf_step_conf_local_nol … Ht0 Ht01 Ht02 Hr01 Hr02 Hnr21 Hp21 Hp12) #t #Ht1 #Ht2
    /4 width=6 by dbfs_neq_dbfd, xprc_des_clear, ex2_intro/
  ]
]
*)
