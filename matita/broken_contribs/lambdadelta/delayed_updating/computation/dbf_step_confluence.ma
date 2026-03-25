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
include "delayed_updating/syntax/path_beta_tl.ma".
include "delayed_updating/syntax/path_beta_root_eq.ma".
include "delayed_updating/substitution/fsubst_fsubst.ma".
include "delayed_updating/reduction/prototerm_x_redex_root_eq.ma".
include "delayed_updating/reduction/prototerm_x_focus_ol.ma".
include "delayed_updating/reduction/prototerm_delayed_ol.ma".
include "delayed_updating/reduction/prototerm_delayed_cx_redex.ma".
include "delayed_updating/reduction/preterm_cx_redex_clear.ma".
include "delayed_updating/reduction/preterm_delayed_x_focus_cx_redex.ma".
include "delayed_updating/reduction/dbf_step_inv.ma".
include "delayed_updating/reduction/dbf_step_adv.ma".
include "delayed_updating/reduction/dbf_step_preterm_post.ma".
include "delayed_updating/computation/dbf_dsteps_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Advanced constructions ***************************************************)

(* UPDATE *)

lemma dbf_step_conf_nol (t0) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      r2 ⧸= r1 → p2◖𝗦 ⧸≚ r1 → p1◖𝗦 ⧸≚ r2 →
      ∃∃t. t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] t &
           r1 ϵ 𝐑❨t2,p1,b1,q1,n1❩ & r2 ϵ 𝐑❨t1,p2,b2,q2,n2❩.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hnr21 #Hp21 #Hp12
lapply (dbfs_preterm_trans … Ht0 Ht01) #Ht1
lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
lapply (dbfs_des_pcxr_neq … Ht0 Ht01 Hnr21 Hr02) #Hr12
lapply (dbfs_des_pcxr_neq … Ht0 Ht02 … Hr01) [ /2 width=1 by/ ] #Hr21
lapply (dbfs_inv_pcxr_sx … Ht01 Hr01) -Ht01 #Ht01
lapply (dbfs_inv_pcxr_sx … Ht02 Hr02) -Ht02 #Ht02
elim (pcxr_dbfs … Hr12) #t3 #Ht13
elim (pcxr_dbfs … Hr21) #t4 #Ht24
cut (t3 ⇔ t4)
[ lapply (dbfs_inv_pcxr_sx … Ht13 Hr12) -Ht13 -Hr12 #Ht13
  lapply (dbfs_inv_pcxr_sx … Ht24 Hr21) -Ht24 -Hr21 #Ht24
  @(fsubst_2_inv_eq ?????????????????? Ht01 Ht02 Ht13 Ht24) -t3 -t4
  [ @fsubst_2_swap_eq
    [ /2 width=3 by brxf_ol_sx/
    | /2 width=3 by brxf_ol_sx/
    | /3 width=16 by neq_inv_pcxr_bi_preterm_brxf/
    | /3 width=17 by neq_inv_preterm_pcxr_bi_brxf_brd/
    | /4 width=17 by neq_inv_preterm_pcxr_bi_brxf_brd, sym_eq/
    ]
  |2,3: @subset_eq_refl
  | @(brd_fsubst_false_eq_repl_fwd … Ht01)
    [ /3 width=7 by root_brxf_des_pcxr/
    | /4 width=12 by term_in_root_brd_des_pcxr, req_inv_clear_bi_side_pcxr/
    ]
  | @(brd_fsubst_false_eq_repl_fwd … Ht02)
    [ /3 width=7 by root_brxf_des_pcxr/
    | /4 width=12 by term_in_root_brd_des_pcxr, req_inv_clear_bi_side_pcxr/
    ]
  ]
| #Ht34
  @(ex4_intro … Ht13 … Hr21 Hr12)
  /2 width=5 by dbfs_eq_canc_dx/
]
qed-.

lemma dbf_step_conf_le (t0) (t1) (t2) (r1) (r2) (p1) (p2) (x) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      (r2 = r1 → ⊥) → p1◖𝗦 ⧸≚ r2 → (p2◖𝗦)●x = r1 →
      ∃∃u,t. t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] u & u ➡𝐝𝐛𝐟[𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●x] t.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #x #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hnr21 #Hp12 #H0 destruct
lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
lapply (dbfs_des_pcxr_neq … Ht0 Ht01 Hnr21 Hr02) #Hr12
elim (pcxr_dbfs … Hr12) #t3 #Ht13
lapply (dbfs_des_pcxr_neq … Ht0 Ht02 … Hr01) [ /2 width=1 by/ ] #Hr21
elim (pcxr_dbfs … Hr21) #t4 #Ht24
elim (dbfs_inv_pcxr_side … Ht02 Hr02 Hr01)
* #y #H1 #H2 #Hy destruct
elim (pcxr_dbfs … Hy) #t6 #Ht26 (* -Ht24 -Ht26 *)
elim (dbf_step_conf_nol … Ht2 Ht24 Ht26 Hr21 Hy)
[1,5: |*: #H0 ]
[|
| -t0 -t1 -t2 -t3 -t4 -t6 -r2
  /2 width=7 by path_nreq_side_p_beta/
| -t0 -t1 -t2 -t3 -t4 -t6 -r2
  /3 width=7 by path_nreq_side_p_beta, path_req_sym/
| -t0 -t1 -t2 -t3 -t4 -t6 -r2
  /3 width=7 by path_neq_p_beta, sym_eq/
| -t0 -t1 -t2 -t3 -t4 -t6 -r2 -q1 -n1
  <path_beta_append_p in H0;
  /2 width=6 by path_nreq_side_p_p3beta/
| -t0 -t1 -t2 -t3 -t4 -t6 -r2 -b2 -q1 -q2 -n1 -n2
  /2 width=6 by path_nreq_side_p_p3beta/
| -t0 -t1 -t2 -t3 -t4 -t6 -r2 -q1 -n1
  /3 width=7 by path_neq_p_beta, sym_eq/
]
#t5 #Ht45 #_ #_ #Hr45 -t6
cut (t3 ⇔ t5)
[2,4: #Ht35
  @(ex3_2_intro … Ht13 Ht24)
  @(dbfs_eq_canc_dx … Ht45) //
|1:|3:
  lapply (dbfs_des_pcxr_chain_b … Ht2 Ht24 Hr21 Hr45) #H0b
(* Note: alternative
  lapply (dbfs_des_pcxr_chain_p … Ht0 Ht01 Hr01 Hr12) #H0b
*)
]
lapply (dbfs_inv_pcxr_sx … Ht01 Hr01) -Ht01 (* -Hr01 *) #Hs01
lapply (dbfs_inv_pcxr_sx … Ht02 Hr02) (* -Ht02 -Hr02 *) #Hs02
lapply (dbfs_inv_pcxr_sx … Ht13 Hr12) -Ht13 -Hr12 #Hs13
lapply (dbfs_inv_pcxr_sx … Ht24 Hr21) (* -Ht24 -Hr21 *) #Hs24
lapply (dbfs_inv_pcxr_sx … Ht45 Hr45) -Ht45 -Hr45 #Hs45
@(fsubst_3_inv_eq ????????????????????????? Hs01 Hs02 Hs13 Hs24 Hs45) -t3 -t5
[4,5,13,14: @subset_eq_refl
|7,16:
  @(brd_fsubst_true_eq_repl_fwd … Hs01)
  @term_ol_grafted_bi [2,5: /2 width=6 by pcxr_des_r/ |1,4: skip ]
  @brxf_mk_rle -t0 -t1 -t2 -t4 -r2
  [ >path_beta_append_p //
  | >path_p2beta_qbeta >path_p2beta_append_q <H2 -q1 -n1
    >list_append_assoc //
  ]
|1,2,10,11: skip
|8,17: @(brd_fsubst_false_eq_repl_fwd … Hs02)
  [ /2 width=6 by nin_root_brxf_side/
  | /2 width=7 by nin_root_brd_side/
  | /2 width=7 by nin_root_brxf_side_trunk/
  | /2 width=8 by nin_root_brd_side_trunk/
  ]
|6: @brd_brxf_append_p
|15: elim (path_eq_inv_xSy_q_beta … H2) -H2 #_ * -q1 @brd_brxf_append_q
|9:
  @brd_brd_append_p
  @(subset_eq_canc_sx … @ dbfs_des_grafted_nreq … Ht24 Hr21 …)
  [ /2 width=7 by path_nreq_side_p_beta/ ]
  @(subset_eq_sym … @ dbfs_des_grafted_full … Ht0 Ht02 Hr02)
|18:
  <H0b in ⊢ (???(??%???));
  elim (path_eq_inv_xSy_q_beta … H2) -H2 #_ * @brd_brd_append_q
  @(subset_eq_canc_sx … @ dbfs_des_grafted_nreq … Ht24 Hr21 …)
  [ /2 width=2 by path_nreq_rcons_AS/ ]
  @(subset_eq_sym … @ dbfs_des_grafted_nreq … Ht02 Hr02 …)
  /2 width=6 by path_nreq_p_p3beta_side/
|3,12:
  @fsubst_3_distr_eq
  [1,2,8,9: /2 width=3 by brxf_ol_sx/
  |3,10: /3 width=16 by neq_inv_pcxr_bi_preterm_brxf/
  |4,11: /3 width=17 by neq_inv_preterm_pcxr_bi_brxf_brd/
  |5,12: /4 width=17 by neq_inv_preterm_pcxr_bi_brxf_brd, sym_eq/
  |6,13:
    @subset_nol_nimp_sx
    [ @brd_nol_brxf_p
    | elim (path_eq_inv_xSy_q_beta … H2) -H2 #_ * -q1
      <H0b in ⊢ (?(???%));
      @brd_nol_brxf_q
    ]
  |7,14:
    @subset_nol_nimp_sx
    @subset_nol_nimp_sx
    [ >(path_p3beta_rcons_d y) in Hy; #Hy
    | elim (path_eq_inv_xSy_q_beta … H2) -H2 #H0 #_ <H0 in Hy; -H0 #Hy
    ] /2 width=17 by preterm_nol_brxf/
  ]
]
qed-.

(* Main destructions with dbfdss ********************************************)

theorem dbf_step_conf (t0) (t1) (t2) (r1) (r2):
        t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
        ∃∃t. t1 Ꟈ➡*𝐝𝐛𝐟[r2 /𝐝𝐛𝐟 r1, Ⓕ] t & t2 Ꟈ➡*𝐝𝐛𝐟[r1 /𝐝𝐛𝐟 r2, Ⓕ] t.
#t0 #t1 #t2 #r1 #r2 #Ht0 #Ht01 #Ht02
elim (eq_path_dec r2 r1) #Hnr21 destruct
[ lapply (dbfs_mono … Ht01 Ht02) -Ht0 -Ht01 -Ht02 #Ht12
  @(ex2_intro … t2) @dbfdss_self //
| cases Ht01 #p1 #b1 #q1 #n1 #Hr01 #_
  cases Ht02 #p2 #b2 #q2 #n2 #Hr02 #_
  elim (path_req_dec (p2◖𝗦) r1) #Hp21
  elim (path_req_dec (p1◖𝗦) r2) #Hp12
  [ cases Hr01 -Hr01 #_ #Hr01
    cases Hr02 -Hr02 #_ #Hr02
    elim (pxr_inv_ol … Hr01 Hr02 Hp21 Hp12)
  | lapply (term_in_comp_clear_root_slice_inv_pcxr_bi … Hr01 Hr02 Hp21) [ // ] -Hp21 #Hp21
    elim (term_in_slice_inv_gen … Hp21) -Hp21 #x #H0
    elim (dbf_step_conf_le … Ht0 Ht01 Ht02 Hr01 Hr02 … H0)
    [ -Ht01 #u #t #Ht10 #Ht2u0 #Hut0
    |*: /2 width=1 by/
    ]
    @(ex2_intro … t)
    [ @(dbfs_neq_dbfdss_cx … Hr01 Hnr21 Hp12 Ht10)
    | @(dbfs_side_dbfdss_preterm … Ht0 Hr01 Hr02 Hp12 H0 Ht2u0 Hut0)
    ]
  | lapply (term_in_comp_clear_root_slice_inv_pcxr_bi … Hr02 Hr01 Hp12) [ // ] -Hp12 #Hp12
    elim (term_in_slice_inv_gen … Hp12) -Hp12 #x #H0
    elim (dbf_step_conf_le … Ht0 Ht02 Ht01 Hr02 Hr01 … H0)
    [ -Ht02 #u #t #Ht20 #Ht1u0 #Hut0
    |*: /2 width=1 by/
    ]
    @(ex2_intro … t)
    [ @(dbfs_side_dbfdss_preterm … Ht0 Hr02 Hr01 Hp21 H0 Ht1u0 Hut0)
    | @(dbfs_neq_dbfdss_cx … Hr02 ? Hp21 Ht20) /2 width=1 by/
    ]
  | elim (dbf_step_conf_nol … Ht0 Ht01 Ht02 Hr01 Hr02 Hnr21 Hp21 Hp12) -t0 #t #Ht1 #Ht2 #Hr1 #Hr2
    /4 width=7 by dbfs_neq_dbfdss_cx, ex2_intro/
  ]
]
qed-.
