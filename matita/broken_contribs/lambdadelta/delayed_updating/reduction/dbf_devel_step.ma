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

include "delayed_updating/substitution/fsubst_fsubst.ma".
include "delayed_updating/reduction/prototerm_delayed_reducible.ma".
include "delayed_updating/reduction/preterm_delayed_xfocus_reducible.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".
include "delayed_updating/reduction/dbf_step_reducibles.ma".
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
      ∃∃t.t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] t.
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
  @(fsubst_fsubst_nol_inv_eq ?????????????????????? Ht01 Ht02 Ht13 Ht24)
  [ /2 width=3 by brxf_ol_sn/
  | /2 width=3 by brxf_ol_sn/
  | /3 width=16 by neq_inv_xprc_bi_brxf/
  | /3 width=17 by neq_inv_xprc_bi_brxf_brd/
  | /4 width=17 by neq_inv_xprc_bi_brxf_brd, sym_eq/
  | //
  | //
  | @(brd_grafted_fsubst_eq_repl_fwd … Ht01)
    [ /3 width=7 by term_in_root_brxf_des_xprc/ | /3 width=7 by term_in_root_brd_des_xprc/ ]
  | @(brd_grafted_fsubst_eq_repl_fwd … Ht02)
    [ /3 width=7 by term_in_root_brxf_des_xprc/ | /3 width=7 by term_in_root_brd_des_xprc/ ]
  ]
| #Ht34 -Hr21 -Hr12
  /3 width=5 by dbfs_eq_canc_dx, ex2_intro/
]
qed-.

lemma in_comp_xprc_side (t) (p1) (p2) (b1) (q1) (s2) (n1):
      (⓪(p2◖𝗦)●⓪s2) ϵ 𝐑❨t,p1,b1,q1,n1❩ →
      ∨∨ (⓪p2) ϵ ⓪↑(p1◖𝗔)
       | (⓪p1) ϵ ⓪↑(p2◖𝗦).
#t #p1 #p2 #b1 #q1 #s1 #n1 #H0
lapply (xprc_des_r … H0) -H0
<path_clear_append #H0
elim (eq_inv_list_append_bi … H0) -H0 * #s
[ <path_clear_A_sn <path_clear_S_dx #H1 #H2
  elim (eq_inv_list_lcons_append ????? H2) -H2 *
  [ /3 width=1 by in_comp_slice_clear_inv_clear_sx, or_intror/ ]
  #s0 #H0 #H2 destruct
  elim (eq_inv_list_rcons_append ????? H1) -H1 *
  [ #_ #H0 destruct ] #s #_ #H1
  lapply (sym_eq ??? H1) -H1 #H1
  elim (eq_inv_list_lcons_append ????? H1) -H1 *
  [ #_ #H0 destruct ] #s1 #H0 #H1 destruct
  <list_append_rcons_sn in H2; >path_clear_A_dx
  /3 width=1 by in_comp_slice_clear_inv_clear_sx, or_introl/
| /3 width=1 by in_comp_slice_clear_inv_clear_sx, or_intror/
]
qed-.

lemma dbf_step_conf_local_le (t0) (t1) (t2) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t0 ϵ 𝐓 → t0 ➡𝐝𝐛𝐟[r1] t1 → t0 ➡𝐝𝐛𝐟[r2] t2 →
      r1 ϵ 𝐑❨t0,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t0,p2,b2,q2,n2❩ →
      (r2 = r1 → ⊥) → r1 ϵ ⓪▵↑(p2◖𝗦) → (r2 ϵ ⓪▵↑(p1◖𝗦) → ⊥) →
      ∃∃t.t1 ➡𝐝𝐛𝐟[r2] t & t2 ➡𝐝𝐛𝐟[r1] t.
#t0 #t1 #t2 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
#Ht0 #Ht01 #Ht02 #Hr01 #Hr02 #Hnr21 #Hp21 #Hp12
lapply (dbfs_preterm_trans … Ht0 Ht02) #Ht2
lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr01 Hr02 Hp21) [ // ] -Hp21 #Hp21
elim (in_comp_inv_term_clear_slice … Hp21) -Hp21 #s2 #H0 #_ destruct
lapply (dbfs_des_xprc_neq … Ht0 Ht02 … Hr01) [ /2 width=1 by/ ] #Hr21
elim (xprc_dbfs … Hr21) #t4 #Ht24
lapply (dbfs_des_reducible_side … (⓪s2) … Ht0 Ht02 Hr02 ?)
[ /2 width=2 by dbfs_inv_reducuble/ ] * #p3 #b3 #q3 #n3 #Hs2
elim (xprc_dbfs … Hs2) #t6 #Ht26
elim (dbf_step_conf_local_nol … Ht2 Ht24 Ht26 Hr21 Hs2 …) -Ht24 -Ht26
[|*: #H0 ]
[
| elim (term_in_comp_clear_root_slice_inv_xprc_gen … Hs2 H0) -H0 #x1 #x2
  >list_append_rcons_sn <list_append_assoc >(path_clear_d_sn … (𝟎)) >path_clear_append #H0
  /3 width=6 by term_in_comp_clear_root_slice_xprc_gen/
| lapply (term_in_comp_clear_root_slice_inv_xprc … Ht2 Hr21 … H0)
  [ /2 width=5 by xprc_des_S/ ] -H0 #H0
  elim (in_comp_xprc_side … Hr21) -Hr21 #Hp
  [ (* argument not moved: p3 begins with (p2◖A) *)

  | (* argument moved *)
  ]
| lapply (eq_inv_list_append_sn_bi … H0) -H0 <path_clear_S_dx #H0 destruct
]

HR02 → r2 ϵ ⓪↑(p2◖𝗔)
Hs2  → (r2◖𝗱𝟎) ϵ ⓪↑(p3◖𝗔) → r2 ϵ ⓪↑(p3◖𝗔)


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

  | lapply (term_in_comp_clear_root_slice_inv_xprc_bi … Hr02 Hr01 Hp12) [ // ] -Hp12 #Hp12

  | elim (dbf_step_conf_local_nol … Ht0 Ht01 Ht02 Hr01 Hr02 Hnr21 Hp21 Hp12) #t #Ht1 #Ht2
    /4 width=6 by dbfs_neq_dbfd, xprc_des_clear, ex2_intro/
  ]
]
