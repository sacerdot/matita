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

include "ground/xoa/ex_3_1.ma".
include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/path_closed_clear.ma".
include "delayed_updating/reduction/prototerm_reducible_eq.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

definition dbfs_inv_prc_side_th (r) (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n): predicate (𝕋) ≝
  λt. ∨∨ ∃∃y. p1●𝗦◗y = p & (y◖𝗔)●b●𝗟◗q = x &
              r◖𝗱𝟎●⓪x ϵ 𝐑❨t,(p1●𝗔◗⓪b1●𝗟◗q1◖𝗱(⁤↑(♭b1+n1)))●y,b,q,n❩
       | ∃∃y. p●𝗔◗b●𝗟◗y = p1 & y●𝗦◗x = q &
              r◖𝗱𝟎●⓪x ϵ 𝐑❨t,p,b,y●𝗔◗⓪b1●𝗟◗q1●𝗱(⁤↑(♭b1+n1))◗x,n❩
.
(* Auxiliary constructions **************************************************)

lemma dbfs_inv_prc_side_th_eq_repl_fwd (r) (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n):
      replace_1_fwd … (subset_eq …) (dbfs_inv_prc_side_th r p1 p x b1 b q1 q n1 n).
#r #p1 #p #x #b1 #b #q1 #q #n1 #n #t1 * *
#y #H1 #H2 #Hr #t2 #Ht12
[ @or_introl | @or_intror ]
@(ex3_intro … H1 H2) -H1 -H2
/3 width=3 by xprc_eq_repl, subset_in_eq_repl_fwd/
qed-.

(* Advanced inversions with preterm *****************************************)

(* UPDATE *)

lemma dbfs_inv_prc_side (t1) (t2) (r) (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n):
      t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p1,b1,q1,n1❩ →
      x◖𝗱(⁤↑n) ϵ ⋔[p1◖𝗦]t1 → ⓪p1◖𝗦●⓪x ϵ 𝐑❨t1,p,b,q,n❩ →
      dbfs_inv_prc_side_th r p1 p x b1 b q1 q n1 n t2.
#t1 #t2 #r #p1 #p #x #b1 #b #q1 #q #n1 #n
#Ht1 #Ht12 #Hr #Hx #H0x
lapply (dbfs_preterm_inv_sn … Ht1 Ht12 Hr) -Ht12 #Ht12
@(dbfs_inv_prc_side_th_eq_repl_fwd … Ht12) -t2
lapply (term_grafted_inv_gen … Hx) -Hx >list_append_rcons_sn #Hx
cases Hr -Hr #H0 #Hb1 #Hq1 #Hn1 destruct
cases H0x -H0x
<path_clear_append <path_clear_A_sn <path_clear_append <path_clear_L_sn
<path_append_pAbLq_1 >list_append_rcons_sn in ⊢ ((???%)→?);
#H0 #Hb #Hq #Hn
elim (path_eq_inv_pbq_pSq_pbc … H0) -H0 [3: // ] * #m0
[ (* Note: argument moved *)
  >path_clear_A_dx #H2 #H1 -Hb1 -Hq1

  elim (eq_inv_path_append_clear … H1) -H1 #m #x1 #H0 #H1 #H3 destruct
  >path_clear_L_sn in H1; >path_clear_append; #H1
  >path_clear_S_sn in H2; >path_clear_append; #H2
  lapply (term_clear_inj … Ht1 … H2) -H2
  [1,2: /2 width=2 by term_in_root/ ] #H2
  lapply (eq_f … (λx.⓪(p◖𝗔)●x) … H1) -H1 >H2 in ⊢ (???%→?);
  >path_clear_append >path_clear_append #H1
  lapply (term_clear_inj … Ht1 … H1) -H1
  [1,2: /2 width=2 by term_in_root_rcons, term_in_comp_root/ ] <H2 #H1
  lapply (eq_inv_list_append_dx_bi … H1) -H1 #H1 destruct

  elim (eq_inv_list_lcons_append ????? H2) -H2 *
  [ #H0 #_ elim (eq_inv_list_empty_rcons ??? H0) ] #s1 #H2 #H0 destruct
  elim (eq_inv_list_lcons_append ????? H2) -H2 *
  [ #_ #H0 | #y #H1 #H2 ] destruct -Hx

  @or_introl @ex3_intro [2,3: // | skip ]
  >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b1+n1)))
  >path_clear_append <(path_append_pAbLq_8 ? y)
  @(xprc_mk … Hb Hq) -Hb -Hq
  @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
  >(list_append_rcons_sn ? y) <list_append_assoc >path_append_pAbLq_9
  @pt_append_in <list_append_rcons_dx
  @in_comp_iref_hd @term_grafted_gen //

| (* Note: argument not moved *)
  -Hb1 #H1 >list_append_rcons_sn #H2

  elim (eq_inv_list_rcons_append ????? H1) -H1 *
  [ #H0 #_ elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct ]
  #x0 #H1 #H0 destruct
  elim (eq_inv_path_append_clear … (sym_eq … H1)) -H1 #y #x1 #H3 #H1 #H4 destruct
  >path_clear_L_sn in H2; >path_clear_append >path_clear_A_sn >path_clear_append #H2
  lapply (term_clear_inj … Ht1 … H2) -H2
  [1,2: /2 width=2 by term_in_root/ ] #H0 destruct

  lapply (eq_f … (λx.⓪(p●𝗔◗b●𝗟◗y)●x) … H1) -H1
  >path_clear_S_sn >path_clear_append >path_clear_append #H1
  lapply (term_clear_inj … Ht1 … H1) -H1
  [1,2: /2 width=2 by term_in_root_rcons, term_in_comp_root/ ] #H1
  lapply (eq_inv_list_append_dx_bi … H1) -H1 #H1 destruct -Hx

  @or_intror @ex3_intro [2,3: // | skip ]
  >path_clear_reduct >(path_clear_d_dx … (⁤↑(♭b1+n1))) >path_clear_append
  <brd_unfold <path_append_pAbLqAbLq_1 <path_append_pAbLqAbLq_2
  @(xprc_mk … n … Hb) -Hb
  [ @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
    <path_append_pAbLqAbLq_3
    @pt_append_in @in_comp_iref_hd @term_grafted_gen //
  | -t1 -p -b <path_append_pAbLq_10 >nplus_succ_dx >nplus_unit_sn
    lapply (pcc_inv_S … Hq) -Hq #Hq
    @pcc_d @pcc_d @(pcc_pcc … Hq1) -Hq1
    @pcc_L @(pcc_pcc (⓪b1) (♭b1)) [ // ] @pcc_A //
  ]
]
qed-.
