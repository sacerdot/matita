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
include "ground/lib/list_tl.ma".
include "delayed_updating/syntax/path_beta_balanced.ma".
include "delayed_updating/syntax/path_beta_closed.ma".
include "delayed_updating/reduction/prototerm_reducible_eq.ma".
include "delayed_updating/reduction/dbf_step_preterm.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

definition dbfs_inv_prc_side_th (r) (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n): predicate (𝕋) ≝
  λt. ∨∨ ∃∃y. p1◖𝗦●y = p & 𝐫❨y,b,q,⁤↑n❩ = x &
              r●⓪x ϵ 𝐑❨t,𝐫❨p1,⓪b1,q1,⁤↑(♭b1+n1)❩●y,b,q,n❩
       | ∃∃y. (𝐫❨p,b,y❩) = p1 & y◖𝗦●x = 𝐫❨q,⁤↑n❩ &
              r●⓪x ϵ 𝐑❨t,p,b,𝐫❨y,⓪b1,q1,⁤↑(♭b1+n1)❩●⇂x,n❩
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
      x ϵ ⋔[p1◖𝗦]t1 → ⓪p1◖𝗦●⓪x ϵ 𝐑❨t1,p,b,q,n❩ →
      dbfs_inv_prc_side_th r p1 p x b1 b q1 q n1 n t2.
#t1 #t2 #r #p1 #p #x #b1 #b #q1 #q #n1 #n
#Ht1 #Ht12 #Hr #Hx #H0x
lapply (dbfs_preterm_inv_sx … Ht1 Ht12 Hr) -Ht12 #Ht12
@(dbfs_inv_prc_side_th_eq_repl_fwd … Ht12) -t2
lapply (term_grafted_inv_gen … Hx) -Hx #Hx
cases Hr -Hr #H0 #Hb1 #Hq1 #Hn1 destruct
cases H0x -H0x <path_clear_beta #H0 #Hb #Hq #Hn
elim (path_eq_inv_beta_balanced_pSq … H0) -H0 [3: // ] * #y0
[ (* Note: argument moved *)
  #H1 #H2 -Hb1 -Hq1

  elim (eq_inv_path_append_clear … (sym_eq … H1)) -H1 #z #y #Hz #Hy #H0 destruct
  elim (eq_inv_path_S_dx_clear … Hz) -Hz #z1 #Hz1 #H0 destruct
  lapply (term_clear_inj … Ht1 … Hz1) -Hz1
  [ >list_append_rcons_sx in Hn; <path_beta_append_p #Hn
    /2 width=2 by term_in_root/
  | /2 width=2 by term_in_root/
  ] #H0 destruct

  >(path_clear_beta … (⁤↑n)) in H2; #H2
  lapply (eq_f … (λx.⓪(z1◖𝗦)●x) … H2) -H2
  >path_clear_append >path_clear_append #H2
  lapply (term_clear_inj … Ht1 … H2) -H2
  [1,2: /2 width=2 by term_in_comp_root/ ] #H2
  lapply (eq_inv_list_append_dx_bi … H2) -H2 #H2 destruct

  @or_introl @ex3_intro [2,3: // | skip ]
  >(path_clear_beta_b … (⁤↑n1) (⁤↑(♭b1+n1)))
  >path_clear_append >path_beta_append_p
  @(xprc_mk … Hb Hq) -Hb -Hq
  @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
  /2 width=1 by pt_append_in/

| (* Note: argument not moved *)
  -Hb1 #H1 #H2

  elim (eq_inv_list_lcons_append ????? H1) -H1 *
  [ #_ #H0 destruct ] #z0 #H1z0 #H2z0
  elim (eq_inv_path_d_dx_clear … H1z0) -H1z0 #z #n0 #Hz #_ #H0 destruct
  elim (eq_inv_path_append_clear … (sym_eq … H2z0)) -H2z0 #y1 #z1 #Hy1 #Hz1 #H0 destruct
  elim (eq_inv_path_S_dx_clear … Hy1) -Hy1 #y #Hy #H0 destruct
  >path_clear_pbeta in H2; #H2
  lapply (term_clear_inj … Ht1 … H2) -H2
  [ /2 width=2 by term_in_root/
  | >list_append_rcons_sx in Hn; <path_beta_append_q #Hn
    /2 width=2 by term_in_root/
  ] #H0 destruct

  lapply (eq_f … (λx.⓪(𝐫❨p,b,y❩◖𝗦)●x) … Hz1) -Hz1
  >path_clear_append >path_clear_append #Hz1
  lapply (term_clear_inj … Ht1 … Hz1) -Hz1
  [1,2: /2 width=2 by term_in_root_rcons/ ] #Hz1
  lapply (eq_inv_list_append_dx_bi … Hz1) -Hz1 #H0 destruct
  lapply (term_root_d_post … Ht1 (𝐫❨p,b,y❩◖𝗦●z1) (𝗱n0) (⁤↑n) ??)
  [1,2: /2 width=2 by term_in_root/ ] -Hx #H0 destruct

  @or_intror @ex3_intro [2,3: // | skip ]
  >(path_clear_beta_b … (⁤↑n1) (⁤↑(♭b1+n1)))
  >path_clear_append <path_beta_swap_pq >path_beta_append_q
  @(xprc_mk … n … Hb) -Hb
  [ @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
    <path_beta_append_q /2 width=1 by pt_append_in/
  | -t1 -p -b <list_tl_lcons >nplus_succ_dx >nplus_unit_sx
    /2 width=1 by path_beta_in_brd_pcc/
  ]
]
qed-.
