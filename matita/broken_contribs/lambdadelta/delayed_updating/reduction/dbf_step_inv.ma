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
include "delayed_updating/reduction/prototerm_cx_redex_eq.ma".
include "delayed_updating/reduction/dbf_step_main.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

definition dbfs_inv_pcr_side_th (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n): predicate (𝕋) ≝
  λt. ∨∨ ∃∃y. p1◖𝗦●y = p & 𝐫❨y,b,q,⁤↑n❩ = x &
              (𝐫❨p1,⓪b1,q1,⁤↑(♭b1+n1)❩●x) ϵ 𝐑❨t,𝐫❨p1,⓪b1,q1,⁤↑(♭b1+n1)❩●y,b,q,n❩
       | ∃∃y. (𝐫❨p,b,y❩) = p1 & y◖𝗦●x = 𝐫❨q,⁤↑n❩ &
              (𝐫❨p1,⓪b1,q1,⁤↑(♭b1+n1)❩●x) ϵ 𝐑❨t,p,b,𝐫❨y,⓪b1,q1,⁤↑(♭b1+n1)❩●⇂x,n❩
.

(* Auxiliary constructions **************************************************)

lemma dbfs_inv_pcr_side_th_eq_repl_fwd (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n):
      replace_1_fwd … (subset_eq …) (dbfs_inv_pcr_side_th p1 p x b1 b q1 q n1 n).
#p1 #p #x #b1 #b #q1 #q #n1 #n #t1 * *
#y #H1 #H2 #Hr #t2 #Ht12
[ @or_introl | @or_intror ]
@(ex3_intro … H1 H2) -H1 -H2
/3 width=3 by pcxr_eq_repl, subset_in_eq_repl_fwd/
qed-.

(* Advanced inversions with preterm *****************************************)

(* UPDATE *)

lemma dbfs_inv_pcxr_side (t1) (t2) (r) (p1) (p) (x) (b1) (b) (q1) (q) (n1) (n):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p1,b1,q1,n1❩ → p1◖𝗦●x ϵ 𝐑❨t1,p,b,q,n❩ →
      dbfs_inv_pcr_side_th p1 p x b1 b q1 q n1 n t2.
#t1 #t2 #r #p1 #p #x #b1 #b #q1 #q #n1 #n #Ht12 #Hr #Hx
lapply (dbfs_inv_pcxr_sx … Ht12 Hr) -Ht12 #Ht12
@(dbfs_inv_pcr_side_th_eq_repl_fwd … Ht12) -t2
cases Hr -Hr #Hn1 * #H0 #Hb1 #Hq1 destruct
cases Hx -Hx #Hn * #H0 #Hb #Hq
elim (path_eq_inv_beta_balanced_pSq … H0) -H0 [3: // ] * #y
[ (* Note: argument moved *)
  #H1 #H2 destruct -Hb1 -Hq1
  @or_introl @ex3_intro [2,3: // | skip ]
  >path_beta_append_p
  @(pcxr_mk … Hb Hq) -Hb -Hq
  @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
  /2 width=1 by pt_append_in/
| (* Note: argument not moved *)
  -Hb1 #H1 #H2 destruct
  elim (eq_inv_list_lcons_append ????? H1) -H1 *
  [ #_ #H0 destruct ] #z #H1 #H2 destruct
  @or_intror @ex3_intro [2,3: // | skip ]
  <path_beta_swap_pq >path_beta_append_q
  @(pcxr_mk … n … Hb) -Hb
  [ @fsubst_in_comp_true [ /2 width=3 by subset_ol_i/ ]
    <path_beta_append_q >path_beta_swap_pq
    /2 width=1 by pt_append_in/
  | -t1 -p -b <list_tl_lcons >nplus_succ_dx >nplus_unit_sx
    /2 width=1 by path_beta_in_brd_pcc/
  ]
]
qed-.
