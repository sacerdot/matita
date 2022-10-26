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

include "delayed_updating/reduction/ifr.ma".

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_after.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_rmap_closed.ma".

include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_compose_eq.ma".

(* IMMEDIATE FOCUSED REDUCTION **********************************************)

(* Constructions with lift **************************************************)

theorem ifr_lift_bi (f) (t1) (t2) (r):
        t1 ➡𝐢𝐟[r] t2 → 🠡[f]t1 ➡𝐢𝐟[🠡[f]r] 🠡[f]t2.
#f #t1 #t2 #r
* #p #q #n #Hr #Hn #Ht1 #Ht2 destruct
@(ex4_3_intro … (🠡[f]p) (🠡[🠢[f](p◖𝗔◖𝗟)]q) (🠢[f](p●𝗔◗𝗟◗q)＠§❨n❩))
[ -Hn -Ht1 -Ht2 //
| -Ht1 -Ht2
  /2 width=1 by lift_path_rmap_closed_L/
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1 -Hn
  <lift_path_d_dx #Ht1 //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | <lift_path_append // ]
  @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
  [ @lift_term_grafted_S | skip ]
  @(subset_eq_trans … (lift_term_after …))
  @(subset_eq_canc_dx … (lift_term_after …))
  @lift_term_eq_repl_sn
(* Note: crux of the proof begins *)
  @(stream_eq_trans … (tr_compose_uni_dx_pap …)) <tr_pap_succ_nap
  @tr_compose_eq_repl // >nsucc_unfold
  /2 width=2 by tls_succ_lift_rmap_append_L_closed_dx/
(* Note: crux of the proof ends *)
]
qed.
