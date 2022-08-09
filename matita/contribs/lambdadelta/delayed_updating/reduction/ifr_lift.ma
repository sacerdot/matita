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
include "delayed_updating/substitution/lift_path_head.ma".
include "delayed_updating/substitution/lift_rmap_head.ma".

include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_compose_eq.ma".

(* IMMEDIATE FOCUSED REDUCTION **********************************************)

(* Constructions with lift **************************************************)

theorem ifr_lift_bi (f) (p) (q) (t1) (t2):
        t1 ➡𝐢𝐟[p,q] t2 → ↑[f]t1 ➡𝐢𝐟[↑[f]p,↑[↑[p◖𝗔◖𝗟]f]q] ↑[f]t2.
#f #p #q #t1 #t2
* #k * #H1k #Ht1 #Ht2
@(ex_intro … ((↑[p●𝗔◗𝗟◗q]f)＠⧣❨k❩)) @and3_intro
[ -Ht1 -Ht2
  <lift_rmap_L_dx >lift_path_L_sn
  <(lift_path_head_closed … H1k) in ⊢ (??%?); -H1k //
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1 -H1k
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
  @(stream_eq_trans … (tr_compose_uni_dx …))
  @tr_compose_eq_repl //
  >list_append_rcons_sn in H1k; #H1k >lift_rmap_A_dx
  /2 width=1 by tls_lift_rmap_closed/
(* Note: crux of the proof ends *)
]
qed.
