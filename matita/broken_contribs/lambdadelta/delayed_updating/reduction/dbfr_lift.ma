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

include "delayed_updating/reduction/dbfr.ma".

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_constructors.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_path_structure.ma".
include "delayed_updating/substitution/lift_path_clear.ma".
include "delayed_updating/substitution/lift_path_depth.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with lift **************************************************)

theorem dbfr_lift_bi (f) (t1) (t2) (r):
        t1 ➡𝐝𝐛𝐟[r] t2 → 🠡[f]t1 ➡𝐝𝐛𝐟[🠡[f]r] 🠡[f]t2.
#f #t1 #t2 #r
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht2 destruct
@(ex5_4_intro … (🠡[f]p) (🠡[🠢[p◖𝗔]f]b) (🠡[🠢[p◖𝗔●b◖𝗟]f]q) n)
[ -Hb -Hn -Ht1 -Ht2 //
| -Hn -Ht1 -Ht2 //
| -Hb -Ht1 -Ht2 <lift_path_closed_des_gen //
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1
  <lift_path_d_dx <path_append_pLq
  <lift_rmap_append_L_closed_dx_xapp_succ //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | // ]
  @(subset_eq_trans … (lift_pt_append …))
  <lift_path_clear_swap @pt_append_eq_repl
  @(subset_eq_trans … (lift_pt_append …))
  <lift_path_L_sn
  <(lift_path_closed_des_gen … Hn) <(lift_path_closed_des_gen … Hn)
  @pt_append_eq_repl
  @(subset_eq_trans … (lift_term_iref_xapp …))
  >lift_rmap_append <lift_rmap_A_dx
  <lift_path_depth <(lift_rmap_append_clear_L_closed_dx_xapp_succ_plus … Hn)
  @iref_eq_repl
  @(subset_eq_canc_sn … (lift_term_grafted_S …))
  @lift_term_eq_repl_sn
(* Note: crux of the proof begins *)
  <ctls_succ_plus_lift_rmap_append_clear_L_closed_dx //
(* Note: crux of the proof ends *)
]
qed.
