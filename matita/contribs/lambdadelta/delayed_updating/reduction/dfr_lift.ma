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

include "delayed_updating/reduction/dfr.ma".

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_constructors.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_rmap_closed.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

(* Constructions with lift **************************************************)

theorem dfr_lift_bi (f) (t1) (t2) (r):
        t1 ➡𝐝𝐟[r] t2 → ↑[f]t1 ➡𝐝𝐟[↑[f]r] ↑[f]t2.
#f #t1 #t2 #r
* #p #q #n #Hr #Hn #Ht1 #Ht2 destruct
@(ex4_3_intro … (↑[f]p) (↑[↑[p◖𝗔◖𝗟]f]q) ((↑[p●𝗔◗𝗟◗q]f)＠§❨n❩))
[ -Hn -Ht1 -Ht2 //
| -Ht1 -Ht2
  /2 width=1 by lift_path_rmap_closed_L/
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1 -Hn
  <lift_path_d_dx #Ht1 //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | // ]
  @(subset_eq_trans … (lift_term_iref_nap …))
  @iref_eq_repl
  @(subset_eq_canc_sn … (lift_term_grafted_S …))
  @lift_term_eq_repl_sn
(* Note: crux of the proof begins *)
  /2 width=1 by tls_succ_lift_rmap_append_L_closed_dx/
(* Note: crux of the proof ends *)
]
qed.
