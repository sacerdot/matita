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
include "delayed_updating/reduction/ifr.ma".

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_constructors.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_head.ma".
include "delayed_updating/substitution/lift_rmap_head.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

(* Constructions with lift **************************************************)

theorem dfr_lift_bi (f) (p) (q) (t1) (t2):
        t1 ➡𝐝𝐟[p,q] t2 → ↑[f]t1 ➡𝐝𝐟[↑[f]p,↑[↑[p◖𝗔◖𝗟]f]q] ↑[f]t2.
#f #p #q #t1 #t2
* #n * #H1n #Ht1 #Ht2
@(ex_intro … ((↑[p●𝗔◗𝗟◗q]f)＠⧣❨n❩)) @and3_intro
[ -Ht1 -Ht2
  <lift_rmap_L_dx >lift_path_L_sn
  >list_append_rcons_sn in H1n; <reverse_append #H1n
  <(lift_path_head … H1n) -H1n //
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1 -H1n
  <lift_path_d_dx #Ht1 //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | // ]
  @(subset_eq_trans … (lift_term_iref …))
  @iref_eq_repl
  @(subset_eq_canc_sn … (lift_term_grafted_S …))
  @lift_term_eq_repl_sn
(* Note: crux of the proof begins *)
  >list_append_rcons_sn in H1n; #H1n >lift_rmap_A_dx
  /2 width=1 by tls_lift_rmap_append_closed/
(* Note: crux of the proof ends *)
]
qed.
