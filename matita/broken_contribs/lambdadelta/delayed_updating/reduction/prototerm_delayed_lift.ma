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

include "delayed_updating/substitution/lift_rmap_beta.ma".
include "delayed_updating/substitution/lift_path_depth.ma".
include "delayed_updating/substitution/lift_path_clear.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_path_beta.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with lift **************************************************)

lemma brd_lift (f) (t) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ →
      (𝐃❨🠡[f]t,🠡[f]p,🠡[🠢[p]f]b,🠡[🠢[𝐫❨p,b❩]f]q,🠢[𝐫❨p,b,q❩]f＠§❨n❩❩) ⇔ 🠡[f]𝐃❨t,p,b,q,n❩.
#f #t #p #b #q #n #Hq
@(subset_eq_trans … (lift_pt_append …))
@pt_append_eq_repl_bi
[ <lift_path_beta <lift_path_clear_swap <lift_path_depth
  <(lift_path_closed_des_gen … Hq)
  <(lift_path_closed_des_gen … Hq)
  <(pcc_lift_rmap_p3beta_xapp_immediate … Hq)
  <(pcc_lift_rmap_p3beta_lapp … Hq) //
(* Note: crux of the proof begins *)
| <(pcc_lift_rmap_beta_delayed … Hq) -Hq
  @(subset_eq_canc_sx … (lift_term_grafted_S …)) //
(* Note: crux of the proof ends *)
]
qed.
