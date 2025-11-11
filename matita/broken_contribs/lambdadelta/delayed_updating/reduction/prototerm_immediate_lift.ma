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
include "delayed_updating/substitution/lift_prototerm_after.ma".
include "delayed_updating/reduction/prototerm_immediate.ma".

(* BALANCED REDUCTION IMMEDIATE SUBREDUCT ***********************************)

(* Constructions with lift **************************************************)

lemma bri_lift (f) (t) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ →
      (𝐈❨🠡[f]t,🠡[f]p,🠡[🠢[p]f]b,🠡[🠢[𝐫❨p,b❩]f]q,🠢[𝐫❨p,b,q❩]f＠§❨n❩❩) ⇔ 🠡[f]𝐈❨t,p,b,q,n❩.
#f #t #p #b #q #n #Hq
@(subset_eq_trans … (lift_pt_append …))
@pt_append_eq_repl_bi
[ <lift_path_p3beta <lift_path_clear_swap
  <(lift_path_closed_des_gen … Hq)
  <(lift_path_closed_des_gen … Hq) //
(* Note: crux of the proof begins *)
| <lift_path_depth <(pcc_lift_rmap_p3beta_lapp … Hq)
  @(subset_eq_canc_dx … (lift_term_after …))
  <(pcc_lift_rmap_p3beta_after_uni … Hq)
  @(subset_eq_canc_sx … (lift_term_after …))
  @lift_term_eq_repl_dx
  @lift_term_grafted_S
(* Note: crux of the proof ends *)
]
qed.
