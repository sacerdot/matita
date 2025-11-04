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

include "delayed_updating/syntax/path_structure_depth.ma".
include "delayed_updating/syntax/path_clear_structure.ma".
include "delayed_updating/syntax/path_beta_structure.ma".
include "delayed_updating/syntax/prototerm_beta.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_prototerm_proper.ma".
include "delayed_updating/unwind/unwind2_rmap_beta.ma".
include "delayed_updating/unwind/unwind2_rmap_crux.ma".
include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_append.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/reduction/prototerm_immediate.ma".

(* BALANCED REDUCTION IMMEDIATE SUBREDUCT ***********************************)

(* Constructions with unwind2 ***********************************************)

lemma bri_unwind2 (f) (t) (p) (b) (q) (n):
      t ϵ 𝐓 → 𝐫❨p,b,q,⁤↑n❩ ϵ t → ♭q = (▶[𝐫❨p,b,q❩]f)＠§❨n❩ →
      (𝐈❨▼[f]t,⊗p,⊗b,⊗q,♭q❩) ⇔ ▼[f](𝐈❨t,p,b,q,n❩).
#f #t #p #b #q #n #Ht #Hn #Hq
lapply (eq_depth_unwind2_rmap_pbeta_lapp_pcc … Hq) -Hq #Hq
@(subset_eq_trans … (unwind2_pt_append_tpc_dx …))
[| @lift_term_proper /2 width=6 by term_le_grafted_S_dx_proper/ ]
<path_structure_pbeta <path_structure_clear_swap
@pt_append_eq_repl_bi [ // ] <depth_structure
@(subset_eq_canc_sx … (lift_term_eq_repl_dx …))
[ @unwind2_term_grafted_S_dx [ // ]
  /2 width=4 by path_beta_pA_in_root/
| skip
] -Hn
@(subset_eq_trans … (lift_unwind2_term_after …))
@(subset_eq_canc_dx … (unwind2_lift_term_after …))
@unwind2_term_eq_repl_sx
(* Note: crux of the proof begins *)
<unwind2_rmap_pbeta_bLq <unwind2_rmap_uni_crux //
(* Note: crux of the proof ends *)
qed.
