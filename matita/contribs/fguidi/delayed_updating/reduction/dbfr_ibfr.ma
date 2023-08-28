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
include "delayed_updating/reduction/ibfr.ma".

include "delayed_updating/unwind_k/unwind2_prototerm_constructors.ma".
include "delayed_updating/unwind_k/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind_k/unwind2_preterm_eq.ma".
include "delayed_updating/unwind_k/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind_k/unwind2_rmap_closed.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_closed_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Main destructions with ibfr **********************************************)

theorem dbfr_des_ibfr (f) (t1) (t2) (r): t1 ϵ 𝐓 →
        t1 ➡𝐝𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H0t1
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht2 destruct
@(ex5_4_intro … (⊗p) (⊗b) (⊗q) (♭q))
[ -H0t1 -Hb -Hn -Ht1 -Ht2 //
| -H0t1 -Hn -Ht1 -Ht2 //
| -H0t1 -Hb -Ht1 -Ht2
  /2 width=2 by path_closed_structure_depth/
| lapply (in_comp_unwind2_path_term f … Ht1) -H0t1 -Hb -Ht2 -Ht1
  <unwind2_path_d_dx >list_append_rcons_dx >list_append_assoc
  <fbr_xapp_succ_lapp <unwind2_rmap_append_closed_Lq_dx_lapp_depth //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_ppc …))
  [ @fsubst_eq_repl [ // | // ]
(*
    @(subset_eq_trans … (unwind2_term_iref …))
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    /2 width=1 by unwind2_rmap_uni_crux/
(* Note: crux of the proof ends *)
*)
  | //
  | /2 width=2 by ex_intro/
  | @tpc_pt_append_sn @tpc_pt_append_dx //
  ]
]
