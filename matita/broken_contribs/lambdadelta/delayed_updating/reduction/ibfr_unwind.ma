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

include "delayed_updating/reduction/ibfr.ma".

include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_prototerm_append.ma".
include "delayed_updating/unwind/unwind2_rmap_crux.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_proper.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/prototerm_proper.ma".
include "delayed_updating/syntax/path_closed_structure.ma".
include "delayed_updating/syntax/path_clear_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with unwind2 ***********************************************)

lemma ibfr_unwind_bi (f) (t1) (t2) (r):
      t1 ϵ 𝐓 →
      t1 ➡𝐢𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H1t1
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht2 destruct
@(ex5_4_intro … (⊗p) (⊗b) (⊗q) (♭q))
[ -H1t1 -Hb -Hn -Ht1 -Ht2 //
| -H1t1 -Hn -Ht1 -Ht2 //
| -H1t1 -Hb -Ht1 -Ht2 //
| lapply (in_comp_unwind2_bi f … Ht1) -Ht2 -Ht1 -H1t1 -Hb
  <unwind2_path_d_dx <path_append_pLq in ⊢ ((???%)→?);
  <fbr_xapp_succ_lapp <unwind2_rmap_append_closed_Lq_dx_lapp_depth //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_and_sn_sn …)) [| // ]
  @(subset_eq_canc_sn … (fsubst_and_rc_sn …))
  @fsubst_eq_repl [ // | /2 width=2 by unwind2_slice_and_sn/ ]
  @(subset_eq_trans … (unwind2_pt_append_tpc_dx …))
  [| @lift_term_proper /2 width=6 by term_grafted_S_dx_proper/ ]
  @pt_append_eq_repl_bi
  [ <structure_append <structure_A_sn
    <structure_append <structure_L_sn //
  | @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S_dx /2 width=2 by term_in_root/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_canc_dx … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    <path_append_pbLq_1 <unwind2_rmap_append
    <unwind2_rmap_uni_crux //
(* Note: crux of the proof ends *)
  ]
]
qed.
