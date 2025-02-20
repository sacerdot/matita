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

include "delayed_updating/reduction/ibf_step.ma".
include "delayed_updating/reduction/preterm_focus_unwind.ma".

include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_prototerm_append.ma".
include "delayed_updating/unwind/unwind2_rmap_crux.ma".

include "delayed_updating/substitution/lift_prototerm_proper.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/path_closed_structure.ma".
include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "delayed_updating/syntax/path_structure_help.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* UPDATE *)

(* Constructions with unwind2 ***********************************************)

lemma ibfs_unwind_bi (f) (t1) (t2) (r):
      t1 ϵ 𝐓 →
      t1 ➡𝐢𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H1t1
* #p #b #q #n #Hr cases Hr #H0 #Hb #Hn #Ht1 #Ht2 destruct
@(ex2_4_intro … (⊗p) (⊗b) (⊗q) (♭q)) [ @and4_intro ]
[ -H1t1 -Hb -Hn -Ht1 -Ht2 //
| -H1t1 -Hn -Ht1 -Ht2 //
| -H1t1 -Hb -Ht1 -Ht2 //
| lapply (in_comp_unwind2_bi f … Ht1) -Ht2 -Ht1 -H1t1 -Hb
  <unwind2_path_d_dx <path_append_pAbLq_6 in ⊢ ((???%)→?);
  <fbr_xapp_succ_lapp <unwind2_rmap_append_closed_Lq_dx_lapp_depth //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_and_sn_sn …)) [| // ]
  @(subset_eq_canc_sn … (fsubst_and_rc_sn …))
  @fsubst_eq_repl [ // | /2 width=3 by brf_unwind/ ]
  @(subset_eq_trans … (unwind2_pt_append_tpc_dx …))
  [| @lift_term_proper /2 width=6 by term_le_grafted_S_dx_proper/ ]
  @pt_append_eq_repl_bi
  [ >path_structure_clear_swap //
  | @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S_dx /2 width=2 by term_in_root/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_canc_dx … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    <path_append_pAbLq_1 <unwind2_rmap_append
    <unwind2_rmap_uni_crux //
(* Note: crux of the proof ends *)
  ]
]
qed.

(* Inversions with unwind2 **************************************************)

lemma ibfs_inv_unwind2_sn (f) (t1) (u2) (s):
      t1 ϵ 𝐓 → ▼[f]t1 ➡𝐢𝐛𝐟[s] u2 →
      ∃∃t2,r. t1 ➡𝐢𝐛𝐟[r] t2 & ▼[f]t2 ⇔ u2 & ⊗r = s.
#f #t1 #u2 #s #H1t1
* #p #b #q #n * #Hs #Hb #Hq * #x0 #H2t1 #H0 #Hu2 destruct
elim (eq_inv_d_dx_unwind2_path … (sym_eq … H0)) -H0 #x1 #n0 #H0 #Hn0 #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #p0 #x2 #H1 #H0 #H2 destruct
elim (eq_inv_A_sn_structure … H0) -H0 #xa #x3 #Ha #H0 #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #b0 #x4 #H1 #H0 #H2 destruct
elim (eq_inv_L_sn_structure … H0) -H0 #xl #q0 #Hl #H0 #H1 destruct
lapply (pcc_inv_structure … Hq) -Hq #H0 destruct
elim (eq_inv_succ_fbr_xapp … Hn0) -Hn0 #H1n0 #H2n0
>path_append_pAbLq_4 in H1n0; <unwind2_rmap_append #H1n0
lapply (eq_succ_depth_unwind2_rmap_Lq_pcc … H1n0) -H1n0 #H1n0
<structure_idem in Hb; #Hb
@(
  let r ≝ (p0●xa●𝗔◗b0●xl●𝗟◗q0) in
  let v ≝ ((p0●xa●𝗔◗(⓪b0)●(⓪xl)●𝗟◗q0)●🠡[𝐮❨⁤↑(♭b0+⫰n0)❩]⋔[p0●xa◖𝗦]t1) in
  ex3_2_intro … (⬕[↑r←v]t1) (⓪r)
)
[ @(ex2_4_intro … (p0●xa) (b0●xl) q0 (⫰n0)) [ @and4_intro ]
  [ 1,3,4: //
  | <structure_append <Hl -xl //
  | @fsubst_eq_repl [ // | <brxf_unfold // ]
    <bri_unfold <depth_append_empty_structure_dx [| // ]
    @pt_append_eq_repl_bi [| // ]
    <path_clear_append //
  ]
| @(subset_eq_canc_sn … Hu2) -u2
  @(subset_eq_trans … (unwind2_term_fsubst_and_sn_sn …)) [| // ]
  @(subset_eq_canc_sn … (fsubst_and_rc_sn …))
  @fsubst_eq_repl
  [ //
  | @(subset_eq_trans … (unwind2_slice_and_sn … H2t1)) [| // ]
    <path_structure_pAbLq_flat [2,3: // ]
    @subset_eq_refl
  ]
  @(subset_eq_trans … (unwind2_pt_append_tpc_dx …))
  [| @lift_term_proper /2 width=6 by term_le_grafted_S_dx_proper/ ]
  @pt_append_eq_repl_bi
  [ <path_structure_pAbLq_clear //
  | @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ >(list_append_empty_sn … (⊗p0)) >Ha in ⊢ (???%); >structure_append
      @unwind2_term_grafted_S_dx [ // ]
      >path_append_pAbLq_2 in H2t1; #H2t1
      /2 width=2 by term_in_root/
    | skip
    ] -H2t1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_canc_dx … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    >path_append_pAbLq_3 <unwind2_rmap_append in ⊢ (??%);
    >path_clear_append >(depth_append_empty_structure_dx b0 … Hl)
    <unwind2_rmap_uni_crux
    [ <depth_append_empty_structure_dx //
    | //
    ]
(* Note: crux of the proof ends *)
  ]
| <path_clear_structure_pAbLq <path_structure_clear
  <path_structure_pAbLq_flat //
]
qed-.
