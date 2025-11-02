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

include "delayed_updating/reduction/dbf_step.ma".
include "delayed_updating/reduction/prototerm_focus_lift.ma".

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_constructors.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_path_structure.ma".
include "delayed_updating/substitution/lift_path_clear.ma".
include "delayed_updating/substitution/lift_path_depth.ma".

include "ground/relocation/fb/fbr_xapp_lapp.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* UPDATE *)

(* Constructions with lift **************************************************)

theorem dbfs_lift_bi (f) (t1) (t2) (r):
        t1 ➡𝐝𝐛𝐟[r] t2 → 🠡[f]t1 ➡𝐝𝐛𝐟[r] 🠡[f]t2.
#f #t1 #t2 #r
* #p #b #q #n * #Hr #Hb #Hn #Ht1 #Ht2 destruct
@(ex2_4_intro … (🠡[f]p) (🠡[🠢[p◖𝗔]f]b) (🠡[🠢[p◖𝗔●b◖𝗟]f]q) n) [ @and4_intro ]
[ -Hb -Hn -Ht1 -Ht2 //
| -Hn -Ht1 -Ht2 //
| -Hb -Ht1 -Ht2 <lift_path_closed_des_gen //
| lapply (in_comp_lift_bi f … Ht1) -Ht2 -Ht1
  <lift_path_d_dx <path_append_pAbLq_6 in ⊢ ((???%)→?);
  <lift_rmap_append_L_closed_dx_xapp_succ //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @(subset_eq_trans … (fsubst_and_rc_sx …))
  @(subset_eq_canc_sx … (fsubst_and_rc_sx …))
  @fsubst_eq_repl [ // | @(subset_eq_canc_dx … (lift_term_and …)) // ]
  @(subset_eq_trans … (lift_pt_append …))
  @pt_append_eq_repl_bi
  [ <lift_path_append <lift_path_A_sx
    <lift_path_append <lift_path_L_sx
    <(lift_path_closed_des_gen … Hn) <(lift_path_closed_des_gen … Hn) //
  | @(subset_eq_trans … (lift_term_iref_xapp …))
(* Note: crux of the proof begins *)
    <path_append_pAbLq_1 <lift_rmap_append
    <(lift_rmap_append_clear_L_closed_dx_xapp_succ_plus … Hn)
    <(ctls_succ_plus_lift_rmap_append_clear_L_closed_dx … Hn)
    @iref_eq_repl_bi [ // ]
    @(subset_eq_canc_sx … (lift_term_grafted_S …)) //
(* Note: crux of the proof ends *)
  ]
]
qed.

(* Inversions with lift *****************************************************)

lemma dbfs_inv_lift_sx (f) (t1) (u2) (s):
      (🠡[f]t1) ➡𝐝𝐛𝐟[s] u2 →
      ∃∃t2. t1 ➡𝐝𝐛𝐟[s] t2 & 🠡[f]t2 ⇔ u2.
#f #t1 #u2 #s
* #p #b #q #n * #Hs #Hb #Hq * #x0 #Ht1 #H0 #Hu2 destruct
elim (eq_inv_d_dx_lift_path … (sym_eq … H0)) -H0 #x1 #n0 #H0 #H1n0 #H1 destruct
elim (eq_inv_append_lift_path … H0) -H0 #p0 #x2 #H1 #H0 #H2 destruct
elim (eq_inv_A_sx_lift_path … H0) -H0 #x3 #H0 #H1 destruct
elim (eq_inv_append_lift_path … H0) -H0 #b0 #x4 #H1 #H0 #H2 destruct
elim (eq_inv_L_sx_lift_path … H0) -H0 #q0 #H0 #H1 destruct
lapply (lift_path_inv_closed … Hq) -Hq #Hq0
elim (eq_inv_succ_fbr_xapp … H1n0) #_ #H2n0 >H2n0 in H1n0;
>(lift_rmap_append_L_closed_dx_xapp_succ f (p0●𝗔◗b0) … Hq0)
<path_append_pAbLq_5 #H1n0
lapply (eq_inv_fbr_xapp_bi … H1n0) -H1n0 #H0
lapply (eq_inv_nsucc_bi … H0) -H0 #H0 destruct
<structure_lift_path in Hb; #Hb
@(
  let r ≝ (p0●𝗔◗b0●𝗟◗q0) in
  let v ≝ ((p0●𝗔◗(⓪b0)●𝗟◗q0)●𝛕(⁤↑(♭b0+⫰n0)).⋔[p0◖𝗦]t1) in
  ex2_intro ??? (⬕[↑r←v]t1)
)
[ @(ex2_4_intro … p0 b0 q0 (⫰n0)) [ @and4_intro ]
  [ 1,2,3,4: //
  | @subset_eq_refl
  ]
| @(subset_eq_canc_sx … Hu2) -u2
  @(subset_eq_trans … (lift_term_fsubst …))
  @(subset_eq_canc_sx … (fsubst_and_rc_sx …))
  @(subset_eq_canc_sx ????? (fsubst_and_rc_sx …))
  @fsubst_eq_repl
  [ @subset_eq_refl
  | @(subset_eq_canc_sx … (lift_slice_and_sx …)) <lift_path_pAbLq
    @subset_eq_refl
  ]
  @(subset_eq_canc_sx … (lift_pt_append …))
  @pt_append_eq_repl_bi
  [ <lift_path_pAbLq >lift_path_clear_swap
    <(lift_path_closed_des_gen … Hq0) <(lift_path_closed_des_gen … Hq0) //
  | @(subset_eq_canc_sx … (lift_term_iref_xapp …))
(* Note: crux of the proof begins *)
    <path_append_pAbLq_1 <lift_rmap_append
    <(lift_rmap_append_clear_L_closed_dx_xapp_succ_plus … Hq0)
    <(ctls_succ_plus_lift_rmap_append_clear_L_closed_dx … Hq0)
    @iref_eq_repl_bi [ // ]
    @(subset_eq_canc_sx … (lift_term_grafted_S …)) //
(* Note: crux of the proof ends *)
  ]
]
qed-.
