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

include "delayed_updating/unwind/unwind2_prototerm_constructors.ma".
include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_prototerm_append.ma".
include "delayed_updating/unwind/unwind2_rmap_crux.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_closed_structure.ma".
include "delayed_updating/syntax/path_clear_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
(*
axiom pippo (f) (t) (p) (b) (q) (n):
      t ϵ 𝐓 → ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → (p◖𝗔)●b●𝗟◗q◖𝗱(⁤↑n) ϵ t →
      ⬕[↑⊗((p◖𝗔)●b●𝗟◗q)←(⊗p◖𝗔)●⓪⊗b●(𝗟◗⊗q)●🠡[𝐮❨⁤↑(♭⊗b+♭q)❩]⋔[⊗p◖𝗦]▼[f]t]▼[f]t⇔
      ▼[f]⬕[↑((p◖𝗔)●b●𝗟◗q)←(p◖𝗔)●⓪b●(𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t]t.
*)

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)
(*
theorem unwind2_ibfr_trans_dbfr (f) (t1) (u2) (s):
        ▼[f]t1 ➡𝐢𝐛𝐟[s] u2 →
        ∃∃t2,r. t1 ➡𝐝𝐛𝐟[r] t2 & ▼[f]t2 ⇔ u2 & ⊗r = s.
#f #t1 #u2 #s
* #p #b #q #n #Hs #Hb #Hn * #x0 #Ht1 #H0 #Hu2 destruct
elim (eq_inv_d_dx_unwind2_path … (sym_eq … H0)) -H0 #x1 #nx #H0 #Hnx #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #p0 #x2 #H1 #H0 #H2 destruct
elim (eq_inv_A_sn_structure … H0) -H0 #xa #x3 #Ha #H0 #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #b0 #x4 #H1 #H0 #H2 destruct
elim (eq_inv_L_sn_structure … H0) -H0 #xl #q0 #Hl #H0 #H1 destruct
<structure_idem in Hb; #Hb
@(
  let r ≝ (p0●xa●𝗔◗b0●xl●𝗟◗q0) in
  let v ≝ ((p0●xa●𝗔◗(⓪b0)●(⓪xl)●𝗟◗q0)●𝛕(⁤↑(♭b0+n0)).⋔[p0●xa◖𝗦]t1) in
  ex3_2_intro … (⬕[↑r←v]t1) r
)
[ @(ex5_4_intro … (p0●xa) (b0●xl) q0 n0)
  [ //
  | <structure_append <Hl -xl //
  |
  | // /2 width=5 by _/ 
  ] 
| @(subset_eq_canc_sn … Hu2) -u2
  @(subset_eq_trans … (pippo …))

| >list_append_rcons_sn -f -t1 -u2 -n -n0 -Hb
  <structure_append <structure_A_sn
  <structure_append <structure_L_sn
  <structure_append <structure_append
  <Ha <Hl -xa -xl //
]
*)
(* Main destructions with ibfr **********************************************)

theorem dbfr_des_ibfr (f) (t1) (t2) (r):
        t1 ϵ 𝐓 →
        t1 ➡𝐝𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H0t1
* #p #b #q #n #Hr #Hb #Hn #Ht1 #Ht2 destruct
@(ex5_4_intro … (⊗p) (⊗b) (⊗q) (♭q))
[ -H0t1 -Hb -Hn -Ht1 -Ht2 //
| -H0t1 -Hn -Ht1 -Ht2 //
| -H0t1 -Hb -Ht1 -Ht2
  /2 width=2 by path_closed_structure_depth/
| lapply (in_comp_unwind2_bi f … Ht1) -H0t1 -Hb -Ht2 -Ht1
  <unwind2_path_d_dx <path_append_pLq in ⊢ ((???%)→?);
  <fbr_xapp_succ_lapp <unwind2_rmap_append_closed_Lq_dx_lapp_depth //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_and_sn_sn …)) [| // ]
  @(subset_eq_canc_sn … (fsubst_and_rc_sn …))
  @fsubst_eq_repl [ // | /2 width=2 by unwind2_slice_and_sn/ ]
  @(subset_eq_trans … (unwind2_pt_append_tpc_dx …)) [| // ]
  @pt_append_eq_repl_bi
  [ <structure_append <structure_A_sn
    <structure_append <structure_L_sn //
  | @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S_dx /2 width=2 by term_in_root/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_trans ????? (unwind2_term_iref …))
    [| /2 width=6 by term_grafted_S_dx_proper/ ]
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    <path_append_pbLq <unwind2_rmap_append
    <unwind2_rmap_uni_crux //
(* Note: crux of the proof ends *)
  ]
]
qed-.
