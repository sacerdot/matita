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

include "delayed_updating/unwind/unwind2_constructors.ma".
include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_rmap_head.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_head_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "delayed_updating/syntax/path_structure_reverse.ma".
include "delayed_updating/syntax/path_depth_reverse.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

(* Main destructions with ifr ***********************************************)

theorem dfr_des_ifr (f) (p) (q) (t1) (t2): t1 ϵ 𝐓 →
        t1 ➡𝐝𝐟[p,q] t2 → ▼[f]t1 ➡𝐟[⊗p,⊗q] ▼[f]t2.
#f #p #q #t1 #t2 #H0t1
* #n * #H1n #Ht1 #Ht2
@(ex_intro … (↑♭⊗q)) @and3_intro
[ -H0t1 -H1n -Ht1 -Ht2
  >list_append_rcons_sn <reverse_append
  >nsucc_unfold >depth_reverse >depth_L_dx >reverse_lcons
  >structure_L_sn >structure_reverse
  <path_head_structure //
| lapply (in_comp_unwind2_path_term f … Ht1) -Ht2 -Ht1 -H0t1
  <unwind2_path_d_dx <depth_structure
  >list_append_rcons_sn in H1n; <reverse_append #H1n
  lapply (unwind2_rmap_append_pap_closed f … H1n)
  <reverse_lcons <depth_L_dx #H2n
  lapply (eq_inv_ninj_bi … H2n) -H2n #H2n <H2n -H2n -H1n #Ht1 //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst …))
  [ @fsubst_eq_repl [ // | // ]
    @(subset_eq_trans … (unwind2_term_iref …))
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    @nstream_eq_inv_ext #m
    <tr_compose_pap <tr_compose_pap
    <tr_uni_pap <tr_uni_pap <tr_pap_plus
    >list_append_rcons_sn in H1n; <reverse_append #H1n
    lapply (unwind2_rmap_append_pap_closed f … H1n) #H2n
    >nrplus_inj_dx in ⊢ (???%); <H2n -H2n
    lapply (tls_unwind2_rmap_append_closed f … H1n) #H2n
    <(tr_pap_eq_repl … H2n) -H2n -H1n //
(* Note: crux of the proof ends *)
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
qed.
