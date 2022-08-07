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

include "delayed_updating/reduction/ifr.ma".

include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_rmap_head.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_proper.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/path_head_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "delayed_updating/syntax/path_structure_reverse.ma".
include "delayed_updating/syntax/path_depth_reverse.ma".

(* IMMEDIATE FOCUSED REDUCTION **********************************************)

(* Constructions with unwind ************************************************)

lemma ifr_unwind_bi (f) (p) (q) (t1) (t2):
      t1 ϵ 𝐓 → t1⋔(p◖𝗦) ϵ 𝐏 →
      t1 ➡𝐢𝐟[p,q] t2 → ▼[f]t1 ➡𝐢𝐟[⊗p,⊗q] ▼[f]t2.
#f #p #q #t1 #t2 #H1t1 #H2t1
* #n * #H1n #Ht1 #Ht2
@(ex_intro … (↑♭q)) @and3_intro
[ -H1t1 -H2t1 -Ht1 -Ht2
  >structure_L_sn >structure_reverse
  >H1n in ⊢ (??%?); >path_head_structure_depth <H1n -H1n //
| lapply (in_comp_unwind2_path_term f … Ht1) -Ht2 -Ht1 -H1t1 -H2t1
  <unwind2_path_d_dx >(list_append_rcons_sn … p) <reverse_append
  lapply (unwind2_rmap_append_pap_closed f … (p◖𝗔)ᴿ … H1n) -H1n
  <reverse_lcons <depth_L_dx #H2n
  lapply (eq_inv_ninj_bi … H2n) -H2n #H2n <H2n -H2n #Ht1 //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst …))
  [ @fsubst_eq_repl [ // | // ]
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_canc_dx … (unwind2_term_after_lift …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    >list_append_rcons_sn <reverse_append
    @(stream_eq_trans … (tr_compose_uni_dx …))
    @tr_compose_eq_repl
    [ <unwind2_rmap_append_pap_closed //
    | >unwind2_rmap_A_sn <reverse_rcons
      /2 width=1 by tls_unwind2_rmap_closed/
    ]
(* Note: crux of the proof ends *)
  | //
  | /2 width=2 by ex_intro/
  | /2 width=6 by lift_term_proper/
  ]
]
qed.