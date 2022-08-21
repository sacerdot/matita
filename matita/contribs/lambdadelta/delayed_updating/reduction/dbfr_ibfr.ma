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

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Main destructions with ibfr **********************************************)

theorem dbfr_des_ibfr (f) (t1) (t2) (r): t1 ϵ 𝐓 →
        t1 ➡𝐝𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H0t1
* #p #b #q #h #k #Hr #Hb #Hh #H1k #Ht1 #Ht2 destruct
@(ex6_5_intro … (⊗p) (⊗b) (⊗q) (♭b) (↑♭q))
[ -H0t1 -Hb -Hh -H1k -Ht1 -Ht2 //
| -H0t1 -Hh -H1k -Ht1 -Ht2 //
| -H0t1 -Hb -Ht1 -H1k -Ht2
  >Hh in ⊢ (??%?); >path_head_structure_depth <Hh -Hh //
| -H0t1 -Hb -Hh -Ht1 -Ht2
  >structure_L_sn
  >H1k in ⊢ (??%?); >path_head_structure_depth <H1k -H1k //
| lapply (in_comp_unwind2_path_term f … Ht1) -Ht2 -Ht1 -H0t1 -Hb -Hh
  <unwind2_path_d_dx >list_append_rcons_dx >list_append_assoc
  lapply (unwind2_rmap_append_pap_closed f … (p●𝗔◗b) … H1k) -H1k
  <depth_L_sn #H2k
  lapply (eq_inv_ninj_bi … H2k) -H2k #H2k <H2k -H2k #Ht1 //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  lapply (path_head_refl_append_bi … Hh H1k) -Hh -H1k <nrplus_inj_sn #H1k
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_ppc …))
  [ @fsubst_eq_repl [ // | // ]
    @(subset_eq_trans … (unwind2_term_iref …))
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    <list_append_rcons_sn
    @(stream_eq_trans … (tr_compose_uni_dx …))
    @tr_compose_eq_repl
    [ <unwind2_rmap_append_pap_closed //
      <depth_append <depth_L_sn
      <nplus_comm <nrplus_npsucc_sn <nplus_succ_sn //
    | >unwind2_rmap_A_dx
      /2 width=1 by tls_unwind2_rmap_closed/
    ]
(* Note: crux of the proof ends *)
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
qed.
