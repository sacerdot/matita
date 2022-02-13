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
include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_constructors.ma".
include "delayed_updating/substitution/lift_preterm_eq.ma".
include "delayed_updating/substitution/lift_structure_depth.ma".
include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_pap_pushs.ma".

include "ground/lib/stream_eq_eq.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

lemma dfr_lift_bi (f) (p) (q) (t1) (t2): t1 ϵ 𝐓 →
      t1 ➡𝐝𝐟[p,q] t2 → ↑[f]t1 ➡𝐟[⊗p,⊗q] ↑[f]t2.
#f #p #q #t1 #t2 #H0t1
* #b #n * #Hb #Hn  #Ht1 #Ht2
@(ex1_2_intro … (⊗b) (↑❘⊗q❘)) @and4_intro
[ //
| #g <lift_rmap_structure <depth_structure
  >tr_pushs_swap <tr_pap_pushs_le //
| lapply (in_comp_lift_bi f … Ht1) -Ht1 -H0t1 -Hb -Ht2
  <lift_path_d_empty_dx //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_fsubst …))
  [ <lift_rmap_append <lift_rmap_A_sn <lift_rmap_append <lift_rmap_L_sn
    <structure_append <structure_A_sn <structure_append <structure_L_sn
    <depth_plus <depth_L_sn <depth_structure <depth_structure
    @fsubst_eq_repl [ // ]
    @(subset_eq_trans … (lift_iref …))
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @lift_grafted_S /2 width=2 by ex_intro/ | skip ]
    @(subset_eq_trans … (lift_term_after …))
    @(subset_eq_canc_dx … (lift_term_after …))
    @lift_term_eq_repl_sn -t1
    @(stream_eq_trans … (tr_compose_uni_dx …))
(*    
    >nrplus_inj_dx <tr_pap_plus
*)    
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
