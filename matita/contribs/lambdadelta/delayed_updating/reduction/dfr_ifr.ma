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
include "delayed_updating/substitution/lift_structure_depth.ma".
include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "ground/relocation/tr_pap_pushs.ma".

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
  <lift_d_empty_dx //
| lapply (eq_lift_bi f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_fsubst …))
  [ <structure_append <structure_A_sn <structure_append <structure_L_sn
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
