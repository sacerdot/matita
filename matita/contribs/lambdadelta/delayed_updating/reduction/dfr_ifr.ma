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
include "delayed_updating/syntax/prototerm_proper_constructors.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

lemma dfr_lift_bi (f) (p) (q) (t1) (t2): t1 ϵ 𝐓 →
      t1 ➡𝐝𝐟[p,q] t2 → ↑[f]t1 ➡𝐟[⊗p,⊗q] ↑[f]t2.
#f #p #q #t1 #t2 #H0t1
* #b * #Hb #Ht1 #Ht2
@(ex_intro … (⊗b)) @and3_intro
[ //
| lapply (in_comp_lift_bi f … Ht1) -Ht1 #Ht1
| lapply (eq_lift_bi f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_fsubst …))
  [ <structure_append <structure_A_sn <structure_append <structure_L_sn
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
  

