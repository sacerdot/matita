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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/notation/functions/class_t_0.ma".

(* PRETERM ******************************************************************)

(* Note: a preterm is a prototerm satislying the condition below *)
(* Note: different root paths have different structure *)
definition structure_injective: predicate prototerm ≝
           λt. ∀p1,p2. p1 ϵ ▵t → p2 ϵ ▵t → ⊗p1 = ⊗p2 → p1 = p2
.

interpretation
  "preterm (prototerm)"
  'ClassT = (structure_injective).

(* Basic inversions *********************************************************)

lemma preterm_in_root_append_inv_structure_empty_dx (t) (p) (q):
      p●q ϵ ▵t → t ϵ 𝐓 → 𝐞 = ⊗q → 𝐞 = q.
#t #p #q #Hpq #Ht #Hq
lapply (Ht p ?? Hpq ?)
[ <structure_append //
| /2 width=2 by prototerm_in_root_append_des_sn/
| /2 width=3 by eq_inv_list_append_dx_dx_refl/
]
qed-.
