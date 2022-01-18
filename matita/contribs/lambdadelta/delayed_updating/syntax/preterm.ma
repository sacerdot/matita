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
include "delayed_updating/notation/relations/predicate_t_hook_1.ma".

(* PRETERM ******************************************************************)

(* Note: different root paths have different structure *)
definition structure_injective: predicate prototerm ≝
           λt. ∀p1,p2. p1 ϵ ▵t → p2 ϵ ▵t → ⊗p1 = ⊗p2 → p1 = p2
.

(* Note: a preterm is a prototerm satislying the conditions above *)
record is_preterm (t): Prop ≝
{
  is_pt_injective: structure_injective t
}.

interpretation
  "preterm condition (prototerm)"
  'PredicateTHook t = (is_preterm t).
