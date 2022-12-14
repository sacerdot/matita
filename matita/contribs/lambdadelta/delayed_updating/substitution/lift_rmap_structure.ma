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

include "delayed_updating/substitution/lift_rmap.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/tr_pushs.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with structure *********************************************)

lemma lift_rmap_structure (f) (q):
      (⫯*[♭q]f) = 🠢[f]⊗q.
#f #q elim q -q //
* [ #k ] #q #IH //
[ <depth_L_dx <tr_pushs_succ <structure_L_dx <lift_rmap_L_dx //
| <depth_A_dx <structure_A_dx <lift_rmap_A_dx //
| <depth_S_dx <structure_S_dx <lift_rmap_S_dx //
]
qed.
