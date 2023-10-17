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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/unwind/unwind2_rmap_lift.ma".
include "delayed_updating/substitution/lift_path_structure.ma".
include "ground/relocation/fb/fbr_after_xapp.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Constructions with lift_path *********************************************)

lemma lift_unwind2_path_after (g) (f) (p):
      (🠡[g]▼[f]p) = ▼[g•f]p.
#g #f * // * [ #k ] #p //
[ <unwind2_path_d_dx <unwind2_path_d_dx <lift_path_d_dx
  <lift_path_structure //
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
qed.

lemma unwind2_lift_path_after (g) (f) (p):
      ▼[g]🠡[f]p = ▼[g•f]p.
#g #f * // * [ #k ] #p
[ <unwind2_path_d_dx <unwind2_path_d_dx
  <structure_lift_path //
| <unwind2_path_m_dx <unwind2_path_m_dx //
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.
