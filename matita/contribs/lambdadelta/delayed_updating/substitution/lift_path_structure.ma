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

include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_structure.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with structure *********************************************)

lemma structure_lift_path (p) (f):
      ⊗p = ⊗↑[f]p.
#p elim p -p //
* [ #n ] #p #IH #f //
[ <lift_path_d_sn <structure_d_sn <structure_d_sn //
| <lift_path_m_sn <structure_m_sn <structure_m_sn //
| <lift_path_L_sn <structure_L_sn <structure_L_sn //
]
qed.

lemma lift_path_structure (p) (f):
      ⊗p = ↑[f]⊗p.
#p elim p -p //
* [ #n ] #p #IH #f //
qed.
