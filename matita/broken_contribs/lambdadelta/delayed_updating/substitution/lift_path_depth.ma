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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_depth.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with depth *************************************************)

lemma lift_path_depth (f) (p):
      ♭p = ♭🠡[f]p.
#f #p elim p -p //
* [ #k ] #p #IH
[ <lift_path_d_dx <depth_d_dx <depth_d_dx
| <lift_path_m_dx <depth_m_dx <depth_m_dx
| <lift_path_L_dx <depth_L_dx <depth_L_dx
| <lift_path_A_dx <depth_A_dx <depth_A_dx
| <lift_path_S_dx <depth_S_dx <depth_S_dx
] //
qed.
