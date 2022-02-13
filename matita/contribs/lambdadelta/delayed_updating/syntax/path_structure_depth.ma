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

include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_depth.ma".

(* STRUCTURE FOR PATH *******************************************************)

(* Constructions with depth *************************************************)

lemma depth_structure (p):
      ❘p❘ = ❘⊗p❘.
#p elim p -p //
* [ #n ] #p #IH //
[ <structure_L_sn <depth_L_sn <depth_L_sn //
| <structure_A_sn <depth_A_sn <depth_A_sn //
| <structure_S_sn <depth_S_sn <depth_S_sn //
]
qed.
