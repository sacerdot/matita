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
      ♭p = ♭⊗p.
#p elim p -p //
* [ #k || #F ] #p #IH //
[ <structure_L_dx <depth_L_dx <depth_L_dx //
| <structure_A_dx <depth_A_dx <depth_A_dx //
| <structure_S_dx <depth_S_dx <depth_S_dx //
]
qed.
