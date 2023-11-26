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
include "delayed_updating/syntax/path_structure.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with structure *********************************************)

lemma structure_lift_path (f) (p):
      ⊗p = ⊗🠡[f]p.
#f #p elim p -p //
* [ #k ] #p #IH //
<lift_path_d_dx <structure_d_dx <structure_d_dx //
qed.

lemma lift_path_structure (f) (p):
      ⊗p = 🠡[f]⊗p.
#f #p elim p -p //
* [ #k ] #p #IH //
qed.
