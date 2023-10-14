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
include "delayed_updating/syntax/path_clear.ma".

(* CLEAR FOR PATH ***********************************************************)

(* Constructions with structure *********************************************)

lemma path_clear_structure (p):
      ⊗p = ⓪⊗p.
#p elim p -p //
* [ #k ] #p #IH //
qed.

lemma path_structure_clear (p):
      ⊗p = ⊗⓪p.
#p elim p -p //
* [ #k ] #p #IH //
[ <path_clear_d_dx
| <structure_m_dx >IH -IH //
] //
qed.

lemma path_structure_clear_swap (p):
      ⓪⊗p = ⊗⓪p.
// qed-.
