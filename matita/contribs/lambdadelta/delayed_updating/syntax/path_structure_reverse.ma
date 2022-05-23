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
include "delayed_updating/syntax/path_reverse.ma".

(* STRUCTURE FOR PATH *******************************************************)

(* Constructions with reverse ***********************************************)

lemma structure_reverse (p):
      (⊗p)ᴿ = ⊗(pᴿ).
#p elim p -p //
* [ #n ] #p #IH <reverse_lcons //
[ <structure_d_sn <structure_d_dx //
| <structure_m_sn <structure_m_dx //
]
qed.
