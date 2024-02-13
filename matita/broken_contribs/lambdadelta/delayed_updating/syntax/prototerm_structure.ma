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
include "delayed_updating/syntax/prototerm.ma".

(* PROTOTERM ****************************************************************)

(* Constructions with path_structure ****************************************)

lemma term_slice_structure (p1) (p2):
      p1 ϵ ↑p2 → ⊗p1 ϵ ↑⊗p2.
#p1 #p2 * #q2 #_ #H0 destruct //
qed.
