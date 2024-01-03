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

include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/path_structure.ma".

(* EQUIVALENCE FOR PROTOTERM ************************************************)

(* Constructions with path_structure ****************************************)

lemma term_slice_structure_pAbLq (p) (xa) (b) (xl) (q):
      (𝐞) = ⊗xa → (𝐞) = ⊗xl →
      ↑(⊗p●𝗔◗⊗b●𝗟◗⊗q) ⇔ ↑⊗(p●xa●𝗔◗b●xl●𝗟◗q).
#p #xa #b #xl #q #Ha #Hl
<structure_append <structure_append <Ha <structure_A_sn -Ha
<structure_append <structure_append <Hl <structure_L_sn -Hl
<list_append_empty_dx <list_append_empty_dx //
qed.
