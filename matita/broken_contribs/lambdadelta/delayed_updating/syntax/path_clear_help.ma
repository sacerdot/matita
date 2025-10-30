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

include "delayed_updating/syntax/path_clear_structure.ma".
(*
include "delayed_updating/syntax/path_predex.ma".
*)
(* CLEAR FOR PATH ***********************************************************)

(* Helper constructions *****************************************************)

(* Helper constructions with structure **************************************)

lemma path_structure_pAbLq_clear (p) (xa) (b) (xl) (q):
      (𝐞) = ⊗xa → (𝐞) = ⊗xl →
      ⊗p●𝗔◗⓪⊗b●𝗟◗⊗q = ⊗(p●xa●𝗔◗⓪b●⓪xl●𝗟◗q).
#p #xa #b #xl #q #Ha #Hl
<structure_append <structure_append <Ha <structure_A_sx -Ha
<structure_append <structure_append <structure_L_sx
<path_structure_clear_swap <path_structure_clear_swap <Hl -Hl
<list_append_empty_dx <list_append_empty_dx //
qed.

lemma path_clear_structure_pAbLq (p) (b) (q):
      ⊗p●𝗔◗⊗b●𝗟◗⊗q = ⓪(⊗p●𝗔◗⊗b●𝗟◗⊗q).
// qed.

