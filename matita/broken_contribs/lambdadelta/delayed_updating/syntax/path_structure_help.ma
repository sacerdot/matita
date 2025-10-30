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

(* STRUCTURE FOR PATH *******************************************************)

(* Helper constructions *****************************************************)

lemma path_structure_pAbLq (p) (b) (q):
      ⊗p●𝗔◗⊗b●𝗟◗⊗q = ⊗(p●𝗔◗b●𝗟◗q).
//
qed.

lemma path_structure_pAbLq_flat (p) (xa) (b) (xl) (q):
      (𝐞) = ⊗xa → (𝐞) = ⊗xl →
      ⊗p●𝗔◗⊗b●𝗟◗⊗q = ⊗(p●xa●𝗔◗b●xl●𝗟◗q).
#p #xa #b #xl #q #Ha #Hl
<structure_append <structure_append <Ha <structure_A_sx -Ha
<structure_append <structure_append <Hl <structure_L_sx -Hl
<list_append_empty_dx <list_append_empty_dx //
qed.

(* Helper inversions ********************************************************)

lemma eq_inv_path_A_sx_append_flat_sx (p) (q1) (q2:ℙ):
      (𝗔)◗q1 = p●q2 → (𝐞) = ⊗p →
      ∧∧ (𝗔)◗q1 = q2 & (𝐞) = p.
#p #q1 #q2
@(list_ind_rcons … p) -p
[ <list_append_empty_dx
  /2 width=1 by conj/
| #p #l #_ <list_append_rcons_dx #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
  <structure_A_sx #H0
  elim (eq_inv_list_empty_rcons ??? H0)
]
qed-.
