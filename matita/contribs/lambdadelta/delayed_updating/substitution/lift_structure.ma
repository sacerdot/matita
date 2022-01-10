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
include "delayed_updating/substitution/lift_eq.ma".

(* LIFT FOR PATH ***********************************************************)

(* Constructions with structure ********************************************)

lemma lift_d_empty_dx (n) (p) (f):
      (⊗p)◖𝗱((↑[p]f)@❨n❩) = ↑[f](p◖𝗱n).
#n #p @(path_ind_lift … p) -p // [ #m #l #p |*: #p ] #IH #f
[ <lift_rmap_d_sn <lift_path_d_lcons_sn //
| <lift_rmap_L_sn <lift_path_L_sn <IH //
| <lift_rmap_A_sn <lift_path_A_sn <IH //
| <lift_rmap_S_sn <lift_path_S_sn <IH //
]
qed.

lemma lift_L_dx (p) (f):
      (⊗p)◖𝗟 = ↑[f](p◖𝗟).
#p @(path_ind_lift … p) -p // #m #l #p #IH #f
<lift_path_d_lcons_sn //
qed.

lemma lift_A_dx (p) (f):
      (⊗p)◖𝗔 = ↑[f](p◖𝗔).
#p @(path_ind_lift … p) -p // #m #l #p #IH #f
<lift_path_d_lcons_sn //
qed.

lemma lift_S_dx (p) (f):
      (⊗p)◖𝗦 = ↑[f](p◖𝗦).
#p @(path_ind_lift … p) -p // #m #l #p #IH #f
<lift_path_d_lcons_sn //
qed.

lemma structure_lift (p) (f):
      ⊗p = ⊗↑[f]p.
#p @(path_ind_lift … p) -p // #p #IH #f
<lift_path_L_sn //
qed.

lemma lift_structure (p) (f):
      ⊗p = ↑[f]⊗p.
#p @(path_ind_lift … p) -p //
qed.
