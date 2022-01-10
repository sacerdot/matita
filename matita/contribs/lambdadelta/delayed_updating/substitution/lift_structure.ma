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

include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_proper.ma".

(* LIFT FOR PATH ***********************************************************)

(* Basic constructions with structure **************************************)

lemma structure_lift (p) (f):
      ⊗p = ⊗↑[f]p.
#p @(path_ind_lift … p) -p // #p #IH #f
<lift_path_L_sn //
qed.

lemma lift_structure (p) (f):
      ⊗p = ↑[f]⊗p.
#p @(path_ind_lift … p) -p //
qed.

(* Properties with proper condition for path ********************************)

lemma lift_append_proper_dx (p2) (p1) (f): Ꝕp2 →
      (⊗p1)●(↑[↑[p1]f]p2) = ↑[f](p1●p2).
#p2 #p1 @(path_ind_lift … p1) -p1 //
[ #n | #n #l #p1 |*: #p1 ] #IH #f #Hp2
[ elim (ppc_inv_lcons … Hp2) -Hp2 #l #q #H destruct //
| <lift_path_d_lcons_sn <IH //
| <lift_path_L_sn <IH //
| <lift_path_A_sn <IH //
| <lift_path_S_sn <IH //
]
qed-.

(* Advanced constructions with structure ************************************)

lemma lift_d_empty_dx (n) (p) (f):
      (⊗p)◖𝗱((↑[p]f)@❨n❩) = ↑[f](p◖𝗱n).
/3 width=3 by ppc_lcons, lift_append_proper_dx/
qed.

lemma lift_L_dx (p) (f):
      (⊗p)◖𝗟 = ↑[f](p◖𝗟).
/3 width=3 by ppc_lcons, lift_append_proper_dx/
qed.

lemma lift_A_dx (p) (f):
      (⊗p)◖𝗔 = ↑[f](p◖𝗔).
/3 width=3 by ppc_lcons, lift_append_proper_dx/
qed.

lemma lift_S_dx (p) (f):
      (⊗p)◖𝗦 = ↑[f](p◖𝗦).
/3 width=3 by ppc_lcons, lift_append_proper_dx/
qed.
