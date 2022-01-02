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
      (⊗p)◖𝗱❨(↑[p◖𝗱❨n❩]f)@❨n❩❩ = ↑[f](p◖𝗱❨n❩).
#n #p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| <list_cons_shift <list_cons_comm <list_cons_comm //
| <lift_d_lcons_sn <lift_d_lcons_sn //
| <lift_L_sn <lift_L_sn <lift_lcons <IH //
| <lift_A_sn <lift_A_sn <lift_lcons <IH //
| <lift_S_sn <lift_S_sn <lift_lcons <IH //
]
qed.

lemma lift_L_dx (p) (f):
      (⊗p)◖𝗟 = ↑[f](p◖𝗟).
#p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| //
| <lift_d_lcons_sn //
| <lift_L_sn <lift_lcons //
| <lift_A_sn <lift_lcons //
| <lift_S_sn <lift_lcons //
]
qed.

lemma lift_A_dx (p) (f):
      (⊗p)◖𝗔 = ↑[f](p◖𝗔).
#p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| //
| <lift_d_lcons_sn //
| <lift_L_sn <lift_lcons //
| <lift_A_sn <lift_lcons //
| <lift_S_sn <lift_lcons //
]
qed.

lemma lift_S_dx (p) (f):
      (⊗p)◖𝗦 = ↑[f](p◖𝗦).
#p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| //
| <lift_d_lcons_sn //
| <lift_L_sn <lift_lcons //
| <lift_A_sn <lift_lcons //
| <lift_S_sn <lift_lcons //
]
qed.

lemma structure_lift (p) (f):
      ⊗p = ⊗↑[f]p.
#p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| //
| //
| <lift_L_sn <lift_lcons //
| <lift_A_sn <lift_lcons //
| <lift_S_sn <lift_lcons //
]
qed.

lemma lift_structure (p) (f):
      ⊗p = ↑[f]⊗p.
#p elim p -p
[| * [ #m * [| #l ]] [|*: #p ] #IH ] #f
[ //
| //
| //
| <structure_L_sn <lift_L_sn <lift_lcons //
| <structure_A_sn <lift_A_sn <lift_lcons //
| <structure_S_sn <lift_S_sn <lift_lcons //
]
qed.
