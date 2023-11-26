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
include "delayed_updating/syntax/path_inner.ma".

(* STRUCTURE FOR PATH *******************************************************)

(* Constructions with pic ***************************************************)

lemma structure_pic (p):
      ⊗p ϵ 𝐈.
#p elim p -p
[ <structure_empty //
| * [ #k ] #p #IH
  [ <structure_d_dx //
  | <structure_L_dx //
  | <structure_A_dx //
  | <structure_S_dx //
  ]
]
qed.

(* Inversions with pic ******************************************************)

lemma eq_inv_empty_structure_inner (p):
      p ϵ 𝐈 → 𝐞 = ⊗p → 𝐞 = p.
#p * -p // #p
[ <structure_L_dx
| <structure_A_dx
| <structure_S_dx
] #H0 destruct
qed-.
