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

include "delayed_updating/substitution/lift_path.ma".
include "ground/lib/list_length.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with list_length *******************************************)

lemma lift_path_length (f) (p):
      ❘p❘ = ❘↑[f]p❘.
#f #p elim p -p // * [ #k ] #p #IH
[ <lift_path_d_dx
| <lift_path_m_dx
| <lift_path_L_dx
| <lift_path_A_dx
| <lift_path_S_dx
]
>list_length_lcons >list_length_lcons //
qed.
