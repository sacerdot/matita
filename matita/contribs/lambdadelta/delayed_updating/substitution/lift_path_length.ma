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
include "ground/lib/list_length.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with list_length *******************************************)

lemma lift_path_length (p) (f):
      ❘p❘ = ❘↑[f]p❘.
#p elim p -p // * [ #n ] #p #IH #f //
[ <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
]
>list_length_lcons >list_length_lcons //
qed.
