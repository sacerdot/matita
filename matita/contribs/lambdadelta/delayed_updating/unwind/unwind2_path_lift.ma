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

include "delayed_updating/unwind/unwind2_path_eq.ma".
include "delayed_updating/substitution/lift_eq.ma".

(* UNWIND FOR PATH **********************************************************)

(* Properties with lift_path ************************************************)

lemma unwind2_lift_path_after (p) (f1) (f2):
      ↑[f2]▼[f1]p = ▼[f2∘f1]p.
#p @(path_ind_unwind … p) -p // [ #n | #p ] #IH #f1 #f2
[ <unwind2_path_d_empty <unwind2_path_d_empty
  <lift_path_d_sn <lift_path_empty //
| <unwind2_path_L_sn <unwind2_path_L_sn <lift_path_L_sn
  >tr_compose_push_bi //
]
qed.
