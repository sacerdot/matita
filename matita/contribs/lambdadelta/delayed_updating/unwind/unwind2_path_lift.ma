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
include "delayed_updating/substitution/lift_path_prelift.ma".

(* UNWIND FOR PATH **********************************************************)

(* Constructions with lift_path *********************************************)

lemma lift_unwind2_path_after (p) (f1) (f2):
      ↑[f2]▼[f1]p = ▼[f2∘f1]p.
#p @(path_ind_unwind … p) -p // [ #n | #p ] #IH #f1 #f2
[ <unwind2_path_d_empty <unwind2_path_d_empty
  <lift_path_d_sn <lift_path_empty //
| <unwind2_path_L_sn <unwind2_path_L_sn <lift_path_L_sn
  >tr_compose_push_bi //
]
qed.

lemma unwind2_path_after_lift (p) (f1) (f2):
      ▼[f2]↑[f1]p = ▼[f2∘f1]p.
#p @(path_ind_unwind … p) -p // [ #n #l ] #p #IH #f1 #f2
[ <lift_path_d_sn <unwind2_path_d_lcons
  <lift_path_lcons_prelift <unwind2_path_d_lcons >lift_path_lcons_prelift
  >IH -IH
  >(unwind2_path_eq_repl … (tr_compose_assoc …))
  >(unwind2_path_eq_repl … (tr_compose_assoc …))
  <unwind2_path_after <unwind2_path_after in ⊢ (???%);
  /3 width=1 by unwind2_path_eq_repl, eq_f/
| <lift_path_m_sn <unwind2_path_m_sn <unwind2_path_m_sn //
| <lift_path_L_sn <unwind2_path_L_sn <unwind2_path_L_sn 
  >tr_compose_push_bi //
]
qed.
