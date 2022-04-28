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

include "delayed_updating/unwind0/unwind1_rmap_eq.ma".
include "delayed_updating/unwind0/unwind1_path.ma".
include "delayed_updating/substitution/lift_structure.ma".

(* BASIC UNWIND FOR PATH ****************************************************)

(* Constructions with structure *********************************************)

fact unwind1_path_d_dx_aux (k) (p) (n):
     k = ❘p❘ → (⊗p)◖𝗱((▶p)@❨n❩) = ▼(p◖𝗱n).
#k @(nat_ind_succ … k) -k
[ #p #n #H0 >(list_length_inv_zero_sn … H0) -p //
| #k #IH *
  [ #n #H0 elim (eq_inv_nsucc_zero … H0)
  | * [ #m ] #p #n #H0
    lapply (eq_inv_nsucc_bi … H0) -H0
    [ cases p -p [ -IH | #l #p ] #H0 destruct <unwind1_path_d_lcons
      [ <lift_path_d_sn <lift_path_empty <unwind1_path_d_empty
        <list_cons_comm <(tr_pap_eq_repl … (unwind1_rmap_d_empty …)) //
      | >list_cons_shift <lift_path_d_dx <IH -IH //
        <structure_lift <structure_d_sn /3 width=1 by eq_f2/
      ]
    | #H0 destruct <unwind1_path_m_sn <IH -IH //
    | #H0 destruct <unwind1_path_L_sn <IH -IH //
    | #H0 destruct <unwind1_path_A_sn <IH -IH //
    | #H0 destruct <unwind1_path_S_sn <IH -IH //
    ]
  ]
]
qed-.

lemma unwind1_path_d_dx (p) (n):
      (⊗p)◖𝗱((▶p)@❨n❩) = ▼(p◖𝗱n).
/2 width=2 by unwind1_path_d_dx_aux/ qed.
