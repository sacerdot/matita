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

include "delayed_updating/unwind/unwind2_rmap_labels.ma".
include "delayed_updating/unwind/nap.ma".
include "delayed_updating/syntax/path_head_depth.ma".
include "delayed_updating/syntax/path_height.ma".

(* UNWIND MAP FOR PATH ******************************************************)

(* Constructions with path_head *********************************************)

lemma unwind2_rmap_head_push (f) (p) (n):
      n + ♯(↳[n]p) = (▶[⫯f]↳[n]p)@↑❨n❩.
#f #p elim p -p
[ #n <path_head_empty <unwind2_rmap_labels_L <height_labels_L
  >tr_pushs_swap <tr_nap_pushs_lt //
| #l #p #IH #n @(nat_ind_succ … n) -n //
  #n #_ cases l [ #m ]
  [ <unwind2_rmap_d_sn <path_head_d_sn <height_d_sn
    <nplus_assoc >IH -IH <tr_compose_nap //
  | <unwind2_rmap_m_sn <path_head_m_sn <height_m_sn //
  | <unwind2_rmap_L_sn <path_head_L_sn <height_L_sn
    <tr_nap_push <npred_succ //
  | <unwind2_rmap_A_sn <path_head_A_sn <height_A_sn //
  | <unwind2_rmap_S_sn <path_head_S_sn <height_S_sn //
  ]
]
qed.
