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
include "delayed_updating/unwind/xap.ma".
include "delayed_updating/syntax/path_head_depth.ma".
include "ground/arith/nat_le_plus.ma".

(* UNWIND MAP FOR PATH ******************************************************)

(* Constructions with path_head *********************************************)

lemma unwind2_rmap_head_xap_closed (f) (p) (n) (k):
      (∃q. p = (↳[n]p)●q) → k ≤ n →
      (▶[f]p)＠❨k❩ = (▶[f]↳[n]p)＠❨k❩.
#f #p elim p -p
[ #n #k * #q #Hq #Hk
  elim (eq_inv_list_empty_append … Hq) -Hq * #_ //
| #l #p #IH #n @(nat_ind_succ … n) -n
  [ #k #_ #Hk <(nle_inv_zero_dx … Hk) -k -IH
   <path_head_zero <unwind2_rmap_empty //
  | #n #_ #k cases l [ #m ] * #q
    [ <path_head_d_sn <list_append_lcons_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_d_sn <unwind2_rmap_d_sn
      <tr_compose_xap <tr_compose_xap
      @IH [ /2 width=2 by ex_intro/ ] (**) (* auto too slow *)
      @nle_trans [| @tr_uni_xap ]
      /2 width=1 by nle_plus_bi_dx/
    | <path_head_m_sn <list_append_lcons_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_m_sn <unwind2_rmap_m_sn
      /3 width=2 by ex_intro/
    | <path_head_L_sn <list_append_lcons_sn #Hq
      @(nat_ind_succ … k) -k // #k #_ #Hk
      lapply (nle_inv_succ_bi … Hk) -Hk #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_L_sn <unwind2_rmap_L_sn
      <tr_xap_push <tr_xap_push
      /4 width=2 by ex_intro, eq_f/
    | <path_head_A_sn <list_append_lcons_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_A_sn <unwind2_rmap_A_sn
      /3 width=2 by ex_intro/
    | <path_head_S_sn <list_append_lcons_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_S_sn <unwind2_rmap_S_sn
      /3 width=2 by ex_intro/
    ]
  ]
]
qed-.

lemma unwind2_rmap_head_xap (f) (p) (n):
      n + ♯(↳[n]p) = (▶[f]↳[n]p)＠❨n❩.
#f #p elim p -p
[ #n <path_head_empty <unwind2_rmap_labels_L <height_labels_L
  <tr_xap_pushs_le //
| #l #p #IH #n @(nat_ind_succ … n) -n //
  #n #_ cases l [ #m ]
  [ <unwind2_rmap_d_sn <path_head_d_sn <height_d_sn
    <nplus_assoc >IH -IH <tr_compose_xap <tr_uni_xap_succ //
  | <unwind2_rmap_m_sn <path_head_m_sn <height_m_sn //
  | <unwind2_rmap_L_sn <path_head_L_sn <height_L_sn
    <tr_xap_push <npred_succ //
  | <unwind2_rmap_A_sn <path_head_A_sn <height_A_sn //
  | <unwind2_rmap_S_sn <path_head_S_sn <height_S_sn //
  ]
]
qed.
