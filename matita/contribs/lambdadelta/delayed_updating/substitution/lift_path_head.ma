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

include "delayed_updating/substitution/lift_gen_eq.ma".
include "delayed_updating/syntax/path_head.ma".
include "delayed_updating/syntax/path_reverse.ma".
include "ground/relocation/xap.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with head for path *****************************************)

lemma lift_path_head (f) (p) (q) (n):
      pᴿ = ↳[n](pᴿ●qᴿ) →
      ↳[↑[q●p]f＠❨n❩](↑[f](q●p))ᴿ = (↑[↑[q]f]p)ᴿ.
#f #p @(list_ind_rcons … p) -p
[ #q #n #H0
  <(eq_inv_path_empty_head … H0) -H0
  <path_head_zero //
| #p #l #IH #q #n @(nat_ind_succ …n) -n [| #m #_ ]
  [ <reverse_rcons <path_head_zero #H0 destruct
  | cases l [ #n ]
    [ <reverse_rcons <path_head_d_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_d_dx <lift_path_d_dx <reverse_rcons
      <tr_xap_succ_nap <path_head_d_sn >tr_xap_succ_nap
      <lift_path_d_dx >lift_rmap_append <reverse_rcons
      <(IH … H0) -IH -H0 <tr_xap_plus //
    | <reverse_rcons <path_head_m_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_m_dx <lift_path_m_dx <reverse_rcons
      <tr_xap_succ_nap <path_head_m_sn >tr_xap_succ_nap
      <lift_path_m_dx <reverse_rcons
      <(IH … H0) -IH -H0 //
    | <reverse_rcons <path_head_L_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_L_dx <lift_path_L_dx <reverse_rcons
      <tr_xap_succ_nap <path_head_L_sn >tr_xap_succ_nap
      <lift_path_L_dx <reverse_rcons
      <(IH … H0) -IH -H0 //
    | <reverse_rcons <path_head_A_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_A_dx <lift_path_A_dx <reverse_rcons
      <tr_xap_succ_nap <path_head_A_sn >tr_xap_succ_nap
      <lift_path_A_dx <reverse_rcons
      <(IH … H0) -IH -H0 //
    | <reverse_rcons <path_head_S_sn #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <list_append_assoc <lift_rmap_S_dx <lift_path_S_dx <reverse_rcons
      <tr_xap_succ_nap <path_head_S_sn >tr_xap_succ_nap
      <lift_path_S_dx <reverse_rcons
      <(IH … H0) -IH -H0 //
    ]
  ]
]
qed.
