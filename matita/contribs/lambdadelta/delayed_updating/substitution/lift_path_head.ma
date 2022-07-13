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
include "delayed_updating/syntax/path_head.ma".
include "ground/relocation/xap.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with head for path *****************************************)

lemma lift_path_head_closed (f) (p) (q) (n):
      q = ↳[n]q →
      ↳[↑[p●q]f＠❨n❩]↑[↑[p]f]q = ↑[↑[p]f]q.
#f #p #q elim q -q
[ #n #H0
  <(eq_inv_path_empty_head … H0) -H0
  <path_head_zero //
| #l #q #IH #n @(nat_ind_succ …n) -n [| #n #_ ]
  [ <path_head_zero #H0 destruct
  | cases l [ #k ]
    [ <path_head_d_dx #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <lift_rmap_d_dx <lift_path_d_dx
      <tr_xap_succ_nap <path_head_d_dx
      <(IH … H0) in ⊢ (???%); -IH -H0 <tr_xap_plus //
    | <path_head_m_dx #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <lift_rmap_m_dx <lift_path_m_dx
      <tr_xap_succ_nap <path_head_m_dx
      <(IH … H0) in ⊢ (???%); -IH -H0 //
    | <path_head_L_dx #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <lift_rmap_L_dx <lift_path_L_dx
      <tr_xap_succ_nap <path_head_L_dx
      <(IH … H0) in ⊢ (???%); -IH -H0 //
    | <path_head_A_dx #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <lift_rmap_A_dx <lift_path_A_dx
      <tr_xap_succ_nap <path_head_A_dx
      <(IH … H0) in ⊢ (???%); -IH -H0 //
    | <path_head_S_dx #H0
      elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #H0
      <lift_rmap_S_dx <lift_path_S_dx
      <tr_xap_succ_nap <path_head_S_dx
      <(IH … H0) in ⊢ (???%); -IH -H0 //
    ]
  ]
]
qed.
