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
include "delayed_updating/unwind/unwind2_rmap_eq.ma".
include "delayed_updating/syntax/path_head_depth.ma".
include "ground/relocation/xap.ma".
include "ground/lib/stream_eq_eq.ma".
include "ground/arith/nat_le_plus.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with path_head *********************************************)

lemma unwind2_rmap_head_xap_le_closed (f) (p) (q) (n) (m):
      q = ↳[n]q → m ≤ n →
      ▶[f](p●q)＠❨m❩ = ▶[f]↳[n](p●q)＠❨m❩.
#f #p #q elim q -q
[ #n #m #Hq
  <(eq_inv_path_empty_head … Hq) -n #Hm
  <(nle_inv_zero_dx … Hm) -m //
| #l #q #IH #n @(nat_ind_succ … n) -n
  [ #m #_ #Hm <(nle_inv_zero_dx … Hm) -m -IH //
  | #n #_ #m cases l [ #k ]
    [ <path_head_d_dx #Hq #Hm
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_d_dx <unwind2_rmap_d_dx
      <tr_compose_xap <tr_compose_xap
      @(IH … Hq) -IH -Hq (**) (* auto too slow *)
      @nle_trans [| @tr_uni_xap ]
      /2 width=1 by nle_plus_bi_dx/
    | <path_head_m_dx #Hq #Hm
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_m_dx <unwind2_rmap_m_dx
      /2 width=2 by/
    | <path_head_L_dx #Hq
      @(nat_ind_succ … m) -m // #m #_ #Hm
      lapply (nle_inv_succ_bi … Hm) -Hm #Hm
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_L_dx <unwind2_rmap_L_dx
      <tr_xap_push <tr_xap_push
      /3 width=2 by eq_f/
    | <path_head_A_dx #Hq #Hm
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_A_dx <unwind2_rmap_A_dx
      /2 width=2 by/
    | <path_head_S_dx #Hq #Hm
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_S_dx <unwind2_rmap_S_dx
      /2 width=2 by/
    ]
  ]
]
qed-.

lemma unwind2_rmap_head_xap_closed (f) (p) (q) (n):
      q = ↳[n]q →
      ▶[f](p●q)＠❨n❩ = ▶[f]↳[n](p●q)＠❨n❩.
/2 width=2 by unwind2_rmap_head_xap_le_closed/
qed-.

lemma unwind2_rmap_head_xap (f) (p) (n):
      n + ♯(↳[n]p) = (▶[f]↳[n]p)＠❨n❩.
#f #p elim p -p
[ #n <path_head_empty <unwind2_rmap_labels_L <height_labels_L
  <tr_xap_pushs_le //
| #l #p #IH #n @(nat_ind_succ … n) -n //
  #n #_ cases l [ #k ]
  [ <unwind2_rmap_d_dx <path_head_d_dx <height_d_dx
    <nplus_comm in ⊢ (??(??%)?); <nplus_assoc
    >IH -IH <tr_compose_xap <tr_uni_xap_succ //
  | <unwind2_rmap_m_dx <path_head_m_dx <height_m_dx //
  | <unwind2_rmap_L_dx <path_head_L_dx <height_L_dx
    <tr_xap_push <npred_succ <nplus_succ_sn //
  | <unwind2_rmap_A_dx <path_head_A_dx <height_A_dx //
  | <unwind2_rmap_S_dx <path_head_S_dx <height_S_dx //
  ]
]
qed.

lemma unwind2_rmap_append_pap_closed (f) (p) (q) (n:pnat):
      q = ↳[n]q →
      ♭q = ninj (▶[f](p●q)＠⧣❨n❩).
#f #p #q #n #Hn
>tr_xap_ninj >(path_head_refl_append p … Hn) in ⊢ (??%?);
>(unwind2_rmap_head_xap_closed … Hn) -Hn
<path_head_depth //
qed.

lemma tls_unwind2_rmap_plus_closed (f) (p) (q) (n) (m):
      q = ↳[n]q →
      ⇂*[m]▶[f]p ≗ ⇂*[n+m]▶[f](p●q).
#f #p #q elim q -q
[ #n #m #Hq
  <(eq_inv_path_empty_head … Hq) -n //
| #l #q #IH #n @(nat_ind_succ … n) -n //
  #n #_ #m cases l [ #k ]
  [ <path_head_d_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq <nrplus_inj_sn
    @(stream_eq_trans … (tls_unwind2_rmap_d_dx …))
    >nrplus_inj_dx >nrplus_inj_sn >nrplus_inj_sn <nplus_plus_comm_23
    /2 width=1 by/
  | <path_head_m_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_m_sn /2 width=1 by/
  | <path_head_L_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_L_dx <nplus_succ_sn /2 width=1 by/
  | <path_head_A_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_A_dx /2 width=2 by/
  | <path_head_S_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_S_dx /2 width=2 by/
  ]
]
qed-.

lemma tls_unwind2_rmap_closed (f) (p) (q) (n):
      q = ↳[n]q →
      ▶[f]p ≗ ⇂*[n]▶[f](p●q).
/2 width=1 by tls_unwind2_rmap_plus_closed/
qed.
