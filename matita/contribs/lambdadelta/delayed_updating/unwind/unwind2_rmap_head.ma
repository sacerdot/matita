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

(* UNWIND MAP FOR PATH ******************************************************)

(* Constructions with path_head *********************************************)

lemma unwind2_rmap_head_xap_le_closed (f) (p) (q) (n) (k):
      p = ↳[n]p → k ≤ n →
      ▶[f](p●q)＠❨k❩ = ▶[f]↳[n](p●q)＠❨k❩.
#f #p elim p -p
[ #q #n #k #Hq
  <(eq_inv_path_empty_head … Hq) -n #Hk
  <(nle_inv_zero_dx … Hk) -k //
| #l #p #IH #q #n @(nat_ind_succ … n) -n
  [ #k #_ #Hk <(nle_inv_zero_dx … Hk) -k -IH //
  | #n #_ #k cases l [ #m ]
    [ <path_head_d_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_d_sn <unwind2_rmap_d_sn
      <tr_compose_xap <tr_compose_xap
      @(IH … Hq) -IH -Hq (**) (* auto too slow *)
      @nle_trans [| @tr_uni_xap ]
      /2 width=1 by nle_plus_bi_dx/
    | <path_head_m_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_m_sn <unwind2_rmap_m_sn
      /2 width=2 by/
    | <path_head_L_sn #Hq
      @(nat_ind_succ … k) -k // #k #_ #Hk
      lapply (nle_inv_succ_bi … Hk) -Hk #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_L_sn <unwind2_rmap_L_sn
      <tr_xap_push <tr_xap_push
      /3 width=2 by eq_f/
    | <path_head_A_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_A_sn <unwind2_rmap_A_sn
      /2 width=2 by/
    | <path_head_S_sn #Hq #Hk
      elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
      <unwind2_rmap_S_sn <unwind2_rmap_S_sn
      /2 width=2 by/
    ]
  ]
]
qed-.

lemma unwind2_rmap_head_xap_closed (f) (p) (q) (n):
      p = ↳[n]p →
      ▶[f](p●q)＠❨n❩ = ▶[f]↳[n](p●q)＠❨n❩.
/2 width=2 by unwind2_rmap_head_xap_le_closed/
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

lemma unwind2_rmap_append_pap_closed (f) (p) (q) (n:pnat):
      p = ↳[n]p →
      ♭p = ninj (▶[f](p●q)＠⧣❨n❩).
#f #p #q #n #Hn
>tr_xap_ninj >(path_head_refl_append q … Hn) in ⊢ (??%?); 
>(unwind2_rmap_head_xap_closed … Hn) -Hn
<path_head_depth //
qed.

lemma tls_unwind2_rmap_plus_closed (f) (p) (q) (n) (k):
      p = ↳[n]p →
      ⇂*[k]▶[f]q ≗ ⇂*[n+k]▶[f](p●q).
#f #p elim p -p
[ #q #n #k #Hq
  <(eq_inv_path_empty_head … Hq) -n //
| #l #p #IH #q #n @(nat_ind_succ … n) -n //
  #n #_ #k cases l [ #m ]
  [ <path_head_d_sn #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq <nrplus_inj_sn
    @(stream_eq_trans … (tls_unwind2_rmap_d_sn …))
    >nrplus_inj_dx >nrplus_inj_sn >nrplus_inj_sn <nplus_plus_comm_23
    /2 width=1 by/
  | <path_head_m_sn #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_m_sn /2 width=1 by/
  | <path_head_L_sn #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_L_sn <nplus_succ_sn /2 width=1 by/
  | <path_head_A_sn #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_A_sn /2 width=2 by/
  | <path_head_S_sn #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <unwind2_rmap_S_sn /2 width=2 by/
  ]
]
qed-.

lemma tls_unwind2_rmap_closed (f) (p) (q) (n):
      p = ↳[n]p →
      ▶[f]q ≗ ⇂*[n]▶[f](p●q).
/2 width=1 by tls_unwind2_rmap_plus_closed/
qed.
