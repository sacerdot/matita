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
include "ground/lib/stream_eq_eq.ma".

(* LIFT MAP FOR PATH ********************************************************)

(* Constructions with path_head *********************************************)

lemma tls_plus_lift_rmap_reverse_closed (f) (q) (p) (n) (k):
      q = (↳[n]q)●p →
      ⇂*[k]↑[pᴿ]f ≗ ⇂*[n+k]↑[qᴿ]f.
#f #q elim q -q
[ #p #n #k #Hp
  elim (eq_inv_list_empty_append … Hp) -Hp #Hn #H0 destruct
  <path_head_empty in Hn; #Hn
  <(eq_inv_empty_labels … Hn) -n //
| #l #q #IH #p #n @(nat_ind_succ … n) -n //
  #n #_ #k cases l [ #m ]
  [ <path_head_d_sn <list_append_lcons_sn #Hp
    elim (eq_inv_list_lcons_bi ????? Hp) -Hp #_ #Hp <nrplus_inj_sn
    <reverse_lcons
    @(stream_eq_trans … (tls_lift_rmap_d_dx …))
    >nrplus_inj_dx >nrplus_inj_sn >nrplus_inj_sn <nplus_plus_comm_23
    >nsucc_unfold /2 width=1 by/
  | <path_head_m_sn <list_append_lcons_sn #Hp
    elim (eq_inv_list_lcons_bi ????? Hp) -Hp #_ #Hp
    <reverse_lcons <lift_rmap_m_dx /2 width=1 by/
  | <path_head_L_sn <list_append_lcons_sn #Hp
    elim (eq_inv_list_lcons_bi ????? Hp) -Hp #_ #Hp
    <reverse_lcons <lift_rmap_L_dx <nplus_succ_sn /2 width=1 by/
  | <path_head_A_sn <list_append_lcons_sn #Hp
    elim (eq_inv_list_lcons_bi ????? Hp) -Hp #_ #Hp
    <reverse_lcons <lift_rmap_A_dx /2 width=2 by/
  | <path_head_S_sn <list_append_lcons_sn #Hp
    elim (eq_inv_list_lcons_bi ????? Hp) -Hp #_ #Hp
    <reverse_lcons <lift_rmap_S_dx /2 width=2 by/
  ]
]
qed-.

lemma tls_lift_rmap_append_closed (f) (p) (q) (n):
      qᴿ = ↳[n](p●q)ᴿ →
      ↑[p]f ≗ ⇂*[n]↑[p●q]f.
#f #p #q #n #H0
>(reverse_reverse p) >(reverse_reverse q)
/2 width=1 by tls_plus_lift_rmap_reverse_closed/
qed.
