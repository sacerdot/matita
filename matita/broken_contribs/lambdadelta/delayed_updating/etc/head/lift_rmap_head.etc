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

include "delayed_updating/substitution/lift_rmap_eq.ma".
include "delayed_updating/syntax/path_head.ma".
include "ground/lib/stream_eq_eq.ma".

(* LIFT MAP FOR PATH ********************************************************)

(* Constructions with path_head *********************************************)

lemma tls_plus_lift_rmap_closed (f) (q) (n) (m):
      q = ↳[n]q →
      ⇂*[m]f ≗ ⇂*[n+m]↑[q]f.
#f #q elim q -q
[ #n #m #Hq
  <(eq_inv_path_empty_head … Hq) -n //
| #l #q #IH #n @(nat_ind_succ … n) -n //
  #n #_ #m cases l [ #k ]
  [ <path_head_d_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq <nrplus_inj_sn
    @(stream_eq_trans … (tls_lift_rmap_d_dx …))
    >nrplus_inj_dx >nrplus_inj_sn >nrplus_inj_sn <nplus_plus_comm_23
    >nsucc_unfold /2 width=1 by/
  | <path_head_m_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <lift_rmap_m_dx /2 width=1 by/
  | <path_head_L_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <lift_rmap_L_dx <nplus_succ_sn /2 width=1 by/
  | <path_head_A_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <lift_rmap_A_dx /2 width=2 by/
  | <path_head_S_dx #Hq
    elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
    <lift_rmap_S_dx /2 width=2 by/
  ]
]
qed-.

lemma tls_lift_rmap_closed (f) (q) (n):
      q = ↳[n]q →
      f ≗ ⇂*[n]↑[q]f.
#f #q #n #H0
/2 width=1 by tls_plus_lift_rmap_closed/
qed.
