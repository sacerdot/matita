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

include "delayed_updating/unwind_k/unwind2_rmap.ma".
include "delayed_updating/syntax/path_unwindable.ma".
include "delayed_updating/syntax/path_structure_width.ma".
include "ground/relocation/trz_push_le.ma".
include "ground/relocation/trz_id.ma".
include "ground/arith/int_nat_le.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with puwc **************************************************)

lemma unwind2_rmap_id_dapp_width (q):
      q ϵ 𝐖 ⃖ →
      ↑♮(⊗q) = (▶[𝐢]q)＠⧣❨↑♮q❩.
#q elim q -q //
* [ #k ] #q #IH #Hq
[ /3 width=2 by puwc_inv_d_dx/
| /3 width=1 by puwc_inv_m_dx/
| elim (puwc_inv_L_dx … Hq) -Hq #H1q #H2q
  <unwind2_rmap_L_dx <structure_L_dx <width_L_dx <width_L_dx
  <trz_push_gt_gt
  [ <(IH … H1q) -IH -H1q -H2q //
  | <(IH … H1q) -IH -H1q -H2q
    /2 width=1 by zle_succ_bi/
  | /2 width=1 by zlt_succ_bi/
  ]
| /3 width=1 by puwc_inv_A_dx/
| /3 width=1 by puwc_inv_S_dx/
]
qed-.

(*

definition closed_1: predicate path ≝
           λr. ∀p,k,q. r = p●𝗱k◗q → k ≤ ♮p.

lemma pippo (q) (m) (f):
      f＠⧣❨m❩+♮(⊗q) = (▶[f]q)＠⧣❨m+♮q❩.
#q @(list_ind_rcons … q) -q //
#q * [ #k ] #IH #m #f //
[ <unwind2_rmap_d_sn <structure_d_sn <width_d_sn
| <unwind2_rmap_L_sn <structure_L_sn <width_L_sn <width_L_sn
  <zplus_succ_shift <zplus_succ_shift <IH -IH
  @eq_f2 //
| <unwind2_rmap_A_sn <structure_A_sn <width_A_sn <width_A_sn //
| <unwind2_rmap_S_sn <structure_S_sn <width_S_sn <width_S_sn //
]

*)