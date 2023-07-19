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
include "delayed_updating/syntax/path_closed.ma". (**)
include "delayed_updating/syntax/path_unwindable.ma".
include "delayed_updating/syntax/path_structure_width.ma".
include "ground/relocation/trz_tls_lapp.ma". (**)
include "ground/relocation/trz_push_le.ma".
include "ground/relocation/trz_id.ma".
include "ground/relocation/trz_lapp.ma".
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
  <trz_push_dapp_gt_gt
  [ <(IH … H1q) -IH -H1q -H2q //
  | <(IH … H1q) -IH -H1q -H2q
    /2 width=1 by zle_succ_bi/
  | /2 width=1 by zlt_succ_bi/
  ]
| /3 width=1 by puwc_inv_A_dx/
| /3 width=1 by puwc_inv_S_dx/
]
qed-.

theorem unwind2_rmap_id_lapp_width (q):
        q ϵ 𝐖 ⃖ →
        ♮(⊗q) = (▶[𝐢]q)＠§❨♮q❩.
#q #Hq
<(unwind2_rmap_id_dapp_width … Hq) -Hq //
qed-.
(*
lemma pippo (p) (q):
      p●q ϵ 𝐖 ⃖ →
      ♮(⊗q) = 𝟎.
#p #q #Hpq
lapply (puwc_des_append … Hpq) #Hp
>(zplus_minus_simpl (♮(⊗q)) (♮(⊗p)))
<zplus_comm in ⊢ (??(?%?)?);
>width_append >structure_append
>(unwind2_rmap_id_lapp_width … Hpq)
>(unwind2_rmap_id_lapp_width … Hp)
<width_append <trz_lapp_plus_dx
<zplus_plus_comm_23

(* <unwind2_rmap_append *)

*)

lemma pippo (p) (f):
      ▶[𝐢]p = f →
      ∀q. p●q ϵ 𝐂 →
      f＠⧣❨𝟎❩+♮(⊗q) = (▶[f]q)＠⧣❨♮q❩.
#p #f #Hf destruct
#q elim q -q //
* [ #k ] #q #IH #Hq
[ elim (pcc_inv_d_dx … Hq) -Hq #Hq #_
  <unwind2_rmap_d_dx <structure_d_dx <width_d_dx
  /2 width=1 by/
| <unwind2_rmap_m_dx <structure_m_dx <width_m_dx
  /3 width=1 by pcc_inv_m_dx/
| elim (pcc_inv_L_dx … Hq) -Hq #H1q #H2q
  <unwind2_rmap_L_dx <structure_L_dx <width_L_dx <width_L_dx
  <zplus_succ_dx >IH -IH // -H1q
| <unwind2_rmap_A_dx <structure_A_dx <width_A_dx <width_A_dx
  /3 width=1 by pcc_inv_A_dx/
| <unwind2_rmap_S_dx <structure_S_dx <width_S_dx <width_S_dx
  /3 width=1 by pcc_inv_S_dx/
]
