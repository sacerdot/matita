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

include "delayed_updating/unwind_k/unwind2_path_append.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/relocation/tr_minus_eq.ma".
include "ground/relocation/tr_id_compose.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/xap.ma".
include "ground/lib/stream_eq_eq.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with depth *************************************************)

lemma unwind2_rmap_decompose (p) (f):
      ▶[f]p ≐ (⫯*[♭p]f)•(▶[𝐢]p).
#p elim p -p
[ #f <unwind2_rmap_empty <unwind2_rmap_empty <tr_pushs_zero //
| * [ #k || #e ] #p #IH #f //
  [ <unwind2_rmap_d_dx <unwind2_rmap_d_dx <depth_d_dx
    @(stream_eq_trans … (tr_compose_assoc …))
    /2 width=1 by tr_compose_eq_repl/
  | <unwind2_rmap_z_dx <unwind2_rmap_z_dx <depth_z_dx
    @(stream_eq_trans … (tr_minus_eq_repl … (IH …))) -IH
  | <unwind2_rmap_L_dx <unwind2_rmap_L_dx <depth_L_dx
    <tr_pushs_succ <tr_compose_push_bi
    /2 width=1 by tr_push_eq_repl/
  ]
]
qed.

lemma unwind2_rmap_unfold_be (f) (p) (h):
      (⁤𝟏) ≤ (▶[𝐢]p)＠⧣❨h❩ → (▶[𝐢]p)＠⧣❨h❩ ≤ ⊕♭p →
      (▶[𝐢]p)＠⧣❨h❩ = (▶[f]p)＠⧣❨h❩.
#f #p #h #H1h #H2h
>(trz_dapp_eq_repl … (▶[f]p) … (unwind2_rmap_decompose …))
<trz_after_dapp <trz_pushs_dapp_be //
qed-.
