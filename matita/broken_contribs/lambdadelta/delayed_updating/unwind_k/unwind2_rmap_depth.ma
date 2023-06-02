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
include "ground/relocation/trz_id_after.ma".
include "ground/relocation/trz_pushs_le.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with depth *************************************************)

lemma unwind2_rmap_decompose (p) (f):
      ▶[f]p ≐ (⫯*[♭p]f)•(▶[𝐢]p).
#p elim p -p
[ #f <unwind2_rmap_empty <unwind2_rmap_empty <trz_pushs_zero //
| * [ #k ] #p #IH #f //
  <unwind2_rmap_L_dx <unwind2_rmap_L_dx <depth_L_dx
  <trz_pushs_succ
  @(trz_eq_trans … (trz_after_push_bi …))
  /2 width=1 by trz_push_eq_repl_fwd/
]
qed.

lemma unwind2_rmap_unfold_be (f) (p) (h):
      (⁤𝟏) ≤ (▶[𝐢]p)＠⧣❨h❩ → (▶[𝐢]p)＠⧣❨h❩ ≤ ⊕♭p →
      (▶[𝐢]p)＠⧣❨h❩ = (▶[f]p)＠⧣❨h❩.
#f #p #h #H1h #H2h
>(trz_dapp_eq_repl_fwd … (▶[f]p) … (unwind2_rmap_decompose …))
<trz_after_unfold <trz_pushs_unfold_be //
qed-.
