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
include "ground/relocation/tr_id_compose.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/xap.ma".
include "ground/lib/stream_eq_eq.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with depth *************************************************)

lemma unwind2_rmap_decompose (p) (f):
      ▶[f]p ≗ (⫯*[♭p]f)∘(▶[𝐢]p).
#p elim p -p
[ #f <unwind2_rmap_empty <unwind2_rmap_empty <tr_pushs_zero //
| * [ #k ] #p #IH #f //
  [ <unwind2_rmap_d_dx <unwind2_rmap_d_dx <depth_d_dx
    @(stream_eq_trans … (tr_compose_assoc …))
    /2 width=1 by tr_compose_eq_repl/
  | <unwind2_rmap_L_dx <unwind2_rmap_L_dx <depth_L_dx
    <tr_pushs_succ <tr_compose_push_bi
    /2 width=1 by tr_push_eq_repl/
  ]
]
qed.

lemma unwind2_rmap_pap_le (f) (p) (h):
      ▶[𝐢]p＠⧣❨h❩ < ↑♭p → ▶[𝐢]p＠⧣❨h❩ = ▶[f]p＠⧣❨h❩.
#f #p #h #Hh
>(tr_pap_eq_repl … (▶[f]p) … (unwind2_rmap_decompose …))
<tr_compose_pap <tr_pap_pushs_le //
qed.

lemma unwind2_rmap_xap_le (f) (p) (n):
      ▶[𝐢]p＠❨n❩ ≤ ♭p → ▶[𝐢]p＠❨n❩ = ▶[f]p＠❨n❩.
(*
#f #p * // #h <tr_xap_ninj #Hh
>unwind2_rmap_pap_le
*)
#f #p #n #Hn
>(tr_xap_eq_repl … (▶[f]p) … (unwind2_rmap_decompose …))
<tr_compose_xap <tr_xap_pushs_le //
qed-.
