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
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/fb/fbr_rconss_xapp.ma".
include "ground/relocation/fb/fbr_after_xapp.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with depth *************************************************)

lemma unwind2_rmap_decompose (p) (f):
      ▶[p]f = (⫯*[♭p]f)•(▶[p]𝐢).
#p elim p -p
[ #f <unwind2_rmap_empty <unwind2_rmap_empty //
| * [ #k ] #p #IH #f //
  <unwind2_rmap_L_dx <unwind2_rmap_L_dx <depth_L_dx
  <fbr_rconss_succ >IH -IH //
]
qed.

lemma unwind2_rmap_unfold_xapp_le (f) (p) (h):
      (▶[p]𝐢)＠❨h❩ ≤ ♭p →
      (▶[p]𝐢)＠❨h❩ = (▶[p]f)＠❨h❩.
#f #p #h #H0
>(unwind2_rmap_decompose … f)
<fbr_xapp_after <fbr_xapp_pushs_le //
qed-.
