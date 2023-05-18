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
include "delayed_updating/syntax/path_structure.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_pn.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/tr_pn_eq.ma".
include "ground/lib/stream_eq_eq.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with tr_after **********************************************)

lemma unwind2_rmap_after (g) (f) (p:path):
      ▶[g]⊗p•▶[f]p ≗ ▶[g•f]p.
#g #f #p elim p -p // * [ #k ] #p #IH //
[ <structure_d_dx <unwind2_rmap_d_dx <unwind2_rmap_d_dx
  @(stream_eq_canc_sn … (tr_compose_assoc …))
  /2 width=1 by tr_compose_eq_repl/
| <structure_L_dx <unwind2_rmap_L_dx <unwind2_rmap_L_dx <unwind2_rmap_L_dx
  /2 width=1 by tr_push_eq_repl/
]
qed.
