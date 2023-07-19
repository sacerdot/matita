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

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with trz_after *********************************************)

lemma unwind2_rmap_after (g) (f) (p:path):
      ▶[g]⊗p•▶[f]p ≐ ▶[g•f]p.
#g #f #p elim p -p // * [ #k ] #p #IH //
[ <structure_L_dx <unwind2_rmap_L_dx <unwind2_rmap_L_dx <unwind2_rmap_L_dx
  /2 width=1 by trz_push_eq_repl/
| <structure_A_dx <unwind2_rmap_A_dx //
| <structure_S_dx <unwind2_rmap_S_dx //
]
qed.
