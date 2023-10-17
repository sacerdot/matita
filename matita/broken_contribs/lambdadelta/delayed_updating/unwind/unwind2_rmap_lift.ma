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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/unwind/preunwind2_rmap_lift.ma".
include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_structure.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with lift_path *********************************************)

lemma lift_unwind2_rmap_after (g) (f) (p):
      (🠢[⊗p]g)•▶[p]f = ▶[p](g•f).
#g #f #p elim p -p //
* [ #k ] #p #IH //
[ <unwind2_rmap_L_dx <unwind2_rmap_L_dx <lift_rmap_L_dx
  <IH -IH //
| <unwind2_rmap_A_dx <unwind2_rmap_A_dx <lift_rmap_A_dx //
| <unwind2_rmap_S_dx <unwind2_rmap_S_dx <lift_rmap_S_dx //
]
qed.

lemma unwind2_lift_rmap_after (g) (f) (p:path):
      ▶[🠡[f]p]g•🠢[p]f = ▶[p](g•f).
#g #f #p elim p -p // #l #p #IH
<lift_path_rcons <lift_rmap_rcons <unwind2_rmap_rcons <unwind2_rmap_rcons
<IH -IH //
qed.
