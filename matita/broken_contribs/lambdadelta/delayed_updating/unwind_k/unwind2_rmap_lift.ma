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
include "delayed_updating/unwind_k/preunwind2_rmap_lift.ma".
include "delayed_updating/unwind_k/preunwind2_rmap_eq.ma".
include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_structure.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with lift_path *********************************************)

lemma lift_unwind2_rmap_after (g) (f) (p):
      (🠢[g]⊗p)•▶[f]p ≐ ▶[g•f]p.
#g #f #p elim p -p //
* [ #k ] #p #IH //
[ <unwind2_rmap_L_dx <unwind2_rmap_L_dx <lift_rmap_L_dx
  /2 width=1 by trz_push_eq_repl_fwd/
| <unwind2_rmap_A_dx <unwind2_rmap_A_dx <lift_rmap_A_dx //
| <unwind2_rmap_S_dx <unwind2_rmap_S_dx <lift_rmap_S_dx //
]
qed.

lemma unwind2_lift_rmap_after (g) (f) (p:path):
      ▶[g]🠡[f]p•🠢[f]p ≐ ▶[g•f]p.
#g #f #p elim p -p // #l #p #IH
<lift_path_rcons <lift_rmap_rcons <unwind2_rmap_rcons <unwind2_rmap_rcons
@(trz_eq_trans … (preunwind2_lift_rmap_after …))
/2 width=1 by preunwind2_rmap_eq_repl/
qed.
