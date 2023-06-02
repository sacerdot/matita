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

include "delayed_updating/unwind_k/unwind2_path_eq.ma".
include "delayed_updating/unwind_k/unwind2_rmap_after.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Properties with trz_after ************************************************)

lemma unwind2_path_after (g) (f) (p):
      ▼[g]▼[f]p = ▼[g•f]p.
#g #f * // * [ #k ] #p //
[ <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.
