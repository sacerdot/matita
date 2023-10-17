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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/unwind/unwind2_rmap_after.ma".
include "ground/relocation/fb/fbr_after_xapp.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Properties with map_after ************************************************)

lemma unwind2_path_after (g) (f) (p):
      ▼[g]▼[f]p = ▼[g•f]p.
#g #f * // * [ #k ] #p //
[ <unwind2_path_d_dx <unwind2_path_d_dx
  >fbr_xapp_after //
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.
