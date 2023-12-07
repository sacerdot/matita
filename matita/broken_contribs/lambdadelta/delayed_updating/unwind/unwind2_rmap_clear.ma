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
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_depth.ma".
include "ground/relocation/fb/fbr_rconss.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with path_clear and depth **********************************)

lemma unwind2_rmap_clear (f) (p):
      (⫯*[♭p]f) = ▶[⓪p]f.
#f #p elim p -p //
* [ #k ] #p #IH
[ <unwind2_rmap_d_dx <fbr_after_id_dx //
| <unwind2_rmap_L_dx <depth_L_dx <fbr_rconss_succ //
| <unwind2_rmap_A_dx //
| <unwind2_rmap_S_dx //
]
qed.
