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

include "delayed_updating/substitution/prelift_rmap.ma".
include "delayed_updating/substitution/prelift_label.ma".
include "ground/relocation/fb/fbr_ctls_after.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* Constructions with map_after *********************************************)

lemma prelift_rmap_after (g) (f) (l):
      (🠢[🠡[f]l]g)•(🠢[l]f) = 🠢[l](g•f).
#g #f * [ #k || #F ] //
<prelift_label_d <prelift_rmap_d <prelift_rmap_d <prelift_rmap_d
<fbr_ctls_after //
qed.
