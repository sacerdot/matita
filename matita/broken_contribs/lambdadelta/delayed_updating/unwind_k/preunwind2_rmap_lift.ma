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

include "delayed_updating/unwind_k/preunwind2_rmap.ma".
include "delayed_updating/substitution/prelift_label.ma".
include "delayed_updating/substitution/prelift_rmap.ma".
include "ground/relocation/trz_uni_after.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

(* Constructions with lift_path *********************************************)

lemma preunwind2_lift_rmap_after (g) (f) (l):
      ▶[g]🠡[f]l•🠢[f]l ≐ ▶[g•f]l.
#g #f * // #k
<prelift_label_d <prelift_rmap_d <preunwind2_rmap_d <preunwind2_rmap_d
@(trz_eq_trans … (trz_after_assoc …))
@(trz_eq_canc_dx … (trz_after_assoc …))
/2 width=1 by trz_after_eq_repl/
qed.
