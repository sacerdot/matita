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
include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/lib/stream_eq_eq.ma".

(* TAILED PREUNWIND FOR RELOCATION MAP **************************************)

(* Constructions with lift_path *********************************************)

lemma preunwind2_lift_rmap_after (g) (f) (l):
      ▶[g]🠡[f]l•🠢[f]l ≗ ▶[g•f]l.
#g #f * // #k
<prelift_label_d <prelift_rmap_d <preunwind2_rmap_d <preunwind2_rmap_d
@(stream_eq_trans … (tr_compose_assoc …))
@(stream_eq_canc_dx … (tr_compose_assoc …))
/2 width=1 by tr_compose_eq_repl/
qed.
