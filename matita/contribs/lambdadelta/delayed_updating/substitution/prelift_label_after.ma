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

include "delayed_updating/substitution/prelift_label.ma".
include "ground/relocation/tr_compose_pap.ma".

(* PRELIFT FOR LABEL ********************************************************)

(* Constructions with tr_after **********************************************)

lemma prelift_label_after (g) (f) (l):
      ↑[g]↑[f]l = ↑[g∘f]l.
#g #f * [ #k ] //
qed.
