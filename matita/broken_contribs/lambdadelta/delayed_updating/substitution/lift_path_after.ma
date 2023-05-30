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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/substitution/lift_rmap_after.ma".
include "delayed_updating/substitution/prelift_label_after.ma".
include "delayed_updating/substitution/prelift_label_eq.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with trz_after *********************************************)

lemma lift_path_after (g) (f) (p:path):
      (🠡[g]🠡[f]p) = 🠡[g•f]p.
#g #f #p elim p -p //
#l #p #IH
<lift_path_rcons <lift_path_rcons <IH -IH
/3 width=1 by prelift_label_eq_repl, eq_f2/
qed.
