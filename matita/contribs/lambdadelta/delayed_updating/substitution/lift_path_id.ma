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
include "delayed_updating/substitution/lift_rmap_id.ma".
include "delayed_updating/substitution/prelift_label_id.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with tr_id *************************************************)

lemma lift_path_id (p):
      p = ↑[𝐢]p.
#p elim p -p //
#l #p #IH
<lift_path_rcons //
qed.
