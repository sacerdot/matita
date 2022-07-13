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

include "delayed_updating/substitution/lift_rmap.ma".
include "delayed_updating/substitution/prelift_rmap_id.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with tr_id *************************************************)

lemma lift_rmap_id (p):
      (𝐢) = ↑[p]𝐢.
#p elim p -p //
qed.
