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

include "delayed_updating/substitution/lift_rmap_eq.ma".
include "delayed_updating/substitution/prelift_rmap_id.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with trz_id ************************************************)

lemma lift_rmap_id (p):
      (𝐢) ≐ 🠢[𝐢]p.
#p elim p -p
/2 width=1 by prelift_rmap_eq_repl/
qed.
