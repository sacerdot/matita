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

include "delayed_updating/substitution/prelift_rmap_after.ma".
include "delayed_updating/substitution/lift_rmap_eq.ma".
include "delayed_updating/substitution/lift_path.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with trz_after *********************************************)

lemma lift_rmap_after (g) (f) (p:path):
      (🠢[g]🠡[f]p•🠢[f]p) ≐ 🠢[g•f]p.
#g #f #p elim p -p //
#l #p #IH <lift_rmap_rcons
/2 width=5 by prelift_rmap_eq_repl/
qed.
