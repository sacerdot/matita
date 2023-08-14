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
include "delayed_updating/substitution/prelift_rmap_eq.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with map_eq ************************************************)

lemma lift_rmap_eq_repl (p):
      compatible_2_fwd … fbr_eq fbr_eq (λf.🠢[p]f).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
/3 width=1 by prelift_rmap_eq_repl/
qed.

lemma lift_rmap_id (p):
      (𝐢) ≐ 🠢[p]𝐢.
#p elim p -p //
#l #p #IH
/3 width=3 by prelift_rmap_eq_repl, fbr_eq_trans/
qed.
