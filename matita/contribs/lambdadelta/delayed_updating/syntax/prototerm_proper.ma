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

include "delayed_updating/syntax/path_proper.ma".
include "ground/lib/subset_ext_equivalence.ma".

(* PROPER CONDITION FOR PROTOTERM *******************************************)

interpretation
  "proper condition (prototerm)"
  'PredicatePTail t = (subset_ext_p1 path ppc t).

(* Basic constructions ******************************************************)

lemma tpc_i (t):
      (𝐞 ⧸ϵ t) → Ꝕt.
#t #Ht * //
#H elim (Ht H)
qed.

(* Basic inversions *********************************************************)

lemma tpc_e (t): Ꝕt → 𝐞 ϵ t → ⊥.
/2 width=5 by subset_in_inv_ext_p1_dx/ qed-.
