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

include "ground/subsets/subsets_wfinite.ma".
include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/syntax/prototerm_clear_listed.ma".

(* CLEARED PROTOTERM ********************************************************)

(* Constructions with subsets_wfinite and subset_le *************************)

lemma term_clear_wfinite (t):
      t ϵ 𝐖𝛀 → ⓪t ϵ 𝐖𝛀.
#t * #l #Hl
lapply (clear_le_repl … Hl) -Hl #Hl
lapply (subset_le_trans … Hl … (term_clear_listed_le …)) -Hl #Hl
/2 width=2 by subsets_wfinite_in/
qed.
