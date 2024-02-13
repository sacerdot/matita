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

include "ground/notation/relations/subset_3.ma".
include "ground/lib/subset_le.ma".

(* STRICT INCLUSION FOR SUBSETS *********************************************)

definition subset_lt (A): relation2 (𝒫❨A❩) (𝒫❨A❩) ≝
           λu1,u2. ∧∧ u1 ⊆ u2 & u2 ⧸⊆ u1
.

interpretation
  "strict inclusion (subset)"
  'Subset A u1 u2 = (subset_lt A u1 u2).
