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

include "ground/notation/functions/powerclass_1.ma".
include "ground/notation/relations/epsilon_3.ma".
include "ground/lib/relations.ma".

(* SUBSETS ******************************************************************)

definition subset (A): Type[0] ≝
           predicate A.

interpretation
  "power class (subset)"
  'PowerClass A = (subset A).

definition subset_in (A): 𝒫❨A❩ → 𝒫❨A❩ ≝
           λu.u.

interpretation
  "membership (subset)"
  'Epsilon A a u = (subset_in A u a).
