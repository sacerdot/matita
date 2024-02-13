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
include "ground/notation/functions/curly_vertical_3.ma".
include "ground/notation/relations/epsilon_3.ma".
include "ground/notation/relations/not_epsilon_3.ma".
include "ground/lib/relations.ma".

(* SUBSETS ******************************************************************)

interpretation
  "power class (subset)"
  'PowerClass A = (predicate A).

definition subset_in (A): 𝒫❨A❩ → 𝒫❨A❩ ≝
           λu.u.

interpretation
  "membership (subset)"
  'Epsilon A a u = (subset_in A u a).

interpretation
  "negated membership (subset)"
  'NotEpsilon A a u = (negation (subset_in A u a)).
