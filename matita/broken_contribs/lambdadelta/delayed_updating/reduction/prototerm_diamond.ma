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

include "delayed_updating/reduction/path_diamond.ma".
include "delayed_updating/notation/relations/white_diamond_2.ma".

(* SUBSET OF DISJOINT REDEXES ***********************************************)

definition term_drc: relation2 (𝕋) (𝕋) ≝
           λt,u.
           ∀r1,r2. r1 ϵ u → r2 ϵ u → r1 ⧸= r2 → r1 ◇[t] r2.

interpretation
  "disjoint redexes condition (prototerm)"
  'WhiteDiamond t u = (term_drc t u).

(* Basic constructions ******************************************************)
