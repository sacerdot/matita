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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_and_le.ma".

(* INTERSECTION FOR SUBSETS *************************************************)

(* Main constructions with subset_eq ****************************************)

theorem subset_and_eq_repl (A):
        compatible_3 … (subset_eq …) (subset_eq …) (subset_eq …) (subset_and A).
#A #u1 #v1 * #H1 #H2 #u2 #v2 * #H3 #H4
/3 width=5 by conj, subset_and_le_repl/
qed.
