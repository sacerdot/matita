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

include "ground/lib/functions.ma".
include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_sum.ma".

(* SUM FOR SUBSETS **********************************************************)

(* Main constructions with subset_le ****************************************)

theorem subset_sum_le_repl (A1) (A2):
        compatible_3 … (subset_le …) (subset_le …) (subset_le …) (subset_sum A1 A2).
#A1 #A2 #u1 #u2 #Hu #v1 #v2 #Hv * #a #H0
[ lapply (subset_in_inv_sum_sx ????? H0)
| lapply (subset_in_inv_sum_dx ????? H0)
] -H0 #Ha
/3 width=1 by subset_in_sum_dx, subset_in_sum_sx/
qed.
