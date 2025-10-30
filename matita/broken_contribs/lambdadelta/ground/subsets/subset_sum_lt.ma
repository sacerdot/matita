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

include "ground/subsets/subset_lt.ma".
include "ground/subsets/subset_sum_le.ma".

(* SUM FOR SUBSETS **********************************************************)

(* Main constructions with subset_lt ****************************************)

theorem subset_sum_lt_le_repl (A1) (A2):
        compatible_3 … (subset_lt …) (subset_le …) (subset_lt …) (subset_sum A1 A2).
#A1 #A2 #u1 #u2 * #Hu #H0 #v1 #v2 #Hv
elim (subsets_inh_inv_in … H0) -H0 #a * #Ha #Hna
@subset_lt_mk [ /2 width=5 by subset_sum_le_repl/ ]
@(subsets_inh_in … (in_1_2 … a))
@subset_in_nimp [ /2 width=1 by subset_in_sum_sx/ ] #H0
lapply (subset_in_inv_sum_sx ????? H0) -H0
/2 width=1 by/
qed.

theorem subset_sum_le_lt_repl (A1) (A2):
        compatible_3 … (subset_le …) (subset_lt …) (subset_lt …) (subset_sum A1 A2).
#A1 #A2 #u1 #u2 #Hu #v1 #v2 * #Hv #H0
elim (subsets_inh_inv_in … H0) -H0 #a * #Ha #Hna
@subset_lt_mk [ /2 width=5 by subset_sum_le_repl/ ]
@(subsets_inh_in … (in_2_2 … a))
@subset_in_nimp [ /2 width=1 by subset_in_sum_dx/ ] #H0
lapply (subset_in_inv_sum_dx ????? H0) -H0
/2 width=1 by/
qed.

theorem subset_sum_lt_repl (A1) (A2):
        compatible_3 … (subset_lt …) (subset_lt …) (subset_lt …) (subset_sum A1 A2).
#A1 #A2 #u1 #u2 #Hu #v1 #v2 #Hv
/3 width=3 by subset_sum_lt_le_repl, subset_lt_des_le/
qed.
