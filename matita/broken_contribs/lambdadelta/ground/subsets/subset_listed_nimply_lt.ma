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
include "ground/subsets/subset_listed_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_nimp and subset_lt *****************************)

lemma subset_lt_nimp_single_dx_refl (A) (u) (a):
      a ϵ u → u⧵❴a:A❵ ⊂ u.
#A #u #a #Ha
@subset_lt_mk //
@(subsets_inh_in … a)
@subset_in_nimp //
* #_ #H0
/2 width=1 by/
qed.
