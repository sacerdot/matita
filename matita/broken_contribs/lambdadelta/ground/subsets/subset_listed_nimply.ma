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

include "ground/subsets/subset_nimply.ma".
include "ground/subsets/subset_listed_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_nimp *******************************************)

lemma in_nimp_single_dx_dec (A:Type[0]) (u) (b):
      (∀a1,a2. Decidable … (a1 =❪A❫ a2)) →
      (∀a:A.Decidable (aϵu)) →
      ∀a:A.Decidable (aϵu⧵❴b❵).
#A #u #b #HA #Hu
/3 width=1 by subset_in_nimp_dec, subset_in_listed_dec/
qed-.
