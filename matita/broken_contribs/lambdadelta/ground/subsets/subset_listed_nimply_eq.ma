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

include "ground/subsets/subset_listed_eq.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_nimp and subset_eq *****************************)

lemma subset_nimp_listed_sn (A:Type[0]) (u) (l1):
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      (∀a. Decidable … (a ϵ u)) →
      ∃∃l. 𝐗❨l1❩ ⧵ u ⇔ 𝐗{A}❨l❩ & ❘l❘ ≤ ❘l1❘.
#A #u #l1 #HA #Hu
@(subset_listed_dx_le_to_eq … HA) //
/3 width=1 by subset_in_nimp_dec, subset_in_listed_dec/
qed-.

lemma subset_nimp_listed_bi (A:Type[0]) (l1) (l2):
      (∀a1,a2. Decidable … (a1 ={A} a2)) →
      ∃∃l. 𝐗❨l1❩ ⧵ 𝐗❨l2❩ ⇔ 𝐗{A}❨l❩ & ❘l❘ ≤ ❘l1❘.
#A #l1 #l2 #HA
/3 width=1 by subset_nimp_listed_sn, subset_in_listed_dec/
qed-.
