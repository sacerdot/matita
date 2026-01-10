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
include "ground/subsets/subset_listed_or_le.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_or and subset_eq *******************************)

lemma subset_eq_or_listed_append (A) (l1) (l2):
      (𝐗❨l1❩) ∪ 𝐗❨l2❩ ⇔ 𝐗❪A❫❨l1⨁l2❩.
#A #l1 #l2
/3 width=1 by subset_le_listed_append_or, subset_le_or_listed_append, conj/
qed.

lemma subset_eq_or_listed_lcons (A) (a1) (l2):
      ❴a1❵ ∪ 𝐗❨l2❩ ⇔ 𝐗❪A❫❨a1⨮l2❩.
/3 width=1 by subset_le_listed_lcons_or, subset_le_or_listed_lcons, conj/
qed.

lemma subset_eq_or_dx_empty_refl (A) (u2):
      u2 ⇔ Ⓕ❪A❫ ∪ u2.
#A #u2 @conj [ // ]
@subset_le_or_sx //
qed.

lemma subset_eq_or_dx_refl_empty (A) (u1):
      u1 ⇔ u1 ∪ Ⓕ❪A❫.
#A #u2 @conj [ // ]
@subset_le_or_sx //
qed.
