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

include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_listed_le_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_or and subset_le *******************************)

lemma subset_le_or_listed_append (A) (l1) (l2):
      (𝐗❨l1❩) ∪ 𝐗❨l2❩ ⊆ 𝐗{A}❨l1⨁l2❩.
/3 width=5 by subset_listed_le_append_sn, subset_listed_le_append_dx, subset_le_or_sn/
qed.

lemma subset_le_or_listed_lcons (A) (a1) (l2):
      ❴a1❵ ∪ 𝐗❨l2❩ ⊆ 𝐗{A}❨a1⨮l2❩.
#A #a1 #l2
@(subset_le_or_listed_append ? (a1⨮ⓔ) l2)
qed.

lemma subset_le_listed_append_or (A) (l1) (l2):
      (𝐗{A}❨l1⨁l2❩) ⊆ (𝐗❨l1❩) ∪ 𝐗❨l2❩.
#A #l1 #l2 #a * #x1 #x2 #H0
elim (eq_inv_list_append_bi … H0) -H0 * #m2 #H1 #H2 destruct
[ /2 width=1 by subset_or_in_dx/
| lapply (eq_inv_list_lcons_append ????? H1) -H1 * * [| #m1 ] #H1 #H2 destruct
  /2 width=1 by subset_or_in_dx, subset_or_in_sn/
]
qed.

lemma subset_le_listed_lcons_or (A) (a1) (l2):
      (𝐗{A}❨a1⨮l2❩) ⊆ ❴a1❵ ∪ 𝐗❨l2❩.
#A #a1 #l2
@(subset_le_listed_append_or ? (a1⨮ⓔ) l2)
qed.

lemma subset_le_or_sn_empty_refl (A) (u): (**)
      (Ⓕ{A}) ∪ u ⊆ u.
/3 width=3 by subset_le_or_sn_refl_dx, subset_empty_le_sn/
qed.

lemma subset_le_or_sn_refl_empty (A) (u): (**)
      u ∪ Ⓕ{A} ⊆ u.
/3 width=3 by subset_le_or_sn_refl_sn, subset_empty_le_sn/
qed.

(* Advances constructions with subset_le ************************************)

lemma subset_le_listed_lcons_sn (A) (a) (l):
      a ϵ{A} 𝐗❨l❩ → 𝐗❨a⨮l❩ ⊆ 𝐗❨l❩.
#A #a #l #Ha
@(subset_le_trans ??? (subset_le_listed_lcons_or …))
/3 width=3 by subset_single_le_sn, subset_le_or_sn_refl_dx/
qed.
