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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_listed.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_le *********************************************)

lemma subset_empty_le_sx (A) (u):
      (Ⓕ❪A❫) ⊆ u.
#A #u #a #H0
elim (subset_nin_inv_empty ?? H0)
qed.

lemma subset_listed_le_lcons_dx (A) (l) (a):
      (𝐗❨l❩) ⊆ 𝐗❪A❫❨a⨮l❩.
/2 width=1 by subset_in_listed_lcons_dx/
qed.

lemma subset_listed_le_append_dx (A) (l1) (l2):
      (𝐗❨l1❩) ⊆ 𝐗❪A❫❨l1⨁l2❩.
#A #l1 #l2 #a * #x1 #x2 #H0 destruct //
qed.

lemma subset_listed_le_append_sx (A) (l1) (l2):
      (𝐗❨l2❩) ⊆ 𝐗❪A❫❨l1⨁l2❩.
#A #l1 #l2 #a * #x1 #x2 #H0 destruct //
qed.

(* Inversions with subset_le ************************************************)

lemma subset_le_inv_listed_append_sx (A) (u) (l1) (l2):
      (𝐗❨l1⨁❪A❫l2❩) ⊆ u →
      ∧∧ 𝐗❨l1❩ ⊆ u & 𝐗❨l2❩ ⊆ u.
#A #u #l1 #l2 #H0
@conj @(subset_le_trans ????? H0) -H0 //
qed-.

lemma subset_le_inv_listed_lcons_sx (A) (u) (l) (a):
      (𝐗❨a⨮l❩) ⊆ u →
      ∧∧ a ϵ❪A❫ u & 𝐗❨l❩ ⊆ u.
#A #u #l #a
>(list_append_empty_sx … l) in ⊢ (%→?);
>list_append_lcons_sx
#H0 elim (subset_le_inv_listed_append_sx … H0) -H0 #Ha #Hu
@conj // -Hu
@(subset_in_le_trans ????? Ha) -Ha //
qed-.

lemma subset_le_inv_listed_lcons_dx_nin (A) (u) (l) (a):
      a ⧸ϵ❪A❫ u → u ⊆ 𝐗❨a⨮l❩ → u ⊆ 𝐗❨l❩.
#A #u #l #a #Ha #Hu #b #Hb
lapply (subset_in_le_trans ???? Hb Hu) -Hu #H0
elim (subset_in_inv_listed_lcons ???? H0) -H0 #Hba destruct //
elim Ha -Ha //
qed-.
