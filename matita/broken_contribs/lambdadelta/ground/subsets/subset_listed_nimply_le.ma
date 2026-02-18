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

include "ground/subsets/subset_nimply_le.ma".
include "ground/subsets/subset_listed_le.ma".
include "ground/subsets/subset_listed_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Constructions with subset_nimp and subset_le *****************************)

lemma subset_le_nimp_empty_sx_empty (A) (u): (**)
      (Ⓕ) ⧵ u ⊆ Ⓕ❪A❫.
/2 width=2 by subset_le_nimp_sx_refl_sx/
qed.

lemma subset_le_nimp_empty (A) (u1) (u2): (**)
      u1 ⊆ u2 → u1 ⧵ u2 ⊆ Ⓕ❪A❫.
#A #u1 #u2 #Hu
@(subset_le_trans ????? (subset_le_nimp_refl_empty … u2 …))
/2 width=5 by subset_le_nimp_bi/
qed.

lemma subset_le_nimp_dx_refl_empty (A) (u): (**)
      u ⊆ u ⧵ Ⓕ❪A❫.
/3 width=3 by subset_in_nimp, subset_nin_inv_empty/
qed.

lemma subset_ge_nimp_refl_single (A) (u) (b): (**)
      b ⧸ϵ u → u ⊆ u ⧵❪A❫ ❴b❵.
#A #u #b #Hnb #a #Ha
/4 width=5 by subset_nin_single, subset_in_nimp/
qed.

(* Inversions with subset_nimp and subset_le ********************************)

lemma subset_le_inv_listed_lcons_dx (A) (u) (l) (a):
      u ⊆ 𝐗❪A❫❨a⨮l❩ → u⧵❴a❵ ⊆ 𝐗❨l❩.
#A #u #l #a #Hu #b * #H1b #H2b
lapply (subset_nin_inv_single ??? H2b) -H2b #H2b
lapply (Hu … H1b) -u #H1b
elim (subset_in_inv_listed_lcons ???? H1b) -H1b #H1b destruct //
elim H2b -H2b //
qed-.
