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

lemma subset_le_nimp_refl_empty (A) (u): (**)
      u ⧵ u ⊆ Ⓕ{A}.
#A #u #a * #Ha #Hna
elim Hna -Hna //
qed.

lemma subset_le_nimp_empty_sn_empty (A) (u): (**)
      (Ⓕ) ⧵ u ⊆ Ⓕ{A}.
/2 width=2 by subset_le_nimp_sn_refl_sn/
qed.

lemma subset_le_nimp_empty (A) (u1) (u2): (**)
      u1 ⊆ u2 → u1 ⧵ u2 ⊆ Ⓕ{A}.
#A #u1 #u2 #Hu
@(subset_le_trans ????? (subset_le_nimp_refl_empty … u2))
/2 width=5 by subset_le_nimp_bi/
qed.

lemma subset_le_nimp_dx_refl_empty (A) (u): (**)
      u ⊆ u ⧵ Ⓕ{A}.
/3 width=3 by subset_in_nimp, subset_nin_inv_empty/
qed.

(* Inversions with subset_nimp and subset_le ********************************)

lemma subset_le_inv_listed_lcons_dx (A) (u) (l) (a):
      u ⊆ 𝐗{A}❨a⨮l❩ → u⧵❴a❵ ⊆ 𝐗❨l❩.
#A #u #l #a #Hu #b * #H1b #H2b
lapply (subset_nin_inv_single ??? H2b) -H2b #H2b
lapply (Hu … H1b) -u #H1b
elim (subset_in_inv_listed_lcons ???? H1b) -H1b #H1b destruct //
elim H2b -H2b //
qed-.
