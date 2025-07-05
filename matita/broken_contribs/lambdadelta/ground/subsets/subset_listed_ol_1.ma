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

include "ground/subsets/subset_ol.ma".
include "ground/subsets/subset_listed_1.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Inversions with subset_ol ************************************************)

lemma subset_ol_inv_single_sn (A) (a) (u):
      ❴a❵ ≬{A} u → a ϵ u.
#A #a #u * #b #H0 #Hb
<(subset_in_inv_single ??? H0) -a //
qed-.

lemma subset_nol_inv_single_sn (A) (a) (u):
      a ⧸ϵ u → ❴a❵ ⧸≬{A} u.
/3 width=1 by subset_ol_inv_single_sn/
qed-.

lemma subset_ol_inv_single_dx (A) (a) (u):
      u ≬{A} ❴a❵ → a ϵ u.
#A #a #u * #b #Hb #H0
<(subset_in_inv_single ??? H0) -a //
qed-.

lemma subset_nol_inv_single_dx (A) (a) (u):
      a ⧸ϵ u → u ⧸≬{A} ❴a❵.
/3 width=1 by subset_ol_inv_single_dx/
qed-.

lemma subset_ol_inv_single_bi (A) (a1) (a2):
      ❴a1❵ ≬{A} ❴a2❵ → a1 = a2.
#A #a1 #a2 * #a #H1 #H2
lapply (subset_in_inv_single ??? H1) -H1 #H1
lapply (subset_in_inv_single ??? H2) -H2 #H2
destruct //
qed-.

lemma subset_nol_inv_single_bi (A) (a1) (a2):
      a1 ⧸= a2 → ❴a1❵ ⧸≬{A} ❴a2❵.
/3 width=1 by subset_ol_inv_single_bi/
qed-.
