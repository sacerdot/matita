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

include "ground/lib/functions.ma".
include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_rest.ma".

(* RESTRICTION FOR SUBSETS **************************************************)

(* Basic constructions with subset_le ***************************************)

lemma subset_rest_le_refl (A) (R) (u): (**)
      ❨R❩❪A❫u ⊆ u.
#A #R #u #a * #_ #Ha
//
qed.

lemma subset_rest_ge_refl (A) (R) (u): (**)
      R → u ⊆ ❨R❩❪A❫u.
#A #R #u #Hx #a #Ha
/2 width=1 by subset_and_in/
qed.

lemma subset_rest_le (A) (R) (u) (v): (**)
      negation R → ❨R❩❪A❫u ⊆ v.
#A #R #u #v #Hnx #a * #Ha #_
elim Hnx -Hnx //
qed.

lemma subset_nrest_le (A) (R) (u) (v): (**)
      R → ❨negation R❩❪A❫u ⊆ v.
#A #R #u #v #Hx #a * #Hna #_
elim Hna -A //
qed.

lemma subset_rest_le_repl (A) (R):
      compatible_2_fwd … (subset_le …) (subset_le …) (subset_rest A R).
#A #R #u1 #u2 #Hu12 #a * #H1a #H2a
/3 width=1 by subset_and_in/ 
qed.

(* Advanced constructions with subset_le ************************************)

lemma subset_rest_le_gen (A) (R) (u) (v): (**)
      (R → u ⊆ v) → ❨R❩❪A❫u ⊆ v.
#A #R #u #v #Huv #a * #H1a #H2a
/2 width=1 by/
qed.

lemma subset_rest_le_estract (A) (R) (u) (v): (**)
      (R → ❨R❩u ⊆ v) → ❨R❩❪A❫u ⊆ v.
#A #R #u #v #Huv #a * #H1a #H2a
/3 width=1 by subset_and_in/
qed.

(* Advanced inversions with subset_le ***************************************)

lemma subset_rest_le_inv_gen (A) (R) (u) (v): (**)
      R → ❨R❩❪A❫u ⊆ v → u ⊆ v.
#A #R #u #v #x #H0 #a #Ha
/3 width=1 by subset_and_in/
qed.
