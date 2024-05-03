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
include "ground/subsets/subset_and.ma".

(* INTERSECTION FOR SUBSETS *************************************************)

(* Inversions with subset_le ************************************************)

lemma subset_le_and_inv_dx_sn (A) (u1) (u2) (v:𝒫❨A❩): (**)
      v ⊆ u1 ∩ u2 → v ⊆ u1.
#A #u1 #u2 #v #Hv #r #Hr
elim (Hv … Hr) -Hv -Hr //
qed-.

lemma subset_le_and_inv_dx_dx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      v ⊆ u1 ∩ u2 → v ⊆ u2.
#A #u1 #u2 #v #Hv #r #Hr
elim (Hv … Hr) -Hv -Hr //
qed-.

(* Constructions with subset_le *********************************************)

lemma subset_le_and_dx (A) (u1) (u2) (v:𝒫❨A❩): (**)
      v ⊆ u1 → v ⊆ u2 → v ⊆ u1 ∩ u2.
#A #u1 #u2 #v #Hu1 #Hu2 #p #Hp
/3 width=1 by subset_and_in/
qed.

lemma subset_le_and_sn_refl_sn (A) (u1) (u2:𝒫❨A❩): (**)
      u1 ∩ u2 ⊆ u1.
/2 width=4 by subset_le_and_inv_dx_sn/
qed.

lemma subset_le_and_sn_refl_dx (A) (u1:𝒫❨A❩) (u2): (**)
      u1 ∩ u2 ⊆ u2.
/2 width=4 by subset_le_and_inv_dx_dx/
qed.

(* Main constructions with subset_le ****************************************)

theorem subset_and_le_repl (A):
        compatible_3 … (subset_le …) (subset_le …) (subset_le …) (subset_and A).
#A #u1 #v1 #H1 #u2 #v2 #H2
@subset_le_and_dx
[ @(subset_le_trans ?? u1) //
| @(subset_le_trans ?? u2) //
] (**) (* auto fails *)
qed.
