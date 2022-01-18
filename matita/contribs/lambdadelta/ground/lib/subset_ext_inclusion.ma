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

include "ground/lib/subset_inclusion.ma".
include "ground/lib/subset_ext.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

(* Constructions with subset_inclusion **************************************)

lemma subset_inclusion_ext_f1_bi (A1) (A0) (f) (u1) (v1):
      u1 ⊆ v1 → subset_ext_f1 A1 A0 f u1 ⊆ subset_ext_f1 A1 A0 f v1.
#A1 #A0 #f #u1 #v1 #Huv1 #a0 * #a1 #Hau1 #H destruct
/3 width=3 by subset_in_ext_f1_dx/
qed.

lemma subset_inclusion_ext_p1_trans (A1) (Q) (u1) (v1):
      u1 ⊆ v1 → subset_ext_p1 A1 Q v1 → subset_ext_p1 A1 Q u1.
#A1 #Q #u1 #v1 #Huv1 #Hv1
/3 width=1 by/
qed-.
