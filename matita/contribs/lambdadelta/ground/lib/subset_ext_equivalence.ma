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

include "ground/lib/subset_ext_inclusion.ma".
include "ground/lib/subset_equivalence.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

(* Constructions with subset_equivalence ************************************)

lemma subset_equivalence_ext_f1_bi (A1) (A0) (f) (u1) (v1):
      u1 ⇔ v1 → subset_ext_f1 A1 A0 f u1 ⇔ subset_ext_f1 A1 A0 f v1.
#A1 #A0 #f #u1 #v1 * #Huv1 #Hvu1
/3 width=3 by subset_inclusion_ext_f1_bi, conj/
qed.
