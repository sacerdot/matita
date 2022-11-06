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
include "ground/lib/exteq.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

(* Constructions with subset_inclusion **************************************)

lemma subset_inclusion_ext_f1_exteq (A1) (A0) (f1) (f2) (u):
      f1 ⊜ f2 → subset_ext_f1 A1 A0 f1 u ⊆ subset_ext_f1 A1 A0 f2 u.
#A1 #A0 #f1 #f2 #u #Hf #a0 * #a1 #Hau1 #H destruct
/2 width=1 by subset_in_ext_f1_dx/
qed.

lemma subset_inclusion_ext_f1_bi (A1) (A0) (f) (u1) (v1):
      u1 ⊆ v1 → subset_ext_f1 A1 A0 f u1 ⊆ subset_ext_f1 A1 A0 f v1.
#A1 #A0 #f #u1 #v1 #Huv1 #a0 * #a1 #Hau1 #H destruct
/3 width=3 by subset_in_ext_f1_dx/
qed.

lemma subset_inclusion_ext_f1_compose_sn (A0) (A1) (A2) (f1) (f2) (u):
      subset_ext_f1 A1 A2 f2 (subset_ext_f1 A0 A1 f1 u) ⊆ subset_ext_f1 A0 A2 (f2∘f1) u.
#A0 #A1 #A2 #f1 #f2 #u #a2 * #a1 * #a0 #Ha0 #H1 #H2 destruct
/2 width=1 by subset_in_ext_f1_dx/
qed.

lemma subset_inclusion_ext_f1_compose_dx (A0) (A1) (A2) (f1) (f2) (u):
      subset_ext_f1 A0 A2 (f2∘f1) u ⊆ subset_ext_f1 A1 A2 f2 (subset_ext_f1 A0 A1 f1 u).
#A0 #A1 #A2 #f1 #f2 #u #a2 * #a0 #Ha0 #H0 destruct
/3 width=1 by subset_in_ext_f1_dx/
qed.

lemma subset_inclusion_ext_f1_1_bi (A11) (A21) (A0) (f1) (f2) (u11) (u21) (v11) (v21):
      u11 ⊆ v11 → u21 ⊆ v21 →
      subset_ext_f1_1 A11 A21 A0 f1 f2 u11 u21 ⊆ subset_ext_f1_1 A11 A21 A0 f1 f2 v11 v21.
#A11 #A21 #A0 #f1 #f2 #u11 #u21 #v11 #v21 #Huv11 #Huv21 #a0 *
/3 width=3 by subset_inclusion_ext_f1_bi, or_introl, or_intror/
qed.

lemma subset_inclusion_ext_p1_trans (A1) (Q) (u1) (v1):
      u1 ⊆ v1 → subset_ext_p1 A1 Q v1 → subset_ext_p1 A1 Q u1.
#A1 #Q #u1 #v1 #Huv1 #Hv1
/3 width=1 by/
qed-.
