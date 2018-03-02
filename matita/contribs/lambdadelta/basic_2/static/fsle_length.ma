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

include "basic_2/syntax/lveq_length.ma".
include "basic_2/static/fsle.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

(* Properties with length for local environments ****************************)

lemma fsle_sort_bi: ∀L1,L2,s1,s2. |L1| = |L2| → ⦃L1, ⋆s1⦄ ⊆ ⦃L2, ⋆s2⦄.
/3 width=8 by lveq_length_eq, frees_sort, sle_refl, ex4_4_intro/ qed.

lemma fsle_gref_bi: ∀L1,L2,l1,l2. |L1| = |L2| → ⦃L1, §l1⦄ ⊆ ⦃L2, §l2⦄.
/3 width=8 by lveq_length_eq, frees_gref, sle_refl, ex4_4_intro/ qed.

lemma fsle_zero_bi: ∀K1,K2. |K1| = |K2| → ∀V1,V2. ⦃K1, V1⦄ ⊆ ⦃K2, V2⦄ →
                    ∀I1,I2. ⦃K1.ⓑ{I1}V1, #O⦄ ⊆ ⦃K2.ⓑ{I2}V2, #O⦄.
#K1 #K2 #HK #V1 #V2
* #n1 #n2 #f1 #f2 #Hf1 #Hf2 #HK12 #Hf12
#I1 #I2
elim (lveq_inj_length … HK12) // -HK #H1 #H2 destruct
/3 width=12 by frees_pair, lveq_bind, sle_next, ex4_4_intro/
qed.
