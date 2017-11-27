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

include "ground_2/relocation/rtmap_id.ma".
include "basic_2/notation/relations/subseteq_4.ma".
include "basic_2/static/frees.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

definition fle: bi_relation lenv term ≝ λL1,T1,L2,T2.
                ∃∃f1,f2. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & f1 ⊆ f2.

interpretation "free variables inclusion (restricted closure)"
   'SubSetEq L1 T1 L2 T2 = (fle L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fle_sort: ∀L1,L2,s1,s2. ⦃L1, ⋆s1⦄ ⊆ ⦃L2, ⋆s2⦄.
/3 width=5 by frees_sort, sle_refl, ex3_2_intro/ qed.

lemma fle_gref: ∀L1,L2,l1,l2. ⦃L1, §l1⦄ ⊆ ⦃L2, §l2⦄.
/3 width=5 by frees_gref, sle_refl, ex3_2_intro/ qed.

lemma fle_bind: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                ∀I1,I2,T1,T2. ⦃L1.ⓑ{I1}V1, T1⦄ ⊆ ⦃L2.ⓑ{I2}V2, T2⦄ →
                ∀p. ⦃L1, ⓑ{p,I1}V1.T1⦄ ⊆ ⦃L2, ⓑ{p,I2}V2.T2⦄.
#L1 #L2 #V1 #V2 * #f1 #g1 #HV1 #HV2 #Hfg1 #I1 #I2 #T1 #T2 * #f2 #g2 #Hf2 #Hg2 #Hfg2 #p
elim (sor_isfin_ex f1 (⫱f2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #f #Hf #_
elim (sor_isfin_ex g1 (⫱g2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ #g #Hg #_
/4 width=12 by frees_bind, monotonic_sle_sor, sle_tl, ex3_2_intro/
qed.

lemma fle_flat: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ⊆ ⦃L2, V2⦄ →
                ∀T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                ∀I1,I2. ⦃L1, ⓕ{I1}V1.T1⦄ ⊆ ⦃L2, ⓕ{I2}V2.T2⦄.
#L1 #L2 #V1 #V2 * #f1 #g1 #HV1 #HV2 #Hfg1 #T1 #T2 * #f2 #g2 #Hf2 #Hg2 #Hfg2 #I1 #I2
elim (sor_isfin_ex f1 f2) /2 width=3 by frees_fwd_isfin/ #f #Hf #_
elim (sor_isfin_ex g1 g2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
/3 width=12 by frees_flat, monotonic_sle_sor, ex3_2_intro/
qed.
