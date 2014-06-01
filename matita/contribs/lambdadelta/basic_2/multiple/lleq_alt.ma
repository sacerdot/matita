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

include "basic_2/multiple/llpx_sn_alt.ma".
include "basic_2/multiple/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Alternative definition (not recursive) ***********************************)

theorem lleq_intro_alt: ∀L1,L2,T,d. |L1| = |L2| →
                        (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → L1 ⊢ i ϵ 𝐅*[d]⦃T⦄ →
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           I1 = I2 ∧ V1 = V2
                        ) → L1 ≡[T, d] L2.
#L1 #L2 #T #d #HL12 #IH @llpx_sn_alt_inv_llpx_sn @conj // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
@(IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 //
qed.

theorem lleq_inv_alt: ∀L1,L2,T,d. L1 ≡[T, d] L2 →
                      |L1| = |L2| ∧
                      ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → L1 ⊢ i ϵ 𝐅*[d]⦃T⦄ →
                      ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                      I1 = I2 ∧ V1 = V2.
#L1 #L2 #T #d #H elim (llpx_sn_llpx_sn_alt … H) -H
#HL12 #IH @conj //
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
@(IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 //
qed-.
