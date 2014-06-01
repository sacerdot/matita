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

include "basic_2/multiple/llpx_sn_alt_rec.ma".
include "basic_2/multiple/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Alternative definition (recursive) ***************************************)

theorem lleq_intro_alt_r: ∀L1,L2,T,d. |L1| = |L2| →
                          (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                             ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                             ∧∧ I1 = I2 & V1 = V2 & K1 ≡[V1, 0] K2
                          ) → L1 ≡[T, d] L2.
#L1 #L2 #T #d #HL12 #IH @llpx_sn_intro_alt_r // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by and3_intro/
qed.

theorem lleq_ind_alt_r: ∀S:relation4 ynat term lenv lenv.
                        (∀L1,L2,T,d. |L1| = |L2| → (
                           ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           ∧∧ I1 = I2 & V1 = V2 & K1 ≡[V1, 0] K2 & S 0 V1 K1 K2
                        ) → S d T L1 L2) →
                        ∀L1,L2,T,d. L1 ≡[T, d] L2 → S d T L1 L2.
#S #IH1 #L1 #L2 #T #d #H @(llpx_sn_ind_alt_r … H) -L1 -L2 -T -d
#L1 #L2 #T #d #HL12 #IH2 @IH1 -IH1 // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH2 … HnT HLK1 HLK2) -IH2 -HnT -HLK1 -HLK2 /2 width=1 by and4_intro/
qed-.

theorem lleq_inv_alt_r: ∀L1,L2,T,d. L1 ≡[T, d] L2 →
                        |L1| = |L2| ∧
                        ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                        ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                        ∧∧ I1 = I2 & V1 = V2 & K1 ≡[V1, 0] K2.
#L1 #L2 #T #d #H elim (llpx_sn_inv_alt_r … H) -H
#HL12 #IH @conj //
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by and3_intro/
qed-.
