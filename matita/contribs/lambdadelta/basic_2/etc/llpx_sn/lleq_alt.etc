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

include "basic_2/relocation/llpx_sn_alt.ma".
include "basic_2/relocation/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Alternative definition ***************************************************)

theorem lleq_intro_alt: ∀L1,L2,T,d. |L1| = |L2| →
                        (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           ∧∧ I1 = I2 & V1 = V2 & K1 ⋕[V1, 0] K2
                        ) → L1 ⋕[T, d] L2.
#L1 #L2 #T #d #HL12 #IH @llpx_sn_intro_alt // -HL12
#I1 #I2 #K1 #K2 #HLK1 #HLK2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by and3_intro/
qed.

theorem lleq_fwd_alt: ∀L1,L2,T,d. L1 ⋕[T, d] L2 →
                      |L1| = |L2| ∧
                      ∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → (∀U. ⇧[i, 1] U ≡ T → ⊥) →
                      ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                      ∧∧ I1 = I2 & V1 = V2 & K1 ⋕[V1, 0] K2.
#L1 #L2 #T #d #H elim (llpx_sn_fwd_alt … H) -H
#HL12 #IH @conj //
#I1 #I2 #K1 #K2 #HLK1 #HLK2 #i #Hid #HnT #HLK1 #HLK2
elim (IH … HnT HLK1 HLK2) -IH -HnT -HLK1 -HLK2 /2 width=1 by and3_intro/
qed-.
