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

include "basic_2/relocation/lpx_sn_alt.ma".
include "basic_2/substitution/llor.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

(* Alternative definition ***************************************************)

theorem llor_intro_alt: ∀T,L2,L1,L. |L1| ≤ |L2| → |L1| = |L| →
                        (∀I1,I,K1,K,V1,V,i. ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L ≡ K.ⓑ{I}V →
                           (K1 ⊢ |L2|-|L1|+i ~ϵ 𝐅*[yinj 0]⦃T⦄ → I1 = I ∧ V1 = V) ∧
                           (∀I2,K2,V2. (K1 ⊢ |L2|-|L1|+i ~ϵ 𝐅*[yinj 0]⦃T⦄ → ⊥) →
                                       ⇩[|L2|-|L1|+i] L2 ≡ K2.ⓑ{I2}V2 → I1 = I ∧ V2 = V
                           )
                        ) → L1 ⩖[T] L2 ≡ L.
#T #L2 #L1 #L #HL12 #HL1 #IH @lpx_sn_intro_alt // -HL1
#I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (ldrop_fwd_length_minus4 … HLK1)
lapply (ldrop_fwd_length_le4 … HLK1)
normalize in ⊢ (%→%→?); #HKL1 #Hi
lapply (plus_minus_minus_be_aux … HL12 Hi) // -Hi <minus_plus #Hi
lapply (transitive_le … HKL1 HL12) -HKL1 -HL12 #HKL1
elim (IH … HLK1 HLK) -IH -HLK1 -HLK #IH1 #IH2
elim (cofrees_dec K1 T 0 (|L2|-|L1|+i))
[ -IH2 #HT elim (IH1 … HT) -IH1
  #HI1 #HV1 @conj // <HV1 -V @clor_sn // <Hi -Hi //
| -IH1 #HnT elim (ldrop_O1_lt (Ⓕ) L2 (|L2|-|L1|+i)) /2 width=1 by monotonic_lt_minus_l/
  #I2 #K2 #V2 #HLK2 elim (IH2 … HLK2) -IH2 /2 width=1 by/
  #HI1 #HV2 @conj // <HV2 -V @(clor_dx … I2 K2) // <Hi -Hi /2 width=1 by/
]
qed.

theorem llor_inv_alt: ∀T,L2,L1,L. L1 ⩖[T] L2 ≡ L → |L1| ≤ |L2| →
                      |L1| = |L| ∧
                      (∀I1,I,K1,K,V1,V,i.
                         ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L ≡ K.ⓑ{I}V →
                         (∧∧ K1 ⊢ |L2|-|L1|+i ~ϵ 𝐅*[yinj 0]⦃T⦄ & I1 = I & V1 = V) ∨
                         (∃∃I2,K2,V2. (K1 ⊢ |L2|-|L1|+i ~ϵ 𝐅*[yinj 0]⦃T⦄ → ⊥) &
                                      ⇩[|L2|-|L1|+i] L2 ≡ K2.ⓑ{I2}V2 &
                                      I1 = I & V2 = V
                         )
                      ).
#T #L2 #L1 #L #H #HL12 elim (lpx_sn_inv_alt … H) -H
#HL1 #IH @conj // -HL1
#I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (ldrop_fwd_length_minus4 … HLK1)
lapply (ldrop_fwd_length_le4 … HLK1)
normalize in ⊢ (%→%→?); #HKL1 #Hi
lapply (plus_minus_minus_be_aux … HL12 Hi) // -HL12 -Hi -HKL1
<minus_plus #Hi >Hi -Hi
elim (IH … HLK1 HLK) -IH #HI1 *
/4 width=5 by or_introl, or_intror, and3_intro, ex4_3_intro/
qed-.
