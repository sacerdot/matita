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

include "basic_2/multiple/llor.ma".
include "basic_2/multiple/lleq_alt.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Properties on poinwise union for local environments **********************)

lemma llpx_sn_llor_dx: ∀R,L1,L2.
                       (∀U,i. L2 ⊢ i ϵ 𝐅*[0]⦃U⦄ → L1 ⊢ i ϵ 𝐅*[0]⦃U⦄) →
                       ∀T. llpx_sn R 0 T L1 L2 → ∀L. L1 ⩖[T] L2 ≡ L → L2 ≡[T, 0] L.
#R #L1 #L2 #HR #T #H1 #L #H2
elim (llpx_sn_llpx_sn_alt … H1) -H1 #HL12 #IH1
elim H2 -H2 #_ #HL1 #IH2
@lleq_intro_alt // #I2 #I #K2 #K #V2 #V #i #Hi #HnT #HLK2 #HLK
lapply (ldrop_fwd_length_lt2 … HLK) #HiL
elim (ldrop_O1_lt (Ⓕ) L1 i) // -HiL #I1 #K1 #V1 #HLK1
elim (IH1 … HLK1 HLK2) -IH1 /2 width=1 by/ #H #_ destruct
elim (IH2 … HLK1 HLK2 HLK) -IH2 -HLK1 -HLK2 -HLK * /2 width=1 by conj/ #H
elim H -H /2 width=1 by/
qed.
