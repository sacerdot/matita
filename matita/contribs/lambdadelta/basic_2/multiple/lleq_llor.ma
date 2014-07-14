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
include "basic_2/multiple/llpx_sn_frees.ma".
include "basic_2/multiple/lleq_alt.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Properties on pointwise union for local environments **********************)

lemma llpx_sn_llor_dx: ∀R. (s_r_confluent1 … R (llpx_sn R 0)) → (frees_trans R) →
                       ∀L1,L2,T,d. llpx_sn R d T L1 L2 → ∀L. L1 ⩖[T, d] L2 ≡ L → L2 ≡[T, d] L.
#R #H1R #H2R #L1 #L2 #T #d #H1 #L #H2
lapply (llpx_sn_frees_trans … H1R H2R … H1) -H1R -H2R #HR
elim (llpx_sn_llpx_sn_alt … H1) -H1 #HL12 #IH1
elim H2 -H2 #_ #HL1 #IH2
@lleq_intro_alt // #I2 #I #K2 #K #V2 #V #i #Hi #HnT #HLK2 #HLK
lapply (drop_fwd_length_lt2 … HLK) #HiL
elim (drop_O1_lt (Ⓕ) L1 i) // -HiL #I1 #K1 #V1 #HLK1
elim (IH1 … HLK1 HLK2) -IH1 /2 width=1 by/ #H #_ destruct
elim (IH2 … HLK1 HLK2 HLK) -IH2 -HLK1 -HLK2 -HLK * /2 width=1 by conj/ #H
[ elim (ylt_yle_false … H) -H //
| elim H -H /2 width=1 by/
]
qed.

lemma llpx_sn_llor_dx_sym: ∀R. (s_r_confluent1 … R (llpx_sn R 0)) → (frees_trans R) →
                           ∀L1,L2,T,d. llpx_sn R d T L1 L2 → ∀L. L1 ⩖[T, d] L2 ≡ L → L ≡[T, d] L2.
/3 width=6 by llpx_sn_llor_dx, lleq_sym/ qed.
