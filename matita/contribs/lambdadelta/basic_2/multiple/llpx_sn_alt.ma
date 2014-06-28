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

include "basic_2/multiple/frees.ma".
include "basic_2/multiple/llpx_sn_alt_rec.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* alternative definition of llpx_sn (not recursive) *)
definition llpx_sn_alt: relation3 lenv term term → relation4 ynat term lenv lenv ≝
                        λR,d,T,L1,L2. |L1| = |L2| ∧
                        (∀I1,I2,K1,K2,V1,V2,i. d ≤ yinj i → L1 ⊢ i ϵ 𝐅*[d]⦃T⦄ →
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           I1 = I2 ∧ R K1 V1 V2
                        ).

(* Main properties **********************************************************)

theorem llpx_sn_llpx_sn_alt: ∀R,T,L1,L2,d. llpx_sn R d T L1 L2 → llpx_sn_alt R d T L1 L2.
#R #U #L1 @(f2_ind … rfw … L1 U) -L1 -U
#n #IHn #L1 #U #Hn #L2 #d #H elim (llpx_sn_inv_alt_r … H) -H
#HL12 #IHU @conj //
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #H #HLK1 #HLK2 elim (frees_inv … H) -H
[ -n #HnU elim (IHU … HnU HLK1 HLK2) -IHU -HnU -HLK1 -HLK2 /2 width=1 by conj/
| * #J1 #K10 #W10 #j #Hdj #Hji #HnU #HLK10 #HnW10 destruct
  lapply (drop_fwd_drop2 … HLK10) #H
  lapply (drop_conf_ge … H … HLK1 ?) -H /2 width=1 by lt_to_le/ <minus_plus #HK10
  elim (drop_O1_lt (Ⓕ) L2 j) [2: <HL12 /2 width=5 by drop_fwd_length_lt2/ ] #J2 #K20 #W20 #HLK20
  lapply (drop_fwd_drop2 … HLK20) #H
  lapply (drop_conf_ge … H … HLK2 ?) -H /2 width=1 by lt_to_le/ <minus_plus #HK20
  elim (IHn K10 W10 … K20 0) -IHn -HL12 /3 width=6 by drop_fwd_rfw/
  elim (IHU … HnU HLK10 HLK20) -IHU -HnU -HLK10 -HLK20 //
]
qed.

theorem llpx_sn_alt_inv_llpx_sn: ∀R,T,L1,L2,d. llpx_sn_alt R d T L1 L2 → llpx_sn R d T L1 L2.
#R #U #L1 @(f2_ind … rfw … L1 U) -L1 -U
#n #IHn #L1 #U #Hn #L2 #d * #HL12 #IHU @llpx_sn_intro_alt_r //
#I1 #I2 #K1 #K2 #V1 #V2 #i #Hdi #HnU #HLK1 #HLK2 destruct
elim (IHU … HLK1 HLK2) /3 width=2 by frees_eq/
#H #HV12 @and3_intro // @IHn -IHn /3 width=6 by drop_fwd_rfw/
lapply (drop_fwd_drop2 … HLK1) #H1
lapply (drop_fwd_drop2 … HLK2) -HLK2 #H2
@conj [ @(drop_fwd_length_eq1 … H1 H2) // ] -HL12
#Z1 #Z2 #Y1 #Y2 #X1 #X2 #j #_
>(minus_plus_m_m j (i+1)) in ⊢ (%→?); >commutative_plus <minus_plus
#HnV1 #HKY1 #HKY2 (**) (* full auto too slow *)
lapply (drop_trans_ge … H1 … HKY1 ?) -H1 -HKY1 // #HLY1
lapply (drop_trans_ge … H2 … HKY2 ?) -H2 -HKY2 // #HLY2
/4 width=14 by frees_be, yle_plus_dx2_trans, yle_succ_dx/
qed-.
