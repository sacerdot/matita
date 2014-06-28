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

(* Properties on context-sensitive free variables ***************************)

fact llpx_sn_frees_trans_aux: ∀R. (s_r_confluent1 … R (llpx_sn R 0)) → (frees_trans R) →
                              ∀L2,U,d,i. L2 ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                              ∀L1. llpx_sn R d U L1 L2 → L1 ⊢ i ϵ 𝐅*[d]⦃U⦄.
#R #H1R #H2R #L2 #U #d #i #H elim H -L2 -U -d -i /3 width=2 by frees_eq/
#I2 #L2 #K2 #U #W2 #d #i #j #Hdj #Hji #HnU #HLK2 #_ #IHW2 #L1 #HL12
elim (llpx_sn_inv_alt_r … HL12) -HL12 #HL12 #IH
lapply (drop_fwd_length_lt2 … HLK2) #Hj
elim (drop_O1_lt (Ⓕ) L1 j) // -Hj -HL12 #I1 #K1 #W1 #HLK1
elim (IH … HnU HLK1 HLK2) // -IH -HLK2 /5 width=11 by frees_be/
qed-.

lemma llpx_sn_frees_trans: ∀R. (s_r_confluent1 … R (llpx_sn R 0)) → (frees_trans R) →
                           ∀L1,L2,U,d. llpx_sn R d U L1 L2 →
                           ∀i. L2 ⊢ i ϵ 𝐅*[d]⦃U⦄ → L1 ⊢ i ϵ 𝐅*[d]⦃U⦄.
/2 width=6 by llpx_sn_frees_trans_aux/ qed-.
