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

include "basic_2/substitution/lpx_sn_alt.ma".
include "basic_2/multiple/llor.ma".
include "basic_2/multiple/lleq_alt.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Inversion lemmas on pointwise union for local environments ****************)

lemma llpx_sn_llor_fwd_sn: ∀R. (∀L. reflexive … (R L)) →
                           ∀L1,L2,T,d. llpx_sn R d T L1 L2 →
                           ∀L. L1 ⩖[T, d] L2 ≡ L → lpx_sn R L1 L.
#R #HR #L1 #L2 #T #d #H1 #L #H2
elim (llpx_sn_llpx_sn_alt … H1) -H1 #HL12 #IH1
elim H2 -H2 #_ #HL1 #IH2
@lpx_sn_intro_alt // #I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (drop_fwd_length_lt2 … HLK) #HiL
elim (drop_O1_lt (Ⓕ) L2 i) // -HiL -HL1 -HL12 #I2 #K2 #V2 #HLK2
elim (IH2 … HLK1 HLK2 HLK) -IH2 -HLK * /2 width=1 by conj/
#HnT #H1 #H2 elim (IH1 … HnT … HLK1 HLK2) -IH1 -HnT -HLK1 -HLK2 /2 width=1 by conj/
qed-.
