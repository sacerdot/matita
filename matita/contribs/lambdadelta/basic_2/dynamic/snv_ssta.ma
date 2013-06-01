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

include "basic_2/dynamic/snv_lift.ma".
include "basic_2/dynamic/snv_cpcs.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on stratified static type assignment for terms ****************)

fact snv_ssta_aux: ∀h,g,L0,T0.
                   (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                   (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_cpr_lpr h g L1 T1) →
                   (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                   ∀L1,T1. L0 = L1 → T0 = T1 → IH_snv_ssta h g L1 T1.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 * * [||||*]
[ #k #HL0 #HT0 #_ #X #l #H2 destruct -IH3 -IH2 -IH1
  elim (ssta_inv_sort1 … H2) -H2 #_ #H destruct //
| #i #HL0 #HT0 #H1 #X #l #H2 destruct -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I #K1 #V1 #HLK1 #HV1
  elim (ssta_inv_lref1 … H2) -H2 * #K0 #V0 #W1 [| #l ] #H #HVW1 #HX [| #_ ]
  lapply (ldrop_mono … H … HLK1) -H #H destruct
  lapply (fsupp_lref … HLK1) #H
  lapply (ldrop_fwd_ldrop2 … HLK1) -HLK1 /4 width=7/
| #p #HL0 #HT0 #H1 #X #l #H2 destruct -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HL0 #HT0 #H1 #X #l #H2 destruct -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  elim (ssta_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct /4 width=5/
| #V1 #T1 #HL0 #HT0 #H1 #X #l #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #W0 #T0 #l0 #HV1 #HT1 #HVW1 #HW10 #HT10
  elim (ssta_inv_appl1 … H2) -H2 #U1 #HTU1 #H destruct
  lapply (IH1 … HT1 … HTU1) -IH1 /2 width=1/ #HU1
  elim (ssta_dxprs_aux … IH3 IH2 … HTU1 … HT10) -IH3 -IH2 // /2 width=2/ -T1 #U #X #HU1U #H #HU0
  elim (sstas_inv_bind1 … H) -H #U0 #HTU0 #H destruct
  elim (cpcs_inv_abst2 … HU0) -HU0 #W2 #U2 #HU2 #HU02
  elim (cprs_fwd_abst … HU02 Abst W0) -HU02 #HW02 #_
  lapply (cprs_trans … HW10 … HW02) -W0 /3 width=10 by snv_appl, ex2_intro/ (**) (* auto is too slow without trace *)
| #W1 #T1 #HL0 #HT0 #H1 #X #l #H2 destruct -IH3 -IH2
  elim (snv_inv_cast … H1) -H1 #U1 #l0 #HW1 #HT1 #HTU1 #HUW1
  lapply (ssta_inv_cast1 … H2) -H2 /3 width=5/
]
qed-.
