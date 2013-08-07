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

include "basic_2/computation/cpds_cpds.ma".
include "basic_2/dynamic/lsubsv_cpds.ma".
include "basic_2/dynamic/lsubsv_cpcs.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties concerning stratified native validity *************************)

fact snv_lsubsv_aux: ∀h,g,G0,L0,T0.
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_ssta_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_ssta h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, g] ⦃G1, L1, T1⦄ → IH_snv_lsubsv h g G1 L1 T1) →
                     ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_lsubsv h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G #L2 * * [||||*] //
[ #i #HG0 #HL0 #HT0 #H #L1 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_lref … H) -H #I2 #K2 #W2 #HLK2 #HW2
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -HL12 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct
    /5 width=8 by snv_lref, fsupp_ygt, fsupp_lref/ (**) (* auto too slow without trace *)
  | #V #W1 #V2 #l #HV #_ #_ #_ #_ #_ #H destruct /2 width=5/
  ]
| #p #HG0 #HL0 #HT0 #H #L1 #HL12 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H)
| #a #I #V #T #HG0 #HL0 #HT0 #H #L1 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H) -H /4 width=4/
| #V #T #HG0 #HL0 #HT0 #H #L1 #HL12 destruct
  elim (snv_inv_appl … H) -H #a #W #W0 #U #l #HV #HT #HVW #HW0 #HTU
  lapply (lsubsv_cprs_trans … HL12 … HW0) -HW0 #HW0
  elim (lsubsv_ssta_trans … HVW … HL12) -HVW #W1 #HVW1 #HW1
  lapply (cpcs_cprs_strap1 … HW1 … HW0) -W #HW10
  elim (lsubsv_cpds_aux … IH4 IH3 IH2 IH1 … HL12 … HTU) -IH4 -IH3 -IH2 -HTU // /2 width=1/ #X #HTU #H
  elim (cprs_inv_abst1 … H) -H #W #U2 #HW0 #HU2 #H destruct
  lapply (cpcs_cprs_strap1 … HW10 … HW0) -W0 #H
  elim (cpcs_inv_cprs … H) -H #W0 #HW10 #HW0
  lapply (cpds_cprs_trans … (ⓛ{a}W0.U2) HTU ?) [ /2 width=1/ ] -HTU -HW0
  /4 width=8 by snv_appl, fsupp_ygt/ (**) (* auto too slow without trace *)
| #W #T #HG0 #HL0 #HT0 #H #L1 #HL12 destruct -IH4 -IH3 -IH2
  elim (snv_inv_cast … H) -H #U #l #HW #HT #HTU #HUW
  lapply (lsubsv_cpcs_trans … HL12 … HUW) -HUW #HUW
  elim (lsubsv_ssta_trans … HTU … HL12) -HTU #U0 #HTU0 #HU0
  lapply (cpcs_trans … HU0 … HUW) -U /4 width=4 by snv_cast, fsupp_ygt/ (**) (* auto too slow without trace *)
]
qed-.
