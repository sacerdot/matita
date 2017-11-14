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
include "basic_2/dynamic/snv_scpes.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on nat-iterated stratified static type assignment for terms ***)

fact snv_lstas_aux: ∀h,o,G0,L0,T0.
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≛[h, o] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h o G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≛[h, o] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h o G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≛[h, o] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h o G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≛[h, o] ⦃G1, L1, T1⦄ → IH_snv_lstas h o G1 L1 T1) →
                    ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_lstas h o G1 L1 T1.
#h #o #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #s #HG0 #HL0 #HT0 #_ #d1 #d2 #Hd21 #Hd1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  >(lstas_inv_sort1 … H2) -X //
| #i #HG0 #HL0 #HT0 #H1 #d1 #d2 #Hd21 #Hd1 #T #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #X0 #HLK0 #HX0
  elim (da_inv_lref … Hd1) -Hd1 * #K1 [ #V1 | #W1 #d0 ] #HLK1 [ #Hd1 | #Hd0 #H ]
  lapply (drop_mono … HLK0 … HLK1) -HLK0 #H0 destruct
  elim (lstas_inv_lref1 … H2) -H2 * #K #Y #X [3,6: #d ] #HLK #HYX [1,2: #HXT #H0 |3,5: #HXT |4,6: #H1 #H2 ]
  lapply (drop_mono … HLK … HLK1) -HLK #H destruct
  [ lapply (le_plus_to_le_c … Hd21) -Hd21 #Hd21 |3: -Hd21 ]
  lapply (fqup_lref … G1 … HLK1) #H
  lapply (drop_fwd_drop2 … HLK1) /4 width=8 by snv_lift, snv_lref, fqup_fpbg/
| #p #HG0 #HL0 #HT0 #H1 #d1 #d2 #Hd21 #Hd1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #d1 #d2 #Hd21 #Hd1 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  lapply (da_inv_bind … Hd1) -Hd1 #Hd1
  elim (lstas_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct /4 width=8 by fqup_fpbg, snv_bind/
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #d1 #d2 #Hd21 #Hd1 #X #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #U1 #d0 #HV1 #HT1 #HVW1 #HTU1
  lapply (da_inv_flat … Hd1) -Hd1 #Hd1
  elim (lstas_inv_appl1 … H2) -H2 #T0 #HT10 #H destruct
  lapply (IH1 … HT1 … Hd1 … HT10) /2 width=1 by fqup_fpbg/ #HT0
  lapply (lstas_scpds_aux … IH1 IH4 IH3 IH2 … Hd1 … HT10 … HTU1) -IH4 -IH3 -IH2 -IH1 /2 width=1 by fqup_fpbg/ -T1 -d1 #H
  elim (scpes_inv_abst2 … H) -H /3 width=6 by snv_appl, scpds_cprs_trans/
| #U1 #T1 #HG0 #HL0 #HT0 #H1 #d1 #d2 #Hd21 #Hd1 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_cast … H1) -H1
  lapply (da_inv_flat … Hd1) -Hd1
  lapply (lstas_inv_cast1 … H2) -H2 /3 width=8 by fqup_fpbg/
]
qed-.
