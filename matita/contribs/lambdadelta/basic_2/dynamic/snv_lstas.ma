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

fact snv_lstas_aux: ∀h,g,G0,L0,T0.
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                    (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                    ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_lstas h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #k #HG0 #HL0 #HT0 #_ #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  >(lstas_inv_sort1 … H2) -X //
| #i #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  [ lapply (lstas_inv_O … H2) -H2 #H destruct // ]
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #X0 #HLK0 #HX0
  elim (da_inv_lref … Hl1) -Hl1 * #K1 [ #V1 | #W1 #l ] #HLK1 [ #Hl1 | #Hl #H ]
  lapply (drop_mono … HLK0 … HLK1) -HLK0 #H0 destruct
  elim (lstas_inv_lref1 … H2) -H2 * #K0 #Y0 #X0 [2,4: #Y1 ] #HLK0 [1,2: #HY01 ] #HYX0 #HX0
  lapply (drop_mono … HLK0 … HLK1) -HLK0 #H destruct
  [ lapply (le_plus_to_le_r … Hl21) -Hl21 #Hl21 ]
  lapply (fqup_lref … G1 … HLK1) #H
  lapply (drop_fwd_drop2 … HLK1) -HLK1 /4 width=8 by fqup_fpbg, snv_lift/
| #p #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  lapply (da_inv_bind … Hl1) -Hl1 #Hl1
  elim (lstas_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct /4 width=8 by fqup_fpbg, snv_bind/
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #U1 #l0 #HV1 #HT1 #HVW1 #HTU1
  lapply (da_inv_flat … Hl1) -Hl1 #Hl1
  elim (lstas_inv_appl1 … H2) -H2 #T0 #HT10 #H destruct
  lapply (IH1 … HT1 … Hl1 … HT10) /2 width=1 by fqup_fpbg/ #HT0
  lapply (lstas_scpds_aux … IH1 IH4 IH3 IH2 … Hl1 … HT10 … HTU1) -IH4 -IH3 -IH2 -IH1 /2 width=1 by fqup_fpbg/ -T1 -l1 #H
  elim (scpes_inv_abst2 … H) -H /3 width=6 by snv_appl, scpds_cprs_trans/
| #U1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  [ lapply (lstas_inv_O … H2) -H2 #H destruct // ]
  elim (snv_inv_cast … H1) -H1 
  lapply (da_inv_flat … Hl1) -Hl1
  lapply (lstas_inv_cast1 … H2) -H2 /3 width=8 by fqup_fpbg/
]
qed-.
