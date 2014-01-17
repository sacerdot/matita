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

(* Properties on nat-iterated stratified static type assignment for terms ***)

fact snv_lsstas_aux: ∀h,g,G0,L0,T0.
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >⋕[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >⋕[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >⋕[h, g] ⦃G1, L1, T1⦄ → IH_lsstas_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >⋕[h, g] ⦃G1, L1, T1⦄ → IH_snv_lsstas h g G1 L1 T1) →
                     ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_snv_lsstas h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #k #HG0 #HL0 #HT0 #_ #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  >(lsstas_inv_sort1 … H2) -X //
| #i #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  [ lapply (lsstas_inv_O … H2) -H2 #H destruct // ]
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #X0 #HLK0 #HX0
  elim (da_inv_lref … Hl1) -Hl1 * #K1 [ #V1 | #W1 #l ] #HLK1 [ #Hl1 | #Hl #H ]
  lapply (ldrop_mono … HLK0 … HLK1) -HLK0 #H0 destruct
  elim (lsstas_inv_lref1 … H2) -H2 * #K0 #Y0 #X0 [2,4: #l0 ] #HLK0 [1,2: #HYl0 ] #HYX0 #HX0
  lapply (ldrop_mono … HLK0 … HLK1) -HLK0 #H destruct
  [ lapply (le_plus_to_le_r … Hl21) -Hl21 #Hl21 ]
  lapply (fqup_lref … G1 … HLK1) #H
  lapply (ldrop_fwd_drop2 … HLK1) -HLK1 /4 width=8 by fqup_fpbg, snv_lift/
| #p #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  elim (snv_inv_bind … H1) -H1 #HV1 #HT1
  lapply (da_inv_bind … Hl1) -Hl1 #Hl1
  elim (lsstas_inv_bind1 … H2) -H2 #U1 #HTU1 #H destruct /4 width=8 by fqup_fpbg, snv_bind/
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 #Hl21 #Hl1 #X #H2 destruct
  elim (snv_inv_appl … H1) -H1 #a #W1 #W0 #T0 #l0 #HV1 #HT1 #Hl0 #HVW1 #HW10 #HT10
  lapply (da_inv_flat … Hl1) -Hl1 #Hl1
  elim (lsstas_inv_appl1 … H2) -H2 #U1 #HTU1 #H destruct
  lapply (IH1 … HT1 … Hl1 … HTU1) /2 width=1 by fqup_fpbg/ #HU1
  elim (lsstas_cpds_aux … IH1 IH4 IH3 IH2 … Hl1 … HTU1 … HT10) -IH4 -IH3 -IH2 -IH1 /2 width=1 by fqup_fpbg/ -T1 -l1 #X #l #_ #H #HU10 -l2
  elim (lsstas_inv_bind1 … H) -H #U0 #_ #H destruct -T0 -l
  elim (cpes_inv_abst2 … HU10) -HU10 #W2 #U2 #HU12 #HU02
  elim (cprs_inv_abst … HU02) -HU02 #HW02 #_
  /3 width=7 by snv_appl, cprs_trans/
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #l1 #l2 @(nat_ind_plus … l2) -l2 [ #_ | #l2 #_ #Hl21 ] #Hl1 #X #H2 destruct -IH4 -IH3 -IH2
  [ lapply (lsstas_inv_O … H2) -H2 #H destruct // ]
  elim (snv_inv_cast … H1) -H1
  lapply (da_inv_flat … Hl1) -Hl1
  lapply (lsstas_inv_cast1 … H2) -H2 /3 width=8 by fqup_fpbg/
]
qed-.
