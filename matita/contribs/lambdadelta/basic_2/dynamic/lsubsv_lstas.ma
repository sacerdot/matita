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

include "basic_2/equivalence/scpes_cpcs.ma".
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on nat-iterated static type assignment ************************)

lemma lsubsv_lstas_trans: ∀h,g,G,L2,T,U2,l2. ⦃G, L2⦄ ⊢ T •*[h, l2] U2 →
                          ∀l1. l2 ≤ l1 → ⦃G, L2⦄ ⊢ T ▪[h, g] l1 →
                          ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                          ∃∃U1. ⦃G, L1⦄ ⊢ T •*[h, l2] U1 & ⦃G, L1⦄ ⊢ U1 ⬌* U2.
#h #g #G #L2 #T #U #l2 #H elim H -G -L2 -T -U -l2
[ /2 width=3 by ex2_intro/
| #G #L2 #K2 #V #W #U #i #l2 #HLK2 #_ #HWU #IHVW #l1 #Hl21 #Hl1 #L1 #HL12
  elim (da_inv_lref … Hl1) -Hl1 * #K0 #V0 [| #l0 ] #HK0 #HV0
  lapply (drop_mono … HK0 … HLK2) -HK0 #H destruct
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #Y #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ | -HWU -IHVW -HLK1 ]
  [ #HK12 #H destruct
    elim (IHVW … Hl21 HV0 … HK12) -K2 -l1 #T #HVT #HTW
    lapply (drop_fwd_drop2 … HLK1) #H
    elim (lift_total T 0 (i+1))
    /3 width=12 by lstas_ldef, cpcs_lift, ex2_intro/
  | #V0 #l0 #_ #_ #_ #_ #_ #H destruct
  ]
| #G #L2 #K2 #V #W #i #HLK2 #_ #IHVW #l1 #_ #Hl1 #L1 #HL12
  elim (da_inv_lref … Hl1) -Hl1 * #K0 #V0 [| #l0 ] #HK0 #HV0 [| #H1 ]
  lapply (drop_mono … HK0 … HLK2) -HK0 #H2 destruct
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #Y #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct
    elim (IHVW … HV0 … HK12) -K2 /3 width=5 by lstas_zero, ex2_intro/
  | #V1 #l1 #_ #_ #HV1 #HV #HK12 #_ #H destruct
    lapply (da_mono … HV0 … HV) -HV #H destruct
    elim (da_lstas … HV1 0) -HV1 #W1 #HVW1 #_
    elim (lift_total W1 0 (i+1)) #U1 #HWU1
    elim (IHVW … HV0 … HK12) -K2 // #X #HVX #_ -W
    @(ex2_intro … U1) /3 width=6 by lstas_cast, lstas_ldef/ (**) (* full auto too slow *)
    @cpcs_cprs_sn @(cprs_delta … HLK1 … HWU1)
    /4 width=2 by cprs_strap1, cpr_cprs, lstas_cpr, cpr_eps/
  ]
| #G #L2 #K2 #V #W #U #i #l2 #HLK2 #_ #HWU #IHVW #l1 #Hl21 #Hl1 #L1 #HL12
  elim (da_inv_lref … Hl1) -Hl1 * #K0 #V0 [| #l0 ] #HK0 #HV0 [| #H1 ]
  lapply (drop_mono … HK0 … HLK2) -HK0 #H2 destruct
  lapply (le_plus_to_le_r … Hl21) -Hl21 #Hl21
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #Y #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct
    elim (IHVW … Hl21 HV0 … HK12) -K2 -Hl21 #X
    lapply (drop_fwd_drop2 … HLK1)
    elim (lift_total X 0 (i+1))
    /3 width=12 by lstas_succ, cpcs_lift, ex2_intro/
  | #V1 #l1 #H0 #_ #HV1 #HV #HK12 #_ #H destruct
    lapply (da_mono … HV0 … HV) -HV #H destruct
    elim (shnv_inv_cast … H0) -H0 #_ #_ #H
    lapply (H … Hl21) -H #HVV1
    elim (IHVW … Hl21 HV0 … HK12) -K2 -Hl21 #X #HVX #HXW
    elim (da_lstas … HV1 (l2+1)) -HV1 #X1 #HVX1 #_
    lapply (scpes_inv_lstas_eq … HVV1 … HVX … HVX1) -HVV1 -HVX #HXX1
    lapply (cpcs_canc_sn … HXX1 … HXW) -X
    elim (lift_total X1 0 (i+1))
    lapply (drop_fwd_drop2 … HLK1)
    /4 width=12 by cpcs_lift, lstas_cast, lstas_ldef, ex2_intro/
  ]
| #a #I #G #L2 #V2 #T2 #U2 #l1 #_ #IHTU2 #l2 #Hl12 #Hl2 #L1 #HL12
  lapply (da_inv_bind … Hl2) -Hl2 #Hl2
  elim (IHTU2 … Hl2 (L1.ⓑ{I}V2) …)
  /3 width=3 by lsubsv_pair, lstas_bind, cpcs_bind_dx, ex2_intro/
| #G #L2 #V2 #T2 #U2 #l1 #_ #IHTU2 #l2 #Hl12 #Hl2 #L1 #HL12
  lapply (da_inv_flat … Hl2) -Hl2 #Hl2
  elim (IHTU2 … Hl2 … HL12) -L2
  /3 width=5 by lstas_appl, cpcs_flat, ex2_intro/
| #G #L2 #W2 #T2 #U2 #l1 #_ #IHTU2 #l2 #Hl12 #Hl2 #L1 #HL12
  lapply (da_inv_flat … Hl2) -Hl2 #Hl2
  elim (IHTU2 … Hl2 … HL12) -L2
  /3 width=3 by lstas_cast, ex2_intro/
]
qed-.

lemma lsubsv_sta_trans: ∀h,g,G,L2,T,U2. ⦃G, L2⦄ ⊢ T •*[h, 1] U2 →
                        ∀l. ⦃G, L2⦄ ⊢ T ▪[h, g] l+1 →
                        ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                        ∃∃U1. ⦃G, L1⦄ ⊢ T •*[h, 1] U1 & ⦃G, L1⦄ ⊢ U1 ⬌* U2.
/2 width=7 by lsubsv_lstas_trans/ qed-.
