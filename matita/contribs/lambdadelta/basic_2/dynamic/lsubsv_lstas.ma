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

include "basic_2/static/lsubd_da.ma".
include "basic_2/unfold/lstas_alt.ma".
include "basic_2/equivalence/scpes_cpcs.ma".
include "basic_2/dynamic/lsubsv_lsubd.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on nat-iterated static type assignment ************************)

lemma lsubsv_lstas_trans: ∀h,g,G,L2,T,U2,l2. ⦃G, L2⦄ ⊢ T •*[h, l2] U2 →
                          ∀l1. l2 ≤ l1 → ⦃G, L2⦄ ⊢ T ▪[h, g] l1 →
                          ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                          ∃∃U1. ⦃G, L1⦄ ⊢ T •*[h, l2] U1 & ⦃G, L1⦄ ⊢ U1 ⬌* U2.
#h #g #G #L2 #T #U #l2 #H @(lstas_ind_alt … H) -G -L2 -T -U -l2
[1,2: /2 width=3 by ex2_intro/
| #G #L2 #K2 #X #Y #U #i #l2 #HLK2 #_ #HYU #IHXY #l1 #Hl21 #Hl1 #L1 #HL12
  elim (da_inv_lref … Hl1) -Hl1 * #K0 #V0 [| #l0 ] #HK0 #HV0
  lapply (drop_mono … HK0 … HLK2) -HK0 #H destruct
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ | -HYU -IHXY -HLK1 ]
  [ #HK12 #H destruct
    elim (IHXY … Hl21 HV0 … HK12) -K2 -l1 #T #HXT #HTY
    lapply (drop_fwd_drop2 … HLK1) #H
    elim (lift_total T 0 (i+1))
    /3 width=12 by lstas_ldef, cpcs_lift, ex2_intro/
  | #V #l0 #_ #_ #_ #_ #_ #H destruct
  ]
| #G #L2 #K2 #X #Y #Y0 #U #i #l2 #HLK2 #HXY0 #_ #HYU #IHXY #l1 #Hl21 #Hl1 #L1 #HL12
  elim (da_inv_lref … Hl1) -Hl1 * #K0 #V0 [| #l0 ] #HK0 #HV0 [| #H1 ]
  lapply (drop_mono … HK0 … HLK2) -HK0 #H2 destruct
  lapply (le_plus_to_le_r … Hl21) -Hl21 #Hl21
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct
    lapply (lsubsv_fwd_lsubd … HK12) #H
    lapply (lsubd_da_trans … HV0 … H) -H #H
    elim (da_inv_sta … H) -H
    elim (IHXY … Hl21 HV0 … HK12) -K2 -Hl21 #Y1
    lapply (drop_fwd_drop2 … HLK1)
    elim (lift_total Y1 0 (i+1))
    /3 width=12 by lstas_ldec, cpcs_lift, ex2_intro/
  | #V #l1 #HXV #_ #HV #HX #HK12 #_ #H destruct
    lapply (da_mono … HV0 … HX) -HX #H destruct
    elim (shnv_inv_cast … HXV) -HXV #_ #_ #H
    lapply (H … Hl21) -H #HXV
    elim (IHXY … Hl21 HV0 … HK12) -K2 -Hl21 #Y0 #HXY0 #HY0
    elim (da_inv_sta … HV) -HV #W #HVW
    elim (lstas_total … HVW (l2+1)) -W #W #HVW
    lapply (scpes_inv_lstas_eq … HXV … HXY0 … HVW) -HXV -HXY0 #HY0W
    lapply (cpcs_canc_sn … HY0W … HY0) -Y0 #HYW
    elim (lift_total W 0 (i+1))
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

lemma lsubsv_sta_trans: ∀h,g,G,L2,T,U2. ⦃G, L2⦄ ⊢ T •[h] U2 →
                        ∀l. ⦃G, L2⦄ ⊢ T ▪[h, g] l+1 →
                        ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                        ∃∃U1. ⦃G, L1⦄ ⊢ T •[h] U1 & ⦃G, L1⦄ ⊢ U1 ⬌* U2.
#h #g #G #L2 #T #U2 #H #l #HTl #L1 #HL12
elim (lsubsv_lstas_trans … U2 1 … HTl … HL12)
/3 width=3 by lstas_inv_SO, sta_lstas, ex2_intro/
qed-.
