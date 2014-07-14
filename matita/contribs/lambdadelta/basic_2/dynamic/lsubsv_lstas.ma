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

include "basic_2/static/da_sta.ma".
include "basic_2/static/lsubd_da.ma".
include "basic_2/unfold/lstas_alt.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/lsubsv_lsubd.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on nat-iterated static type assignment ************************)

lemma lsubsv_lstas_trans: ∀h,g,G,L2,T,U2,l1. ⦃G, L2⦄ ⊢ T •*[h, l1] U2 →
                          ∀l2. l1 ≤ l2 → ⦃G, L2⦄ ⊢ T ▪[h, g] l2 →
                          ∀L1. G ⊢ L1 ⫃¡[h, g] L2 →
                          ∃∃U1. ⦃G, L1⦄ ⊢ T •*[h, l1] U1 & ⦃G, L1⦄ ⊢ U1 ⬌* U2.
#h #g #G #L2 #T #U #l1 #H @(lstas_ind_alt … H) -G -L2 -T -U -l1
[1,2: /2 width=3 by ex2_intro/
| #G #L2 #K2 #X #Y #U #i #l1 #HLK2 #_ #HYU #IHXY #l2 #Hl12 #Hl2 #L1 #HL12
  elim (da_inv_lref … Hl2) -Hl2 * #K0 #V0 [| #l0 ] #HK0 #HV0
  lapply (drop_mono … HK0 … HLK2) -HK0 #H destruct
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1 [ | -HYU -IHXY -HLK1 ]
  [ #HK12 #H destruct
    elim (IHXY … Hl12 HV0 … HK12) -K2 -l2 #T #HXT #HTY
    lapply (drop_fwd_drop2 … HLK1) #H
    elim (lift_total T 0 (i+1))
    /3 width=12 by lstas_ldef, cpcs_lift, ex2_intro/
  | #V #l0 #_ #_ #_ #_ #_ #_ #_ #H destruct
  ]
| #G #L2 #K2 #X #Y #Y0 #U #i #l1 #HLK2 #HXY0 #_ #HYU #IHXY #l2 #Hl12 #Hl2 #L1 #HL12
  elim (da_inv_lref … Hl2) -Hl2 * #K0 #V0 [| #l0 ] #HK0 #HV0 [| #H1 ]
  lapply (drop_mono … HK0 … HLK2) -HK0 #H2 destruct
  lapply (le_plus_to_le_r … Hl12) -Hl12 #Hl12
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct
    lapply (lsubsv_fwd_lsubd … HK12) #H
    lapply (lsubd_da_trans … HV0 … H) -H #H
    elim (da_inv_sta … H) -H
    elim (IHXY … Hl12 HV0 … HK12) -K2 -Hl12 #Y1
    lapply (drop_fwd_drop2 … HLK1)
    elim (lift_total Y1 0 (i+1))
    /3 width=12 by lstas_ldec, cpcs_lift, ex2_intro/
  | #V #l #_ #_ #HVX #_ #HV #HX #HK12 #_ #H destruct
    lapply (da_mono … HX … HV0) -HX #H destruct
    elim (IHXY … Hl12 HV0 … HK12) -K2 #Y0 #HXY0 #HY0
    elim (da_inv_sta … HV) -HV #W #HVW
    elim (lstas_total … HVW (l1+1)) -W #W #HVW
    lapply (HVX … Hl12 HVW HXY0) -HVX -Hl12 -HXY0 #HWY0
    lapply (cpcs_trans … HWY0 … HY0) -Y0
    lapply (drop_fwd_drop2 … HLK1)
    elim (lift_total W 0 (i+1))
    /4 width=12 by lstas_ldef, lstas_cast, cpcs_lift, ex2_intro/
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
