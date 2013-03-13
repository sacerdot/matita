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

include "basic_2/dynamic/snv_cpcs.ma".
include "basic_2/dynamic/lsubsv_ssta.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties for the preservation results **********************************)

fact sstas_lsubsv_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_lsubsv h g L1 T1) →
                       ∀L2,T. h ⊢ ⦃L0, T0⦄ >[g] ⦃L2, T⦄ → ⦃h, L2⦄ ⊩ T :[g] →
                       ∀L1. h ⊢ L1 ⊩:⊑[g] L2 → ∀U2. ⦃h, L2⦄ ⊢ T •*[g] U2 →
                       ∃∃U1. ⦃h, L1⦄ ⊢ T •*[g] U1 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH4 #IH3 #IH2 #IH1 #L2 #T #HLT0 #HT #L1 #HL12 #U2 #H @(sstas_ind … H) -U2 [ /2 width=3/ ]
#U2 #W #l #HTU2 #HU2W * #U1 #HTU1 #HU12
lapply (IH1 … HT … HL12) // #H
lapply (snv_sstas_aux … IH2 … HTU1) // /3 width=4 by ygt_yprs_trans, lsubsv_yprs/ -H #HU1
lapply (snv_sstas_aux … IH2 … HTU2) // #H
lapply (IH1 … H … HL12) [ /3 width=4 by ygt_yprs_trans, sstas_yprs/ ] -H #HU2
elim (snv_fwd_ssta … HU1) #W1 #l1 #HUW1
elim (lsubsv_ssta_trans … HU2W … HL12) -HU2W #W2 #HUW2 #HW2
elim (ssta_ltpr_cpcs_aux … IH4 IH3 … HU1 HU2 … HUW1 … HUW2 … HU12) -HU1 -HU2 -HUW2 -HU12 //
[2,3: /4 width=4 by ygt_yprs_trans, sstas_yprs, lsubsv_yprs/ ] -L2 -L0 -T0 -U2 #H #HW12 destruct
lapply (cpcs_trans … HW12 … HW2) -W2 /3 width=4/
qed-.

fact dxprs_lsubsv_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_lsubsv h g L1 T1) →
                       ∀L2,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L2, T1⦄ → ⦃h, L2⦄ ⊩ T1 :[g] →
                       ∀L1. h ⊢ L1 ⊩:⊑[g] L2 → ∀T2. ⦃h, L2⦄ ⊢ T1 •*➡*[g] T2 →
                       ∃∃T. ⦃h, L1⦄ ⊢ T1 •*➡*[g] T & L1 ⊢ T2 ➡* T.
#h #g #L0 #T0 #IH4 #IH3 #IH2 #IH1 #L2 #T1 #HLT0 #HT1 #L1 #HL12 #T2 * #T #HT1T #HTT2
lapply (lsubsv_cprs_trans … HL12 … HTT2) -HTT2 #HTT2
elim (sstas_lsubsv_aux … IH4 IH3 IH2 IH1 … HLT0 … HL12 … HT1T) // -L2 -L0 -T0 #T0 #HT10 #HT0
lapply (cpcs_cprs_strap1 … HT0 … HTT2) -T #HT02
elim (cpcs_inv_cprs … HT02) -HT02 /3 width=3/
qed-.
