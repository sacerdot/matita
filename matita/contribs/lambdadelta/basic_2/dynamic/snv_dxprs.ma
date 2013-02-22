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

include "basic_2/computation/ygt.ma".
include "basic_2/dynamic/snv_cpr.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on context-free parallel computation for closures *************)

fact ssta_cprs_aux: ∀h,g,L0,T0. (
                       ∀L,T2. h ⊢ ⦃L0, T0⦄ >[g] ⦃L, T2⦄ →
                       ∀T1. L ⊢ T1 ⬌* T2 → ⦃h, L⦄ ⊩ T1 :[g] → ⦃h, L⦄ ⊩ T2 :[g] →
                       ∀U1,l1. ⦃h, L⦄ ⊢ T1 •[g, l1] U1 →
                       ∀U2,l2. ⦃h, L⦄ ⊢ T2 •[g, l2] U2 →
                       L ⊢ U1 ⬌* U2 ∧ l1 = l2
                    ) → (
                       ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∀L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T2. ⦃h, L2⦄ ⊢ T1 •*➡*[g] T2 → ⦃h, L2⦄ ⊩ T2 :[g]
                    ) → (
                       ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ →
                       ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 → ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∀L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T2. L2 ⊢ T1 ➡* T2 →
                       ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                   ) →
                   ∀L1,T1,T2. L1 ⊢ T1 ➡* T2 → L0 = L1 → T0 = T1 →
                   ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 → ⦃h, L1⦄ ⊩ T1 :[g] →
                   ∃∃U2. ⦃h, L1⦄ ⊢ T2 •[g, l] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #T2 #H
@(cprs_ind_dx … H) -T1 [ /2 width=3/ ]
#T1 #T #HT1T #HTT2 #IH #H1 #H2 #U1 #l #HTU1 #HT1 destruct
elim (term_eq_dec T1 T) #H destruct [ /2 width=1/ ] -IH
elim (ssta_cpr_aux … HTU1 … HT1T HT1) -HTU1
[2: // |3: skip |4,5,6: /3 width=9 by inj, dxprs_strap2, fw_ygt/ ] -IH3 #U #HTU #HU1
lapply (snv_cpr_aux … HT1 … HT1T) -HT1
[ // | skip |3,4: /3 width=6 by inj, fw_ygt/ ] -IH2 #HT
elim (IH1 … HTU HT … HTT2) -IH1 -HTU -HT -HTT2 // [2: /3 width=1/ ] -T #U2 #HTU2 #HU2
lapply (fpcs_inv_cpcs … HU2) -HU2 #HU2
lapply (cpcs_trans … HU1 … HU2) -U /2 width=3/
qed-.

fact snv_cprs_aux: ∀h,g,L0,T0. (
                      ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ →
                      ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                      ∀L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T2. L2 ⊢ T1 ➡* T2 → ⦃h, L1⦄ ⊩ T1 :[g] →
                      ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄
                   ) → (
                      ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                      ∀L2. ⦃L1⦄ ➡ ⦃L2⦄ → ∀T2. ⦃h, L2⦄ ⊢ T1 •*➡*[g] T2 → ⦃h, L2⦄ ⊩ T2 :[g]
                   ) →
                   ∀L1,T1. L0 = L1 → T0 = T1 → ⦃h, L1⦄ ⊩ T1 :[g] →
                   ∀T2. L1 ⊢ T1 ➡* T2 → ⦃h, L1⦄ ⊩ T2 :[g].
#h #g #L0 #T0 #IH2 #IH1 #L1 #T1 #H1 #H2 #HT1 #T2 #H
@(cprs_ind … H) -T2 // -HT1
#T #T2 #HT1T #HTT2 #HT destruct
lapply (snv_cpr_aux … HT … HTT2) -HT -HTT2 [1,5: // |2: skip ]
/4 width=6 by cprs_ygt_trans, inj, fw_ygt/
qed-.
