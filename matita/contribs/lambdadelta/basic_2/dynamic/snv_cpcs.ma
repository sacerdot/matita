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

include "basic_2/unfold/sstas_sstas.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/snv_sstas.ma".
include "basic_2/dynamic/ygt.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Inductive premises for the preservation results **************************)

definition IH_snv_cpr_lpr: ∀h:sh. sd h → relation2 lenv term ≝
                           λh,g,L1,T1. ⦃h, L1⦄ ⊢ T1 ¡[g] →
                           ∀T2. L1 ⊢ T1 ➡ T2 → ∀L2. L1 ⊢ ➡ L2 → ⦃h, L2⦄ ⊢ T2 ¡[g].

definition IH_ssta_cpr_lpr: ∀h:sh. sd h → relation2 lenv term ≝
                            λh,g,L1,T1. ⦃h, L1⦄ ⊢ T1 ¡[g] →
                            ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                            ∀T2. L1 ⊢ T1 ➡ T2 → ∀L2. L1 ⊢ ➡ L2 →
                            ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L1 ⊢ U1 ⬌* U2.

definition IH_snv_ssta: ∀h:sh. sd h → relation2 lenv term ≝
                        λh,g,L1,T1. ⦃h, L1⦄ ⊢ T1 ¡[g] →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l+1, U1⦄ → ⦃h, L1⦄ ⊢ U1 ¡[g].

definition IH_snv_lsubsv: ∀h:sh. sd h → relation2 lenv term ≝
                          λh,g,L2,T. ⦃h, L2⦄ ⊢ T ¡[g] →
                          ∀L1. h ⊢ L1 ¡⊑[g] L2 → ⦃h, L1⦄ ⊢ T ¡[g].

(* Properties for the preservation results **********************************)

fact snv_cprs_lpr_aux: ∀h,g,L0,T0.
                       (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                       ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                       ∀T2. L1 ⊢ T1 ➡* T2 → ∀L2. L1 ⊢ ➡ L2 → ⦃h, L2⦄ ⊢ T2 ¡[g].
#h #g #L0 #T0 #IH #L1 #T1 #HLT0 #HT1 #T2 #H
elim H -T2 [ /2 width=6/ ] -HT1
/4 width=6 by ygt_yprs_trans, cprs_yprs/
qed-.

fact ssta_cprs_lpr_aux: ∀h,g,L0,T0.
                        (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                        (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_cpr_lpr h g L1 T1) →
                        ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                        ∀T2. L1 ⊢ T1 ➡* T2 → ∀L2. L1 ⊢ ➡ L2 → 
                        ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L1 #T1 #H01 #HT1 #U1 #l #HTU1 #T2 #H
elim H -T2 [ /2 width=5/ ]
#T #T2 #HT1T #HTT2 #IHT1 #L2 #HL12
elim (IHT1 L1) // -IHT1 #U #HTU #HU1
elim (IH1 … HTU … HTT2 … HL12) -IH1 -HTU -HTT2 -HL12
[2: /3 width=9 by snv_cprs_lpr_aux/
|3: /5 width=6 by ygt_yprs_trans, cprs_yprs/
] -L0 -T0 -T1 -T #U2 #HTU2 #HU2
lapply (cpcs_trans … HU1 … HU2) -U /2 width=3/
qed-.

fact ssta_cpcs_aux: ∀h,g,L0,T0.
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_cpr_lpr h g L1 T1) →
                    ∀L,T1,T2. h ⊢ ⦃L0, T0⦄ >[g] ⦃L, T1⦄ → h ⊢ ⦃L0, T0⦄ >[g] ⦃L, T2⦄ →
                        ⦃h, L⦄ ⊢ T1 ¡[g] → ⦃h, L⦄ ⊢ T2 ¡[g] →
                    ∀U1,l1. ⦃h, L⦄ ⊢ T1 •[g] ⦃l1, U1⦄ →
                    ∀U2,l2. ⦃h, L⦄ ⊢ T2 •[g] ⦃l2, U2⦄ →
                    L ⊢ T1 ⬌* T2 → l1 = l2 ∧ L ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L #T1 #T2 #HLT01 #HLT02 #HT1 #HT2 #U1 #l1 #HTU1 #U2 #l2 #HTU2 #H
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (ssta_cprs_lpr_aux … HLT01 HT1 … HTU1 … H1 L) -T1 // /2 width=1/ #W1 #H1 #HUW1
elim (ssta_cprs_lpr_aux … HLT02 HT2 … HTU2 … H2 L) -T2 // /2 width=1/ #W2 #H2 #HUW2 -L0 -T0
elim (ssta_mono … H1 … H2) -h -T #H1 #H2 destruct
lapply (cpcs_canc_dx … HUW1 … HUW2) -W2 /2 width=1/
qed-.

fact snv_sstas_aux: ∀h,g,L0,T0.
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                    ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                    ∀U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 → ⦃h, L1⦄ ⊢ U1 ¡[g].
#h #g #L0 #T0 #IH #L1 #T1 #HLT0 #HT1 #U1 #H
@(sstas_ind … H) -U1 // -HT1 /4 width=5 by ygt_yprs_trans, sstas_yprs/
qed-.

fact sstas_cprs_lpr_aux: ∀h,g,L0,T0.
                         (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                         (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_cpr_lpr h g L1 T1) →
                         (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_cpr_lpr h g L1 T1) →
                         ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                         ∀T2. L1 ⊢ T1 ➡* T2 → ∀U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 → ∀L2. L1 ⊢ ➡ L2 →
                         ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*[g] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #H01 #HT1 #L2 #HL12 #T2 #HT12 #U1 #H
@(sstas_ind … H) -U1 [ /3 width=3/ ]
#U1 #W1 #l1 #HTU1 #HUW1 * #U2 #HTU2 #HU12
lapply (snv_ltpr_cprs_aux … IH2 … HT1 … HT12) // #HT2
elim (snv_sstas_fwd_correct … HTU2) // #W2 #l2 #HUW2
elim (ssta_ltpr_cpcs_aux … IH2 IH1 … HUW1 … HUW2 … HU12) -IH2 -IH1 -HUW1 -HU12 //
[2: /4 width=8 by snv_sstas_aux, ygt_yprs_trans, ltpr_cprs_yprs/
|3: /3 width=7 by snv_sstas_aux, ygt_yprs_trans, cprs_yprs/
|4: /4 width=5 by ygt_yprs_trans, ltpr_cprs_yprs, sstas_yprs/
|5: /3 width=4 by ygt_yprs_trans, cprs_yprs, sstas_yprs/
] -L0 -T0 -T1 -HT2 #H #HW12 destruct /3 width=4/
qed-.

fact dxprs_ltpr_cprs_aux: ∀h,g,L0,T0.
                          (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                          (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                          (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                          ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                          ∀U1. ⦃h, L1⦄ ⊢ T1 •*➡*[g] U1 →
                          ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡* T2 →
                          ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*➡*[g] U2 & L2 ⊢ U1 ➡* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #H01 #HT1 #U1 * #W1 #HTW1 #HWU1 #L2 #HL12 #T2 #HT12
elim (sstas_ltpr_cprs_aux … IH3 IH2 IH1 … H01 … HT12 … HTW1) // -L0 -T0 -T1 #W2 #HTW2 #HW12
lapply (ltpr_cprs_conf … HL12 … HWU1) -L1 #HWU1
lapply (cpcs_canc_sn … HW12 HWU1) -W1 #H
elim (cpcs_inv_cprs … H) -H /3 width=3/
qed-.

fact ssta_dxprs_aux: ∀h,g,L0,T0.
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                     ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊢ T1 ¡[g] →
                     ∀l,U1. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l+1, U1⦄ → ∀T2. ⦃h, L1⦄ ⊢ T1 •*➡*[g] T2 →
                     ∃∃U,U2. ⦃h, L1⦄ ⊢ U1 •*[g] U & ⦃h, L1⦄ ⊢ T2 •*[g] U2 & L1 ⊢ U ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L1 #T1 #H01 #HT1 #l #U1 #HTU1 #T2 * #T #HT1T #HTT2
elim (sstas_strip … HT1T … HTU1) #HU1T destruct [ -HT1T | -L0 -T0 -T1 ]
[ elim (ssta_ltpr_cprs_aux … IH2 IH1 … HTU1 L1 … HTT2) // -L0 -T0 -T /3 width=5/
| @(ex3_2_intro …T2 HU1T) // /2 width=1/
]
qed-.
