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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/computation/ygt.ma".
include "basic_2/dynamic/snv_ltpss_dx.ma".
include "basic_2/dynamic/snv_sstas.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Inductive premises for the preservation results **************************)
(*
definition IH_snv_dxprs: ∀h:sh. sd h → relation2 lenv term ≝
                         λh,g,L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                         ∀L2. L1 ➡ L2 → ∀T2. ⦃h, L2⦄ ⊢ T1 •*➡*[g] T2 → ⦃h, L2⦄ ⊩ T2 :[g].
*)
definition IH_ssta_ltpr_tpr: ∀h:sh. sd h → relation2 lenv term ≝
                             λh,g,L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                             ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                             ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 →
                             ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & L1 ⊢ U1 ⬌* U2.

definition IH_snv_ltpr_tpr: ∀h:sh. sd h → relation2 lenv term ≝
                            λh,g,L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                            ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → ⦃h, L2⦄ ⊩ T2 :[g].

definition IH_snv_ssta: ∀h:sh. sd h → relation2 lenv term ≝
                        λh,g,L1,T1. ⦃h, L1⦄ ⊩ T1 :[g] →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l + 1] U1 → ⦃h, L1⦄ ⊩ U1 :[g].

fact ssta_ltpr_cpr_aux: ∀h,g,L1,T1. IH_ssta_ltpr_tpr h g L1 T1 →
                        ⦃h, L1⦄ ⊩ T1 :[g] →
                        ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 →
                        ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡ T2 →
                        ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g, l] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L1 #T1 #IH #HT1 #U1 #l #HTU1 #L2 #HL12 #T2 * #T #HT1T #HTT2
elim (IH … HTU1 … HL12 … HT1T) // -T1 #U #HTU #HU1
elim (ssta_tpss_conf … HTU … HTT2) -T #U2 #HTU2 #HU2
lapply (ltpr_cpr_trans … HL12 U U2 ?) -HL12 /2 width=3/ -HU2 #HU2
lapply (cpcs_cprs_strap1 … HU1 … HU2) -U /2 width=3/
qed-.

fact snv_ltpr_cpr_aux: ∀h,g,L1,T1. IH_snv_ltpr_tpr h g L1 T1 →
                       ⦃h, L1⦄ ⊩ T1 :[g] →
                       ∀L2. L1 ➡ L2 → ∀T2. L2 ⊢ T1 ➡ T2 → ⦃h, L2⦄ ⊩ T2 :[g].
#h #g #L1 #T1 #IH #HT1 #L2 #HL12 #T2 * #T #HT1T #HTT2
lapply (IH … HL12 … HT1T) -HL12 // -T1 #HT0
lapply (snv_tpss_conf … HT0 … HTT2) -T //
qed-.

fact snv_cprs_aux: ∀h,g,L0,T0.
                   (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                   ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                   ∀T2. L1 ⊢ T1 ➡* T2 → ⦃h, L1⦄ ⊩ T2 :[g].
#h #g #L0 #T0 #IH #L1 #T1 #HLT0 #HT1 #T2 #H
@(cprs_ind … H) -T2 // -HT1
/4 width=6 by snv_ltpr_cpr_aux, ygt_cprs_trans/
qed-.

fact ssta_cprs_aux: ∀h,g,L0,T0.
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                    ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                    ∀U1,l. ⦃h, L1⦄ ⊢ T1 •[g, l] U1 → ∀T2. L1 ⊢ T1 ➡* T2 →
                    ∃∃U2. ⦃h, L1⦄ ⊢ T2 •[g, l] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L1 #T1 #H01 #HT1 #U1 #l #HTU1 #T2 #H
@(cprs_ind … H) -T2 [ /2 width=3/ ]
#T #T2 #HT1T #HTT2 * #U #HTU #HU1 
elim (ssta_ltpr_cpr_aux … HTU … HTT2) //
[2: /3 width=7 by snv_cprs_aux, ygt_cprs_trans/
|3: /3 width=3 by ygt_cprs_trans/
] -L0 -T0 -T1 -T #U2 #HTU2 #HU2
lapply (cpcs_trans … HU1 … HU2) -U /2 width=3/
qed-.

fact ssta_cpcs_aux: ∀h,g,L0,T0.
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                    ∀L,T1,T2. h ⊢ ⦃L0, T0⦄ >[g] ⦃L, T1⦄ → h ⊢ ⦃L0, T0⦄ >[g] ⦃L, T2⦄ →
                    ⦃h, L⦄ ⊩ T1 :[g] → ⦃h, L⦄ ⊩ T2 :[g] →
                    ∀U1,l1. ⦃h, L⦄ ⊢ T1 •[g, l1] U1 →
                    ∀U2,l2. ⦃h, L⦄ ⊢ T2 •[g, l2] U2 →
                    L ⊢ T1 ⬌* T2 →
                    l1 = l2 ∧ L ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L #T1 #T2 #HLT01 #HLT02 #HT1 #HT2 #U1 #l1 #HTU1 #U2 #l2 #HTU2 #H
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (ssta_cprs_aux … HLT01 HT1 … HTU1 … H1) -T1 /2 width=1/ #W1 #H1 #HUW1
elim (ssta_cprs_aux … HLT02 HT2 … HTU2 … H2) -T2 /2 width=1/ #W2 #H2 #HUW2 -L0 -T0
elim (ssta_mono … H1 … H2) -h -T #H1 #H2 destruct
lapply (cpcs_canc_dx … HUW1 … HUW2) -W2 /2 width=1/
qed-.

fact snv_sstas_aux: ∀h,g,L0,T0.
                    (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                    ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                    ∀U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 → ⦃h, L1⦄ ⊩ U1 :[g].
#h #g #L0 #T0 #IH #L1 #T1 #HLT0 #HT1 #U1 #H
@(sstas_ind … H) -U1 // -HT1 /3 width=5 by ygt_sstas_trans/
qed-.

fact sstas_cprs_aux: ∀h,g,L0,T0.
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                     ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                     ∀T2. L1 ⊢ T1 ➡* T2 → ∀U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 →
                     ∃∃U2. ⦃h, L1⦄ ⊢ T2 •*[g] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #H01 #HT1 #T2 #HT12 #U1 #H
@(sstas_ind … H) -U1 [ /3 width=3/ ]
#U1 #W1 #l1 #HTU1 #HUW1 * #U2 #HTU2 #HU12
lapply (snv_cprs_aux … IH2 … HT1 … HT12) // #HT2
elim (snv_sstas_fwd_correct … HTU2) // #W2 #l2 #HUW2
elim (ssta_cpcs_aux … IH2 IH1 … HUW1 … HUW2 … HU12) -IH2 -IH1 -HUW1 -HU12
[2,3: /3 width=7 by snv_sstas_aux, ygt_cprs_trans/
|4,5: /3 width=3 by ygt_sstas_trans, ygt_cprs_trans/
] -L0 -T0 -T1 -HT2 #H #HW12 destruct /3 width=4/
qed-.

fact dxprs_cprs_aux: ∀h,g,L0,T0.
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                     ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                     ∀T2. L1 ⊢ T1 ➡* T2 → ∀U1. ⦃h, L1⦄ ⊢ T1 •*➡*[g] U1 →
                     ∃∃U2. ⦃h, L1⦄ ⊢ T2 •*➡*[g] U2 & L1 ⊢ U1 ➡* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #H01 #HT1 #T2 #HT12 #U1 * #W1 #HTW1 #HWU1
elim (sstas_cprs_aux … IH3 IH2 IH1 … H01 … HT12 … HTW1) // -L0 -T0 -T1 #W2 #HTW2 #HW12
lapply (cpcs_cprs_conf … HWU1 … HW12) -W1 #H
elim (cpcs_inv_cprs … H) -H /3 width=3/
qed-.

fact sstas_ltpr_aux: ∀h,g,L0,T0.
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                     (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                     ∀L1,T. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T⦄ → ⦃h, L1⦄ ⊩ T :[g] →
                     ∀L2. L1 ➡ L2 → ∀U1. ⦃h, L1⦄ ⊢ T •*[g] U1 →
                     ∃∃U2. ⦃h, L2⦄ ⊢ T •*[g] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH2 #IH1 #L1 #T #H01 #HT #L2 #HL12 #U1 #H
@(sstas_ind … H) -U1 [ /4 width=3/ ]
#W1 #U1 #l1 #HTW1 #HWU1 * #W2 #HTW2 #HW12
lapply (snv_sstas_aux … IH2 … HTW1) // -IH2 -HT #HW1

(*
elim (IH1 … HWU1 … HL12 W1) // -IH1 -HW1 -HWU1 -HL12
[2: /2 width=3 by ygt_sstas_trans/ ] #U2 
*)
(*
fact sstas_dxprs_aux: ∀h,g,L0,T0.
                      (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ssta h g L1 T1) →
                      (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_snv_ltpr_tpr h g L1 T1) →
                      (∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → IH_ssta_ltpr_tpr h g L1 T1) →
                      ∀L1,T1. h ⊢ ⦃L0, T0⦄ >[g] ⦃L1, T1⦄ → ⦃h, L1⦄ ⊩ T1 :[g] →
                      ∀U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 → ∀T2. ⦃h, L1⦄ ⊢ T1 •*➡*[g] T2 →
                      ∃∃U2. ⦃h, L1⦄ ⊢ T2 •*[g] U2 & L1 ⊢ U1 ⬌* U2.
#h #g #L0 #T0 #IH3 #IH2 #IH1 #L1 #T1 #H01 #HT1 #U1 #HTU1 #T2 * #T #HT1T #HTT2
*)