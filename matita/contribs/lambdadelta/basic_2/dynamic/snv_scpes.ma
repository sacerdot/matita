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

include "basic_2/computation/fpbs_lift.ma".
include "basic_2/computation/fpbg_fleq.ma".
include "basic_2/equivalence/scpes_cpcs.ma".
include "basic_2/equivalence/scpes_scpes.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Inductive premises for the preservation results **************************)

definition IH_snv_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                           λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                           ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ¡[h, g].

definition IH_da_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                          λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                          ∀l. ⦃G, L1⦄ ⊢ T1 ▪[h, g] l →
                          ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                          ⦃G, L2⦄ ⊢ T2 ▪[h, g] l.

definition IH_lstas_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                             λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                             ∀l1,l2. l2 ≤ l1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] l1 →
                             ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, l2] U1 →
                             ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                             ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, l2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.

definition IH_snv_lstas: ∀h:sh. sd h → relation3 genv lenv term ≝
                         λh,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] →
                         ∀l1,l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ T ▪[h, g] l1 →
                         ∀U. ⦃G, L⦄ ⊢ T •*[h, l2] U → ⦃G, L⦄ ⊢ U ¡[h, g].

(* Properties for the preservation results **********************************)

fact snv_cprs_lpr_aux: ∀h,g,G0,L0,T0.
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                       ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                       ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G0 #L0 #T0 #IH #G #L1 #T1 #HLT0 #HT1 #T2 #H
@(cprs_ind … H) -T2 /4 width=6 by fpbg_fpbs_trans, cprs_fpbs/
qed-.

fact da_cprs_lpr_aux: ∀h,g,G0,L0,T0.
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                      ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                      ∀l. ⦃G, L1⦄ ⊢ T1 ▪[h, g] l →
                      ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ▪[h, g] l.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #HLT0 #HT1 #l #Hl #T2 #H
@(cprs_ind … H) -T2 /4 width=10 by snv_cprs_lpr_aux, fpbg_fpbs_trans, cprs_fpbs/
qed-.

fact da_scpds_lpr_aux: ∀h,g,G0,L0,T0.
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                       ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                       ∀l1. ⦃G, L1⦄ ⊢ T1 ▪[h, g] l1 →
                       ∀T2,l2. ⦃G, L1⦄ ⊢ T1 •*➡*[h, g, l2] T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                       l2 ≤ l1 ∧ ⦃G, L2⦄ ⊢ T2 ▪[h, g] l1-l2.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L1 #T1 #HLT0 #HT1 #l1 #Hl1 #T2 #l2 * #T #l0 #Hl20 #H #HT1 #HT2 #L2 #HL12
lapply (da_mono … H … Hl1) -H #H destruct
lapply (lstas_da_conf … HT1 … Hl1) #Hl12
lapply (da_cprs_lpr_aux … IH2 IH1 … Hl12 … HT2 … HL12) -IH2 -IH1 -HT2 -HL12
/3 width=8 by fpbg_fpbs_trans, lstas_fpbs, conj/
qed-.

fact da_scpes_aux: ∀h,g,G0,L0,T0.
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                   ∀G,L,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T1⦄ → ⦃G, L⦄ ⊢ T1 ¡[h, g] →
                   ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T2⦄ → ⦃G, L⦄ ⊢ T2 ¡[h, g] →
                   ∀l11. ⦃G, L⦄ ⊢ T1 ▪[h, g] l11 → ∀l12. ⦃G, L⦄ ⊢ T2 ▪[h, g] l12 →
                   ∀l21,l22. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l21, l22] T2 →
                   ∧∧ l21 ≤ l11 & l22 ≤ l12 & l11 - l21 = l12 - l22.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L #T1 #HLT01 #HT1 #T2 #HLT02 #HT2 #l11 #Hl11 #l12 #Hl12 #l21 #l22 * #T #HT1 #HT2
elim (da_scpds_lpr_aux … IH3 IH2 IH1 … Hl11 … HT1 … L) -Hl11 -HT1 //
elim (da_scpds_lpr_aux … IH3 IH2 IH1 … Hl12 … HT2 … L) -Hl12 -HT2 //
/3 width=7 by da_mono, and3_intro/
qed-.

fact lstas_cprs_lpr_aux: ∀h,g,G0,L0,T0.
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                         ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                         ∀l1,l2. l2 ≤ l1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] l1 →
                         ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, l2] U1 →
                         ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                         ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, l2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #l1 #l2 #Hl21 #Hl1 #U1 #HTU1 #T2 #H
@(cprs_ind … H) -T2 [ /2 width=10 by/ ]
#T #T2 #HT1T #HTT2 #IHT1 #L2 #HL12
elim (IHT1 L1) // -IHT1 #U #HTU #HU1
elim (IH1 … Hl21 … HTU … HTT2 … HL12) -IH1 -HTU -HTT2
[2: /3 width=12 by da_cprs_lpr_aux/
|3: /3 width=10 by snv_cprs_lpr_aux/
|4: /3 width=5 by fpbg_fpbs_trans, cprs_fpbs/
] -G0 -L0 -T0 -T1 -T -l1
/4 width=5 by lpr_cpcs_conf, cpcs_trans, ex2_intro/
qed-.

fact scpds_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                        ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                        ∀U1,l. ⦃G, L1⦄ ⊢ T1 •*➡*[h, g, l] U1 →
                        ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                        ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*➡*[h, g, l] U2 & ⦃G, L2⦄ ⊢ U1 ➡* U2.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #U1 #l2 * #W1 #l1 #Hl21 #HTl1 #HTW1 #HWU1 #T2 #HT12 #L2 #HL12
elim (IH1 … H01 … HTW1 … HT12 … HL12) -IH1 // #W2 #HTW2 #HW12
lapply (IH2 … H01 … HTl1 … HT12 … HL12) -L0 -T0 // -T1
lapply (lpr_cprs_conf … HL12 … HWU1) -L1 #HWU1
lapply (cpcs_canc_sn … HW12 HWU1) -W1 #H
elim (cpcs_inv_cprs … H) -H /3 width=6 by ex4_2_intro, ex2_intro/
qed-.

fact scpes_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                        ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                        ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T2⦄ → ⦃G, L1⦄ ⊢ T2 ¡[h, g] →
                        ∀l1,l2. ⦃G, L1⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2 →
                        ∀U1. ⦃G, L1⦄ ⊢ T1 ➡ U1 → ∀U2. ⦃G, L1⦄ ⊢ T2 ➡ U2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                        ⦃G, L2⦄ ⊢ U1 •*⬌*[h, g, l1, l2] U2.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #T2 #HT02 #HT2 #l1 #l2 * #T0 #HT10 #HT20 #U1 #HTU1 #U2 #HTU2 #L2 #HL12
elim (scpds_cpr_lpr_aux … IH2 IH1 … HT10 … HTU1 … HL12) -HT10 -HTU1 // #X1 #HUX1 #H1
elim (scpds_cpr_lpr_aux … IH2 IH1 … HT20 … HTU2 … HL12) -HT20 -HTU2 // #X2 #HUX2 #H2
elim (cprs_conf … H1 … H2) -T0
/3 width=5 by scpds_div, scpds_cprs_trans/
qed-.

fact lstas_scpds_aux: ∀h,g,G0,L0,T0.
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                      (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                      ∀G,L,T. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G, L⦄ ⊢ T ¡[h, g] →
                      ∀l,l1. l1 ≤ l → ⦃G, L⦄ ⊢ T ▪[h, g] l → ∀T1. ⦃G, L⦄ ⊢ T •*[h, l1] T1 →
                      ∀T2,l2. ⦃G, L⦄ ⊢ T •*➡*[h, g, l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l2-l1, l1-l2] T2.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G #L #T #H0 #HT #l #l1 #Hl1 #HTl #T1 #HT1 #T2 #l2 * #X #l0 #Hl20 #H #HTX #HXT2
lapply (da_mono … H … HTl) -H #H destruct
lapply (lstas_da_conf … HT1 … HTl) #HTl1
lapply (lstas_da_conf … HTX … HTl) #HXl
lapply (da_cprs_lpr_aux … IH3 IH2 … HXl … HXT2 L ?)
[1,2,3: /3 width=8 by fpbg_fpbs_trans, lstas_fpbs/ ] #HTl2
elim (le_or_ge l1 l2) #Hl12 >(eq_minus_O … Hl12)
[ /5 width=3 by scpds_refl, lstas_conf_le, monotonic_le_minus_l, ex4_2_intro, ex2_intro/
| lapply (lstas_conf_le … HTX … HT1) // #HXT1 -HT1
  elim (lstas_cprs_lpr_aux … IH3 IH2 IH1 … HXl … HXT1 … HXT2 L) -IH3 -IH2 -IH1 -HXl -HXT1 -HXT2
  /3 width=8 by cpcs_scpes, fpbg_fpbs_trans, lstas_fpbs, monotonic_le_minus_l/
]
qed-.

fact scpes_le_aux: ∀h,g,G0,L0,T0.
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                   ∀G,L,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T1⦄ → ⦃G, L⦄ ⊢ T1 ¡[h, g] →
                   ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T2⦄ → ⦃G, L⦄ ⊢ T2 ¡[h, g] →
                   ∀l11. ⦃G, L⦄ ⊢ T1 ▪[h, g] l11 → ∀l12. ⦃G, L⦄ ⊢ T2 ▪[h, g] l12 →
                   ∀l21,l22,l. l21 + l ≤ l11 → l22 + l ≤ l12 →
                   ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l21, l22] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l21+l, l22+l] T2.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G #L #T1 #H01 #HT1 #T2 #H02 #HT2 #l11 #Hl11 #Hl12 #Hl12 #l21 #l22 #l #H1 #H2 * #T0 #HT10 #HT20 
elim (da_inv_sta … Hl11) #X1 #HTX1
elim (lstas_total … HTX1 (l21+l)) -X1 #X1 #HTX1
elim (da_inv_sta … Hl12) #X2 #HTX2
elim (lstas_total … HTX2 (l22+l)) -X2 #X2 #HTX2
lapply (lstas_scpds_aux … IH4 IH3 IH2 IH1 … Hl11 … HTX1 … HT10) -HT10
[1,2,3: // | >eq_minus_O [2: // ] <minus_plus_m_m_commutative #HX1 ]
lapply (lstas_scpds_aux … IH4 IH3 IH2 IH1 … Hl12 … HTX2 … HT20) -HT20
[1,2,3: // | >eq_minus_O [2: // ] <minus_plus_m_m_commutative #HX2 ]
lapply (lstas_scpes_trans … Hl11 … HTX1 … HX1) [ // ] -Hl11 -HTX1 -HX1 -H1 #H1
lapply (lstas_scpes_trans … Hl12 … HTX2 … HX2) [ // ] -Hl12 -HTX2 -HX2 -H2 #H2
lapply (scpes_canc_dx … H1 … H2) // (**) (* full auto raises NTypeChecker failure *)
qed-.

(* Advanced properties ******************************************************)

lemma snv_cast_scpes: ∀h,g,G,L,U,T. ⦃G, L⦄ ⊢ U ¡[h, g] →  ⦃G, L⦄ ⊢ T ¡[h, g] →
                      ⦃G, L⦄ ⊢ U •*⬌*[h, g, 0, 1] T → ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g].
#h #g #G #L #U #T #HU #HT * /3 width=3 by snv_cast, scpds_fwd_cprs/
qed.
