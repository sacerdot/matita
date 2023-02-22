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

include "basic_2A/computation/fpbg_fpbs.ma".
include "basic_2A/equivalence/scpes_cpcs.ma".
include "basic_2A/equivalence/scpes_scpes.ma".
include "basic_2A/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Inductive premises for the preservation results **************************)

definition IH_snv_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                           λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                           ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ¡[h, g].

definition IH_da_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                          λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                          ∀d. ⦃G, L1⦄ ⊢ T1 ▪[h, g] d →
                          ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                          ⦃G, L2⦄ ⊢ T2 ▪[h, g] d.

definition IH_lstas_cpr_lpr: ∀h:sh. sd h → relation3 genv lenv term ≝
                             λh,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                             ∀d1,d2. d2 ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] d1 →
                             ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d2] U1 →
                             ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                             ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, d2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.

definition IH_snv_lstas: ∀h:sh. sd h → relation3 genv lenv term ≝
                         λh,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] →
                         ∀d1,d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ T ▪[h, g] d1 →
                         ∀U. ⦃G, L⦄ ⊢ T •*[h, d2] U → ⦃G, L⦄ ⊢ U ¡[h, g].

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
                      ∀d. ⦃G, L1⦄ ⊢ T1 ▪[h, g] d →
                      ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ▪[h, g] d.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #HLT0 #HT1 #d #Hd #T2 #H
@(cprs_ind … H) -T2 /4 width=10 by snv_cprs_lpr_aux, fpbg_fpbs_trans, cprs_fpbs/
qed-.

fact da_scpds_lpr_aux: ∀h,g,G0,L0,T0.
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                       (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                       ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                       ∀d1. ⦃G, L1⦄ ⊢ T1 ▪[h, g] d1 →
                       ∀T2,d2. ⦃G, L1⦄ ⊢ T1 •*➡*[h, g, d2] T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                       d2 ≤ d1 ∧ ⦃G, L2⦄ ⊢ T2 ▪[h, g] d1-d2.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L1 #T1 #HLT0 #HT1 #d1 #Hd1 #T2 #d2 * #T #d0 #Hd20 #H #HT1 #HT2 #L2 #HL12
lapply (da_mono … H … Hd1) -H #H destruct
lapply (lstas_da_conf … HT1 … Hd1) #Hd12
lapply (da_cprs_lpr_aux … IH2 IH1 … Hd12 … HT2 … HL12) -IH2 -IH1 -HT2 -HL12
/3 width=8 by fpbg_fpbs_trans, lstas_fpbs, conj/
qed-.

fact da_scpes_aux: ∀h,g,G0,L0,T0.
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                   ∀G,L,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T1⦄ → ⦃G, L⦄ ⊢ T1 ¡[h, g] →
                   ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T2⦄ → ⦃G, L⦄ ⊢ T2 ¡[h, g] →
                   ∀d11. ⦃G, L⦄ ⊢ T1 ▪[h, g] d11 → ∀d12. ⦃G, L⦄ ⊢ T2 ▪[h, g] d12 →
                   ∀d21,d22. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d21, d22] T2 →
                   ∧∧ d21 ≤ d11 & d22 ≤ d12 & d11 - d21 = d12 - d22.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L #T1 #HLT01 #HT1 #T2 #HLT02 #HT2 #d11 #Hd11 #d12 #Hd12 #d21 #d22 * #T #HT1 #HT2
elim (da_scpds_lpr_aux … IH3 IH2 IH1 … Hd11 … HT1 … L) -Hd11 -HT1 //
elim (da_scpds_lpr_aux … IH3 IH2 IH1 … Hd12 … HT2 … L) -Hd12 -HT2 //
/3 width=7 by da_mono, and3_intro/
qed-.

fact lstas_cprs_lpr_aux: ∀h,g,G0,L0,T0.
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                         (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                         ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                         ∀d1,d2. d2 ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] d1 →
                         ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d2] U1 →
                         ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                         ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, d2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #d1 #d2 #Hd21 #Hd1 #U1 #HTU1 #T2 #H
@(cprs_ind … H) -T2 [ /2 width=10 by/ ]
#T #T2 #HT1T #HTT2 #IHT1 #L2 #HL12
elim (IHT1 L1) // -IHT1 #U #HTU #HU1
elim (IH1 … Hd21 … HTU … HTT2 … HL12) -IH1 -HTU -HTT2
[2: /3 width=12 by da_cprs_lpr_aux/
|3: /3 width=10 by snv_cprs_lpr_aux/
|4: /3 width=5 by fpbg_fpbs_trans, cprs_fpbs/
] -G0 -L0 -T0 -T1 -T -d1
/4 width=5 by lpr_cpcs_conf, cpcs_trans, ex2_intro/
qed-.

fact scpds_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                        ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                        ∀U1,d. ⦃G, L1⦄ ⊢ T1 •*➡*[h, g, d] U1 →
                        ∀T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                        ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*➡*[h, g, d] U2 & ⦃G, L2⦄ ⊢ U1 ➡* U2.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #U1 #d2 * #W1 #d1 #Hd21 #HTd1 #HTW1 #HWU1 #T2 #HT12 #L2 #HL12
elim (IH1 … H01 … HTW1 … HT12 … HL12) -IH1 // #W2 #HTW2 #HW12
lapply (IH2 … H01 … HTd1 … HT12 … HL12) -L0 -T0 // -T1
lapply (lpr_cprs_conf … HL12 … HWU1) -L1 #HWU1
lapply (cpcs_canc_sn … HW12 HWU1) -W1 #H
elim (cpcs_inv_cprs … H) -H /3 width=6 by ex4_2_intro, ex2_intro/
qed-.

fact scpes_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                        (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                        ∀G,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T1⦄ → ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                        ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L1, T2⦄ → ⦃G, L1⦄ ⊢ T2 ¡[h, g] →
                        ∀d1,d2. ⦃G, L1⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2 →
                        ∀U1. ⦃G, L1⦄ ⊢ T1 ➡ U1 → ∀U2. ⦃G, L1⦄ ⊢ T2 ➡ U2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                        ⦃G, L2⦄ ⊢ U1 •*⬌*[h, g, d1, d2] U2.
#h #g #G0 #L0 #T0 #IH2 #IH1 #G #L1 #T1 #H01 #HT1 #T2 #HT02 #HT2 #d1 #d2 * #T0 #HT10 #HT20 #U1 #HTU1 #U2 #HTU2 #L2 #HL12
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
                      ∀d,d1. d1 ≤ d → ⦃G, L⦄ ⊢ T ▪[h, g] d → ∀T1. ⦃G, L⦄ ⊢ T •*[h, d1] T1 →
                      ∀T2,d2. ⦃G, L⦄ ⊢ T •*➡*[h, g, d2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d2-d1, d1-d2] T2.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G #L #T #H0 #HT #d #d1 #Hd1 #HTd #T1 #HT1 #T2 #d2 * #X #d0 #Hd20 #H #HTX #HXT2
lapply (da_mono … H … HTd) -H #H destruct
lapply (lstas_da_conf … HT1 … HTd) #HTd1
lapply (lstas_da_conf … HTX … HTd) #HXd
lapply (da_cprs_lpr_aux … IH3 IH2 … HXd … HXT2 L ?)
[1,2,3: /3 width=8 by fpbg_fpbs_trans, lstas_fpbs/ ] #HTd2
elim (le_or_ge d1 d2) #Hd12 >(eq_minus_O … Hd12)
[ elim (da_lstas … HTd2 0) #X2 #HTX2 #_ -IH4 -IH3 -IH2 -IH1 -H0 -HT -HTd -HXd
  /5 width=6 by lstas_scpds, scpds_div, cprs_strap1, lstas_cpr, lstas_conf_le, monotonic_le_minus_l, ex4_2_intro/
| elim (da_lstas … HTd1 0) #X1 #HTX1 #_
  lapply (lstas_conf_le … HTX … HT1) // #HXT1 -HT1
  elim (lstas_cprs_lpr_aux … IH3 IH2 IH1 … HXd … HXT1 … HXT2 L) -IH3 -IH2 -IH1 -HXd -HXT1 -HXT2
  /4 width=8 by cpcs_scpes, cpcs_cpr_conf, fpbg_fpbs_trans, lstas_fpbs, lstas_cpr, monotonic_le_minus_l/
]
qed-.

fact scpes_le_aux: ∀h,g,G0,L0,T0.
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                   (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_lstas_cpr_lpr h g G1 L1 T1) →
                   ∀G,L,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T1⦄ → ⦃G, L⦄ ⊢ T1 ¡[h, g] →
                   ∀T2. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G, L, T2⦄ → ⦃G, L⦄ ⊢ T2 ¡[h, g] →
                   ∀d11. ⦃G, L⦄ ⊢ T1 ▪[h, g] d11 → ∀d12. ⦃G, L⦄ ⊢ T2 ▪[h, g] d12 →
                   ∀d21,d22,d. d21 + d ≤ d11 → d22 + d ≤ d12 →
                   ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d21, d22] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d21+d, d22+d] T2.
#h #g #G0 #L0 #T0 #IH4 #IH3 #IH2 #IH1 #G #L #T1 #H01 #HT1 #T2 #H02 #HT2 #d11 #Hd11 #Hd12 #Hd12 #d21 #d22 #d #H1 #H2 * #T0 #HT10 #HT20
elim (da_lstas … Hd11 (d21+d)) #X1 #HTX1 #_
elim (da_lstas … Hd12 (d22+d)) #X2 #HTX2 #_
lapply (lstas_scpds_aux … IH4 IH3 IH2 IH1 … Hd11 … HTX1 … HT10) -HT10
[1,2,3: // | >eq_minus_O [2: // ] <minus_plus_m_m_commutative #HX1 ]
lapply (lstas_scpds_aux … IH4 IH3 IH2 IH1 … Hd12 … HTX2 … HT20) -HT20
[1,2,3: // | >eq_minus_O [2: // ] <minus_plus_m_m_commutative #HX2 ]
lapply (lstas_scpes_trans … Hd11 … HTX1 … HX1) [ // ] -Hd11 -HTX1 -HX1 -H1 #H1
lapply (lstas_scpes_trans … Hd12 … HTX2 … HX2) [ // ] -Hd12 -HTX2 -HX2 -H2 #H2
/2 width=4 by scpes_canc_dx/ (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

lemma snv_cast_scpes: ∀h,g,G,L,U,T. ⦃G, L⦄ ⊢ U ¡[h, g] →  ⦃G, L⦄ ⊢ T ¡[h, g] →
                      ⦃G, L⦄ ⊢ U •*⬌*[h, g, 0, 1] T → ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g].
#h #g #G #L #U #T #HU #HT * /2 width=3 by snv_cast/
qed.
