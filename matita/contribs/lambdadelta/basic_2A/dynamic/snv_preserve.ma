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

include "basic_2A/computation/fsb_aaa.ma".
include "basic_2A/dynamic/snv_da_lpr.ma".
include "basic_2A/dynamic/snv_lstas.ma".
include "basic_2A/dynamic/snv_lstas_lpr.ma".
include "basic_2A/dynamic/snv_lpr.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Main preservation properties *********************************************)

lemma snv_preserve: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] →
                    ∧∧ IH_da_cpr_lpr h g G L T
                     & IH_snv_cpr_lpr h g G L T
                     & IH_snv_lstas h g G L T
                     & IH_lstas_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_fwd_aaa … HT) -HT
#A #HT @(aaa_ind_fpbg h g … HT) -G -L -T -A
#G #L #T #A #_ #IH -A @and4_intro
[ letin aux ≝ da_cpr_lpr_aux | letin aux ≝ snv_cpr_lpr_aux
| letin aux ≝ snv_lstas_aux | letin aux ≝ lstas_cpr_lpr_aux
]
@(aux … G L T) // #G0 #L0 #T0 #H elim (IH … H) -IH -H //
qed-.

theorem da_cpr_lpr: ∀h,g,G,L,T. IH_da_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_cpr_lpr: ∀h,g,G,L,T. IH_snv_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_lstas: ∀h,g,G,L,T. IH_snv_lstas h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=5 by/
qed-.

theorem lstas_cpr_lpr: ∀h,g,G,L,T. IH_lstas_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=3 by/
qed-.

(* Advanced preservation properties *****************************************)

lemma snv_cprs_lpr: ∀h,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                    ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G #L1 #T1 #HT1 #T2 #H
@(cprs_ind … H) -T2 /3 width=5 by snv_cpr_lpr/
qed-.

lemma da_cprs_lpr: ∀h,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                   ∀d. ⦃G, L1⦄ ⊢ T1 ▪[h, g] d →
                   ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ▪[h, g] d.
#h #g #G #L1 #T1 #HT1 #d #Hd #T2 #H
@(cprs_ind … H) -T2 /3 width=6 by snv_cprs_lpr, da_cpr_lpr/
qed-.

lemma lstas_cprs_lpr: ∀h,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                      ∀d1,d2. d2 ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] d1 →
                      ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d2] U1 →
                      ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                      ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, d2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #g #G #L1 #T1 #HT1 #d1 #d2 #Hd21 #Hd1 #U1 #HTU1 #T2 #H
@(cprs_ind … H) -T2 [ /2 width=10 by lstas_cpr_lpr/ ]
#T #T2 #HT1T #HTT2 #IHT1 #L2 #HL12
elim (IHT1 L1) // -IHT1 #U #HTU #HU1
elim (lstas_cpr_lpr … g … Hd21 … HTU … HTT2 … HL12) -HTU -HTT2
[2,3: /2 width=7 by snv_cprs_lpr, da_cprs_lpr/ ] -T1 -T -d1
/4 width=5 by lpr_cpcs_conf, cpcs_trans, ex2_intro/
qed-.

lemma lstas_cpcs_lpr: ∀h,g,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, g] →
                      ∀d,d1. d ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, g] d1 → ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d] U1 →
                      ∀T2. ⦃G, L1⦄ ⊢ T2 ¡[h, g] →
                      ∀d2. d ≤ d2 → ⦃G, L1⦄ ⊢ T2 ▪[h, g] d2 → ∀U2. ⦃G, L1⦄ ⊢ T2 •*[h, d] U2 →
                      ⦃G, L1⦄ ⊢ T1 ⬌* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #g #G #L1 #T1 #HT1 #d #d1 #Hd1 #HTd1 #U1 #HTU1 #T2 #HT2 #d2 #Hd2 #HTd2 #U2 #HTU2 #H #L2 #HL12
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (lstas_cprs_lpr … HT1 … Hd1 HTd1 … HTU1 … H1 … HL12) -T1 #W1 #H1 #HUW1
elim (lstas_cprs_lpr … HT2 … Hd2 HTd2 … HTU2 … H2 … HL12) -T2 #W2 #H2 #HUW2
lapply (lstas_mono … H1 … H2) -h -T -d #H destruct /2 width=3 by cpcs_canc_dx/
qed-.
