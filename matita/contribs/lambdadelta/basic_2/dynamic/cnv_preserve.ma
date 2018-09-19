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

include "basic_2/dynamic/cnv_cpms_conf.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Main preservation properties *********************************************)
(*
(* Basic_2A1: uses: snv_preserve *)
lemma cnv_preserve (a) (h): ∀G,L,T. ⦃G,L⦄ ⊢ T ![a,h] →
                            ∧∧ IH_cnv_cpms_conf_lpr a h G L T
                             & IH_cnv_cpm_trans_lpr a h G L T.
#a #h #G #L #T #HT
elim (tdpos_total h … T) #o
lapply (cnv_fwd_fsb … o … HT) -HT #H
@(fsb_ind_fpbg … H) -G -L -T #G #L #T #_ #IH #Ho
@conj [ letin aux ≝ cnv_cpms_conf_lpr_aux | letin aux ≝ cnv_cpm_trans_lpr_aux ]
@(aux … o … G L T) // #G0 #L0 #T0 #H
elim (IH … H) -IH -H //


lemma snv_preserve: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, o] →
                    ∧∧ IH_da_cpr_lpr h o G L T
                     & IH_snv_cpr_lpr h o G L T
                     & IH_snv_lstas h o G L T
                     & IH_lstas_cpr_lpr h o G L T.
#h #o #G #L #T #HT elim (snv_fwd_aaa … HT) -HT
#A #HT @(aaa_ind_fpbg h o … HT) -G -L -T -A
#G #L #T #A #_ #IH -A @and4_intro
[ letin aux ≝ da_cpr_lpr_aux | letin aux ≝ snv_cpr_lpr_aux
| letin aux ≝ snv_lstas_aux | letin aux ≝ lstas_cpr_lpr_aux
]
@(aux … G L T) // #G0 #L0 #T0 #H elim (IH … H) -IH -H //
qed-.

theorem da_cpr_lpr: ∀h,o,G,L,T. IH_da_cpr_lpr h o G L T.
#h #o #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_cpr_lpr: ∀h,o,G,L,T. IH_snv_cpr_lpr h o G L T.
#h #o #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_lstas: ∀h,o,G,L,T. IH_snv_lstas h o G L T.
#h #o #G #L #T #HT elim (snv_preserve … HT) /2 width=5 by/
qed-.

theorem lstas_cpr_lpr: ∀h,o,G,L,T. IH_lstas_cpr_lpr h o G L T.
#h #o #G #L #T #HT elim (snv_preserve … HT) /2 width=3 by/
qed-.

(* Advanced preservation properties *****************************************)

lemma snv_cprs_lpr: ∀h,o,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, o] →
                    ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ¡[h, o].
#h #o #G #L1 #T1 #HT1 #T2 #H
@(cprs_ind … H) -T2 /3 width=5 by snv_cpr_lpr/
qed-.

lemma da_cprs_lpr: ∀h,o,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, o] →
                   ∀d. ⦃G, L1⦄ ⊢ T1 ▪[h, o] d →
                   ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ T2 ▪[h, o] d.
#h #o #G #L1 #T1 #HT1 #d #Hd #T2 #H
@(cprs_ind … H) -T2 /3 width=6 by snv_cprs_lpr, da_cpr_lpr/
qed-.

lemma lstas_cprs_lpr: ∀h,o,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, o] →
                      ∀d1,d2. d2 ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, o] d1 →
                      ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d2] U1 →
                      ∀T2. ⦃G, L1⦄ ⊢ T1 ➡* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 →
                      ∃∃U2. ⦃G, L2⦄ ⊢ T2 •*[h, d2] U2 & ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #o #G #L1 #T1 #HT1 #d1 #d2 #Hd21 #Hd1 #U1 #HTU1 #T2 #H
@(cprs_ind … H) -T2 [ /2 width=10 by lstas_cpr_lpr/ ]
#T #T2 #HT1T #HTT2 #IHT1 #L2 #HL12
elim (IHT1 L1) // -IHT1 #U #HTU #HU1
elim (lstas_cpr_lpr … o … Hd21 … HTU … HTT2 … HL12) -HTU -HTT2
[2,3: /2 width=7 by snv_cprs_lpr, da_cprs_lpr/ ] -T1 -T -d1
/4 width=5 by lpr_cpcs_conf, cpcs_trans, ex2_intro/
qed-.

lemma lstas_cpcs_lpr: ∀h,o,G,L1,T1. ⦃G, L1⦄ ⊢ T1 ¡[h, o] →
                      ∀d,d1. d ≤ d1 → ⦃G, L1⦄ ⊢ T1 ▪[h, o] d1 → ∀U1. ⦃G, L1⦄ ⊢ T1 •*[h, d] U1 →
                      ∀T2. ⦃G, L1⦄ ⊢ T2 ¡[h, o] →
                      ∀d2. d ≤ d2 → ⦃G, L1⦄ ⊢ T2 ▪[h, o] d2 → ∀U2. ⦃G, L1⦄ ⊢ T2 •*[h, d] U2 →
                      ⦃G, L1⦄ ⊢ T1 ⬌* T2 → ∀L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L2⦄ ⊢ U1 ⬌* U2.
#h #o #G #L1 #T1 #HT1 #d #d1 #Hd1 #HTd1 #U1 #HTU1 #T2 #HT2 #d2 #Hd2 #HTd2 #U2 #HTU2 #H #L2 #HL12
elim (cpcs_inv_cprs … H) -H #T #H1 #H2
elim (lstas_cprs_lpr … HT1 … Hd1 HTd1 … HTU1 … H1 … HL12) -T1 #W1 #H1 #HUW1
elim (lstas_cprs_lpr … HT2 … Hd2 HTd2 … HTU2 … H2 … HL12) -T2 #W2 #H2 #HUW2
lapply (lstas_mono … H1 … H2) -h -T -d #H destruct /2 width=3 by cpcs_canc_dx/
qed-.
*)
