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

include "basic_2/substitution/lpss_lpss.ma".
include "basic_2/reduction/lpr_lpss.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties on parallel substitution for terms ****************************)

(* Basic_1: was: pr3_subst1 *)
lemma cprs_cpss_conf: ∀L,T0,T1. L ⊢ T0 ➡* T1 → ∀T2. L ⊢ T0 ▶* T2 →
                      ∃∃T. L ⊢ T1 ▶* T & L ⊢ T2 ➡* T.
#L @TC_strip1 /2 width=3 by cpr_cpss_conf/ qed-. (**) (* auto /3 width=3/ fails because a δ-expansion gets in the way *)

(* Properties on sn parallel substitution for local environments ************)

lemma cprs_lpss_conf_dx: ∀L0,T0,T1. L0 ⊢ T0 ➡* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L1 ⊢ T1 ▶* T & L1 ⊢ T0 ➡* T.
#L0 #T0 #T1 #H elim H -T1
[ #T1 #HT01 #L1 #HL01
  elim (cpr_lpss_conf_dx … HT01 … HL01) -L0 /3 width=3/
| #T #T1 #_ #HT1 #IHT0 #L1 #HL01
  elim (IHT0 … HL01) #T2 #HT2 #HT02
  elim (cpr_lpss_conf_dx … HT1 … HL01) -L0 #T3 #HT13 #HT3
  elim (cpr_cpss_conf … HT3 … HT2) -T #T #HT3 #HT2
  lapply (cpss_trans … HT13 … HT3) -T3
  lapply (cprs_strap1 … HT02 … HT2) -T2 /2 width=3/
]
qed-.

lemma cprs_lpss_conf_sn: ∀L0,T0,T1. L0 ⊢ T0 ➡* T1 → ∀L1. L0 ⊢ ▶* L1 →
                         ∃∃T. L0 ⊢ T1 ▶* T & L1 ⊢ T0 ➡* T.
#L0 #T0 #T1 #HT01 #L1 #HL01
elim (cprs_lpss_conf_dx … HT01 … HL01) -HT01 #T #HT1
lapply (lpss_cpss_trans … HL01 … HT1) -HT1 /2 width=3/
qed-.

lemma cprs_cpss_lpss_conf_sn: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 →
                              ∀T2. L1 ⊢ T1 ▶* T2 → ∀L2. L1 ⊢ ▶* L2 →
                              ∃∃U2. L2 ⊢ T2 ➡* U2 & L1 ⊢ U1 ▶* U2.
#L1 #T1 #U1 #HTU1 #T2 #HT12 #L2 #HL12
elim (cprs_cpss_conf … HTU1 … HT12) -T1 #U #HU1 #HT2U
elim (cprs_lpss_conf_sn … HT2U … HL12) -HT2U -HL12 #U2 #HU2 #HTU2
lapply (cpss_trans … HU1 … HU2) -U /2 width=3/
qed-.

lemma cprs_cpss_lpss_conf_dx: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 →
                              ∀T2. L1 ⊢ T1 ▶* T2 → ∀L2. L1 ⊢ ▶* L2 →
                              ∃∃U2. L2 ⊢ T2 ➡* U2 & L2 ⊢ U1 ▶* U2.
#L1 #T1 #U1 #HTU1 #T2 #HT12 #L2 #HL12
elim (cprs_lpss_conf_dx … HTU1 … HL12) -HTU1 #U2 #HU12 #HT1U2
elim (lpss_cpss_conf_dx … HT12 … HL12) -L1 #T #HT1 #HT2
elim (cprs_cpss_conf … HT1U2 … HT1) -T1 #U #HU2 #HTU
lapply (cpss_trans … HU12 … HU2) -U2
lapply (cpss_cprs_trans … HT2 … HTU) -T /2 width=3/
qed-.


lemma cprs_cpss2_lpss_conf_sn: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 → ∀T2. L1 ⊢ T1 ▶* T2 →
                               ∀U2. L1 ⊢ U1 ▶* U2 → ∀L2. L1 ⊢ ▶* L2 →
                               ∃∃U. L2 ⊢ T2 ➡* U & L1 ⊢ U2 ▶* U.
#L1 #T1 #U1 #HTU1 #T2 #HT12 #U2 #HU12 #L2 #HL12
elim (cprs_cpss_lpss_conf_sn … HTU1 … HT12 … HL12) -T1 #T1 #HT21 #HUT1
elim (cpss_conf … HU12 … HUT1) -U1 #U1 #HU21 #HTU1
elim (lpss_cpss_conf_sn … HTU1 … HL12) -HTU1 -HL12 #U2 #HT1U2 #HU12
lapply (cpss_trans … HU21 … HU12) -U1
lapply (cprs_cpss_trans … HT21 … HT1U2) -T1 /2 width=3/
qed-.

lemma cprs_cpss2_lpss_conf_dx: ∀L1,T1,U1. L1 ⊢ T1 ➡* U1 → ∀T2. L1 ⊢ T1 ▶* T2 →
                               ∀U2. L1 ⊢ U1 ▶* U2 → ∀L2. L1 ⊢ ▶* L2 →
                               ∃∃U. L2 ⊢ T2 ➡* U & L2 ⊢ U2 ▶* U.
#L1 #T1 #U1 #HTU1 #T2 #HT12 #U2 #HU12 #L2 #HL12
elim (cprs_cpss_lpss_conf_dx … HTU1 … HT12 … HL12) -T1 #T1 #HT21 #HUT1
elim (lpss_cpss_conf_dx … HU12 … HL12) -L1 #U #HU1 #HU2
elim (cpss_conf … HU1 … HUT1) -U1 #U1 #HU1 #HTU1
lapply (cpss_trans … HU2 … HU1) -U
lapply (cprs_cpss_trans … HT21 … HTU1) -T1 /2 width=3/
qed-.
