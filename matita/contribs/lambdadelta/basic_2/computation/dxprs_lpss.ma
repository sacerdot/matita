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

include "basic_2/unfold/sstas_lpss.ma".
include "basic_2/computation/cprs_lpss.ma".
include "basic_2/computation/dxprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Properties about sn parallel substitution for local environments *********)

lemma dxprs_lpss_conf: ∀h,g,L1,T,U1. ⦃h, L1⦄ ⊢ T •*➡*[g] U1 → ∀L2. L1 ⊢ ▶* L2 →
                       ∃∃U2. ⦃h, L2⦄ ⊢ T •*➡*[g] U2 & L1 ⊢ U1 ▶* U2.
#h #g #L1 #T #U1 * #U #HTU #HU1 #L2 #HL12
elim (sstas_lpss_conf … HTU … HL12) -HTU #U0 #HTU0 #HU0
elim (cprs_cpss_conf … HU1 … HU0) -U #U #HU1 #HU0
elim (cprs_lpss_conf_sn … HU0 … HL12) -HU0 -HL12 #U2 #HU2 #HU02
lapply (cpss_trans … HU1 … HU2) -U /3 width=3/
qed-.

lemma dxprs_cpss_conf: ∀h,g,L,T1,U1. ⦃h, L⦄ ⊢ T1 •*➡*[g] U1 → ∀T2. L ⊢ T1 ▶* T2 →
                       ∃∃U2. ⦃h, L⦄ ⊢ T2 •*➡*[g] U2 & L ⊢ U1 ▶* U2.
#h #g #L #T1 #U1 * #W1 #HTW1 #HWU1 #T2 #HT12
elim (sstas_cpss_conf … HTW1 … HT12) -T1 #W2 #HTW2 #HW12
elim (cprs_cpss_conf … HWU1 … HW12) -W1 /3 width=3/
qed-.

lemma dxprs_cpss_lpss_conf: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*➡*[g] U1 →
                            ∀T2. L1 ⊢ T1 ▶* T2 → ∀L2. L1 ⊢ ▶* L2 →
                            ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*➡*[g] U2 & L1 ⊢ U1 ▶* U2.
#h #g #L1 #T1 #U1 #HTU1 #T2 #HT12 #L2 #HL12
elim (dxprs_cpss_conf … HTU1 … HT12) -T1 #U2 #HTU2 #HU12
elim (dxprs_lpss_conf … HTU2 … HL12) -HTU2 -HL12 #U #HT2U #HU2
lapply (cpss_trans … HU12 … HU2) -U2 /2 width=3/
qed-.
