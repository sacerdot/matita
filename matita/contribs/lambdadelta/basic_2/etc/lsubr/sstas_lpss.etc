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

include "basic_2/static/ssta_lpss.ma".
include "basic_2/unfold/sstas.ma".

(* ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *********************)

(* Properties about sn parallel substitution for local environments *********)

lemma sstas_cpss_lpss_conf: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*[g] U1 →
                            ∀T2. L1 ⊢ T1 ▶* T2 → ∀L2. L1 ⊢ ▶* L2 →
                            ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*[g] U2 & L1 ⊢ U1 ▶* U2.
#h #g #L1 #T1 #U1 #H @(sstas_ind_dx … H) -T1 /2 width=3/
#T0 #U0 #l0 #HTU0 #_ #IHU01 #T #HT0 #L2 #HL12
elim (ssta_cpss_lpss_conf … HTU0 … HT0 … HL12) -HTU0 -HT0 #U #HTU #HU0
elim (IHU01 … HU0 … HL12) -IHU01 -U0 -HL12 /3 width=4/
qed-.

lemma sstas_cpss_conf: ∀h,g,L,T1,U1. ⦃h, L⦄ ⊢ T1 •*[g] U1 →
                       ∀T2. L ⊢ T1 ▶* T2 →
                       ∃∃U2. ⦃h, L⦄ ⊢ T2 •*[g] U2 & L ⊢ U1 ▶* U2.
/2 width=3 by sstas_cpss_lpss_conf/ qed-.

lemma sstas_lpss_conf: ∀h,g,L1,T,U1. ⦃h, L1⦄ ⊢ T •*[g] U1 →
                       ∀L2. L1 ⊢ ▶* L2 →
                       ∃∃U2. ⦃h, L2⦄ ⊢ T •*[g] U2 & L1 ⊢ U1 ▶* U2.
/2 width=3 by sstas_cpss_lpss_conf/ qed-.
