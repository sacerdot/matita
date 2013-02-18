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

include "basic_2/unwind/sstas_ltpss_dx.ma".
include "basic_2/computation/cprs_ltpss_dx.ma".
include "basic_2/computation/dxprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Properties about dx parallel unfold **************************************)

lemma dxprs_ltpss_dx_conf: ∀h,g,L1,T,U1. ⦃h, L1⦄ ⊢ T •*➡*[g] U1 →
                           ∀L2,d,e. L1 ▶* [d, e] L2 →
                           ∃∃U2. ⦃h, L2⦄ ⊢ T •*➡*[g] U2 & L2 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T #U1 * #U #HTU #HU1 #L2 #d #e #HL12
elim (sstas_ltpss_dx_conf … HTU … HL12) -HTU #U0 #HTU0 #HU0
elim (cprs_ltpss_dx_conf … HU1 … HL12) -L1 #U2 #HU2 #HU12
elim (cprs_tpss_conf … HU2 … HU0) -U #U #HU2 #HU0
lapply (tpss_trans_eq … HU12 HU2) -U2 /3 width=3/
qed-.

lemma dxprs_tpss_conf: ∀h,g,L,T1,U1. ⦃h, L⦄ ⊢ T1 •*➡*[g] U1 →
                       ∀T2,d,e. L ⊢ T1 ▶* [d, e] T2 →
                       ∃∃U2. ⦃h, L⦄ ⊢ T2 •*➡*[g] U2 & L ⊢ U1 ▶* [d, e] U2.
#h #g #L #T1 #U1 * #W1 #HTW1 #HWU1 #T2 #d #e #HT12
elim (sstas_tpss_conf … HTW1 … HT12) -T1 #W2 #HTW2 #HW12
elim (cprs_tpss_conf … HWU1 … HW12) -W1 /3 width=3/
qed-.

lemma dxprs_ltpss_dx_tpss_conf: ∀h,g,L1,T1,U1. ⦃h, L1⦄ ⊢ T1 •*➡*[g] U1 →
                                ∀L2,d,e. L1 ▶* [d, e] L2 →
                                ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                                ∃∃U2. ⦃h, L2⦄ ⊢ T2 •*➡*[g] U2 &
                                      L2 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T1 #U1 #HTU1 #L2 #d #e #HL12 #T2 #HT12
elim (dxprs_ltpss_dx_conf … HTU1 … HL12) -L1 #U #HT1U #HU1
elim (dxprs_tpss_conf … HT1U … HT12) -T1 #U2 #HTU2 #HU2
lapply (tpss_trans_eq … HU1 HU2) -U /2 width=3/
qed-.
