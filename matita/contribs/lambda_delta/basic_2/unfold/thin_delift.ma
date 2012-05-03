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

include "basic_2/unfold/delift_tpss.ma".
include "basic_2/unfold/delift_ltpss.ma".
include "basic_2/unfold/thin.ma".

(* DELIFT ON LOCAL ENVIRONMENTS *********************************************)

(* Properties on inverse term relocation ************************************)

lemma thin_delift1: ∀L1,L2,d,e. L1 [d, e] ≡ L2 → ∀V1,V2. L1 ⊢ V1 [d, e] ≡ V2 →
                    ∀I. L1.ⓑ{I}V1 [d + 1, e] ≡ L2.ⓑ{I}V2.
#L1 #L2 #d #e * #L #HL1 #HL2 #V1 #V2 * #V #HV1 #HV2 #I
elim (ltpss_tpss_conf … HV1 … HL1) -HV1 #V0 #HV10 #HV0
elim (tpss_inv_lift1_be … HV0 … HL2 … HV2 ? ?) -HV0 // <minus_n_n #X #H1 #H2
lapply (tpss_inv_refl_O2 … H1) -H1 #H destruct
lapply (lift_mono … H2 … HV2) -H2 #H destruct /3 width=5/
qed.

lemma thin_delift_tpss_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶* U2 →
                                ∀T1,dd,ee. L ⊢ U1 [dd, ee] ≡ T1 →
                                ∀K. L [dd, ee] ≡ K → d ≤ dd → dd + ee ≤ d + e →
                                ∃∃T2. K ⊢ T1 [d, e - ee] ▶* T2 &
                                      L ⊢ U2 [dd, ee] ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee #HUT1 #K * #Y #HLY #HYK #Hdd #Hddee
lapply (delift_ltpss_conf_eq … HUT1 … HLY) -HUT1 #HUT1
elim (ltpss_tpss_conf … HU12 … HLY) -HU12 #U #HU1 #HU2
elim (delift_tpss_conf_be … HU1 … HUT1 … HYK ? ?) -HU1 -HUT1 // -Hdd -Hddee #T #HT1 #HUT
lapply (tpss_delift_trans_eq … HU2 … HUT) -U #HU2T
lapply (ltpss_delift_trans_eq … HLY … HU2T) -Y /2 width=3/
qed.

lemma thin_delift_tps_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶ U2 →
                               ∀T1,dd,ee. L ⊢ U1 [dd, ee] ≡ T1 →
                               ∀K. L [dd, ee] ≡ K → d ≤ dd → dd + ee ≤ d + e →
                               ∃∃T2. K ⊢ T1 [d, e - ee] ▶* T2 &
                                     L ⊢ U2 [dd, ee] ≡ T2.
/3 width=3/ qed.
