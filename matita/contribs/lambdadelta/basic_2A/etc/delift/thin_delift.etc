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

(* BASIC DELIFT ON LOCAL ENVIRONMENTS ***************************************)

(* Inversion lemmas on inverse basic term relocation ************************)

lemma thin_inv_delift1: ∀I,K1,V1,L2,d,e. ▼*[d, e] K1. ⓑ{I} V1 ≡ L2 → 0 < d →
                        ∃∃K2,V2. ▼*[d - 1, e] K1 ≡ K2 &
                                 K1 ⊢ ▼*[d - 1, e] V1 ≡ V2 &
                                 L2 = K2. ⓑ{I} V2.
#I #K1 #V1 #L2 #d #e * #X #HK1 #HL2 #e
elim (ltpss_sn_inv_tpss11 … HK1 ?) -HK1 // #K #V #HK1 #HV1 #H destruct
elim (ldrop_inv_skip1 … HL2 ?) -HL2 // #K2 #V2 #HK2 #HV2 #H destruct /3 width=5/
qed-.

(* Properties on inverse basic term relocation ******************************)

lemma thin_delift: ∀L1,L2,d,e. ▼*[d, e] L1 ≡ L2 → ∀V1,V2. L1 ⊢ ▼*[d, e] V1 ≡ V2 →
                   ∀I. ▼*[d + 1, e] L1.ⓑ{I}V1 ≡ L2.ⓑ{I}V2.
#L1 #L2 #d #e * #L #HL1 #HL2 #V1 #V2 * #V #HV1 #HV2 #I
elim (ltpss_sn_tpss_conf … HV1 … HL1) -HV1 #V0 #HV10 #HV0
lapply (tpss_inv_lift1_eq … HV0 … HV2) -HV0 #H destruct
lapply (ltpss_sn_tpss_trans_eq … HV10 … HL1) -HV10 /3 width=5/
qed.

lemma thin_delift_tpss_conf_le: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                                ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                                ∀K. ▼*[dd, ee] L ≡ K → d + e ≤ dd →
                                ∃∃T2. K ⊢ T1 ▶* [d, e] T2 &
                                      L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee #HUT1 #K * #Y #HLY #HYK #Hdedd
lapply (delift_ltpss_sn_conf_eq … HUT1 … HLY) -HUT1 #HUT1
elim (ltpss_sn_tpss_conf … HU12 … HLY) -HU12 #U #HU1 #HU2
elim (delift_tpss_conf_le … HU1 … HUT1 … HYK ?) -HU1 -HUT1 -HYK // -Hdedd #T #HT1 #HUT
lapply (ltpss_sn_delift_trans_eq … HLY … HUT) -HLY -HUT #HUT
lapply (tpss_delift_trans_eq … HU2 … HUT) -U /2 width=3/
qed.

lemma thin_delift_tps_conf_le: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                               ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                               ∀K. ▼*[dd, ee] L ≡ K → d + e ≤ dd →
                               ∃∃T2. K ⊢ T1 ▶* [d, e] T2 &
                                     L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=3/ qed.

lemma thin_delift_tpss_conf_le_up: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                                   ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                                   ∀K. ▼*[dd, ee] L ≡ K →
                                   d ≤ dd → dd ≤ d + e → d + e ≤ dd + ee →
                                   ∃∃T2. K ⊢ T1 ▶* [d, dd - d] T2 &
                                         L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee #HUT1 #K * #Y #HLY #HYK #Hdd #Hdde #Hddee
lapply (delift_ltpss_sn_conf_eq … HUT1 … HLY) -HUT1 #HUT1
elim (ltpss_sn_tpss_conf … HU12 … HLY) -HU12 #U #HU1 #HU2
elim (delift_tpss_conf_le_up … HU1 … HUT1 … HYK ? ? ?) -HU1 -HUT1 -HYK // -Hdd -Hdde -Hddee #T #HT1 #HUT
lapply (ltpss_sn_delift_trans_eq … HLY … HUT) -HLY -HUT #HUT
lapply (tpss_delift_trans_eq … HU2 … HUT) -U /2 width=3/
qed.

lemma thin_delift_tps_conf_le_up: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                                  ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                                  ∀K. ▼*[dd, ee] L ≡ K →
                                  d ≤ dd → dd ≤ d + e → d + e ≤ dd + ee →
                                  ∃∃T2. K ⊢ T1 ▶* [d, dd - d] T2 &
                                        L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=6 by thin_delift_tpss_conf_le_up, tpss_strap2/ qed. (**) (* too slow without trace *)

lemma thin_delift_tpss_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                                ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                                ∀K. ▼*[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                                ∃∃T2. K ⊢ T1 ▶* [d, e - ee] T2 &
                                      L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee #HUT1 #K * #Y #HLY #HYK #Hdd #Hddee
lapply (delift_ltpss_sn_conf_eq … HUT1 … HLY) -HUT1 #HUT1
elim (ltpss_sn_tpss_conf … HU12 … HLY) -HU12 #U #HU1 #HU2
elim (delift_tpss_conf_be … HU1 … HUT1 … HYK ? ?) -HU1 -HUT1 -HYK // -Hdd -Hddee #T #HT1 #HUT
lapply (ltpss_sn_delift_trans_eq … HLY … HUT) -HLY -HUT #HUT
lapply (tpss_delift_trans_eq … HU2 … HUT) -U /2 width=3/
qed.

lemma thin_delift_tps_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                               ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                               ∀K. ▼*[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                               ∃∃T2. K ⊢ T1 ▶* [d, e - ee] T2 &
                                     L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=3/ qed.
