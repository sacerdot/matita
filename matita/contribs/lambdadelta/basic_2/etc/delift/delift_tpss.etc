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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Properties on partial unfold on terms ************************************)

lemma delift_tpss_conf_le: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                           ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                           ∀K. ⇩[dd, ee] L ≡ K → d + e ≤ dd →
                           ∃∃T2. K ⊢ T1 ▶* [d, e] T2 & L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee * #X1 #HUX1 #HTX1 #K #HLK #H1
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
elim (tpss_inv_lift1_le … HXU1 … HLK … HTX1 ?) -X1 -HLK // -H1 /3 width=5/
qed.

lemma delift_tps_conf_le: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                          ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                          ∀K. ⇩[dd, ee] L ≡ K → d + e ≤ dd →
                          ∃∃T2. K ⊢ T1 ▶* [d, e] T2 & L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=3/ qed.

lemma delift_tpss_conf_le_up: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                              ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                              ∀K. ⇩[dd, ee] L ≡ K →
                              d ≤ dd → dd ≤ d + e → d + e ≤ dd + ee →
                              ∃∃T2. K ⊢ T1 ▶* [d, dd - d] T2 &
                                    L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee * #X1 #HUX1 #HTX1 #K #HLK #H1 #H2 #H3
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
elim (tpss_inv_lift1_le_up … HXU1 … HLK … HTX1 ? ? ?) -X1 -HLK // -H1 -H2 -H3 /3 width=5/
qed.

lemma delift_tps_conf_le_up: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                             ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                             ∀K. ⇩[dd, ee] L ≡ K →
                             d ≤ dd → dd ≤ d + e → d + e ≤ dd + ee →
                             ∃∃T2. K ⊢ T1 ▶* [d, dd - d] T2 &
                                   L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=6/ qed.

lemma delift_tpss_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                           ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                           ∀K. ⇩[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                           ∃∃T2. K ⊢ T1 ▶* [d, e - ee] T2 &
                                 L ⊢ ▼*[dd, ee] U2 ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee * #X1 #HUX1 #HTX1 #K #HLK #H1 #H2
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
elim (tpss_inv_lift1_be … HXU1 … HLK … HTX1 ? ?) -X1 -HLK // -H1 -H2 /3 width=5/
qed.

lemma delift_tps_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                          ∀T1,dd,ee. L ⊢ ▼*[dd, ee] U1 ≡ T1 →
                          ∀K. ⇩[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                          ∃∃T2. K ⊢ T1 ▶* [d, e - ee] T2 &
                                L ⊢ ▼*[dd, ee] U2 ≡ T2.
/3 width=3/ qed.

lemma delift_tpss_conf_eq: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                           ∀T. L ⊢ ▼*[d, e] U1 ≡ T → L ⊢ ▼*[d, e] U2 ≡ T.
#L #U1 #U2 #d #e #HU12 #T * #X1 #HUX1 #HTX1
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
lapply (tpss_inv_lift1_eq … HXU1 … HTX1) -HXU1 #H destruct /2 width=3/
qed.

lemma delift_tps_conf_eq: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                          ∀T. L ⊢ ▼*[d, e] U1 ≡ T → L ⊢ ▼*[d, e] U2 ≡ T.
/3 width=3/ qed.

lemma tpss_delift_trans_eq: ∀L,U1,U2,d,e. L ⊢ U1 ▶* [d, e] U2 →
                            ∀T. L ⊢ ▼*[d, e] U2 ≡ T → L ⊢ ▼*[d, e] U1 ≡ T.
#L #U1 #U2 #d #e #HU12 #T * #X1 #HUX1 #HTX1
lapply (tpss_trans_eq … HU12 … HUX1) -U2 /2 width=3/
qed.

lemma tps_delift_trans_eq: ∀L,U1,U2,d,e. L ⊢ U1 ▶ [d, e] U2 →
                           ∀T. L ⊢ ▼*[d, e] U2 ≡ T → L ⊢ ▼*[d, e] U1 ≡ T.
/3 width=3/ qed.
