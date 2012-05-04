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

(* INVERSE TERM RELOCATION  *************************************************)

(* Properties on partial unfold on terms ************************************)

lemma delift_tpss_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶* U2 →
                           ∀T1,dd,ee. L ⊢ U1 [dd, ee] ≡ T1 →
                           ∀K. ⇩[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                           ∃∃T2. K ⊢ T1 [d, e - ee] ▶* T2 &
                                 L ⊢ U2 [dd, ee] ≡ T2.
#L #U1 #U2 #d #e #HU12 #T1 #dd #ee * #X1 #HUX1 #HTX1 #K #HLK #H1 #H2
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
elim (tpss_inv_lift1_be … HXU1 … HLK … HTX1 ? ?) -X1 -HLK // /3 width=5/
qed.

lemma delift_tps_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶ U2 →
                          ∀T1,dd,ee. L ⊢ U1 [dd, ee] ≡ T1 →
                          ∀K. ⇩[dd, ee] L ≡ K → d ≤ dd → dd + ee ≤ d + e →
                          ∃∃T2. K ⊢ T1 [d, e - ee] ▶* T2 &
                                L ⊢ U2 [dd, ee] ≡ T2.
/3 width=3/ qed.

lemma delift_tpss_conf_eq: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶* U2 →
                           ∀T. L ⊢ U1 [d, e] ≡ T → L ⊢ U2 [d, e] ≡ T.
#L #U1 #U2 #d #e #HU12 #T * #X1 #HUX1 #HTX1
elim (tpss_conf_eq … HU12 … HUX1) -U1 #U1 #HU21 #HXU1
lapply (tpss_inv_lift1_eq … HXU1 … HTX1) -HXU1 #H destruct /2 width=3/
qed.

lemma delift_tps_conf_eq: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶ U2 →
                          ∀T. L ⊢ U1 [d, e] ≡ T → L ⊢ U2 [d, e] ≡ T.
/3 width=3/ qed.

lemma tpss_delift_trans_eq: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶* U2 →
                            ∀T. L ⊢ U2 [d, e] ≡ T → L ⊢ U1 [d, e] ≡ T.
#L #U1 #U2 #d #e #HU12 #T * #X1 #HUX1 #HTX1
lapply (tpss_trans_eq … HU12 … HUX1) -U2 /2 width=3/
qed.

lemma tps_delift_trans_eq: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶ U2 →
                           ∀T. L ⊢ U2 [d, e] ≡ T → L ⊢ U1 [d, e] ≡ T.
/3 width=3/ qed.                            