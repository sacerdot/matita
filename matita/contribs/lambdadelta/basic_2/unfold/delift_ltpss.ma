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

include "basic_2/unfold/ltpss_sn_alt.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Properties on sn partial unfold on local environments ********************)

lemma delift_ltpss_sn_conf_eq: ∀L,T1,T2,d,e. L ⊢ ▼*[d, e] T1 ≡ T2 →
                               ∀K. L ⊢ ▶* [d, e] K → K ⊢ ▼*[d, e] T1 ≡ T2.
#L #T1 #T2 #d #e * #T #HT1 #HT2 #K #HLK
elim (ltpss_sn_tpss_conf … HT1 … HLK) -HT1 -HLK #T0 #HT10 #HT0
lapply (tpss_inv_lift1_eq … HT0 … HT2) -HT0 #H destruct /2 width=3/
qed.

lemma ltpss_sn_delift_trans_eq: ∀L,K,d,e. L ⊢ ▶* [d, e] K →
                                ∀T1,T2. K ⊢ ▼*[d, e] T1 ≡ T2 → L ⊢ ▼*[d, e] T1 ≡ T2.
#L #K #d #e #HLK #T1 #T2 * #T #HT1 #HT2
lapply (ltpss_sn_tpss_trans_eq … HT1 … HLK) -K /2 width=3/
qed.
