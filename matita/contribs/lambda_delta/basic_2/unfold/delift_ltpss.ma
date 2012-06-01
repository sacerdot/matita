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

include "basic_2/unfold/ltpss_ltpss.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Properties on partial unfold on local environments ***********************)

lemma delift_ltpss_conf_eq: ∀L,T1,T2,d,e. L ⊢ T1 ▼*[d, e] ≡ T2 →
                            ∀K. L ▶* [d, e] K → K ⊢ T1 ▼*[d, e] ≡ T2.
#L #T1 #T2 #d #e * #T #HT1 #HT2 #K #HLK
elim (ltpss_tpss_conf … HT1 … HLK) -L #T0 #HT10 #HT0
lapply (tpss_inv_lift1_eq … HT0 … HT2) -HT0 #H destruct /2 width=3/
qed.

lemma ltpss_delift_trans_eq: ∀L,K,d,e. L ▶* [d, e] K →
                             ∀T1,T2. K ⊢ T1 ▼*[d, e] ≡ T2 → L ⊢ T1 ▼*[d, e] ≡ T2.
#L #K #d #e #HLK #T1 #T2 * #T #HT1 #HT2 
lapply (ltpss_tpss_trans_eq … HT1 … HLK) -K /2 width=3/
qed.
