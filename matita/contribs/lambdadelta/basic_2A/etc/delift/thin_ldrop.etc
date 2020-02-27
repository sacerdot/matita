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

include "basic_2/unfold/ltpss_sn_ldrop.ma".
include "basic_2/unfold/thin.ma".

(* BASIC LOCAL ENVIRONMENT THINNING *****************************************)

(* Properties on local environment slicing **********************************)

lemma thin_ldrop_conf_ge: ∀L0,L1,d1,e1. ▼*[d1, e1] L0 ≡ L1 →
                          ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                          d1 + e1 ≤ e2 → ⇩[0, e2 - e1] L1 ≡ L2.
#L0 #L1 #d1 #e1 * /3 width=8 by ltpss_sn_ldrop_conf_ge, ldrop_conf_ge/
qed.

lemma thin_ldrop_conf_be: ∀L0,L1,d1,e1. ▼*[d1, e1] L0 ≡ L1 →
                          ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                          ∃∃L. ▼*[0, d1 + e1 - e2] L2 ≡ L & ⇩[0, d1] L1 ≡ L.
#L0 #L1 #d1 #e1 * #L #HL0 #HL1 #L2 #e2 #HL02 #Hd1e2 #He2de1
elim (ltpss_sn_ldrop_conf_be … HL0 … HL02 ? ?) -L0 // #L0 #HL20 #HL0
elim (ldrop_conf_be … HL1 … HL0 ? ?) -L // -Hd1e2 -He2de1 /3 width=3/
qed.

lemma thin_ldrop_conf_le: ∀L0,L1,d1,e1. ▼*[d1, e1] L0 ≡ L1 →
                          ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                          ∃∃L. ▼*[d1 - e2, e1] L2 ≡ L & ⇩[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 * #L #HL0 #HL1 #L2 #e2 #HL02 #He2d1
elim (ltpss_sn_ldrop_conf_le … HL0 … HL02 ?) -L0 // #L0 #HL20 #HL0
elim (ldrop_conf_le … HL1 … HL0 ?) -L // -He2d1 /3 width=3/
qed.

lemma thin_ldrop_trans_ge: ∀L1,L0,d1,e1. ▼*[d1, e1] L1 ≡ L0 →
                           ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                           d1 ≤ e2 → ⇩[0, e1 + e2] L1 ≡ L2.
#L1 #L0 #d1 #e1 * #L #HL1 #HL0 #L2 #e2 #HL02 #Hd1e2
lapply (ldrop_trans_ge … HL0 … HL02 ?) -L0 // #HL2
lapply (ltpss_sn_ldrop_trans_ge … HL1 … HL2 ?) -L // /2 width=1/
qed.

lemma thin_ldrop_trans_le: ∀L1,L0,d1,e1. ▼*[d1, e1] L1 ≡ L0 →
                           ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                           ∃∃L. ▼*[d1 - e2, e1] L ≡ L2 & ⇩[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 * #L #HL1 #HL0 #L2 #e2 #HL02 #He2d1
elim (ldrop_trans_le … HL0 … HL02 He2d1) -L0 #L0 #HL0 #HL02
elim (ltpss_sn_ldrop_trans_le … HL1 … HL0 He2d1) -L -He2d1 /3 width=3/
qed.
