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

include "basic_2/unfold/ltpss_ldrop.ma".
include "basic_2/unfold/ltpsss.ma".

(* ITERATED PARTIAL UNFOLD ON LOCAL ENVIRONMENTS ****************************)

lemma ltpsss_ldrop_conf_ge: ∀L0,L1,d1,e1. L0 [d1, e1] ▶** L1 →
                            ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                            d1 + e1 ≤ e2 → ⇩[0, e2] L1 ≡ L2.
#L0 #L1 #d1 #e1 #H @(ltpsss_ind … H) -L1 // /3 width=6/
qed.

lemma ltpsss_ldrop_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ▶** L0 →
                             ∀L2,e2. ⇩[0, e2] L0 ≡ L2 →
                             d1 + e1 ≤ e2 → ⇩[0, e2] L1 ≡ L2.
#L1 #L0 #d1 #e1 #H @(ltpsss_ind … H) -L0 // /3 width=6/
qed.

lemma ltpsss_ldrop_conf_be: ∀L0,L1,d1,e1. L0 [d1, e1] ▶** L1 →
                            ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                            ∃∃L. L2 [0, d1 + e1 - e2] ▶** L & ⇩[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H @(ltpsss_ind … H) -L1
[ /2 width=3/
| #L #L1 #_ #HL1 #IHL #L2 #e2 #HL02 #Hd1e2 #He2de1
  elim (IHL … HL02 Hd1e2 He2de1) -L0 #L0 #HL20 #HL0
  elim (ltpss_ldrop_conf_be … HL1 … HL0 Hd1e2 He2de1) -L /3 width=3/
]
qed.

lemma ltpsss_ldrop_trans_be: ∀L1,L0,d1,e1. L1 [d1, e1] ▶** L0 →
                             ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                             ∃∃L. L [0, d1 + e1 - e2] ▶** L2 & ⇩[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H @(ltpsss_ind … H) -L0
[ /2 width=3/
| #L #L0 #_ #HL0 #IHL #L2 #e2 #HL02 #Hd1e2 #He2de1
  elim (ltpss_ldrop_trans_be … HL0 … HL02 Hd1e2 He2de1) -L0 #L0 #HL02 #HL0
  elim (IHL … HL0 Hd1e2 He2de1) -L /3 width=3/
]
qed.

lemma ltpsss_ldrop_conf_le: ∀L0,L1,d1,e1. L0 [d1, e1] ▶** L1 →
                            ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                            ∃∃L. L2 [d1 - e2, e1] ▶** L & ⇩[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H @(ltpsss_ind … H) -L1
[ /2 width=3/
| #L #L1 #_ #HL1 #IHL #L2 #e2 #HL02 #He2d1
  elim (IHL … HL02 He2d1) -L0 #L0 #HL20 #HL0
  elim (ltpss_ldrop_conf_le … HL1 … HL0 He2d1) -L /3 width=3/
]
qed.

lemma ltpsss_ldrop_trans_le: ∀L1,L0,d1,e1. L1 [d1, e1] ▶** L0 →
                             ∀L2,e2. ⇩[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                             ∃∃L. L [d1 - e2, e1] ▶** L2 & ⇩[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H @(ltpsss_ind … H) -L0
[ /2 width=3/
| #L #L0 #_ #HL0 #IHL #L2 #e2 #HL02 #He2d1
  elim (ltpss_ldrop_trans_le … HL0 … HL02 He2d1) -L0 #L0 #HL02 #HL0
  elim (IHL … HL0 He2d1) -L /3 width=3/
]
qed.
