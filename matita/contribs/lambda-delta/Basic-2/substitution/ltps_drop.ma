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

include "Basic-2/substitution/ltps.ma".

(* PARALLEL SUBSTITUTION ON LOCAL ENVIRONMENTS ******************************)

lemma ltps_drop_conf_ge: ∀L0,L1,d1,e1. L0 [d1, e1] ≫ L1 →
                         ∀L2,e2. ↓[0, e2] L0 ≡ L2 →
                         d1 + e1 ≤ e2 → ↓[0, e2] L1 ≡ L2.
#L0 #L1 #d1 #e1 #H elim H -H L0 L1 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H //
| //
| normalize #K0 #K1 #I #V0 #V1 #e1 #_ #_ #IHK01 #L2 #e2 #H #He12
  lapply (plus_le_weak … He12) #He2
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  lapply (IHK01 … HK0L2 ?) -IHK01 HK0L2 /2/
| #K0 #K1 #I #V0 #V1 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK01 #L2 #e2 #H #Hd1e2
  lapply (plus_le_weak … Hd1e2) #He2
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  lapply (IHK01 … HK0L2 ?) -IHK01 HK0L2 /2/
]
qed.

lemma ltps_drop_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ≫ L0 →
                          ∀L2,e2. ↓[0, e2] L0 ≡ L2 →
                          d1 + e1 ≤ e2 → ↓[0, e2] L1 ≡ L2.
#L1 #L0 #d1 #e1 #H elim H -H L1 L0 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H //
| //
| normalize #K1 #K0 #I #V1 #V0 #e1 #_ #_ #IHK10 #L2 #e2 #H #He12
  lapply (plus_le_weak … He12) #He2
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  lapply (IHK10 … HK0L2 ?) -IHK10 HK0L2 /2/
| #K0 #K1 #I #V1 #V0 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK10 #L2 #e2 #H #Hd1e2
  lapply (plus_le_weak … Hd1e2) #He2
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  lapply (IHK10 … HK0L2 ?) -IHK10 HK0L2 /2/
]
qed.

lemma ltps_drop_conf_be: ∀L0,L1,d1,e1. L0 [d1, e1] ≫ L1 →
                         ∀L2,e2. ↓[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                         ∃∃L. L2 [0, d1 + e1 - e2] ≫ L & ↓[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H elim H -H L0 L1 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H /2/
| normalize #L #I #V #L2 #e2 #HL2 #_ #He2
  lapply (le_n_O_to_eq … He2) -He2 #H destruct -e2;
  lapply (drop_inv_refl … HL2) -HL2 #H destruct -L2 /2/
| normalize #K0 #K1 #I #V0 #V1 #e1 #HK01 #HV01 #IHK01 #L2 #e2 #H #_ #He21
  lapply (drop_inv_O1 … H) -H * * #He2 #HK0L2
  [ destruct -IHK01 He21 e2 L2 <minus_n_O /3/
  | -HK01 HV01 <minus_le_minus_minus_comm //
    elim (IHK01 … HK0L2 ? ?) -IHK01 HK0L2 /3/
  ]
| #K0 #K1 #I #V0 #V1 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK01 #L2 #e2 #H #Hd1e2 #He2de1
  lapply (plus_le_weak … Hd1e2) #He2
  <minus_le_minus_minus_comm //
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  elim (IHK01 … HK0L2 ? ?) -IHK01 HK0L2 /3/
]
qed.

lemma ltps_drop_trans_be: ∀L1,L0,d1,e1. L1 [d1, e1] ≫ L0 →
                          ∀L2,e2. ↓[0, e2] L0 ≡ L2 → d1 ≤ e2 → e2 ≤ d1 + e1 →
                          ∃∃L. L [0, d1 + e1 - e2] ≫ L2 & ↓[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H elim H -H L1 L0 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H /2/
| normalize #L #I #V #L2 #e2 #HL2 #_ #He2
  lapply (le_n_O_to_eq … He2) -He2 #H destruct -e2;
  lapply (drop_inv_refl … HL2) -HL2 #H destruct -L2 /2/
| normalize #K1 #K0 #I #V1 #V0 #e1 #HK10 #HV10 #IHK10 #L2 #e2 #H #_ #He21
  lapply (drop_inv_O1 … H) -H * * #He2 #HK0L2
  [ destruct -IHK10 He21 e2 L2 <minus_n_O /3/
  | -HK10 HV10 <minus_le_minus_minus_comm //
    elim (IHK10 … HK0L2 ? ?) -IHK10 HK0L2 /3/
  ]
| #K1 #K0 #I #V1 #V0 #d1 #e1 >plus_plus_comm_23 #_ #_ #IHK10 #L2 #e2 #H #Hd1e2 #He2de1
  lapply (plus_le_weak … Hd1e2) #He2
  <minus_le_minus_minus_comm //
  lapply (drop_inv_drop1 … H ?) -H // #HK0L2
  elim (IHK10 … HK0L2 ? ?) -IHK10 HK0L2 /3/
]
qed.

lemma ltps_drop_conf_le: ∀L0,L1,d1,e1. L0 [d1, e1] ≫ L1 →
                         ∀L2,e2. ↓[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                         ∃∃L. L2 [d1 - e2, e1] ≫ L & ↓[0, e2] L1 ≡ L.
#L0 #L1 #d1 #e1 #H elim H -H L0 L1 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H /2/
| /2/
| normalize #K0 #K1 #I #V0 #V1 #e1 #HK01 #HV01 #_ #L2 #e2 #H #He2
  lapply (le_n_O_to_eq … He2) -He2 #He2 destruct -e2;
  lapply (drop_inv_refl … H) -H #H destruct -L2 /3/
| #K0 #K1 #I #V0 #V1 #d1 #e1 #HK01 #HV01 #IHK01 #L2 #e2 #H #He2d1
  lapply (drop_inv_O1 … H) -H * * #He2 #HK0L2
  [ destruct -IHK01 He2d1 e2 L2 <minus_n_O /3/
  | -HK01 HV01 <minus_le_minus_minus_comm //
    elim (IHK01 … HK0L2 ?) -IHK01 HK0L2 /3/
  ]
]
qed.

lemma ltps_trans_conf_le: ∀L1,L0,d1,e1. L1 [d1, e1] ≫ L0 →
                          ∀L2,e2. ↓[0, e2] L0 ≡ L2 → e2 ≤ d1 →
                          ∃∃L. L [d1 - e2, e1] ≫ L2 & ↓[0, e2] L1 ≡ L.
#L1 #L0 #d1 #e1 #H elim H -H L1 L0 d1 e1
[ #d1 #e1 #L2 #e2 #H >(drop_inv_sort1 … H) -H /2/
| /2/
| normalize #K1 #K0 #I #V1 #V0 #e1 #HK10 #HV10 #_ #L2 #e2 #H #He2
  lapply (le_n_O_to_eq … He2) -He2 #He2 destruct -e2;
  lapply (drop_inv_refl … H) -H #H destruct -L2 /3/
| #K1 #K0 #I #V1 #V0 #d1 #e1 #HK10 #HV10 #IHK10 #L2 #e2 #H #He2d1
  lapply (drop_inv_O1 … H) -H * * #He2 #HK0L2
  [ destruct -IHK10 He2d1 e2 L2 <minus_n_O /3/
  | -HK10 HV10 <minus_le_minus_minus_comm //
    elim (IHK10 … HK0L2 ?) -IHK10 HK0L2 /3/
  ]
]
qed.
