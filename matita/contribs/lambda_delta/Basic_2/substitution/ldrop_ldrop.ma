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

include "Basic_2/substitution/lift_lift.ma".
include "Basic_2/substitution/ldrop.ma".

(* DROPPING *****************************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: drop_mono *)
theorem ldrop_mono: ∀d,e,L,L1. ⇩[d, e] L ≡ L1 →
                    ∀L2. ⇩[d, e] L ≡ L2 → L1 = L2.
#d #e #L #L1 #H elim H -d -e -L -L1
[ #d #e #L2 #H
  >(ldrop_inv_atom1 … H) -L2 //
| #K #I #V #L2 #HL12
   <(ldrop_inv_refl … HL12) -L2 //
| #L #K #I #V #e #_ #IHLK #L2 #H
  lapply (ldrop_inv_ldrop1 … H ?) -H // /2 width=1/
| #L #K1 #I #T #V1 #d #e #_ #HVT1 #IHLK1 #X #H
  elim (ldrop_inv_skip1 … H ?) -H // <minus_plus_m_m #K2 #V2 #HLK2 #HVT2 #H destruct
  >(lift_inj … HVT1 … HVT2) -HVT1 -HVT2
  >(IHLK1 … HLK2) -IHLK1 -HLK2 //
]
qed-.

(* Basic_1: was: drop_conf_ge *)
theorem ldrop_conf_ge: ∀d1,e1,L,L1. ⇩[d1, e1] L ≡ L1 →
                       ∀e2,L2. ⇩[0, e2] L ≡ L2 → d1 + e1 ≤ e2 →
                       ⇩[0, e2 - e1] L1 ≡ L2.
#d1 #e1 #L #L1 #H elim H -d1 -e1 -L -L1
[ #d #e #e2 #L2 #H
  >(ldrop_inv_atom1 … H) -L2 //
| //
| #L #K #I #V #e #_ #IHLK #e2 #L2 #H #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H /2 width=2/ #HL2
  <minus_plus >minus_minus_comm /3 width=1/
| #L #K #I #V1 #V2 #d #e #_ #_ #IHLK #e2 #L2 #H #Hdee2
  lapply (transitive_le 1 … Hdee2) // #He2
  lapply (ldrop_inv_ldrop1 … H ?) -H // -He2 #HL2
  lapply (transitive_le (1 + e) … Hdee2) // #Hee2
  @ldrop_ldrop_lt >minus_minus_comm /3 width=1/ (**) (* explicit constructor *)
]
qed.

(* Basic_1: was: drop_conf_lt *)
theorem ldrop_conf_lt: ∀d1,e1,L,L1. ⇩[d1, e1] L ≡ L1 →
                       ∀e2,K2,I,V2. ⇩[0, e2] L ≡ K2. ⓑ{I} V2 →
                       e2 < d1 → let d ≝ d1 - e2 - 1 in
                       ∃∃K1,V1. ⇩[0, e2] L1 ≡ K1. ⓑ{I} V1 &
                                ⇩[d, e1] K2 ≡ K1 & ⇧[d, e1] V1 ≡ V2.
#d1 #e1 #L #L1 #H elim H -d1 -e1 -L -L1
[ #d #e #e2 #K2 #I #V2 #H
  lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L #I #V #e2 #K2 #J #V2 #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #I #V #e #_ #_ #e2 #K2 #J #V2 #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #IHL12 #e2 #K2 #J #V #H #He2d
  elim (ldrop_inv_O1 … H) -H *
  [ -IHL12 -He2d #H1 #H2 destruct /2 width=5/
  | -HL12 -HV12 #He #HLK
    elim (IHL12 … HLK ?) -IHL12 -HLK [ <minus_minus /3 width=5/ | /2 width=1/ ] (**) (* a bit slow *)
  ]
]
qed.

(* Basic_1: was: drop_trans_le *)
theorem ldrop_trans_le: ∀d1,e1,L1,L. ⇩[d1, e1] L1 ≡ L →
                        ∀e2,L2. ⇩[0, e2] L ≡ L2 → e2 ≤ d1 →
                        ∃∃L0. ⇩[0, e2] L1 ≡ L0 & ⇩[d1 - e2, e1] L0 ≡ L2.
#d1 #e1 #L1 #L #H elim H -d1 -e1 -L1 -L
[ #d #e #e2 #L2 #H
  >(ldrop_inv_atom1 … H) -L2 /2 width=3/
| #K #I #V #e2 #L2 #HL2 #H
  lapply (le_n_O_to_eq … H) -H #H destruct /2 width=3/
| #L1 #L2 #I #V #e #_ #IHL12 #e2 #L #HL2 #H
  lapply (le_n_O_to_eq … H) -H #H destruct
  elim (IHL12 … HL2 ?) -IHL12 -HL2 // #L0 #H #HL0
  lapply (ldrop_inv_refl … H) -H #H destruct /3 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #IHL12 #e2 #L #H #He2d
  elim (ldrop_inv_O1 … H) -H *
  [ -He2d -IHL12 #H1 #H2 destruct /3 width=5/
  | -HL12 -HV12 #He2 #HL2
    elim (IHL12 … HL2 ?) -L2 [ >minus_le_minus_minus_comm // /3 width=3/ | /2 width=1/ ]
  ]
]
qed.

(* Basic_1: was: drop_trans_ge *)
theorem ldrop_trans_ge: ∀d1,e1,L1,L. ⇩[d1, e1] L1 ≡ L →
                        ∀e2,L2. ⇩[0, e2] L ≡ L2 → d1 ≤ e2 → ⇩[0, e1 + e2] L1 ≡ L2.
#d1 #e1 #L1 #L #H elim H -d1 -e1 -L1 -L
[ #d #e #e2 #L2 #H
  >(ldrop_inv_atom1 … H) -H -L2 //
| //
| /3 width=1/
| #L1 #L2 #I #V1 #V2 #d #e #H_ #_ #IHL12 #e2 #L #H #Hde2
  lapply (lt_to_le_to_lt 0 … Hde2) // #He2
  lapply (lt_to_le_to_lt … (e + e2) He2 ?) // #Hee2
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HL2
  @ldrop_ldrop_lt // >le_plus_minus // @IHL12 /2 width=1/ (**) (* explicit constructor *)
]
qed.

theorem ldrop_trans_ge_comm: ∀d1,e1,e2,L1,L2,L.
                             ⇩[d1, e1] L1 ≡ L → ⇩[0, e2] L ≡ L2 → d1 ≤ e2 →
                             ⇩[0, e2 + e1] L1 ≡ L2.
#e1 #e1 #e2 >commutative_plus /2 width=5/
qed.

(* Basic_1: was: drop_conf_rev *)
axiom ldrop_div: ∀e1,L1,L. ⇩[0, e1] L1 ≡ L → ∀e2,L2. ⇩[0, e2] L2 ≡ L →
                 ∃∃L0. ⇩[0, e1] L0 ≡ L2 & ⇩[e1, e2] L0 ≡ L1.
