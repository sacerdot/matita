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

include "lambda-delta/substitution/drop_defs.ma".

(* DROPPING *****************************************************************)

(* the main properties ******************************************************)

lemma drop_conf_ge: ∀d1,e1,L,L1. ↑[d1, e1] L1 ≡ L →
                    ∀e2,L2. ↑[0, e2] L2 ≡ L → d1 + e1 ≤ e2 →
                    ↑[0, e2 - e1] L2 ≡ L1.
#d1 #e1 #L #L1 #H elim H -H d1 e1 L L1
[ //
| #L #K #I #V #e #_ #IHLK #e2 #L2 #H #He2
  lapply (drop_inv_drop1 … H ?) -H /2/ #HL2
  <minus_plus_comm /3/
| #L #K #I #V1 #V2 #d #e #_ #_ #IHLK #e2 #L2 #H #Hdee2
  lapply (transitive_le 1 … Hdee2) // #He2
  lapply (drop_inv_drop1 … H ?) -H // -He2 #HL2
  lapply (transitive_le (1+e) … Hdee2) // #Hee2
  @drop_drop_lt >minus_minus_comm /3/ (**) (* explicit constructor *)
]
qed.

lemma drop_conf_lt: ∀d1,e1,L,L1. ↑[d1, e1] L1 ≡ L →
                    ∀e2,K2,I,V2. ↑[0, e2] K2. 𝕓{I} V2 ≡ L →
                    e2 < d1 → let d ≝ d1 - e2 - 1 in
                    ∃∃K1,V1. ↑[0, e2] K1. 𝕓{I} V1 ≡ L1 & 
                             ↑[d, e1] K1 ≡ K2 & ↑[d,e1] V1 ≡ V2.
#d1 #e1 #L #L1 #H elim H -H d1 e1 L L1
[ #L0 #e2 #K2 #I #V2 #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #I #V #e #_ #_ #e2 #K2 #J #V2 #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #IHL12 #e2 #K2 #J #V #H #He2d
  elim (drop_inv_O1 … H) -H *
  [ -IHL12 He2d #H1 #H2 destruct -e2 K2 J V /2 width=5/
  | -HL12 -HV12 #He #HLK
    elim (IHL12 … HLK ?) -IHL12 HLK [ <minus_minus /3 width=5/ | /2/ ] (**) (* a bit slow *)
  ]
]
qed.

lemma drop_trans_le: ∀d1,e1,L1. ∀L:lenv. ↑[d1, e1] L ≡ L1 →
                     ∀e2,L2. ↑[0, e2] L2 ≡ L → e2 ≤ d1 →
                     ∃∃L0. ↑[0, e2] L0 ≡ L1 & ↑[d1 - e2, e1] L2 ≡ L0.
#d1 #e1 #L1 #L #H elim H -H d1 e1 L1 L
[ #L #e2 #L2 #HL2 #H
  lapply (le_O_to_eq_O … H) -H #H destruct -e2 /2/
| #L1 #L2 #I #V #e #_ #IHL12 #e2 #L #HL2 #H
  lapply (le_O_to_eq_O … H) -H #H destruct -e2;
  elim (IHL12 … HL2 ?) -IHL12 HL2 // #L0 #H #HL0
  lapply (drop_inv_refl … H) -H #H destruct -L1 /3 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #IHL12 #e2 #L #H #He2d
  elim (drop_inv_O1 … H) -H *
  [ -He2d IHL12 #H1 #H2 destruct -e2 L /3 width=5/
  | -HL12 HV12 #He2 #HL2
    elim (IHL12 … HL2 ?) -IHL12 HL2 L2
    [ <minus_le_minus_minus_comm /3/ | /2/ ]
  ]
]
qed.

lemma drop_trans_ge: ∀d1,e1,L1,L. ↑[d1, e1] L ≡ L1 →
                     ∀e2,L2. ↑[0, e2] L2 ≡ L → d1 ≤ e2 → ↑[0, e1 + e2] L2 ≡ L1.
#d1 #e1 #L1 #L #H elim H -H d1 e1 L1 L
[ //
| /3/
| #L1 #L2 #I #V1 #V2 #d #e #H_ #_ #IHL12 #e2 #L #H #Hde2
  lapply (lt_to_le_to_lt 0 … Hde2) // #He2
  lapply (lt_to_le_to_lt … (e + e2) He2 ?) // #Hee2
  lapply (drop_inv_drop1 … H ?) -H // #HL2
  @drop_drop_lt // >le_plus_minus // @IHL12 /2/ (**) (* explicit constructor *)
]
qed.

axiom drop_div: ∀e1,L1. ∀L:lenv. ↑[0, e1] L ≡ L1 → ∀e2,L2. ↑[0, e2] L ≡ L2 →
                ∃∃L0. ↑[0, e1] L2 ≡ L0 & ↑[e1, e2] L1 ≡ L0.
