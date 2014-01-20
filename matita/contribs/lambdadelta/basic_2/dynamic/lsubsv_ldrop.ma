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

include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties concerning basic local environment slicing ********************)

(* Note: the constant 0 cannot be generalized *)
lemma lsubsv_ldrop_O1_conf: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 →
                            ∀K1,s,e. ⇩[s, 0, e] L1 ≡ K1 →
                            ∃∃K2. G ⊢ K1 ¡⊑[h, g] K2 & ⇩[s, 0, e] L2 ≡ K2.
#h #g #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K1 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsubsv_pair, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #l #H1W #HV #HVW #H2W #H1l #H2l #_ #IHL12 #K1 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=4 by lsubsv_abbr, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsubsv_ldrop_O1_trans: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 →
                             ∀K2,s, e. ⇩[s, 0, e] L2 ≡ K2 →
                             ∃∃K1. G ⊢ K1 ¡⊑[h, g] K2 & ⇩[s, 0, e] L1 ≡ K1.
#h #g #G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K2 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsubsv_pair, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #l #H1W #HV #HVW #H2W #H1l #H2l #_ #IHL12 #K2 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=4 by lsubsv_abbr, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
]
qed-.
