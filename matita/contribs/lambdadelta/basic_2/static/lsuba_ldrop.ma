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

include "basic_2/static/lsuba.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

(* Properties concerning basic local environment slicing ********************)

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_ldrop_O1_conf: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → ∀K1,s,e. ⇩[s, 0, e] L1 ≡ K1 →
                           ∃∃K2. G ⊢ K1 ⁝⊑ K2 & ⇩[s, 0, e] L2 ≡ K2.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3/
| #I #L1 #L2 #V #_ #IHL12 #K1 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K1 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_abbr, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_ldrop_O1_trans: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → ∀K2,s,e. ⇩[s, 0, e] L2 ≡ K2 →
                            ∃∃K1. G ⊢ K1 ⁝⊑ K2 & ⇩[s, 0, e] L1 ≡ K1.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3/
| #I #L1 #L2 #V #_ #IHL12 #K2 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K2 #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(ldrop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_abbr, ldrop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
]
qed-.
