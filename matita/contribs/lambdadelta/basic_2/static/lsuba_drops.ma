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

include "basic_2/notation/relations/lrsubeqa_3.ma".
include "basic_2/static/lsubr.ma".
include "basic_2/static/aaa.ma".

(* RESTRICTED REFINEMENT FOR ATOMIC ARITY ASSIGNMENT ************************)

(* Basic properties *********************************************************)

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_drop_O1_conf: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀K1,c,k. ⬇[c, 0, k] L1 ≡ K1 →
                          ∃∃K2. G ⊢ K1 ⫃⁝ K2 & ⬇[c, 0, k] L2 ≡ K2.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K1 #c #k #H
  elim (drop_inv_O1_pair1 … H) -H * #Hm #HLK1
  [ destruct
    elim (IHL12 L1 c 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K1 #c #k #H
  elim (drop_inv_O1_pair1 … H) -H * #Hm #HLK1
  [ destruct
    elim (IHL12 L1 c 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_drop_O1_trans: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀K2,c,k. ⬇[c, 0, k] L2 ≡ K2 →
                           ∃∃K1. G ⊢ K1 ⫃⁝ K2 & ⬇[c, 0, k] L1 ≡ K1.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K2 #c #k #H
  elim (drop_inv_O1_pair1 … H) -H * #Hm #HLK2
  [ destruct
    elim (IHL12 L2 c 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K2 #c #k #H
  elim (drop_inv_O1_pair1 … H) -H * #Hm #HLK2
  [ destruct
    elim (IHL12 L2 c 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.
