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

include "basic_2/dynamic/lsubn.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE TYPE ASSIGNMENT ******************)

(* Properties concerning basic local environment slicing ********************)

(* Note: the constant 0 cannot be generalized *)
lemma lsubn_ldrop_O1_conf: ∀h,L1,L2. h ⊢ L1 :⊑ L2 → ∀K1,e. ⇩[0, e] L1 ≡ K1 →
                           ∃∃K2. h ⊢ K1 :⊑ K2 & ⇩[0, e] L2 ≡ K2.
#h #L1 #L2 #H elim H -L1 -L2
[ /2 width=3/
| #I #L1 #L2 #V #_ #IHL12 #K1 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 0 ?) -IHL12 // #X #HL12 #H
    <(ldrop_inv_refl … H) in HL12; -H /3 width=3/
  | elim (IHL12 … HLK1) -L1 /3 width=3/
  ]
| #L1 #L2 #V #W #H1VW #H2VW #_ #IHL12 #K1 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 0 ?) -IHL12 // #X #HL12 #H
    <(ldrop_inv_refl … H) in HL12; -H /3 width=3/
  | elim (IHL12 … HLK1) -L1 /3 width=3/
  ]
]
qed.

(* Note: the constant 0 cannot be generalized *)
(* Basic_1: was only: csubt_drop_abbr csubt_drop_abst *)
lemma lsubn_ldrop_O1_trans: ∀h,L1,L2. h ⊢ L1 :⊑ L2 → ∀K2,e. ⇩[0, e] L2 ≡ K2 →
                            ∃∃K1. h ⊢ K1 :⊑ K2 & ⇩[0, e] L1 ≡ K1.
#h #L1 #L2 #H elim H -L1 -L2
[ /2 width=3/
| #I #L1 #L2 #V #_ #IHL12 #K2 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 0 ?) -IHL12 // #X #HL12 #H
    <(ldrop_inv_refl … H) in HL12; -H /3 width=3/
  | elim (IHL12 … HLK2) -L2 /3 width=3/
  ]
| #L1 #L2 #V #W #H1VW #H2VW #_ #IHL12 #K2 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 0 ?) -IHL12 // #X #HL12 #H
    <(ldrop_inv_refl … H) in HL12; -H /3 width=3/
  | elim (IHL12 … HLK2) -L2 /3 width=3/
  ]
]
qed.
