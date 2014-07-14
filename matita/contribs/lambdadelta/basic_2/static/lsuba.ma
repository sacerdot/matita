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

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

inductive lsuba (G:genv): relation lenv ≝
| lsuba_atom: lsuba G (⋆) (⋆)
| lsuba_pair: ∀I,L1,L2,V. lsuba G L1 L2 → lsuba G (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsuba_beta: ∀L1,L2,W,V,A. ⦃G, L1⦄ ⊢ ⓝW.V ⁝ A → ⦃G, L2⦄ ⊢ W ⁝ A →
              lsuba G L1 L2 → lsuba G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (atomic arity assignment)"
  'LRSubEqA G L1 L2 = (lsuba G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsuba_inv_atom1_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → L1 = ⋆ → L2 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsuba_inv_atom1: ∀G,L2. G ⊢ ⋆ ⫃⁝ L2 → L2 = ⋆.
/2 width=4 by lsuba_inv_atom1_aux/ qed-.

fact lsuba_inv_pair1_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀I,K1,X. L1 = K1.ⓑ{I}X →
                          (∃∃K2. G ⊢ K1 ⫃⁝ K2 & L2 = K2.ⓑ{I}X) ∨
                          ∃∃K2,W,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A &
                                      G ⊢ K1 ⫃⁝ K2 & I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#G #L1 #L2 * -L1 -L2
[ #J #K1 #X #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #X #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K1 #X #H destruct /3 width=9 by or_intror, ex6_4_intro/
]
qed-.

lemma lsuba_inv_pair1: ∀I,G,K1,L2,X. G ⊢ K1.ⓑ{I}X ⫃⁝ L2 →
                       (∃∃K2. G ⊢ K1 ⫃⁝ K2 & L2 = K2.ⓑ{I}X) ∨
                       ∃∃K2,W,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A & G ⊢ K1 ⫃⁝ K2 &
                                   I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsuba_inv_pair1_aux/ qed-.

fact lsuba_inv_atom2_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → L2 = ⋆ → L1 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsubc_inv_atom2: ∀G,L1. G ⊢ L1 ⫃⁝ ⋆ → L1 = ⋆.
/2 width=4 by lsuba_inv_atom2_aux/ qed-.

fact lsuba_inv_pair2_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀I,K2,W. L2 = K2.ⓑ{I}W →
                          (∃∃K1. G ⊢ K1 ⫃⁝ K2 & L1 = K1.ⓑ{I}W) ∨
                          ∃∃K1,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A &
                                    G ⊢ K1 ⫃⁝ K2 & I = Abst & L1 = K1.ⓓⓝW.V.
#G #L1 #L2 * -L1 -L2
[ #J #K2 #U #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K2 #U #H destruct /3 width=7 by or_intror, ex5_3_intro/
]
qed-.

lemma lsuba_inv_pair2: ∀I,G,L1,K2,W. G ⊢ L1 ⫃⁝ K2.ⓑ{I}W →
                       (∃∃K1. G ⊢ K1 ⫃⁝ K2 & L1 = K1.ⓑ{I}W) ∨
                       ∃∃K1,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A & G ⊢ K1 ⫃⁝ K2 &
                                 I = Abst & L1 = K1.ⓓⓝW.V.
/2 width=3 by lsuba_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsuba_fwd_lsubr: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → L1 ⫃ L2.
#G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsubr_pair, lsubr_beta/
qed-.

(* Basic properties *********************************************************)

lemma lsuba_refl: ∀G,L. G ⊢ L ⫃⁝ L.
#G #L elim L -L /2 width=1 by lsuba_atom, lsuba_pair/
qed.

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_drop_O1_conf: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀K1,s,e. ⇩[s, 0, e] L1 ≡ K1 →
                          ∃∃K2. G ⊢ K1 ⫃⁝ K2 & ⇩[s, 0, e] L2 ≡ K2.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K1 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K1 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK1
  [ destruct
    elim (IHL12 L1 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK1) -L1 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Note: the constant 0 cannot be generalized *)
lemma lsuba_drop_O1_trans: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀K2,s,e. ⇩[s, 0, e] L2 ≡ K2 →
                           ∃∃K1. G ⊢ K1 ⫃⁝ K2 & ⇩[s, 0, e] L1 ≡ K1.
#G #L1 #L2 #H elim H -L1 -L2
[ /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #K2 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_pair, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #W #V #A #HV #HW #_ #IHL12 #K2 #s #e #H
  elim (drop_inv_O1_pair1 … H) -H * #He #HLK2
  [ destruct
    elim (IHL12 L2 s 0) -IHL12 // #X #HL12 #H
    <(drop_inv_O2 … H) in HL12; -H /3 width=3 by lsuba_beta, drop_pair, ex2_intro/
  | elim (IHL12 … HLK2) -L2 /3 width=3 by drop_drop_lt, ex2_intro/
  ]
]
qed-.
