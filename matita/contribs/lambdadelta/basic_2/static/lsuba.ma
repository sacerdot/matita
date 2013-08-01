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
include "basic_2/static/aaa.ma". (**) (* disambiguation error *)
include "basic_2/substitution/lsubr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

inductive lsuba (G:genv): relation lenv ≝
| lsuba_atom: lsuba G (⋆) (⋆)
| lsuba_pair: ∀I,L1,L2,V. lsuba G L1 L2 → lsuba G (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsuba_abbr: ∀L1,L2,W,V,A. ⦃G, L1⦄ ⊢ ⓝW.V ⁝ A → ⦃G, L2⦄ ⊢ W ⁝ A →
              lsuba G L1 L2 → lsuba G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (atomic arity assigment)"
  'LRSubEqA G L1 L2 = (lsuba G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsuba_inv_atom1_aux: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → L1 = ⋆ → L2 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsuba_inv_atom1: ∀G,L2. G ⊢ ⋆ ⁝⊑ L2 → L2 = ⋆.
/2 width=4 by lsuba_inv_atom1_aux/ qed-.

fact lsuba_inv_pair1_aux: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → ∀I,K1,X. L1 = K1.ⓑ{I}X →
                          (∃∃K2. G ⊢ K1 ⁝⊑ K2 & L2 = K2.ⓑ{I}X) ∨
                          ∃∃K2,W,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A &
                                      G ⊢ K1 ⁝⊑ K2 & I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#G #L1 #L2 * -L1 -L2
[ #J #K1 #X #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #X #H destruct /3 width=3/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K1 #X #H destruct /3 width=9/
]
qed-.

lemma lsuba_inv_pair1: ∀I,G,K1,L2,X. G ⊢ K1.ⓑ{I}X ⁝⊑ L2 →
                       (∃∃K2. G ⊢ K1 ⁝⊑ K2 & L2 = K2.ⓑ{I}X) ∨
                       ∃∃K2,W,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A & G ⊢ K1 ⁝⊑ K2 &
                                   I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsuba_inv_pair1_aux/ qed-.

fact lsuba_inv_atom2_aux: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → L2 = ⋆ → L1 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsubc_inv_atom2: ∀G,L1. G ⊢ L1 ⁝⊑ ⋆ → L1 = ⋆.
/2 width=4 by lsuba_inv_atom2_aux/ qed-.

fact lsuba_inv_pair2_aux: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → ∀I,K2,W. L2 = K2.ⓑ{I}W →
                          (∃∃K1. G ⊢ K1 ⁝⊑ K2 & L1 = K1.ⓑ{I}W) ∨
                          ∃∃K1,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A &
                                    G ⊢ K1 ⁝⊑ K2 & I = Abst & L1 = K1.ⓓⓝW.V.
#G #L1 #L2 * -L1 -L2
[ #J #K2 #U #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U #H destruct /3 width=3/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K2 #U #H destruct /3 width=7/
]
qed-.

lemma lsuba_inv_pair2: ∀I,G,L1,K2,W. G ⊢ L1 ⁝⊑ K2.ⓑ{I}W →
                       (∃∃K1. G ⊢ K1 ⁝⊑ K2 & L1 = K1.ⓑ{I}W) ∨
                       ∃∃K1,V,A. ⦃G, K1⦄ ⊢ ⓝW.V ⁝ A & ⦃G, K2⦄ ⊢ W ⁝ A & G ⊢ K1 ⁝⊑ K2 &
                                 I = Abst & L1 = K1.ⓓⓝW.V.
/2 width=3 by lsuba_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsuba_fwd_lsubr: ∀G,L1,L2. G ⊢ L1 ⁝⊑ L2 → L1 ⊑ L2.
#G #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma lsuba_refl: ∀G,L. G ⊢ L ⁝⊑ L.
#G #L elim L -L // /2 width=1/
qed.
