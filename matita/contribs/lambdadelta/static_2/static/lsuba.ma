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

include "ground_2/xoa/ex_5_4.ma".
include "static_2/notation/relations/lrsubeqa_3.ma".
include "static_2/static/aaa.ma".

(* RESTRICTED REFINEMENT FOR ATOMIC ARITY ASSIGNMENT ************************)

inductive lsuba (G:genv): relation lenv ≝
| lsuba_atom: lsuba G (⋆) (⋆)
| lsuba_bind: ∀I,L1,L2. lsuba G L1 L2 → lsuba G (L1.ⓘ[I]) (L2.ⓘ[I])
| lsuba_beta: ∀L1,L2,W,V,A. ❪G,L1❫ ⊢ ⓝW.V ⁝ A → ❪G,L2❫ ⊢ W ⁝ A →
              lsuba G L1 L2 → lsuba G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (atomic arity assignment)"
  'LRSubEqA G L1 L2 = (lsuba G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsuba_inv_atom1_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → L1 = ⋆ → L2 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsuba_inv_atom1: ∀G,L2. G ⊢ ⋆ ⫃⁝ L2 → L2 = ⋆.
/2 width=4 by lsuba_inv_atom1_aux/ qed-.

fact lsuba_inv_bind1_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀I,K1. L1 = K1.ⓘ[I] →
                          (∃∃K2. G ⊢ K1 ⫃⁝ K2 & L2 = K2.ⓘ[I]) ∨
                          ∃∃K2,W,V,A. ❪G,K1❫ ⊢ ⓝW.V ⁝ A & ❪G,K2❫ ⊢ W ⁝ A &
                                      G ⊢ K1 ⫃⁝ K2 & I = BPair Abbr (ⓝW.V) & L2 = K2.ⓛW.
#G #L1 #L2 * -L1 -L2
[ #J #K1 #H destruct
| #I #L1 #L2 #HL12 #J #K1 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K1 #H destruct /3 width=9 by ex5_4_intro, or_intror/
]
qed-.

lemma lsuba_inv_bind1: ∀I,G,K1,L2. G ⊢ K1.ⓘ[I] ⫃⁝ L2 →
                       (∃∃K2. G ⊢ K1 ⫃⁝ K2 & L2 = K2.ⓘ[I]) ∨
                       ∃∃K2,W,V,A. ❪G,K1❫ ⊢ ⓝW.V ⁝ A & ❪G,K2❫ ⊢ W ⁝ A & G ⊢ K1 ⫃⁝ K2 &
                                   I = BPair Abbr (ⓝW.V) & L2 = K2.ⓛW.
/2 width=3 by lsuba_inv_bind1_aux/ qed-.

fact lsuba_inv_atom2_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → L2 = ⋆ → L1 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #W #V #A #_ #_ #_ #H destruct
]
qed-.

lemma lsubc_inv_atom2: ∀G,L1. G ⊢ L1 ⫃⁝ ⋆ → L1 = ⋆.
/2 width=4 by lsuba_inv_atom2_aux/ qed-.

fact lsuba_inv_bind2_aux: ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → ∀I,K2. L2 = K2.ⓘ[I] →
                          (∃∃K1. G ⊢ K1 ⫃⁝ K2 & L1 = K1.ⓘ[I]) ∨
                          ∃∃K1,V,W,A. ❪G,K1❫ ⊢ ⓝW.V ⁝ A & ❪G,K2❫ ⊢ W ⁝ A &
                                       G ⊢ K1 ⫃⁝ K2 & I = BPair Abst W & L1 = K1.ⓓⓝW.V.
#G #L1 #L2 * -L1 -L2
[ #J #K2 #H destruct
| #I #L1 #L2 #HL12 #J #K2 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #A #HV #HW #HL12 #J #K2 #H destruct /3 width=9 by ex5_4_intro, or_intror/
]
qed-.

lemma lsuba_inv_bind2: ∀I,G,L1,K2. G ⊢ L1 ⫃⁝ K2.ⓘ[I] →
                       (∃∃K1. G ⊢ K1 ⫃⁝ K2 & L1 = K1.ⓘ[I]) ∨
                       ∃∃K1,V,W,A. ❪G,K1❫ ⊢ ⓝW.V ⁝ A & ❪G,K2❫ ⊢ W ⁝ A & G ⊢ K1 ⫃⁝ K2 &
                                   I = BPair Abst W & L1 = K1.ⓓⓝW.V.
/2 width=3 by lsuba_inv_bind2_aux/ qed-.

(* Basic properties *********************************************************)

lemma lsuba_refl: ∀G,L. G ⊢ L ⫃⁝ L.
#G #L elim L -L /2 width=1 by lsuba_atom, lsuba_bind/
qed.
