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

include "basic_2/notation/relations/lrsubeqf_4.ma".
include "basic_2/static/frees.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

inductive lsubf: relation4 lenv rtmap lenv rtmap ≝
| lsubf_atom: ∀f1,f2. f2 ⊆ f1 → lsubf (⋆) f1 (⋆) f2
| lsubf_pair: ∀f1,f2,I,L1,L2,V. lsubf L1 (⫱f1) L2 (⫱f2) → f2 ⊆ f1 →
              lsubf (L1.ⓑ{I}V) f1 (L2.ⓑ{I}V) f2
| lsubf_beta: ∀f,f1,f2,L1,L2,W,V. L1 ⊢ 𝐅*⦃V⦄ ≡ f → f ⋓ ⫱f2 ≡ ⫱f1 → f2 ⊆ f1 →
              lsubf L1 (⫱f1) L2 (⫱f2) → lsubf (L1.ⓓⓝW.V) f1 (L2.ⓛW) f2
.

interpretation
  "local environment refinement (context-sensitive free variables)"
  'LRSubEqF L1 f1 L2 f2 = (lsubf L1 f1 L2 f2).

(* Basic inversion lemmas ***************************************************)

fact lsubf_inv_atom1_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L1 = ⋆ →
                          L2 = ⋆ ∧ f2 ⊆ f1.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I #L1 #L2 #V #_ #_ #H destruct
| #f #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom1: ∀f1,f2,L2. ⦃⋆, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L2 = ⋆ ∧ f2 ⊆ f1.
/2 width=3 by lsubf_inv_atom1_aux/ qed-.

fact lsubf_inv_pair1_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀I,K1,X. L1 = K1.ⓑ{I}X →
                          (∃∃K2. f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & L2 = K2.ⓑ{I}X) ∨
                          ∃∃f,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ f & f ⋓ ⫱f2 ≡ ⫱f1 &
                                      f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #J #K1 #X #H destruct
| #f1 #f2 #I #L1 #L2 #V #HL12 #H21 #J #K1 #X #H destruct
  /3 width=3 by ex3_intro, or_introl/
| #f #f1 #f2 #L1 #L2 #W #V #Hf #Hf1 #H21 #HL12 #J #K1 #X #H destruct
  /3 width=11 by ex7_4_intro, or_intror/
]
qed-.

lemma lsubf_inv_pair1: ∀f1,f2,I,K1,L2,X. ⦃K1.ⓑ{I}X, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                       (∃∃K2. f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & L2 = K2.ⓑ{I}X) ∨
                       ∃∃f,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ f & f ⋓ ⫱f2 ≡ ⫱f1 &
                                   f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsubf_inv_pair1_aux/ qed-.

fact lsubf_inv_atom2_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L2 = ⋆ →
                          L1 = ⋆ ∧ f2 ⊆ f1.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I #L1 #L2 #V #_ #_ #H destruct
| #f #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom2: ∀f1,f2,L1. ⦃L1, f1⦄ ⫃𝐅* ⦃⋆, f2⦄ → L1 = ⋆ ∧ f2 ⊆ f1.
/2 width=3 by lsubf_inv_atom2_aux/ qed-.

fact lsubf_inv_pair2_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀I,K2,W. L2 = K2.ⓑ{I}W →
                          (∃∃K1.f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & L1 = K1.ⓑ{I}W) ∨
                          ∃∃f,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ f & f ⋓ ⫱f2 ≡ ⫱f1 &
                                    f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & I = Abst & L1 = K1.ⓓⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #J #K2 #X #H destruct
| #f1 #f2 #I #L1 #L2 #V #HL12 #H21 #J #K2 #X #H destruct
  /3 width=3 by ex3_intro, or_introl/
| #f #f1 #f2 #L1 #L2 #W #V #Hf #Hf1 #H21 #HL12 #J #K2 #X #H destruct
  /3 width=7 by ex6_3_intro, or_intror/
]
qed-.

lemma lsubf_inv_pair2: ∀f1,f2,I,L1,K2,W. ⦃L1, f1⦄ ⫃𝐅* ⦃K2.ⓑ{I}W, f2⦄ →
                       (∃∃K1.f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & L1 = K1.ⓑ{I}W) ∨
                       ∃∃f,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ f & f ⋓ ⫱f2 ≡ ⫱f1 &
                                 f2 ⊆ f1 & ⦃K1, ⫱f1⦄ ⫃𝐅* ⦃K2, ⫱f2⦄ & I = Abst & L1 = K1.ⓓⓝW.V.
/2 width=5 by lsubf_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubf_fwd_sle: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → f2 ⊆ f1.
#f1 #f2 #L1 #L2 * //
qed-.

(* Basic properties *********************************************************)

lemma lsubf_refl: ∀L,f1,f2. f2 ⊆ f1 → ⦃L, f1⦄ ⫃𝐅* ⦃L, f2⦄.
#L elim L -L /4 width=1 by lsubf_atom, lsubf_pair, sle_tl/
qed.
