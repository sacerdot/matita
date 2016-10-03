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
| lsubf_atom: ∀f. lsubf (⋆) f (⋆) f
| lsubf_push: ∀f1,f2,I,L1,L2,V. lsubf L1 f1 L2 f2 →
              lsubf (L1.ⓑ{I}V) (↑f1) (L2.ⓑ{I}V) (↑f2)
| lsubf_next: ∀f1,f2,I,L1,L2,V. lsubf L1 f1 L2 f2 →
              lsubf (L1.ⓑ{I}V) (⫯f1) (L2.ⓑ{I}V) (⫯f2)
| lsubf_peta: ∀f1,f,f2,L1,L2,W,V. L1 ⊢ 𝐅*⦃V⦄ ≡ f → f2 ⋓ f ≡ f1 →
              lsubf L1 f1 L2 f2 → lsubf (L1.ⓓⓝW.V) (↑f1) (L2.ⓛW) (↑f2)
| lsubf_neta: ∀f1,f,f2,L1,L2,W,V. L1 ⊢ 𝐅*⦃V⦄ ≡ f → f2 ⋓ f ≡ f1 →
              lsubf L1 f1 L2 f2 → lsubf (L1.ⓓⓝW.V) (⫯f1) (L2.ⓛW) (⫯f2)
.

interpretation
  "local environment refinement (context-sensitive free variables)"
  'LRSubEqF L1 f1 L2 f2 = (lsubf L1 f1 L2 f2).

(* Basic inversion lemmas ***************************************************)

fact lsubf_inv_atom1_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L1 = ⋆ →
                          L2 = ⋆ ∧ f1 = f2.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I #L1 #L2 #V #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #_ #H destruct
| #f1 #f #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
| #f1 #f #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom1: ∀f1,f2,L2. ⦃⋆, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                       L2 = ⋆ ∧ f1 = f2.
/2 width=3 by lsubf_inv_atom1_aux/ qed-.

fact lsubf_inv_push1_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀g1,I,K1,X. f1 = ↑g1 → L1 = K1.ⓑ{I}X →
                          (∃∃g2,K2. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f2 = ↑g2 & L2 = K2.ⓑ{I}X) ∨
                          ∃∃g,g2,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                         ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abbr & f2 = ↑g2 & L2 = K2.ⓛW & X = ⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f #g1 #J #K1 #X #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #HL12 #g1 #J #K1 #X #H1 #H2 destruct
  /3 width=5 by injective_push, ex3_2_intro, or_introl/
| #f1 #f2 #I #L1 #L2 #V #_ #g1 #J #K1 #X #H elim (discr_next_push … H)
| #f1 #f2 #f #L1 #L2 #W #V #Hf2 #Hf1 #HL12 #g1 #J #K1 #X #H1 #H2 destruct
  /3 width=11 by injective_push, ex7_5_intro, or_intror/
| #f1 #f2 #f #L1 #L2 #W #V #_ #_ #_ #g1 #J #K1 #X #H elim (discr_next_push … H)
]
qed-.

lemma lsubf_inv_push1: ∀g1,f2,I,K1,L2,X. ⦃K1.ⓑ{I}X, ↑g1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                       (∃∃g2,K2. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f2 = ↑g2 & L2 = K2.ⓑ{I}X) ∨
                       ∃∃g,g2,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                      ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abbr & f2 = ↑g2 & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=5 by lsubf_inv_push1_aux/ qed-.

fact lsubf_inv_next1_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀g1,I,K1,X. f1 = ⫯g1 → L1 = K1.ⓑ{I}X →
                          (∃∃g2,K2. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f2 = ⫯g2 & L2 = K2.ⓑ{I}X) ∨
                          ∃∃g,g2,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                         ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abbr & f2 = ⫯g2 & L2 = K2.ⓛW & X = ⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f #g1 #J #K1 #X #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #_ #g1 #J #K1 #X #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #V #HL12 #g1 #J #K1 #X #H1 #H2 destruct
  /3 width=5 by injective_next, ex3_2_intro, or_introl/
| #f1 #f2 #f #L1 #L2 #W #V #_ #_ #_ #g1 #J #K1 #X #H elim (discr_push_next … H)
| #f1 #f2 #f #L1 #L2 #W #V #Hf2 #Hf1 #HL12 #g1 #J #K1 #X #H1 #H2 destruct
  /3 width=11 by injective_next, ex7_5_intro, or_intror/
]
qed-.

lemma lsubf_inv_next1: ∀g1,f2,I,K1,L2,X. ⦃K1.ⓑ{I}X, ⫯g1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                       (∃∃g2,K2. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f2 = ⫯g2 & L2 = K2.ⓑ{I}X) ∨
                       ∃∃g,g2,K2,W,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                      ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abbr & f2 = ⫯g2 & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=5 by lsubf_inv_next1_aux/ qed-.

fact lsubf_inv_atom2_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ → L2 = ⋆ →
                          L1 = ⋆ ∧ f1 = f2.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I #L1 #L2 #V #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #_ #H destruct
| #f1 #f #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
| #f1 #f #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom2: ∀f1,f2,L1. ⦃L1, f1⦄ ⫃𝐅* ⦃⋆, f2⦄ →
                       L1 = ⋆ ∧ f1 = f2.
/2 width=3 by lsubf_inv_atom2_aux/ qed-.

fact lsubf_inv_push2_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀g2,I,K2,W. f2 = ↑g2 → L2 = K2.ⓑ{I}W →
                          (∃∃g1,K1. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f1 = ↑g1 & L1 = K1.ⓑ{I}W) ∨
                          ∃∃g,g1,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                       ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abst & f1 = ↑g1 & L1 = K1.ⓓⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f #g2 #J #K2 #X #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #HL12 #g2 #J #K2 #X #H1 #H2 destruct
  /3 width=5 by injective_push, ex3_2_intro, or_introl/
| #f1 #f2 #I #L1 #L2 #V #_ #g2 #J #K2 #X #H elim (discr_next_push … H)
| #f1 #f2 #f #L1 #L2 #W #V #Hf2 #Hf1 #HL12 #g2 #J #K2 #X #H1 #H2 destruct
  /3 width=9 by injective_push, ex6_4_intro, or_intror/
| #f1 #f2 #f #L1 #L2 #W #V #_ #_ #_ #g2 #J #K2 #X #H elim (discr_next_push … H)
]
qed-.

lemma lsubf_inv_push2: ∀f1,g2,I,L1,K2,W. ⦃L1, f1⦄ ⫃𝐅* ⦃K2.ⓑ{I}W, ↑g2⦄ →
                       (∃∃g1,K1. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f1 = ↑g1 & L1 = K1.ⓑ{I}W) ∨
                       ∃∃g,g1,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                    ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abst & f1 = ↑g1 & L1 = K1.ⓓⓝW.V.
/2 width=5 by lsubf_inv_push2_aux/ qed-.

fact lsubf_inv_next2_aux: ∀f1,f2,L1,L2. ⦃L1, f1⦄ ⫃𝐅* ⦃L2, f2⦄ →
                          ∀g2,I,K2,W. f2 = ⫯g2 → L2 = K2.ⓑ{I}W →
                          (∃∃g1,K1. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f1 = ⫯g1 & L1 = K1.ⓑ{I}W) ∨
                          ∃∃g,g1,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                       ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abst & f1 = ⫯g1 & L1 = K1.ⓓⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f #g2 #J #K2 #X #_ #H destruct
| #f1 #f2 #I #L1 #L2 #V #_ #g2 #J #K2 #X #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #V #HL12 #g2 #J #K2 #X #H1 #H2 destruct
  /3 width=5 by injective_next, ex3_2_intro, or_introl/
| #f1 #f2 #f #L1 #L2 #W #V #_ #_ #_ #g2 #J #K2 #X #H elim (discr_push_next … H)
| #f1 #f2 #f #L1 #L2 #W #V #Hf2 #Hf1 #HL12 #g2 #J #K2 #X #H1 #H2 destruct
  /3 width=9 by injective_next, ex6_4_intro, or_intror/
]
qed-.

lemma lsubf_inv_next2: ∀f1,g2,I,L1,K2,W. ⦃L1, f1⦄ ⫃𝐅* ⦃K2.ⓑ{I}W, ⫯g2⦄ →
                       (∃∃g1,K1. ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & f1 = ⫯g1 & L1 = K1.ⓑ{I}W) ∨
                       ∃∃g,g1,K1,V. K1 ⊢ 𝐅*⦃V⦄ ≡ g & g2 ⋓ g ≡ g1 &
                                    ⦃K1, g1⦄ ⫃𝐅* ⦃K2, g2⦄ & I = Abst & f1 = ⫯g1 & L1 = K1.ⓓⓝW.V.
/2 width=5 by lsubf_inv_next2_aux/ qed-.

(* Basic properties *********************************************************)

lemma lsubf_refl: bi_reflexive … lsubf.
#L elim L -L //
#L #I #V #IH #f elim (pn_split f) * /2 width=1 by lsubf_push, lsubf_next/
qed.
