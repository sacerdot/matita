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

include "basic_2/notation/relations/lrsubeqc_4.ma".
include "basic_2/static/aaa.ma".
include "basic_2/static/gcp_cr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR GENERIC REDUCIBILITY ********************)

inductive lsubc (RP) (G): relation lenv ≝
| lsubc_atom: lsubc RP G (⋆) (⋆)
| lsubc_bind: ∀I,L1,L2. lsubc RP G L1 L2 → lsubc RP G (L1.ⓘ{I}) (L2.ⓘ{I})
| lsubc_beta: ∀L1,L2,V,W,A. ⦃G, L1, V⦄ ϵ[RP] 〚A〛 → ⦃G, L1, W⦄ ϵ[RP] 〚A〛 → ⦃G, L2⦄ ⊢ W ⁝ A →
              lsubc RP G L1 L2 → lsubc RP G (L1. ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (generic reducibility)"
  'LRSubEqC RP G L1 L2 = (lsubc RP G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubc_inv_atom1_aux: ∀RP,G,L1,L2. G ⊢ L1 ⫃[RP] L2 → L1 = ⋆ → L2 = ⋆.
#RP #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #V #W #A #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was just: csubc_gen_sort_r *)
lemma lsubc_inv_atom1: ∀RP,G,L2. G ⊢ ⋆ ⫃[RP] L2 → L2 = ⋆.
/2 width=5 by lsubc_inv_atom1_aux/ qed-.

fact lsubc_inv_bind1_aux: ∀RP,G,L1,L2. G ⊢ L1 ⫃[RP] L2 → ∀I,K1. L1 = K1.ⓘ{I} →
                          (∃∃K2. G ⊢ K1 ⫃[RP] K2 & L2 = K2.ⓘ{I}) ∨
                          ∃∃K2,V,W,A. ⦃G, K1, V⦄ ϵ[RP] 〚A〛 & ⦃G, K1, W⦄ ϵ[RP] 〚A〛 & ⦃G, K2⦄ ⊢ W ⁝ A &
                                      G ⊢ K1 ⫃[RP] K2 &
                                      L2 = K2. ⓛW & I = BPair Abbr (ⓝW.V).
#RP #G #L1 #L2 * -L1 -L2
[ #I #K1 #H destruct
| #J #L1 #L2 #HL12 #I #K1 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #V1 #W2 #A #HV1 #H1W2 #H2W2 #HL12 #I #K1 #H destruct
  /3 width=10 by ex6_4_intro, or_intror/
]
qed-.

(* Basic_1: was: csubc_gen_head_r *)
lemma lsubc_inv_bind1: ∀RP,I,G,K1,L2. G ⊢ K1.ⓘ{I} ⫃[RP] L2 →
                       (∃∃K2. G ⊢ K1 ⫃[RP] K2 & L2 = K2.ⓘ{I}) ∨
                       ∃∃K2,V,W,A. ⦃G, K1, V⦄ ϵ[RP] 〚A〛 & ⦃G, K1, W⦄ ϵ[RP] 〚A〛 & ⦃G, K2⦄ ⊢ W ⁝ A &
                                   G ⊢ K1 ⫃[RP] K2 &
                                   L2 = K2.ⓛW & I = BPair Abbr (ⓝW.V).
/2 width=3 by lsubc_inv_bind1_aux/ qed-.

fact lsubc_inv_atom2_aux: ∀RP,G,L1,L2. G ⊢ L1 ⫃[RP] L2 → L2 = ⋆ → L1 = ⋆.
#RP #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #V #W #A #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: was just: csubc_gen_sort_l *)
lemma lsubc_inv_atom2: ∀RP,G,L1. G ⊢ L1 ⫃[RP] ⋆ → L1 = ⋆.
/2 width=5 by lsubc_inv_atom2_aux/ qed-.

fact lsubc_inv_bind2_aux: ∀RP,G,L1,L2. G ⊢ L1 ⫃[RP] L2 → ∀I,K2. L2 = K2.ⓘ{I} →
                          (∃∃K1. G ⊢ K1 ⫃[RP] K2 & L1 = K1. ⓘ{I}) ∨
                          ∃∃K1,V,W,A. ⦃G, K1, V⦄ ϵ[RP] 〚A〛 & ⦃G, K1, W⦄ ϵ[RP] 〚A〛 & ⦃G, K2⦄ ⊢ W ⁝ A &
                                      G ⊢ K1 ⫃[RP] K2 &
                                      L1 = K1.ⓓⓝW.V & I = BPair Abst W.
#RP #G #L1 #L2 * -L1 -L2
[ #I #K2 #H destruct
| #J #L1 #L2 #HL12 #I #K2 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #V1 #W2 #A #HV1 #H1W2 #H2W2 #HL12 #I #K2 #H destruct
  /3 width=10 by ex6_4_intro, or_intror/
]
qed-.

(* Basic_1: was just: csubc_gen_head_l *)
lemma lsubc_inv_bind2: ∀RP,I,G,L1,K2. G ⊢ L1 ⫃[RP] K2.ⓘ{I} →
                       (∃∃K1. G ⊢ K1 ⫃[RP] K2 & L1 = K1.ⓘ{I}) ∨
                       ∃∃K1,V,W,A. ⦃G, K1, V⦄ ϵ[RP] 〚A〛 & ⦃G, K1, W⦄ ϵ[RP] 〚A〛 & ⦃G, K2⦄ ⊢ W ⁝ A &
                                   G ⊢ K1 ⫃[RP] K2 &
                                   L1 = K1.ⓓⓝW.V & I = BPair Abst W.
/2 width=3 by lsubc_inv_bind2_aux/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: csubc_refl *)
lemma lsubc_refl: ∀RP,G,L. G ⊢ L ⫃[RP] L.
#RP #G #L elim L -L /2 width=1 by lsubc_bind/
qed.

(* Basic_1: removed theorems 3:
            csubc_clear_conf csubc_getl_conf csubc_csuba
*)
