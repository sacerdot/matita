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

include "basic_2/static/aaa.ma".
include "basic_2/computation/acp_cr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

inductive lsubc (RP:lenv→predicate term): relation lenv ≝
| lsubc_atom: lsubc RP (⋆) (⋆)
| lsubc_pair: ∀I,L1,L2,V. lsubc RP L1 L2 → lsubc RP (L1. ⓑ{I} V) (L2. ⓑ{I} V)
| lsubc_abbr: ∀L1,L2,V,W,A. ⦃L1, V⦄ [RP] ϵ 〚A〛 → L2 ⊢ W ⁝ A →
              lsubc RP L1 L2 → lsubc RP (L1. ⓓV) (L2. ⓛW)
.

interpretation
  "local environment refinement (abstract candidates of reducibility)"
  'CrSubEq L1 RP L2 = (lsubc RP L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubc_inv_atom1_aux: ∀RP,L1,L2. L1 [RP] ⊑ L2 → L1 = ⋆ → L2 = ⋆.
#RP #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #A #_ #_ #_ #H destruct
]
qed.

(* Basic_1: was: csubc_gen_sort_r *)
lemma lsubc_inv_atom1: ∀RP,L2. ⋆ [RP] ⊑ L2 → L2 = ⋆.
/2 width=4/ qed-.

fact lsubc_inv_pair1_aux: ∀RP,L1,L2. L1 [RP] ⊑ L2 → ∀I,K1,V. L1 = K1. ⓑ{I} V →
                          (∃∃K2. K1 [RP] ⊑ K2 & L2 = K2. ⓑ{I} V) ∨
                          ∃∃K2,W,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & K2 ⊢ W ⁝ A &
                                    K1 [RP] ⊑ K2 &
                                    L2 = K2. ⓛW & I = Abbr.
#RP #L1 #L2 * -L1 -L2
[ #I #K1 #V #H destruct
| #J #L1 #L2 #V #HL12 #I #K1 #W #H destruct /3 width=3/
| #L1 #L2 #V1 #W2 #A #HV1 #HW2 #HL12 #I #K1 #V #H destruct /3 width=7/
]
qed.

(* Basic_1: was: csubc_gen_head_r *)
lemma lsubc_inv_pair1: ∀RP,I,K1,L2,V. K1. ⓑ{I} V [RP] ⊑ L2 →
                       (∃∃K2. K1 [RP] ⊑ K2 & L2 = K2. ⓑ{I} V) ∨
                       ∃∃K2,W,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & K2 ⊢ W ⁝ A &
                                 K1 [RP] ⊑ K2 &
                                 L2 = K2. ⓛW & I = Abbr.
/2 width=3/ qed-.

fact lsubc_inv_atom2_aux: ∀RP,L1,L2. L1 [RP] ⊑ L2 → L2 = ⋆ → L1 = ⋆.
#RP #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #A #_ #_ #_ #H destruct
]
qed.

(* Basic_1: was: csubc_gen_sort_l *)
lemma lsubc_inv_atom2: ∀RP,L1. L1 [RP] ⊑ ⋆ → L1 = ⋆.
/2 width=4/ qed-.

fact lsubc_inv_pair2_aux: ∀RP,L1,L2. L1 [RP] ⊑ L2 → ∀I,K2,W. L2 = K2. ⓑ{I} W →
                          (∃∃K1. K1 [RP] ⊑ K2 & L1 = K1. ⓑ{I} W) ∨
                          ∃∃K1,V,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & K2 ⊢ W ⁝ A &
                                    K1 [RP] ⊑ K2 &
                                    L1 = K1. ⓓV & I = Abst.
#RP #L1 #L2 * -L1 -L2
[ #I #K2 #W #H destruct
| #J #L1 #L2 #V #HL12 #I #K2 #W #H destruct /3 width=3/
| #L1 #L2 #V1 #W2 #A #HV1 #HW2 #HL12 #I #K2 #W #H destruct /3 width=7/
]
qed.

(* Basic_1: was: csubc_gen_head_l *)
lemma lsubc_inv_pair2: ∀RP,I,L1,K2,W. L1 [RP] ⊑ K2. ⓑ{I} W →
                       (∃∃K1. K1 [RP] ⊑ K2 & L1 = K1. ⓑ{I} W) ∨
                       ∃∃K1,V,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & K2 ⊢ W ⁝ A &
                                 K1 [RP] ⊑ K2 &
                                 L1 = K1. ⓓV & I = Abst.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: csubc_refl *)
lemma lsubc_refl: ∀RP,L. L [RP] ⊑ L.
#RP #L elim L -L // /2 width=1/
qed.

(* Basic_1: removed theorems 2: csubc_clear_conf csubc_getl_conf *)
