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

include "basic_2/notation/relations/lazyor_5.ma".
include "basic_2/multiple/frees.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

definition llor: ynat → relation4 term lenv lenv lenv ≝ λd,T,L2,L1,L.
                 ∧∧ |L1| = |L2| & |L1| = |L|
                  & (∀I1,I2,I,K1,K2,K,V1,V2,V,i.
                       ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 → ⇩[i] L ≡ K.ⓑ{I}V → ∨∨
                       (∧∧ yinj i < d & I1 = I & V1 = V) |
                       (∧∧ (L1 ⊢ i ϵ 𝐅*[d]⦃T⦄ → ⊥) & I1 = I & V1 = V) |
                       (∧∧ d ≤ yinj i & L1 ⊢ i ϵ 𝐅*[d]⦃T⦄ & I2 = I & V2 = V)
                    ).

interpretation
   "lazy union (local environment)"
   'LazyOr L1 T d L2 L = (llor d T L2 L1 L).

(* Basic properties *********************************************************)

(* Note: this can be proved by llor_skip *)
lemma llor_atom: ∀T,d. ⋆ ⩖[T, d] ⋆ ≡ ⋆.
#T #d @and3_intro //
#I1 #I2 #I #K1 #K2 #K #V1 #V2 #V #i #HLK1
elim (drop_inv_atom1 … HLK1) -HLK1 #H destruct
qed.
