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

include "Basic_2/computation/acp_cr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

inductive lsubc (RP:lenv→predicate term): relation lenv ≝
| lsubc_atom: lsubc RP (⋆) (⋆)
| lsubc_pair: ∀I,L1,L2,V. lsubc RP L1 L2 → lsubc RP (L1. 𝕓{I} V) (L2. 𝕓{I} V)
| lsubc_abbr: ∀L1,L2,V,W,A. ⦃L1, V⦄ [RP] ϵ 〚A〛 → ⦃L2, W⦄ [RP] ϵ 〚A〛 →
              lsubc RP L1 L2 → lsubc RP (L1. 𝕓{Abbr} V) (L2. 𝕓{Abst} W)
.

interpretation
  "local environment refinement (abstract candidates of reducibility)"
  'CrSubEq L1 RP L2 = (lsubc RP L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubc_inv_pair2_aux: ∀RP,L1,L2. L1 [RP] ⊑ L2 → ∀I,K2,W. L2 = K2. 𝕓{I} W →
                          (∃∃K1. K1 [RP] ⊑ K2 & L1 = K1. 𝕓{I} W) ∨
                          ∃∃K1,V,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & ⦃K2, W⦄ [RP] ϵ 〚A〛 & 
                                    K1 [RP] ⊑ K2 & L1 = K1. 𝕓{Abbr} V &
                                    I = Abst.
#RP #L1 #L2 * -L1 -L2
[ #I #K2 #W #H destruct
| #J #L1 #L2 #V #HL12 #I #K2 #W #H destruct /3 width=3/
| #L1 #L2 #V1 #W2 #A #H #HV1 #HW2 #I #K2 #W #H destruct /3 width=7/
]
qed.

lemma lsubc_inv_pair2: ∀RP,I,L1,K2,W. L1 [RP] ⊑ K2. 𝕓{I} W →
                       (∃∃K1. K1 [RP] ⊑ K2 & L1 = K1. 𝕓{I} W) ∨
                       ∃∃K1,V,A. ⦃K1, V⦄ [RP] ϵ 〚A〛 & ⦃K2, W⦄ [RP] ϵ 〚A〛 & 
                                 K1 [RP] ⊑ K2 & L1 = K1. 𝕓{Abbr} V &
                                 I = Abst.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

lemma lsubc_refl: ∀RP,L. L [RP] ⊑ L.
#RP #L elim L -L // /2 width=1/
qed.
