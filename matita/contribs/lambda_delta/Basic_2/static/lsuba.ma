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

include "Basic_2/static/aaa.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

inductive lsuba: relation lenv ≝
| lsuba_atom: lsuba (⋆) (⋆)
| lsuba_pair: ∀I,L1,L2,V. lsuba L1 L2 → lsuba (L1. 𝕓{I} V) (L2. 𝕓{I} V)
| lsuba_abbr: ∀L1,L2,V,W,A. L1 ⊢ V ÷ A → L2 ⊢ W ÷ A → 
              lsuba L1 L2 → lsuba (L1. 𝕓{Abbr} V) (L2. 𝕓{Abst} W)
.

interpretation
  "local environment refinement (atomic arity assigment)"
  'CrSubEqA L1 L2 = (lsuba L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsuba_inv_pair2_aux: ∀L1,L2. L1 ÷⊑ L2 → ∀I,K2,W. L2 = K2. 𝕓{I} W →
                          (∃∃K1. K1 ÷⊑ K2 & L1 = K1. 𝕓{I} W) ∨
                          ∃∃K1,V,A. K1 ⊢ V ÷ A & K2 ⊢ W ÷ A & K1 ÷⊑ K2 &
                                    L1 = K1. 𝕓{Abbr} V & I = Abst.
#L1 #L2 * -L1 -L2
[ #I #K2 #W #H destruct
| #J #L1 #L2 #V #HL12 #I #K2 #W #H destruct /3 width=3/
| #L1 #L2 #V1 #W2 #A #HV1 #HW2 #HL12 #I #K2 #W #H destruct /3 width=7/
]
qed.

lemma lsuba_inv_pair2: ∀I,L1,K2,W. L1 ÷⊑ K2. 𝕓{I} W →
                       (∃∃K1. K1 ÷⊑ K2 & L1 = K1. 𝕓{I} W) ∨
                       ∃∃K1,V,A. K1 ⊢ V ÷ A & K2 ⊢ W ÷ A & K1 ÷⊑ K2 &
                                 L1 = K1. 𝕓{Abbr} V & I = Abst.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

lemma lsuba_refl: ∀L. L ÷⊑ L.
#L elim L -L // /2 width=1/
qed.
