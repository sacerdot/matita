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

include "Plogic/equality.ma".

(* experimental: JMeq support *)

ninductive jmeq (A:Type[2]) (a:A) : ∀B:Type[2].B → Prop ≝
| refl_jmeq : jmeq A a A a.

naxiom jmeq_to_eq : ∀A:Type[2].∀a,b:A.jmeq A a A b → a = b.

ncoercion jmeq_to_eq : ∀A:Type[2].∀a,b:A.∀p:jmeq A a A b.a = b ≝ 
  jmeq_to_eq on _p: jmeq ???? to eq ???.

notation > "hvbox(a break ≃ b)" 
  non associative with precedence 45
for @{ 'jmeq ? $a ? $b }.

notation < "hvbox(term 46 a break maction (≃) (≃\sub(t,u)) term 46 b)" 
  non associative with precedence 45
for @{ 'jmeq $t $a $u $b }.

interpretation "john major's equality" 'jmeq t x u y = (jmeq t x u y).

naxiom streicherKjmeq : ∀T:Type[2].∀t:T.∀P:t ≃ t → Type[2].P (refl_jmeq ? t) → ∀p.P p.