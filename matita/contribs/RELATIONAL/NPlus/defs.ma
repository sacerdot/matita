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



include "datatypes/Nat.ma".

inductive NPlus (p:Nat): Nat → Nat → Prop ≝
   | nplus_zero_2: NPlus p zero p
   | nplus_succ_2: ∀q, r. NPlus p q r → NPlus p (succ q) (succ r).

interpretation "natural plus predicate" 'rel_plus x y z = (NPlus x y z).

notation "hvbox(a break ⊕ b break ≍ c)"
  non associative with precedence 45
for @{'rel_plus $a $b $c}.
