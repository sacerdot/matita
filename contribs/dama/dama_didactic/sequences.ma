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



include "reals.ma".

axiom continuo: (R → R) → Prop.
axiom tends_to: (nat → R) → R → Prop.
axiom tends_to_inf: (nat → R) → Prop.

definition monotone_not_increasing ≝
 λ alpha:nat→R.
 ∀n:nat.alpha (S n) ≤ alpha n.

definition inf_bounded ≝
 λ alpha:nat → R.
 ∃ m. ∀ n:nat. m ≤ alpha n.

axiom converge: ∀ alpha.
 monotone_not_increasing alpha →
 inf_bounded alpha →
 ∃ l. tends_to alpha l.

definition punto_fisso :=
 λ F:R→R. λ x. x = F x.

let rec successione F x (n:nat) on n : R ≝
 match n with
  [ O ⇒ x
  | S n ⇒ F (successione F x n)
  ].

axiom lim_punto_fisso:
∀ F: R → R. ∀b:R. continuo F →
 let alpha := successione F b in
  ∀ l. tends_to alpha l →
    punto_fisso F l.

definition monotone_not_decreasing ≝
 λ alpha:nat→R.
 ∀n:nat.alpha n ≤ alpha (S n).
 
definition sup_bounded ≝
 λ alpha:nat → R.
 ∃ m. ∀ n:nat. alpha n ≤ m.
