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

include "nat/order.ma".

nlet rec minus (n:nat) (m:nat) on m : nat ≝
 match m with
  [ O ⇒ n
  | S m' ⇒
     match n with
      [ O ⇒ O
      | S n' ⇒ minus n' m']].

interpretation "natural minus" 'minus x y = (minus x y).

naxiom le_minus: ∀n,m,p. le n m → le (minus n p) m.
naxiom lt_minus: ∀n,m,p. lt n m → lt (minus n p) m.
