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



include "nat/nat.ma".

include "logic/equality.ma".

axiom bad_ind : ∀P : nat -> Prop. ∀n.(n = O -> P n) -> (∀n.P n -> P (S n)) -> P n.

theorem absurd: ∀n. n = O.
  intros.
  letin P ≝ (λx:nat. n = O).
  apply (bad_ind P n); simplify; intros; unfold; autobatch.
qed.