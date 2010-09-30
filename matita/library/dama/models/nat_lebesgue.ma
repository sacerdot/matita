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

include "dama/lebesgue.ma".
include "dama/models/nat_order_continuous.ma".

alias symbol "dependent_pair" = "dependent pair".
theorem nat_lebesgue_oc:
   ∀a:sequence ℕ.∀s:‡ℕ.∀H:∀i:nat.a i ∈ s. 
     ∀x:ℕ.a order_converges x → 
      x ∈ s ∧ 
      ∀h:x ∈ s.
       uniform_converge {[s]} ⌊n,≪a n,H n≫⌋ ≪x,h≫.
intros; apply lebesgue_oc; [apply nat_us_is_oc] assumption;
qed.

