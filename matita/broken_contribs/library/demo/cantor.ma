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

include "demo/formal_topology.ma".
include "datatypes/constructors.ma".

axiom A: Type.
axiom S: A → Ω \sup A.

definition axs: axiom_set.
 constructor 1;
  [ apply A;
  | intro; apply unit;
  | intros; apply (S a)]
qed.

definition S' : axs → Ω \sup axs ≝ S.

definition emptyset: Ω \sup axs ≝ {x | False}.

definition Z: Ω \sup axs ≝ {x | x ◃ emptyset}.

theorem cantor: ∀a:axs. ¬ (Z ⊆ S' a ∧ S' a ⊆ Z).
 intros 2; cases H; clear H;
 cut (a ◃ S' a);
  [2: constructor 2; [constructor 1 | whd in ⊢ (? ? ? % ?); apply iter; autobatch]]
 cut (a ◃ emptyset);
  [2: apply transitivity; [apply (S' a)]
       [ assumption
       | constructor 1; intros;
         lapply (H2 ? H); whd in Hletin; assumption]]
 cut (a ∈ S' a);
  [2: apply H1; whd; assumption]
 generalize in match Hcut2; clear Hcut2;
 change with (a ∈ {a | a ∈ S' a → False});
 apply (covers_elim ?????? Hcut1);
  [ intros 2; simplify; intros; assumption;
  | intros; simplify; intros; whd in H3; simplify in H3; apply (H3 a1);
     [ assumption
     | assumption
     ]]
qed.
