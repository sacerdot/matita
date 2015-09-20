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

include "u0_predicates.ma".

(* CLASSES ************************************************************)

record u0_class: Type[1] ≝ {
   u0_class_t :> Type[0];
   u0_class_in:  u0_predicate1 u0_class_t;
   u0_class_eq:  u0_predicate2 u0_class_t
}.

interpretation "u0 class membership" 'mem a C = (u0_class_in C a).

definition u0_class_all: ∀C:u0_class. u0_quantifier C ≝ λC,P. ∀a. a ∈ C → P a.

definition u0_class_ex: ∀C:u0_class. u0_quantifier C ≝ λC,P. ∃a. a ∈ C ∧ P a.

record is_u0_class (C:u0_class): Prop ≝ {
   u0_class_repl1: can_u0_replace1 C (u0_class_all C) (u0_class_eq C) (u0_class_in C);
   u0_class_refl : is_u0_reflexive C (u0_class_all C) (u0_class_eq C)
}.
