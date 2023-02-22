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

include "ground/lib/relations.ma".

(* FUNCTIONS ****************************************************************)

definition left_identity (A) (f):
           predicate A ≝
           λi. ∀a:A. a = f i a.

definition right_identity (A) (f):
           predicate A ≝
           λi. ∀a:A. a = f a i.

definition compatible_2 (A) (B):
           relation3 … (relation A) (relation B) ≝
           λf,Sa,Sb.
           ∀a1,a2. Sa a1 a2 → Sb (f a1) (f a2).

definition compatible_3 (A) (B) (C):
           relation4 … (relation A) (relation B) (relation C) ≝
           λf,Sa,Sb,Sc.
           ∀a1,a2. Sa a1 a2 → ∀b1,b2. Sb b1 b2 → Sc (f a1 b1) (f a2 b2).

definition annulment_2 (A) (f):
           predicate A ≝
           λi:A.
           ∀a1,a2. i = f a1 a2 → ∧∧ i = a1 & i = a2.
