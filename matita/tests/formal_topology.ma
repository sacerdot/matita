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

include "logic/connectives.ma".

coinductive fish (A:Type) (i: A → Type) (C: ∀a:A.i a → A → Prop) (U: A → Prop)
               : A → Prop
≝
 mk_foo: ∀a:A. (U a ∧ ∀j: i a. ∃y: A. C a j y ∧ fish A i C U y) → fish A i C U a.

let corec fish_rec (A:Type) (i: A → Type) (C: ∀a:A.i a → A → Prop) (U: A → Prop)
 (P: A → Prop) (H1: ∀a:A. P a → U a)
  (H2: ∀a:A. P a → ∀j: i a. ∃y: A. C a j y ∧ P y) :
   ∀a:A. ∀p: P a. fish A i C U a ≝
 λa,p.
  mk_foo A i C U a
   (conj ? ? (H1 ? p)
   (λj: i a.
    match H2 a p j with
     [ ex_intro (y: A) (Ha: C a j y ∧ P y) ⇒
        match Ha with
         [ conj (fHa: C a j y) (sHa: P y) ⇒
            ex_intro A (λy.C a j y ∧ fish A i C U y) y
             (conj ? ? fHa (fish_rec A i C U P H1 H2 y sHa))
         ]
     ])).