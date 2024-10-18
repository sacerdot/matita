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

definition compatible_2_fwd (A) (B):
           relation3 (relation A) (relation B) … ≝
           λSa,Sb,f.
           ∀a1,a2. Sa a1 a2 → Sb (f a1) (f a2).

definition compatible_3 (A) (B) (C):
           relation4 (relation A) (relation B) (relation C) … ≝
           λSa,Sb,Sc,f.
           ∀a1,a2. Sa a1 a2 → ∀b1,b2. Sb b1 b2 → Sc (f a1 b1) (f a2 b2).

definition compatible_4 (A) (B) (C) (D):
           relation5 (relation A) (relation B) (relation C) (relation D) … ≝
           λSa,Sb,Sc,Sd,f.
           ∀a1,a2. Sa a1 a2 → ∀b1,b2. Sb b1 b2 → ∀c1,c2. Sc c1 c2 →
           Sd (f a1 b1 c1) (f a2 b2 c2).

definition injective_2_fwd (A) (B): relation3 (relation A) (relation B) … ≝
           λSa,Sb,f.
           ∀a1,a2. Sb (f a1) (f a2) → Sa a1 a2.

definition left_identity (A) (f):
           predicate A ≝
           λi. ∀a:A. a = f i a.

definition right_identity (A) (f):
           predicate A ≝
           λi. ∀a:A. a = f a i.

definition annulment_2 (A) (f):
           predicate A ≝
           λi:A.
           ∀a1,a2. i = f a1 a2 → ∧∧ i = a1 & i = a2.

(* Constructions with compose ***********************************************)

lemma compose_unfold (A) (B) (C:Type[0]) (g) (f) (a):
      g (f a) = (g∘{A,B,C}f) a.
// qed.

lemma compose_injective_2_fwd (A) (B) (C) (Sa) (Sb) (Sc) (f) (g):
      injective_2_fwd A B Sa Sb f → injective_2_fwd B C Sb Sc g →
      injective_2_fwd … Sa Sc (g∘f).
#A #B #C #Sa #Sb #Sc #f #g #Hf #HG #a1 #a2 #Hc
/3 width=1 by/
qed.
