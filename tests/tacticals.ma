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



inductive myand (A, B: Prop) : Prop \def
 | myconj : ∀a:A.∀b:B. myand A B. 
 
lemma prova: 
  ∀A,B,C,D:Prop.∀a:A.∀b:B.∀c:C.∀d:D.myand (myand A B) (myand C D).
  intros; try (apply myconj); try assumption; try (apply myconj);
  try assumption.
qed.

lemma prova2: 
  ∀A,B,C,D:Prop.∀a:A.∀b:B.∀c:C.∀d:D.myand (myand A B) (myand C D).
  intros; progress (apply myconj; apply myconj);
  solve [assumption].
qed.  

lemma prova3: 
  ∀A,B,C,D:Prop.∀a:A.∀b:B.∀c:C.∀d:D.myand (myand A B) (myand C D).
  intros; repeat first [ assumption | apply myconj].
qed.

lemma prova4: 
 ∀A,B,C,D:Prop.∀a:A.∀b:B.∀c:C.∀d:D.myand (myand A B) (myand C D).
  intros;
  repeat apply myconj;
  assumption.
qed.

lemma prova6: 
  ∀A,B,C,D:Prop.∀a:A.∀b:B.∀c:C.∀d:D.myand (myand A B) (myand C D).
  intros; apply myconj;  
  [1:repeat (constructor 1; try assumption)
  |2:repeat (constructor 1; try assumption)
  ]
qed.