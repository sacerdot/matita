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



theorem prova: 
  \forall A,B,C:Prop.
  \forall H:A \to A \to C \to A \to A \to B.A \to C \to B.
intros.
apply H;
  [assumption 
  |3,5:
   [ exact H2;
   | exact H1 ]
  |4:assumption
  |*:assumption
  ]
qed.

theorem prova1: 
  \forall A,B:Prop.
  \forall H:A \to A \to A \to A \to A \to B.A \to B.
intros.
apply H;
  [*:assumption]
qed. 

include "logic/connectives.ma".

theorem prova2: 
  \forall A,B:Prop.
  \forall H:A \to A \to A \to (A \land A) \to A \to B.A \to B.
intros.
apply H;
  [2:assumption
  |4:split.assumption
  |3,5:assumption
  |*:assumption
  ]
assumption.
qed. 

