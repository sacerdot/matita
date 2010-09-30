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

(* test _with_ the WHD on the apply argument *)

include "coq.ma".

alias id "not" = "cic:/Coq/Init/Logic/not.con".
alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".

theorem b:
  \forall x:Prop.
  (not x) \to x \to False.
intros.
apply H.
assumption.
qed.

(* test _without_ the WHD on the apply argument *)

alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".

theorem a:
  \forall A:Set.
  \forall x: A.
  not (x=x) \to not (x=x).
intros.
apply H.
qed.


(* this test shows what happens when a term of type A -> ? is applied to
   a goal of type A' -> B: if A unifies with A' the unifier becomes ? := B
   and no goal is opened; otherwise the unifier becomes ? := A' -> B and a
   new goal of type A is created. *)
theorem c:
 \forall A,B:Prop.
   A \to (\forall P: Prop. A \to P) \to (A \to B) \land (B \to B).
 intros 4; split; [ apply H1 | apply H1; exact H ].
qed.

(* this test requires the delta-expansion of not in the type of the applied
   term (to reveal a product) *)
theorem d: \forall A: Prop. \lnot A \to A \to False.
 intros. apply H. assumption.
qed.
