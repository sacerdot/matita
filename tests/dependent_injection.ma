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



include "coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "bool" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".

inductive ttree : Type → Type :=
   tempty: ttree nat
 | tnode : ∀A. ttree A → ttree A → ttree A.

(* CSC: there is an undecidable unification problem here:
    consider a constructor k : \forall x. f x -> i (g x)
    The head of the outtype of the injection MutCase should be (f ?1)
    such that (f ?1) unifies with (g d) [ where d is the Rel that binds
    the corresponding right parameter in the outtype ]
    Coq dodges the problem by generating an equality between sigma-types
    (that state the existence of a ?1 such that ...) *)
theorem injection_test3:
 ∀t,t'. tnode nat t tempty = tnode nat t' tempty → t = t'.
 intros.
 destruct H.
 reflexivity.
qed.

theorem injection_test3:
 ∀t,t'.
  tnode nat (tnode nat t t') tempty = tnode nat (tnode nat t' tempty) tempty →
   t = t'.
 intros;
 destruct H;
 assumption.
qed.
