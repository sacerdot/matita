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

set "baseuri" "cic:/matita/test/injection/".

include "legacy/coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "bool" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".

inductive t0 : Type :=
   k0 : nat → nat → t0
 | k0' : bool → bool → t0.

theorem injection_test0: ∀n,n',m,m'. k0 n m = k0 n' m' → m = m'.
 intros;
 injection H;
 assumption.
qed.

inductive t : Type → Type :=
   k : nat → t nat
 | k': bool → t bool.
 
theorem injection_test1: ∀n,n'. k n = k n' → n = n'.
 intros;
 injection H;
 assumption.
qed.

inductive tt (A:Type) : Type -> Type :=
   k1: nat → nat → tt A nat
 | k2: bool → bool → tt A bool.
 
theorem injection_test2: ∀n,n',m,m'. k1 bool n n' = k1 bool m m' → n' = m'.
 intros;
 injection H;
 assumption.
qed.

inductive ttree : Type → Type :=
   tempty: ttree nat
 | tnode : ∀A. ttree A → ttree A → ttree A.

theorem injection_test3:
 ∀t,t'. tnode nat t tempty = tnode nat t' tempty → t = t'.
 intros;
 injection H;
 assumption.
qed.

theorem injection_test3:
 ∀t,t'.
  tnode nat (tnode nat t t') tempty = tnode nat (tnode nat t' tempty) tempty →
   t = t'.
 intros;
 injection H;
 

theorem injection_test4:
 ∀n,n',m,m'. k1 bool (S n) (S m) = k1 bool (S n') (S (S m')) → m = S m'.
 intros;
 injection H;
 assumption.
qed.


