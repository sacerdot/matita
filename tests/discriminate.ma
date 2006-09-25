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

set "baseuri" "cic:/matita/tests/discriminate".
include "legacy/coq.ma".
alias id "not" = "cic:/Coq/Init/Logic/not.con".
alias num (instance 0) = "natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "bool" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1)".

inductive foo: Prop \def I_foo: foo.

alias num (instance 0) = "binary integer number".
theorem stupid:
  1 = 0 \to (\forall p:Prop. p \to not p).
  intros.
  generalize in match I_foo.
  discriminate H.
qed.

inductive bar_list (A:Set): Set \def
  | bar_nil: bar_list A
  | bar_cons: A \to bar_list A \to bar_list A.


theorem stupid2:
  \forall A:Set.\forall x:A.\forall l:bar_list A.
  bar_nil A = bar_cons A x l \to False.
  intros.
  discriminate H.
qed.

inductive dt (A:Type): Type \to Type \def
 | k1: \forall T:Type. dt A T
 | k2: \forall T:Type. \forall T':Type. dt A (T \to T').
 
theorem stupid3:
 k1 False (False → True) = k2 False False True → False.
 intros;
 discriminate H.
qed.

inductive dddt (A:Type): Type \to Type \def
 | kkk1: dddt A nat
 | kkk2: dddt A nat.
 
theorem stupid4: kkk1 False = kkk2 False \to False.
 intros;
 discriminate H.
qed.