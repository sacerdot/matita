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

inductive foo: Prop \def I_foo: foo.

theorem stupid:
  1 = 0 \to (\forall p:Prop. p \to not p).
  intros.
  generalize in match I_foo.
  discriminate H.
qed.

inductive bar_list (A:Set): Set \def
  | bar_nil: bar_list A
  | bar_cons: A \to bar_list A \to bar_list A.

alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".
theorem stupid2:
  \forall A:Set.\forall x:A.\forall l:bar_list A.
  bar_nil A = bar_cons A x l \to False.
  intros.
  discriminate H.
qed.
