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
alias num (instance 0) = "natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".

theorem stupid:
  \forall a: True.
  \forall b: 0 = 0.
  0 = 0.
intros 1 (H).
clear H.
intros 1 (H).
exact H.
qed.

