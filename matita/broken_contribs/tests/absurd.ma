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
alias id "not" = "cic:/Coq/Init/Logic/not.con".

theorem stupid : \forall a:Prop. a \to not a \to 0 = 1.
intros.
absurd a.
assumption.
assumption.
qed.
