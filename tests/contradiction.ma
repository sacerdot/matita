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
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
alias id "not" = "cic:/Coq/Init/Logic/not.con".
alias num (instance 0) = "natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".



theorem stupid: \forall a:Prop. a \to not a \to 0 = 2.
intros.
letin H \def (H1 H).
contradiction.
qed.



