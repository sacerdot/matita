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
alias num (instance 0) = "Coq natural number".
alias symbol "and" (instance 0) = "Coq's logical and".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "plus" (instance 0) = "Coq's natural plus".


theorem stupid:
  \forall a: 0 = 0.
  \forall b: 3 + 2 = 5.
  \forall c: (\lambda x:nat.x) 3 = 3.
  0=0 \land 3 + 2 = 5 \land 3 = 3.
intros.
split.
split.
clear H2. clear H1. 
assumption.
clear H.
assumption.
assumption.
qed.

