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

alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
theorem a:\forall x.x=x.
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
[ exact nat.
| intro. reflexivity.
]
qed.
alias num (instance 0) = "natural number".
alias symbol "times" (instance 0) = "Coq's natural times".

theorem b:\forall p:nat. p * 0=0.
intro.
autobatch library.
qed.
