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

alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "minus" (instance 0) = "Coq's natural minus".
alias symbol "plus" (instance 0) = "Coq's natural plus".
alias symbol "times" (instance 0) = "Coq's natural times".
theorem a : \forall x,y:nat. x*x+(S y) = O - x.
intros.
auto new depth = 4 width = 3 use_paramod = false.
