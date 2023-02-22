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
alias id "plus" = "cic:/Coq/Init/Peano/plus.con".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "not" = "cic:/Coq/Init/Logic/not.con".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "plus_comm" = "cic:/Coq/Arith/Plus/plus_comm.con".

theorem t: let f \def \lambda x,y. x y in f (\lambda x.S x) O = S O.
 intros. simplify. change in \vdash (? ? (? ? %) ?) with O. 
 reflexivity. qed.

theorem X: \forall x:nat. let myplus \def plus x in myplus (S O) = S x.
 intros. simplify. change in \vdash (? ? (% ?) ?) with (plus x).

rewrite > plus_comm. reflexivity. qed.

theorem R: \forall x:nat. let uno \def x + O in S O + uno = 1 + x.
 intros. simplify.
  change in \vdash (? ? (? %) ?) with (x + O).
  rewrite > plus_comm. reflexivity. qed.
 
