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

alias num (instance 0) = "Coq natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "plus" (instance 0) = "Coq's natural plus".
alias id "plus_comm" = "cic:/Coq/Arith/Plus/plus_comm.con".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".

(* This tests is for the case of a pattern that contains metavariables *)
theorem t: \forall x. x + 4 = 4 + x.
 intro.
 generalize in match (S ?).
 intro; apply plus_comm.
qed. 
 
(* This test used to fail because x was used in the wrong context *)
(* Once this was fixed it still did not work since apply is not   *)
(* able to solve a goal that ends in a product.                   *)
theorem test2: \forall x. 4 + x = x + 4.
 generalize in match 4.
 exact plus_comm.
qed.
