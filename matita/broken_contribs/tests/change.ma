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
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".

theorem stupid: 
  \forall a:nat.
  a = 5 \to 
  (3 + 2) = a.
intros.
change in \vdash (? ? % ?) with 5.
rewrite < H in \vdash (? ? % ?). 
reflexivity.
qed.

(* tests changing a term under a binder *)
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
theorem t: (\forall x:nat. x=x) \to True.
 intro H.
 change in match x in H : (\forall _.%) with (0+x).
 change in H: (\forall _.(? ? ? (? % ?))) with 0.
 constructor 1.
qed.

