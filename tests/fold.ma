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
alias num (instance 0) = "natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "plus" (instance 0) = "Coq's natural plus".
theorem t: \forall x:nat. 0+x=x.
 intro.
 simplify in match (0+x) in \vdash (? ? % ?).
 fold simplify (0 + x) in \vdash (? ? % ?).
 reflexivity.
qed.
