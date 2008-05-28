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

theorem stupid : 
  let x \def 0 + 1 in x + 2 = x + 2.
  intros.
  clearbody x. 
  simplify.
  generalize in \vdash (? ? (? % ?) (? % ?)).
  intros.
  reflexivity.
  qed.
  
