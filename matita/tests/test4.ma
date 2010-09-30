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


(* commento che va nell'ast, ma non viene contato
    come step perche' non e' un executable
*)

alias num (instance 0) = "natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
theorem a:0=0.

(* nota *)
(**


apply Prop.
*)
apply cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1). 

(* commenti che non devono essere colorati perche'
   non c'e' nulla di eseguibile dopo di loro
*)
qed.
