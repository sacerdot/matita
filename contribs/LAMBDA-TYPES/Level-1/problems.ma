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

(* Problematic objects for disambiguation/typechecking ********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "LambdaDelta/theory.ma".

(* Problem 1: disambiguation errors with these objects *)

(*  leq_trans (in problems-4)
 *)

(* Problem 2: assertion failure raised by type checker on this object *)

inductive tau1 (g:G) (c:C) (t1:T): T \to Prop \def
| tau1_tau0: \forall (t2: T).((tau0 g c t1 t2) \to (tau1 g c t1 t2))
| tau1_sing: \forall (t: T).((tau1 g c t1 t) \to (\forall (t2: T).((tau0 g c 
t t2) \to (tau1 g c t1 t2)))).
