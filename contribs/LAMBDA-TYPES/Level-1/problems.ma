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

definition foo ≝
\lambda g:G.\lambda c:C.\lambda t:T.
\lambda P:T\to Prop.
\lambda H:\forall t1:T.\forall H:tau0 g c t t1.P t1.
\lambda H1:
 \forall t1:T.\forall H1:tau1 g c t t1.
  P t1 \to \forall t2:T.\forall H2:tau0 g c t1 t2.P t2.
 let rec f (t1:T) (H2:tau1 g c t t1) on H2 ≝
  match H2 return \lambda t2:T.\lambda H3:tau1 g c t t2.P t2 with
  [ tau1_tau0 => \lambda t2:T.\lambda H3:(tau0 g c t t2).H t2 H3
  | tau1_sing =>
     \lambda t2:T.\lambda H3:(tau1 g c t t2).\lambda t3:T.
      \lambda H4:tau0 g c t2 t3.H1 t2 H3 (f t2 H3) t3 H4
  ]
 in f.


inductive tau1 (g:G) (c:C) (t1:T): T \to Prop \def
| tau1_tau0: \forall (t2: T).((tau0 g c t1 t2) \to (tau1 g c t1 t2))
| tau1_sing: \forall (t: T).((tau1 g c t1 t) \to (\forall (t2: T).((tau0 g c 
t t2) \to (tau1 g c t1 t2))))).
