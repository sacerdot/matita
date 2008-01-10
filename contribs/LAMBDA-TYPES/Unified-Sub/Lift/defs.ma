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



(* LIFT RELATION
   - Usage: invoke with positive polarity
*)

include "datatypes/Term.ma".

inductive Lift (l: Nat): Nat \to Term \to Term \to Prop \def
   | lift_sort   : \forall i,h. 
                   Lift l i (sort h) (sort h)
   | lift_lref_gt: \forall i,j. i > j \to 
                   Lift l i (lref j) (lref j)
   | lift_lref_le: \forall i,j1. i <= j1 \to
                   \forall j2. (l + j1  == j2) \to
                   Lift l i (lref j1) (lref j2)
   | lift_bind   : \forall i,u1,u2. Lift l i u1 u2 \to
                   \forall t1,t2. Lift l (succ i) t1 t2 \to 
                   \forall r. Lift l i (intb r u1 t1) (intb r u2 t2)
   | lift_flat   : \forall i,u1,u2. Lift l i u1 u2 \to
                   \forall t1,t2. Lift l i t1 t2 \to 
                   \forall r. Lift l i (intf r u1 t1) (intf r u2 t2)
.
