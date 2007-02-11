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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/defs".

(* LIFT RELATION
   - Usage: invoke with positive polarity
*)

include "Term/defs.ma".

inductive Lift: Bool \to Nat \to Nat \to Term \to Term \to Prop \def
   | lift_sort   : \forall l,q,i,h. 
                   Lift q l i (leaf (sort h)) (leaf (sort h))
   | lift_lref   : \forall l,i,j. 
                   Lift false l i (leaf (lref j)) (leaf (lref j))
   | lift_lref_lt: \forall l,i,j. j < i \to 
                   Lift true l i (leaf (lref j)) (leaf (lref j))
   | lift_lref_ge: \forall l,i,j1. i <= j1 \to
                   \forall j2. (j1 + l == j2) \to
                   Lift true l i (leaf (lref j1)) (leaf (lref j2))
   | lift_bind   : \forall l,i,u1,u2. Lift true l i u1 u2 \to
                   \forall q,t1,t2. Lift q l (succ i) t1 t2 \to 
                   \forall r.
                   Lift q l i (head q (bind r) u1 t1) (head q (bind r) u2 t2)
   | lift_flat   : \forall l,i,u1,u2. Lift true l i u1 u2 \to
                   \forall q,t1,t2. Lift q l i t1 t2 \to 
                   \forall r.
                   Lift q l i (head q (flat r) u1 t1) (head q (flat r) u2 t2)
   | lift_head   : \forall l,qt,q. (qt = q \to False) \to
                   \forall i,u1,u2. Lift false l i u1 u2 \to
                   \forall t1,t2. Lift qt l i t1 t2 \to 
                   \forall z.
                   Lift qt l i (head q z u1 t1) (head q z u2 t2)
.
