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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified/Lift/defs".

(* LIFT RELATION
   - Usage: invoke with positive polarity
*)

include "logic/equality.ma".
include "../../RELATIONAL/NPlus/defs.ma".
include "../../RELATIONAL/NLE/defs.ma".
include "../../RELATIONAL/BEq/defs.ma".

include "P/defs.ma".
include "Inc/defs.ma".

inductive Lift (l: Nat): Nat \to Bool \to P \to P \to Prop \def
   | lift_sort    : \forall i,a,h. Lift l i a (sort h) (sort h)
   | lift_lref_neg: \forall i,j. Lift l i false (lref j) (lref j)
   | lift_lref_lt : \forall i,j. 
                    j < i \to Lift l i true (lref j) (lref j)
   | lift_lref_ge : \forall i,j1,j2.
                    i <= j1 \to (j1 + l == j2) \to
                    Lift l i true (lref j1) (lref j2)
   | lift_head    : \forall i,i',a,b,a',z,q1,q2,p1,p2. 
                    (a * b == a') \to Inc i a' z i' \to
                    Lift l i a' q1 q2 \to Lift l i' a p1 p2 \to 
                    Lift l i a (head b z q1 p1) (head b z q2 p2)
.
