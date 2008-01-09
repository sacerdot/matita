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



(* INSERT RELATION FOR CONTEXTS
*)

include "Lift/defs.ma".
include "datatypes_defs/Context.ma".

inductive Insert (p,q:Proof) (S:Sequent): 
                 Nat \to Context \to Context \to Prop \def
   | insert_zero: \forall P. Insert p q S zero P (abst P p q S)
   | insert_succ: \forall P,Q,i. Insert p q S i P Q \to 
                  \forall p1,p2. Lift i (succ zero) p1 p2 \to 
                  \forall q1,q2. Lift i (succ zero) q1 q2 \to \forall R. 
                  Insert p q S (succ i) (abst P p1 q1 R) (abst Q p2 q2 R)
.
