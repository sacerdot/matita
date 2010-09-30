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



(* ORDER RELATION BETWEEN POSITIONS AND CONTEXTS
*)

include "datatypes_defs/Context.ma".

inductive CLE: Nat \to Context \to Prop \def
   | cle_zero: \forall Q. CLE zero Q
   | cle_succ: \forall Q,i. CLE i Q \to 
               \forall p1,p2,R. CLE (succ i) (abst Q p1 p2 R)
.

interpretation "order relation between positions and contexts" 
   'leq x y = (CLE x y).
