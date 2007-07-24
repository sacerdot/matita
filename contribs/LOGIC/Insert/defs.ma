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

set "baseuri" "cic:/matita/LOGIC/Insert/defs".

(* INSERT RELATION FOR CONTEXTS
*)

include "datatypes/Context.ma".

inductive Insert (S:Sequent): Nat \to Context \to Context \to Prop \def
   | insert_zero: \forall P. Insert S zero P (abst P S)
   | insert_succ: \forall P,Q,R,i. 
                  Insert S i P Q \to Insert S (succ i) (abst P R) (abst Q R)
.
