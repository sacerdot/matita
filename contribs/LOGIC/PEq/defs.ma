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



(* EQUALITY PREDICATE FOR PROOFS IN CONTEXT
*)

include "datatypes_defs/Context.ma".

inductive PEq (Q1:Context) (p1:Proof) (Q2:Context) (p2:Proof): Prop \def
   | peq_intro: Q1 = Q2 \land p1 = p2 \to PEq Q1 p1 Q2 p2
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation 
   "leibniz equality between proofs in context"
   'eq2 x1 y1 x2 y2 = 
      (cic:/matita/LOGIC/PEq/defs/PEq.ind#xpointer(1/1) x1 y1 x2 y2)
.

notation "hvbox([a1,b1] break = [a2,b2])" 
  non associative with precedence 45
for @{ 'eq2 $a1 $b1 $a2 $b2 }.
