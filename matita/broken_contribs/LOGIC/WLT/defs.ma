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



(* ORDER RELATION BETWEEN PROOFS IN CONTEXT
*)

include "Weight/defs.ma".

inductive WLT (Q1:Context) (p1:Proof) (Q2:Context) (p2:Proof): Prop \def
   | wlt_intro: \forall m,m1. Weight m Q1 p1 m1 \to
                \forall m2. Weight m Q2 p2 m2 \to
                m1 < m2 \to WLT Q1 p1 Q2 p2               
.

interpretation "order relation between proofs in context" 
   'lt2 x1 y1 x2 y2 = 
      (cic:/matita/LOGIC/WLT/defs/WLT.ind#xpointer(1/1) x1 y1 x2 y2).

notation "hvbox([a1, b1] break \lt [a2, b2])" 
  non associative with precedence 45
for @{ 'lt2 $a1 $b1 $a2 $b2 }.
