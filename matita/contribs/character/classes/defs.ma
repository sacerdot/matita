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

include "preamble.ma".

(* NOTE: OEIS sequence identifiers 
   P(n): A016777 "3n+1"
   T(n): A155504 "(3h+1)*3^(k+1)"
*)

inductive P: nat → Prop ≝
   | p1: P 1
   | p2: ∀i,j. T i → P j → P (i + j)
with T: nat → Prop ≝
   | t1: ∀i. P i → T (i * 3)
   | t2: ∀i. T i → T (i * 3)
.

inductive S: nat → Prop ≝
   | s1: ∀i. P i → S (i * 2)
   | s2: ∀i. T i → S (i * 2)
.
