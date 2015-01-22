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

(* This file was automatically generated: do not edit *********************)

include "Ground-1/preamble.ma".

inductive and3 (P0: Prop) (P1: Prop) (P2: Prop): Prop \def
| and3_intro: P0 \to (P1 \to (P2 \to (and3 P0 P1 P2))).

inductive and4 (P0: Prop) (P1: Prop) (P2: Prop) (P3: Prop): Prop \def
| and4_intro: P0 \to (P1 \to (P2 \to (P3 \to (and4 P0 P1 P2 P3)))).

inductive and5 (P0: Prop) (P1: Prop) (P2: Prop) (P3: Prop) (P4: Prop): Prop 
\def
| and5_intro: P0 \to (P1 \to (P2 \to (P3 \to (P4 \to (and5 P0 P1 P2 P3 
P4))))).

inductive or3 (P0: Prop) (P1: Prop) (P2: Prop): Prop \def
| or3_intro0: P0 \to (or3 P0 P1 P2)
| or3_intro1: P1 \to (or3 P0 P1 P2)
| or3_intro2: P2 \to (or3 P0 P1 P2).

inductive or4 (P0: Prop) (P1: Prop) (P2: Prop) (P3: Prop): Prop \def
| or4_intro0: P0 \to (or4 P0 P1 P2 P3)
| or4_intro1: P1 \to (or4 P0 P1 P2 P3)
| or4_intro2: P2 \to (or4 P0 P1 P2 P3)
| or4_intro3: P3 \to (or4 P0 P1 P2 P3).

inductive or5 (P0: Prop) (P1: Prop) (P2: Prop) (P3: Prop) (P4: Prop): Prop 
\def
| or5_intro0: P0 \to (or5 P0 P1 P2 P3 P4)
| or5_intro1: P1 \to (or5 P0 P1 P2 P3 P4)
| or5_intro2: P2 \to (or5 P0 P1 P2 P3 P4)
| or5_intro3: P3 \to (or5 P0 P1 P2 P3 P4)
| or5_intro4: P4 \to (or5 P0 P1 P2 P3 P4).

inductive ex3 (A0: Set) (P0: A0 \to Prop) (P1: A0 \to Prop) (P2: A0 \to 
Prop): Prop \def
| ex3_intro: \forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to (ex3 A0 
P0 P1 P2)))).

inductive ex4 (A0: Set) (P0: A0 \to Prop) (P1: A0 \to Prop) (P2: A0 \to Prop) 
(P3: A0 \to Prop): Prop \def
| ex4_intro: \forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to ((P3 x0) 
\to (ex4 A0 P0 P1 P2 P3))))).

inductive ex_2 (A0: Set) (A1: Set) (P0: A0 \to (A1 \to Prop)): Prop \def
| ex_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to (ex_2 A0 A1 
P0))).

inductive ex2_2 (A0: Set) (A1: Set) (P0: A0 \to (A1 \to Prop)) (P1: A0 \to 
(A1 \to Prop)): Prop \def
| ex2_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) 
\to (ex2_2 A0 A1 P0 P1)))).

inductive ex3_2 (A0: Set) (A1: Set) (P0: A0 \to (A1 \to Prop)) (P1: A0 \to 
(A1 \to Prop)) (P2: A0 \to (A1 \to Prop)): Prop \def
| ex3_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) 
\to ((P2 x0 x1) \to (ex3_2 A0 A1 P0 P1 P2))))).

inductive ex4_2 (A0: Set) (A1: Set) (P0: A0 \to (A1 \to Prop)) (P1: A0 \to 
(A1 \to Prop)) (P2: A0 \to (A1 \to Prop)) (P3: A0 \to (A1 \to Prop)): Prop 
\def
| ex4_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) 
\to ((P2 x0 x1) \to ((P3 x0 x1) \to (ex4_2 A0 A1 P0 P1 P2 P3)))))).

inductive ex_3 (A0: Set) (A1: Set) (A2: Set) (P0: A0 \to (A1 \to (A2 \to 
Prop))): Prop \def
| ex_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 
x2) \to (ex_3 A0 A1 A2 P0)))).

inductive ex2_3 (A0: Set) (A1: Set) (A2: Set) (P0: A0 \to (A1 \to (A2 \to 
Prop))) (P1: A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex2_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 
x1 x2) \to ((P1 x0 x1 x2) \to (ex2_3 A0 A1 A2 P0 P1))))).

inductive ex3_3 (A0: Set) (A1: Set) (A2: Set) (P0: A0 \to (A1 \to (A2 \to 
Prop))) (P1: A0 \to (A1 \to (A2 \to Prop))) (P2: A0 \to (A1 \to (A2 \to 
Prop))): Prop \def
| ex3_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 
x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to (ex3_3 A0 A1 A2 P0 P1 
P2)))))).

inductive ex4_3 (A0: Set) (A1: Set) (A2: Set) (P0: A0 \to (A1 \to (A2 \to 
Prop))) (P1: A0 \to (A1 \to (A2 \to Prop))) (P2: A0 \to (A1 \to (A2 \to 
Prop))) (P3: A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex4_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 
x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to ((P3 x0 x1 x2) \to (ex4_3 A0 
A1 A2 P0 P1 P2 P3))))))).

inductive ex5_3 (A0: Set) (A1: Set) (A2: Set) (P0: A0 \to (A1 \to (A2 \to 
Prop))) (P1: A0 \to (A1 \to (A2 \to Prop))) (P2: A0 \to (A1 \to (A2 \to 
Prop))) (P3: A0 \to (A1 \to (A2 \to Prop))) (P4: A0 \to (A1 \to (A2 \to 
Prop))): Prop \def
| ex5_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 
x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to ((P3 x0 x1 x2) \to ((P4 x0 
x1 x2) \to (ex5_3 A0 A1 A2 P0 P1 P2 P3 P4)))))))).

inductive ex3_4 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (P0: A0 \to (A1 \to 
(A2 \to (A3 \to Prop)))) (P1: A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P2: A0 
\to (A1 \to (A2 \to (A3 \to Prop)))): Prop \def
| ex3_4_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to 
(ex3_4 A0 A1 A2 A3 P0 P1 P2))))))).

inductive ex4_4 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (P0: A0 \to (A1 \to 
(A2 \to (A3 \to Prop)))) (P1: A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P2: A0 
\to (A1 \to (A2 \to (A3 \to Prop)))) (P3: A0 \to (A1 \to (A2 \to (A3 \to 
Prop)))): Prop \def
| ex4_4_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to 
((P3 x0 x1 x2 x3) \to (ex4_4 A0 A1 A2 A3 P0 P1 P2 P3)))))))).

inductive ex4_5 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (A4: Set) (P0: A0 \to 
(A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P1: A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))) (P2: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P3: 
A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))): Prop \def
| ex4_5_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 x1 x2 x3 x4) \to 
((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to (ex4_5 A0 A1 A2 A3 A4 P0 P1 
P2 P3))))))))).

inductive ex5_5 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (A4: Set) (P0: A0 \to 
(A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P1: A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))) (P2: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P3: 
A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P4: A0 \to (A1 \to (A2 \to 
(A3 \to (A4 \to Prop))))): Prop \def
| ex5_5_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 x1 x2 x3 x4) \to 
((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to ((P4 x0 x1 x2 x3 x4) \to 
(ex5_5 A0 A1 A2 A3 A4 P0 P1 P2 P3 P4)))))))))).

inductive ex6_6 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (A4: Set) (A5: Set) 
(P0: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P1: A0 \to 
(A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P2: A0 \to (A1 \to (A2 
\to (A3 \to (A4 \to (A5 \to Prop)))))) (P3: A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to (A5 \to Prop)))))) (P4: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 
\to Prop)))))) (P5: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to 
Prop)))))): Prop \def
| ex6_6_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).(\forall (x4: A4).(\forall (x5: A5).((P0 x0 x1 x2 x3 x4 x5) \to ((P1 
x0 x1 x2 x3 x4 x5) \to ((P2 x0 x1 x2 x3 x4 x5) \to ((P3 x0 x1 x2 x3 x4 x5) 
\to ((P4 x0 x1 x2 x3 x4 x5) \to ((P5 x0 x1 x2 x3 x4 x5) \to (ex6_6 A0 A1 A2 
A3 A4 A5 P0 P1 P2 P3 P4 P5)))))))))))).

inductive ex6_7 (A0: Set) (A1: Set) (A2: Set) (A3: Set) (A4: Set) (A5: Set) 
(A6: Set) (P0: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))) (P1: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))) (P2: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))) (P3: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))) (P4: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))) (P5: A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to 
Prop))))))): Prop \def
| ex6_7_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall 
(x3: A3).(\forall (x4: A4).(\forall (x5: A5).(\forall (x6: A6).((P0 x0 x1 x2 
x3 x4 x5 x6) \to ((P1 x0 x1 x2 x3 x4 x5 x6) \to ((P2 x0 x1 x2 x3 x4 x5 x6) 
\to ((P3 x0 x1 x2 x3 x4 x5 x6) \to ((P4 x0 x1 x2 x3 x4 x5 x6) \to ((P5 x0 x1 
x2 x3 x4 x5 x6) \to (ex6_7 A0 A1 A2 A3 A4 A5 A6 P0 P1 P2 P3 P4 
P5))))))))))))).

