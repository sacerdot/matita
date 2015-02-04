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

include "ground_1/types/defs.ma".

theorem and3_rect:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P: 
Type[0]).(((P0 \to (P1 \to (P2 \to P)))) \to ((and3 P0 P1 P2) \to P)))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P: 
Type[0]).(\lambda (f: ((P0 \to (P1 \to (P2 \to P))))).(\lambda (a: (and3 P0 
P1 P2)).(match a with [(and3_intro x x0 x1) \Rightarrow (f x x0 x1)])))))).

theorem and3_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P: 
Prop).(((P0 \to (P1 \to (P2 \to P)))) \to ((and3 P0 P1 P2) \to P)))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P: 
Prop).(and3_rect P0 P1 P2 P)))).

theorem and4_rect:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P: Type[0]).(((P0 \to (P1 \to (P2 \to (P3 \to P))))) \to 
((and4 P0 P1 P2 P3) \to P))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P: Type[0]).(\lambda (f: ((P0 \to (P1 \to (P2 \to (P3 \to 
P)))))).(\lambda (a: (and4 P0 P1 P2 P3)).(match a with [(and4_intro x x0 x1 
x2) \Rightarrow (f x x0 x1 x2)]))))))).

theorem and4_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P: Prop).(((P0 \to (P1 \to (P2 \to (P3 \to P))))) \to ((and4 
P0 P1 P2 P3) \to P))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P: Prop).(and4_rect P0 P1 P2 P3 P))))).

theorem and5_rect:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P4: Prop).(\forall (P: Type[0]).(((P0 \to (P1 \to (P2 \to (P3 
\to (P4 \to P)))))) \to ((and5 P0 P1 P2 P3 P4) \to P)))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P4: Prop).(\lambda (P: Type[0]).(\lambda (f: ((P0 \to (P1 \to 
(P2 \to (P3 \to (P4 \to P))))))).(\lambda (a: (and5 P0 P1 P2 P3 P4)).(match a 
with [(and5_intro x x0 x1 x2 x3) \Rightarrow (f x x0 x1 x2 x3)])))))))).

theorem and5_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P4: Prop).(\forall (P: Prop).(((P0 \to (P1 \to (P2 \to (P3 
\to (P4 \to P)))))) \to ((and5 P0 P1 P2 P3 P4) \to P)))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P4: Prop).(\lambda (P: Prop).(and5_rect P0 P1 P2 P3 P4 
P)))))).

theorem or3_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P: 
Prop).(((P0 \to P)) \to (((P1 \to P)) \to (((P2 \to P)) \to ((or3 P0 P1 P2) 
\to P)))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P: 
Prop).(\lambda (f: ((P0 \to P))).(\lambda (f0: ((P1 \to P))).(\lambda (f1: 
((P2 \to P))).(\lambda (o: (or3 P0 P1 P2)).(match o with [(or3_intro0 x) 
\Rightarrow (f x) | (or3_intro1 x) \Rightarrow (f0 x) | (or3_intro2 x) 
\Rightarrow (f1 x)])))))))).

theorem or4_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P: Prop).(((P0 \to P)) \to (((P1 \to P)) \to (((P2 \to P)) 
\to (((P3 \to P)) \to ((or4 P0 P1 P2 P3) \to P)))))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P: Prop).(\lambda (f: ((P0 \to P))).(\lambda (f0: ((P1 \to 
P))).(\lambda (f1: ((P2 \to P))).(\lambda (f2: ((P3 \to P))).(\lambda (o: 
(or4 P0 P1 P2 P3)).(match o with [(or4_intro0 x) \Rightarrow (f x) | 
(or4_intro1 x) \Rightarrow (f0 x) | (or4_intro2 x) \Rightarrow (f1 x) | 
(or4_intro3 x) \Rightarrow (f2 x)])))))))))).

theorem or5_ind:
 \forall (P0: Prop).(\forall (P1: Prop).(\forall (P2: Prop).(\forall (P3: 
Prop).(\forall (P4: Prop).(\forall (P: Prop).(((P0 \to P)) \to (((P1 \to P)) 
\to (((P2 \to P)) \to (((P3 \to P)) \to (((P4 \to P)) \to ((or5 P0 P1 P2 P3 
P4) \to P)))))))))))
\def
 \lambda (P0: Prop).(\lambda (P1: Prop).(\lambda (P2: Prop).(\lambda (P3: 
Prop).(\lambda (P4: Prop).(\lambda (P: Prop).(\lambda (f: ((P0 \to 
P))).(\lambda (f0: ((P1 \to P))).(\lambda (f1: ((P2 \to P))).(\lambda (f2: 
((P3 \to P))).(\lambda (f3: ((P4 \to P))).(\lambda (o: (or5 P0 P1 P2 P3 
P4)).(match o with [(or5_intro0 x) \Rightarrow (f x) | (or5_intro1 x) 
\Rightarrow (f0 x) | (or5_intro2 x) \Rightarrow (f1 x) | (or5_intro3 x) 
\Rightarrow (f2 x) | (or5_intro4 x) \Rightarrow (f3 x)])))))))))))).

theorem ex3_ind:
 \forall (A0: Type[0]).(\forall (P0: ((A0 \to Prop))).(\forall (P1: ((A0 \to 
Prop))).(\forall (P2: ((A0 \to Prop))).(\forall (P: Prop).(((\forall (x0: 
A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to P))))) \to ((ex3 A0 P0 P1 P2) \to 
P))))))
\def
 \lambda (A0: Type[0]).(\lambda (P0: ((A0 \to Prop))).(\lambda (P1: ((A0 \to 
Prop))).(\lambda (P2: ((A0 \to Prop))).(\lambda (P: Prop).(\lambda (f: 
((\forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to P)))))).(\lambda 
(e: (ex3 A0 P0 P1 P2)).(match e with [(ex3_intro x x0 x1 x2) \Rightarrow (f x 
x0 x1 x2)]))))))).

theorem ex4_ind:
 \forall (A0: Type[0]).(\forall (P0: ((A0 \to Prop))).(\forall (P1: ((A0 \to 
Prop))).(\forall (P2: ((A0 \to Prop))).(\forall (P3: ((A0 \to 
Prop))).(\forall (P: Prop).(((\forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 
x0) \to ((P3 x0) \to P)))))) \to ((ex4 A0 P0 P1 P2 P3) \to P)))))))
\def
 \lambda (A0: Type[0]).(\lambda (P0: ((A0 \to Prop))).(\lambda (P1: ((A0 \to 
Prop))).(\lambda (P2: ((A0 \to Prop))).(\lambda (P3: ((A0 \to 
Prop))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).((P0 x0) \to ((P1 
x0) \to ((P2 x0) \to ((P3 x0) \to P))))))).(\lambda (e: (ex4 A0 P0 P1 P2 
P3)).(match e with [(ex4_intro x x0 x1 x2 x3) \Rightarrow (f x x0 x1 x2 
x3)])))))))).

theorem ex_2_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (P0: ((A0 \to (A1 \to 
Prop)))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) 
\to P)))) \to ((ex_2 A0 A1 P0) \to P)))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (P0: ((A0 \to (A1 \to 
Prop)))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: 
A1).((P0 x0 x1) \to P))))).(\lambda (e: (ex_2 A0 A1 P0)).(match e with 
[(ex_2_intro x x0 x1) \Rightarrow (f x x0 x1)])))))).

theorem ex2_2_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (P0: ((A0 \to (A1 \to 
Prop)))).(\forall (P1: ((A0 \to (A1 \to Prop)))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to 
P))))) \to ((ex2_2 A0 A1 P0 P1) \to P))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (P0: ((A0 \to (A1 \to 
Prop)))).(\lambda (P1: ((A0 \to (A1 \to Prop)))).(\lambda (P: Prop).(\lambda 
(f: ((\forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to 
P)))))).(\lambda (e: (ex2_2 A0 A1 P0 P1)).(match e with [(ex2_2_intro x x0 x1 
x2) \Rightarrow (f x x0 x1 x2)]))))))).

theorem ex3_2_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (P0: ((A0 \to (A1 \to 
Prop)))).(\forall (P1: ((A0 \to (A1 \to Prop)))).(\forall (P2: ((A0 \to (A1 
\to Prop)))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: A1).((P0 x0 
x1) \to ((P1 x0 x1) \to ((P2 x0 x1) \to P)))))) \to ((ex3_2 A0 A1 P0 P1 P2) 
\to P)))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (P0: ((A0 \to (A1 \to 
Prop)))).(\lambda (P1: ((A0 \to (A1 \to Prop)))).(\lambda (P2: ((A0 \to (A1 
\to Prop)))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: 
A1).((P0 x0 x1) \to ((P1 x0 x1) \to ((P2 x0 x1) \to P))))))).(\lambda (e: 
(ex3_2 A0 A1 P0 P1 P2)).(match e with [(ex3_2_intro x x0 x1 x2 x3) 
\Rightarrow (f x x0 x1 x2 x3)])))))))).

theorem ex4_2_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (P0: ((A0 \to (A1 \to 
Prop)))).(\forall (P1: ((A0 \to (A1 \to Prop)))).(\forall (P2: ((A0 \to (A1 
\to Prop)))).(\forall (P3: ((A0 \to (A1 \to Prop)))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to 
((P2 x0 x1) \to ((P3 x0 x1) \to P))))))) \to ((ex4_2 A0 A1 P0 P1 P2 P3) \to 
P))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (P0: ((A0 \to (A1 \to 
Prop)))).(\lambda (P1: ((A0 \to (A1 \to Prop)))).(\lambda (P2: ((A0 \to (A1 
\to Prop)))).(\lambda (P3: ((A0 \to (A1 \to Prop)))).(\lambda (P: 
Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 
x0 x1) \to ((P2 x0 x1) \to ((P3 x0 x1) \to P)))))))).(\lambda (e: (ex4_2 A0 
A1 P0 P1 P2 P3)).(match e with [(ex4_2_intro x x0 x1 x2 x3 x4) \Rightarrow (f 
x x0 x1 x2 x3 x4)]))))))))).

theorem ex_3_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P: Prop).(((\forall (x0: 
A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to P))))) \to ((ex_3 
A0 A1 A2 P0) \to P))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P: Prop).(\lambda (f: 
((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to 
P)))))).(\lambda (e: (ex_3 A0 A1 A2 P0)).(match e with [(ex_3_intro x x0 x1 
x2) \Rightarrow (f x x0 x1 x2)]))))))).

theorem ex2_3_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: 
A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to P)))))) \to 
((ex2_3 A0 A1 A2 P0 P1) \to P)))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall 
(x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to 
P))))))).(\lambda (e: (ex2_3 A0 A1 A2 P0 P1)).(match e with [(ex2_3_intro x 
x0 x1 x2 x3) \Rightarrow (f x x0 x1 x2 x3)])))))))).

theorem ex3_3_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) 
\to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to P))))))) \to ((ex3_3 A0 A1 A2 P0 P1 
P2) \to P))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P: 
Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: 
A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to 
P)))))))).(\lambda (e: (ex3_3 A0 A1 A2 P0 P1 P2)).(match e with [(ex3_3_intro 
x x0 x1 x2 x3 x4) \Rightarrow (f x x0 x1 x2 x3 x4)]))))))))).

theorem ex4_3_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P3: 
((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P: Prop).(((\forall (x0: 
A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to 
((P2 x0 x1 x2) \to ((P3 x0 x1 x2) \to P)))))))) \to ((ex4_3 A0 A1 A2 P0 P1 P2 
P3) \to P)))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P3: 
((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P: Prop).(\lambda (f: ((\forall 
(x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 
x2) \to ((P2 x0 x1 x2) \to ((P3 x0 x1 x2) \to P))))))))).(\lambda (e: (ex4_3 
A0 A1 A2 P0 P1 P2 P3)).(match e with [(ex4_3_intro x x0 x1 x2 x3 x4 x5) 
\Rightarrow (f x x0 x1 x2 x3 x4 x5)])))))))))).

theorem ex5_3_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P3: 
((A0 \to (A1 \to (A2 \to Prop))))).(\forall (P4: ((A0 \to (A1 \to (A2 \to 
Prop))))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall 
(x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to ((P3 x0 x1 
x2) \to ((P4 x0 x1 x2) \to P))))))))) \to ((ex5_3 A0 A1 A2 P0 P1 P2 P3 P4) 
\to P))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(P0: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P1: ((A0 \to (A1 \to (A2 
\to Prop))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P3: 
((A0 \to (A1 \to (A2 \to Prop))))).(\lambda (P4: ((A0 \to (A1 \to (A2 \to 
Prop))))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: 
A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) 
\to ((P3 x0 x1 x2) \to ((P4 x0 x1 x2) \to P)))))))))).(\lambda (e: (ex5_3 A0 
A1 A2 P0 P1 P2 P3 P4)).(match e with [(ex5_3_intro x x0 x1 x2 x3 x4 x5 x6) 
\Rightarrow (f x x0 x1 x2 x3 x4 x5 x6)]))))))))))).

theorem ex3_4_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (P0: ((A0 \to (A1 \to (A2 \to (A3 \to 
Prop)))))).(\forall (P1: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\forall 
(P2: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: 
A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to 
P)))))))) \to ((ex3_4 A0 A1 A2 A3 P0 P1 P2) \to P)))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (P0: ((A0 \to (A1 \to (A2 \to (A3 \to 
Prop)))))).(\lambda (P1: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\lambda 
(P2: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\lambda (P: Prop).(\lambda 
(f: ((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: 
A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to 
P))))))))).(\lambda (e: (ex3_4 A0 A1 A2 A3 P0 P1 P2)).(match e with 
[(ex3_4_intro x x0 x1 x2 x3 x4 x5) \Rightarrow (f x x0 x1 x2 x3 x4 
x5)])))))))))).

theorem ex4_4_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (P0: ((A0 \to (A1 \to (A2 \to (A3 \to 
Prop)))))).(\forall (P1: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\forall 
(P2: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\forall (P3: ((A0 \to (A1 
\to (A2 \to (A3 \to Prop)))))).(\forall (P: Prop).(((\forall (x0: 
A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).((P0 x0 x1 x2 x3) 
\to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to ((P3 x0 x1 x2 x3) \to 
P))))))))) \to ((ex4_4 A0 A1 A2 A3 P0 P1 P2 P3) \to P))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (P0: ((A0 \to (A1 \to (A2 \to (A3 \to 
Prop)))))).(\lambda (P1: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\lambda 
(P2: ((A0 \to (A1 \to (A2 \to (A3 \to Prop)))))).(\lambda (P3: ((A0 \to (A1 
\to (A2 \to (A3 \to Prop)))))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: 
A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).((P0 x0 x1 x2 x3) 
\to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to ((P3 x0 x1 x2 x3) \to 
P)))))))))).(\lambda (e: (ex4_4 A0 A1 A2 A3 P0 P1 P2 P3)).(match e with 
[(ex4_4_intro x x0 x1 x2 x3 x4 x5 x6) \Rightarrow (f x x0 x1 x2 x3 x4 x5 
x6)]))))))))))).

theorem ex4_5_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (A4: Type[0]).(\forall (P0: ((A0 \to (A1 \to (A2 \to 
(A3 \to (A4 \to Prop))))))).(\forall (P1: ((A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\forall (P3: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall 
(x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 
x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to 
P)))))))))) \to ((ex4_5 A0 A1 A2 A3 A4 P0 P1 P2 P3) \to P)))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (A4: Type[0]).(\lambda (P0: ((A0 \to (A1 \to (A2 \to 
(A3 \to (A4 \to Prop))))))).(\lambda (P1: ((A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\lambda (P3: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: 
A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 
x4) \to ((P1 x0 x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 
x4) \to P))))))))))).(\lambda (e: (ex4_5 A0 A1 A2 A3 A4 P0 P1 P2 P3)).(match 
e with [(ex4_5_intro x x0 x1 x2 x3 x4 x5 x6 x7) \Rightarrow (f x x0 x1 x2 x3 
x4 x5 x6 x7)])))))))))))).

theorem ex5_5_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (A4: Type[0]).(\forall (P0: ((A0 \to (A1 \to (A2 \to 
(A3 \to (A4 \to Prop))))))).(\forall (P1: ((A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\forall (P3: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\forall (P4: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\forall (P: Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall 
(x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 
x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to ((P4 x0 x1 
x2 x3 x4) \to P))))))))))) \to ((ex5_5 A0 A1 A2 A3 A4 P0 P1 P2 P3 P4) \to 
P))))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (A4: Type[0]).(\lambda (P0: ((A0 \to (A1 \to (A2 \to 
(A3 \to (A4 \to Prop))))))).(\lambda (P1: ((A0 \to (A1 \to (A2 \to (A3 \to 
(A4 \to Prop))))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\lambda (P3: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\lambda (P4: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to 
Prop))))))).(\lambda (P: Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: 
A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 
x4) \to ((P1 x0 x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 
x4) \to ((P4 x0 x1 x2 x3 x4) \to P)))))))))))).(\lambda (e: (ex5_5 A0 A1 A2 
A3 A4 P0 P1 P2 P3 P4)).(match e with [(ex5_5_intro x x0 x1 x2 x3 x4 x5 x6 x7 
x8) \Rightarrow (f x x0 x1 x2 x3 x4 x5 x6 x7 x8)]))))))))))))).

theorem ex6_6_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (A4: Type[0]).(\forall (A5: Type[0]).(\forall (P0: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P1: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P2: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P3: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P4: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P5: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: 
A3).(\forall (x4: A4).(\forall (x5: A5).((P0 x0 x1 x2 x3 x4 x5) \to ((P1 x0 
x1 x2 x3 x4 x5) \to ((P2 x0 x1 x2 x3 x4 x5) \to ((P3 x0 x1 x2 x3 x4 x5) \to 
((P4 x0 x1 x2 x3 x4 x5) \to ((P5 x0 x1 x2 x3 x4 x5) \to P))))))))))))) \to 
((ex6_6 A0 A1 A2 A3 A4 A5 P0 P1 P2 P3 P4 P5) \to P))))))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (A4: Type[0]).(\lambda (A5: Type[0]).(\lambda (P0: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P1: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P2: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P3: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P4: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P5: 
((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))))).(\lambda (P: 
Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: 
A2).(\forall (x3: A3).(\forall (x4: A4).(\forall (x5: A5).((P0 x0 x1 x2 x3 x4 
x5) \to ((P1 x0 x1 x2 x3 x4 x5) \to ((P2 x0 x1 x2 x3 x4 x5) \to ((P3 x0 x1 x2 
x3 x4 x5) \to ((P4 x0 x1 x2 x3 x4 x5) \to ((P5 x0 x1 x2 x3 x4 x5) \to 
P)))))))))))))).(\lambda (e: (ex6_6 A0 A1 A2 A3 A4 A5 P0 P1 P2 P3 P4 
P5)).(match e with [(ex6_6_intro x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) 
\Rightarrow (f x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)]))))))))))))))).

theorem ex6_7_ind:
 \forall (A0: Type[0]).(\forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall 
(A3: Type[0]).(\forall (A4: Type[0]).(\forall (A5: Type[0]).(\forall (A6: 
Type[0]).(\forall (P0: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 
\to Prop))))))))).(\forall (P1: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 
\to (A6 \to Prop))))))))).(\forall (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 
\to (A5 \to (A6 \to Prop))))))))).(\forall (P3: ((A0 \to (A1 \to (A2 \to (A3 
\to (A4 \to (A5 \to (A6 \to Prop))))))))).(\forall (P4: ((A0 \to (A1 \to (A2 
\to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))))).(\forall (P5: ((A0 \to (A1 
\to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))))).(\forall (P: 
Prop).(((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: 
A3).(\forall (x4: A4).(\forall (x5: A5).(\forall (x6: A6).((P0 x0 x1 x2 x3 x4 
x5 x6) \to ((P1 x0 x1 x2 x3 x4 x5 x6) \to ((P2 x0 x1 x2 x3 x4 x5 x6) \to ((P3 
x0 x1 x2 x3 x4 x5 x6) \to ((P4 x0 x1 x2 x3 x4 x5 x6) \to ((P5 x0 x1 x2 x3 x4 
x5 x6) \to P)))))))))))))) \to ((ex6_7 A0 A1 A2 A3 A4 A5 A6 P0 P1 P2 P3 P4 
P5) \to P)))))))))))))))
\def
 \lambda (A0: Type[0]).(\lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda 
(A3: Type[0]).(\lambda (A4: Type[0]).(\lambda (A5: Type[0]).(\lambda (A6: 
Type[0]).(\lambda (P0: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 
\to Prop))))))))).(\lambda (P1: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 
\to (A6 \to Prop))))))))).(\lambda (P2: ((A0 \to (A1 \to (A2 \to (A3 \to (A4 
\to (A5 \to (A6 \to Prop))))))))).(\lambda (P3: ((A0 \to (A1 \to (A2 \to (A3 
\to (A4 \to (A5 \to (A6 \to Prop))))))))).(\lambda (P4: ((A0 \to (A1 \to (A2 
\to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))))).(\lambda (P5: ((A0 \to (A1 
\to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))))).(\lambda (P: 
Prop).(\lambda (f: ((\forall (x0: A0).(\forall (x1: A1).(\forall (x2: 
A2).(\forall (x3: A3).(\forall (x4: A4).(\forall (x5: A5).(\forall (x6: 
A6).((P0 x0 x1 x2 x3 x4 x5 x6) \to ((P1 x0 x1 x2 x3 x4 x5 x6) \to ((P2 x0 x1 
x2 x3 x4 x5 x6) \to ((P3 x0 x1 x2 x3 x4 x5 x6) \to ((P4 x0 x1 x2 x3 x4 x5 x6) 
\to ((P5 x0 x1 x2 x3 x4 x5 x6) \to P))))))))))))))).(\lambda (e: (ex6_7 A0 A1 
A2 A3 A4 A5 A6 P0 P1 P2 P3 P4 P5)).(match e with [(ex6_7_intro x x0 x1 x2 x3 
x4 x5 x6 x7 x8 x9 x10 x11) \Rightarrow (f x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 
x11)])))))))))))))))).

