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

include "legacy_1/coq/defs.ma".

theorem False_rect:
 \forall (P: Type[0]).(False \to P)
\def
 \lambda (P: Type[0]).(\lambda (f: False).(match f in False with [])).

theorem False_ind:
 \forall (P: Prop).(False \to P)
\def
 \lambda (P: Prop).(False_rect P).

theorem land_rect:
 \forall (A: Prop).(\forall (B: Prop).(\forall (P: Type[0]).(((A \to (B \to 
P))) \to ((land A B) \to P))))
\def
 \lambda (A: Prop).(\lambda (B: Prop).(\lambda (P: Type[0]).(\lambda (f: ((A 
\to (B \to P)))).(\lambda (a: (land A B)).(match a with [(conj x x0) 
\Rightarrow (f x x0)]))))).

theorem land_ind:
 \forall (A: Prop).(\forall (B: Prop).(\forall (P: Prop).(((A \to (B \to P))) 
\to ((land A B) \to P))))
\def
 \lambda (A: Prop).(\lambda (B: Prop).(\lambda (P: Prop).(land_rect A B P))).

theorem or_ind:
 \forall (A: Prop).(\forall (B: Prop).(\forall (P: Prop).(((A \to P)) \to 
(((B \to P)) \to ((or A B) \to P)))))
\def
 \lambda (A: Prop).(\lambda (B: Prop).(\lambda (P: Prop).(\lambda (f: ((A \to 
P))).(\lambda (f0: ((B \to P))).(\lambda (o: (or A B)).(match o with 
[(or_introl x) \Rightarrow (f x) | (or_intror x) \Rightarrow (f0 x)])))))).

theorem ex_ind:
 \forall (A: Type[0]).(\forall (P: ((A \to Prop))).(\forall (P0: 
Prop).(((\forall (x: A).((P x) \to P0))) \to ((ex A P) \to P0))))
\def
 \lambda (A: Type[0]).(\lambda (P: ((A \to Prop))).(\lambda (P0: 
Prop).(\lambda (f: ((\forall (x: A).((P x) \to P0)))).(\lambda (e: (ex A 
P)).(match e with [(ex_intro x x0) \Rightarrow (f x x0)]))))).

theorem ex2_ind:
 \forall (A: Type[0]).(\forall (P: ((A \to Prop))).(\forall (Q: ((A \to 
Prop))).(\forall (P0: Prop).(((\forall (x: A).((P x) \to ((Q x) \to P0)))) 
\to ((ex2 A P Q) \to P0)))))
\def
 \lambda (A: Type[0]).(\lambda (P: ((A \to Prop))).(\lambda (Q: ((A \to 
Prop))).(\lambda (P0: Prop).(\lambda (f: ((\forall (x: A).((P x) \to ((Q x) 
\to P0))))).(\lambda (e: (ex2 A P Q)).(match e with [(ex_intro2 x x0 x1) 
\Rightarrow (f x x0 x1)])))))).

theorem eq_rect:
 \forall (A: Type[0]).(\forall (x: A).(\forall (P: ((A \to Type[0]))).((P x) 
\to (\forall (y: A).((eq A x y) \to (P y))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (P: ((A \to 
Type[0]))).(\lambda (f: (P x)).(\lambda (y: A).(\lambda (e: (eq A x 
y)).(match e with [refl_equal \Rightarrow f])))))).

theorem eq_ind:
 \forall (A: Type[0]).(\forall (x: A).(\forall (P: ((A \to Prop))).((P x) \to 
(\forall (y: A).((eq A x y) \to (P y))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (P: ((A \to Prop))).(eq_rect A 
x P))).

let rec le_ind (n: nat) (P: (nat \to Prop)) (f: P n) (f0: (\forall (m: 
nat).((le n m) \to ((P m) \to (P (S m)))))) (n0: nat) (l: le n n0) on l: P n0 
\def match l with [le_n \Rightarrow f | (le_S m l0) \Rightarrow (f0 m l0 
((le_ind n P f f0) m l0))].

let rec Acc_ind (A: Type[0]) (R: (A \to (A \to Prop))) (P: (A \to Prop)) (f: 
(\forall (x: A).(((\forall (y: A).((R y x) \to (Acc A R y)))) \to (((\forall 
(y: A).((R y x) \to (P y)))) \to (P x))))) (a: A) (a0: Acc A R a) on a0: P a 
\def match a0 with [(Acc_intro x a1) \Rightarrow (f x a1 (\lambda (y: 
A).(\lambda (r: (R y x)).((Acc_ind A R P f) y (a1 y r)))))].

