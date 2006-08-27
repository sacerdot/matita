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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/Base".

include "legacy/coq.ma".

axiom insert_eq: \forall (S: Set).(\forall (x: S).(\forall (P: ((S \to Prop))).(\forall (G: Prop).(((\forall (y: S).((P y) \to ((eq S y x) \to G)))) \to ((P x) \to G))))) .

axiom unintro: \forall (A: Set).(\forall (a: A).(\forall (P: ((A \to Prop))).(((\forall (x: A).(P x))) \to (P a)))) .

axiom xinduction: \forall (A: Set).(\forall (t: A).(\forall (P: ((A \to Prop))).(((\forall (x: A).((eq A t x) \to (P x)))) \to (P t)))) .

axiom nat_dec: \forall (n1: nat).(\forall (n2: nat).(or (eq nat n1 n2) ((eq nat n1 n2) \to (\forall (P: Prop).P)))) .

axiom simpl_plus_r: \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus m n) (plus p n)) \to (eq nat m p)))) .

axiom minus_plus_r: \forall (m: nat).(\forall (n: nat).(eq nat (minus (plus m n) n) m)) .

axiom plus_permute_2_in_3: \forall (x: nat).(\forall (y: nat).(\forall (z: nat).(eq nat (plus (plus x y) z) (plus (plus x z) y)))) .

axiom plus_permute_2_in_3_assoc: \forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq nat (plus (plus n h) k) (plus n (plus k h))))) .

axiom plus_O: \forall (x: nat).(\forall (y: nat).((eq nat (plus x y) O) \to (land (eq nat x O) (eq nat y O)))) .

axiom minus_Sx_SO: \forall (x: nat).(eq nat (minus (S x) (S O)) x) .

axiom eq_nat_dec: \forall (i: nat).(\forall (j: nat).(or (not (eq nat i j)) (eq nat i j))) .

axiom neq_eq_e: \forall (i: nat).(\forall (j: nat).(\forall (P: Prop).((((not (eq nat i j)) \to P)) \to ((((eq nat i j) \to P)) \to P)))) .

axiom le_false: \forall (m: nat).(\forall (n: nat).(\forall (P: Prop).((le m n) \to ((le (S n) m) \to P)))) .

axiom le_Sx_x: \forall (x: nat).((le (S x) x) \to (\forall (P: Prop).P)) .

axiom minus_le: \forall (x: nat).(\forall (y: nat).(le (minus x y) x)) .

axiom le_plus_minus_sym: \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus (minus m n) n)))) .

axiom le_minus_minus: \forall (x: nat).(\forall (y: nat).((le x y) \to (\forall (z: nat).((le y z) \to (le (minus y x) (minus z x)))))) .

axiom le_minus_plus: \forall (z: nat).(\forall (x: nat).((le z x) \to (\forall (y: nat).(eq nat (minus (plus x y) z) (plus (minus x z) y))))) .

axiom le_minus: \forall (x: nat).(\forall (z: nat).(\forall (y: nat).((le (plus x y) z) \to (le x (minus z y))))) .

axiom le_trans_plus_r: \forall (x: nat).(\forall (y: nat).(\forall (z: nat).((le (plus x y) z) \to (le y z)))) .

axiom le_gen_S: \forall (m: nat).(\forall (x: nat).((le (S m) x) \to (ex2 nat (\lambda (n: nat).(eq nat x (S n))) (\lambda (n: nat).(le m n))))) .

axiom lt_x_plus_x_Sy: \forall (x: nat).(\forall (y: nat).(lt x (plus x (S y)))) .

axiom simpl_lt_plus_r: \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((lt (plus n p) (plus m p)) \to (lt n m)))) .

axiom minus_x_Sy: \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq nat (minus x y) (S (minus x (S y)))))) .

axiom lt_plus_minus: \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus x (minus y (S x))))))) .

axiom lt_plus_minus_r: \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus (minus y (S x)) x))))) .

axiom minus_x_SO: \forall (x: nat).((lt O x) \to (eq nat x (S (minus x (S O))))) .

axiom le_x_pred_y: \forall (y: nat).(\forall (x: nat).((lt x y) \to (le x (pred y)))) .

axiom lt_le_minus: \forall (x: nat).(\forall (y: nat).((lt x y) \to (le x (minus y (S O))))) .

axiom lt_le_e: \forall (n: nat).(\forall (d: nat).(\forall (P: Prop).((((lt n d) \to P)) \to ((((le d n) \to P)) \to P)))) .

axiom lt_eq_e: \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) \to ((((eq nat x y) \to P)) \to ((le x y) \to P))))) .

axiom lt_eq_gt_e: \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) \to ((((eq nat x y) \to P)) \to ((((lt y x) \to P)) \to P))))) .

axiom lt_gen_xS: \forall (x: nat).(\forall (n: nat).((lt x (S n)) \to (or (eq nat x O) (ex2 nat (\lambda (m: nat).(eq nat x (S m))) (\lambda (m: nat).(lt m n)))))) .

axiom le_lt_false: \forall (x: nat).(\forall (y: nat).((le x y) \to ((lt y x) \to (\forall (P: Prop).P)))) .

axiom lt_neq: \forall (x: nat).(\forall (y: nat).((lt x y) \to (not (eq nat x y)))) .

axiom arith0: \forall (h2: nat).(\forall (d2: nat).(\forall (n: nat).((le (plus d2 h2) n) \to (\forall (h1: nat).(le (plus d2 h1) (minus (plus n h1) h2)))))) .

axiom O_minus: \forall (x: nat).(\forall (y: nat).((le x y) \to (eq nat (minus x y) O))) .

axiom minus_minus: \forall (z: nat).(\forall (x: nat).(\forall (y: nat).((le z x) \to ((le z y) \to ((eq nat (minus x z) (minus y z)) \to (eq nat x y)))))) .

axiom plus_plus: \forall (z: nat).(\forall (x1: nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 z) \to ((le x2 z) \to ((eq nat (plus (minus z x1) y1) (plus (minus z x2) y2)) \to (eq nat (plus x1 y2) (plus x2 y1))))))))) .

axiom ex2_sym: \forall (A: Set).(\forall (P: ((A \to Prop))).(\forall (Q: ((A \to Prop))).((ex2 A (\lambda (x: A).(P x)) (\lambda (x: A).(Q x))) \to (ex2 A (\lambda (x: A).(Q x)) (\lambda (x: A).(P x)))))) .

inductive and3 (P0:Prop) (P1:Prop) (P2:Prop): Prop \def
| and3_intro: P0 \to (P1 \to (P2 \to (and3 P0 P1 P2))).

inductive or3 (P0:Prop) (P1:Prop) (P2:Prop): Prop \def
| or3_intro0: P0 \to (or3 P0 P1 P2)
| or3_intro1: P1 \to (or3 P0 P1 P2)
| or3_intro2: P2 \to (or3 P0 P1 P2).

inductive or4 (P0:Prop) (P1:Prop) (P2:Prop) (P3:Prop): Prop \def
| or4_intro0: P0 \to (or4 P0 P1 P2 P3)
| or4_intro1: P1 \to (or4 P0 P1 P2 P3)
| or4_intro2: P2 \to (or4 P0 P1 P2 P3)
| or4_intro3: P3 \to (or4 P0 P1 P2 P3).

inductive ex3 (A0:Set) (P0:A0 \to Prop) (P1:A0 \to Prop) (P2:A0 \to Prop): Prop \def
| ex3_intro: \forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to (ex3 A0 P0 P1 P2)))).

inductive ex4 (A0:Set) (P0:A0 \to Prop) (P1:A0 \to Prop) (P2:A0 \to Prop) (P3:A0 \to Prop): Prop \def
| ex4_intro: \forall (x0: A0).((P0 x0) \to ((P1 x0) \to ((P2 x0) \to ((P3 x0) \to (ex4 A0 P0 P1 P2 P3))))).

inductive ex_2 (A0:Set) (A1:Set) (P0:A0 \to (A1 \to Prop)): Prop \def
| ex_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to (ex_2 A0 A1 P0))).

inductive ex2_2 (A0:Set) (A1:Set) (P0:A0 \to (A1 \to Prop)) (P1:A0 \to (A1 \to Prop)): Prop \def
| ex2_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to (ex2_2 A0 A1 P0 P1)))).

inductive ex3_2 (A0:Set) (A1:Set) (P0:A0 \to (A1 \to Prop)) (P1:A0 \to (A1 \to Prop)) (P2:A0 \to (A1 \to Prop)): Prop \def
| ex3_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to ((P2 x0 x1) \to (ex3_2 A0 A1 P0 P1 P2))))).

inductive ex4_2 (A0:Set) (A1:Set) (P0:A0 \to (A1 \to Prop)) (P1:A0 \to (A1 \to Prop)) (P2:A0 \to (A1 \to Prop)) (P3:A0 \to (A1 \to Prop)): Prop \def
| ex4_2_intro: \forall (x0: A0).(\forall (x1: A1).((P0 x0 x1) \to ((P1 x0 x1) \to ((P2 x0 x1) \to ((P3 x0 x1) \to (ex4_2 A0 A1 P0 P1 P2 P3)))))).

inductive ex_3 (A0:Set) (A1:Set) (A2:Set) (P0:A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to (ex_3 A0 A1 A2 P0)))).

inductive ex2_3 (A0:Set) (A1:Set) (A2:Set) (P0:A0 \to (A1 \to (A2 \to Prop))) (P1:A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex2_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to (ex2_3 A0 A1 A2 P0 P1))))).

inductive ex3_3 (A0:Set) (A1:Set) (A2:Set) (P0:A0 \to (A1 \to (A2 \to Prop))) (P1:A0 \to (A1 \to (A2 \to Prop))) (P2:A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex3_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to (ex3_3 A0 A1 A2 P0 P1 P2)))))).

inductive ex4_3 (A0:Set) (A1:Set) (A2:Set) (P0:A0 \to (A1 \to (A2 \to Prop))) (P1:A0 \to (A1 \to (A2 \to Prop))) (P2:A0 \to (A1 \to (A2 \to Prop))) (P3:A0 \to (A1 \to (A2 \to Prop))): Prop \def
| ex4_3_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).((P0 x0 x1 x2) \to ((P1 x0 x1 x2) \to ((P2 x0 x1 x2) \to ((P3 x0 x1 x2) \to (ex4_3 A0 A1 A2 P0 P1 P2 P3))))))).

inductive ex3_4 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P1:A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P2:A0 \to (A1 \to (A2 \to (A3 \to Prop)))): Prop \def
| ex3_4_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to (ex3_4 A0 A1 A2 A3 P0 P1 P2))))))).

inductive ex4_4 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P1:A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P2:A0 \to (A1 \to (A2 \to (A3 \to Prop)))) (P3:A0 \to (A1 \to (A2 \to (A3 \to Prop)))): Prop \def
| ex4_4_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).((P0 x0 x1 x2 x3) \to ((P1 x0 x1 x2 x3) \to ((P2 x0 x1 x2 x3) \to ((P3 x0 x1 x2 x3) \to (ex4_4 A0 A1 A2 A3 P0 P1 P2 P3)))))))).

inductive ex4_5 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (A4:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P1:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P2:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P3:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))): Prop \def
| ex4_5_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to (ex4_5 A0 A1 A2 A3 A4 P0 P1 P2 P3))))))))).

inductive ex5_5 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (A4:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P1:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P2:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P3:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))) (P4:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to Prop))))): Prop \def
| ex5_5_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).((P0 x0 x1 x2 x3 x4) \to ((P1 x0 x1 x2 x3 x4) \to ((P2 x0 x1 x2 x3 x4) \to ((P3 x0 x1 x2 x3 x4) \to ((P4 x0 x1 x2 x3 x4) \to (ex5_5 A0 A1 A2 A3 A4 P0 P1 P2 P3 P4)))))))))).

inductive ex6_6 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (A4:Set) (A5:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P1:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P2:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P3:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P4:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))) (P5:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to Prop)))))): Prop \def
| ex6_6_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).(\forall (x5: A5).((P0 x0 x1 x2 x3 x4 x5) \to ((P1 x0 x1 x2 x3 x4 x5) \to ((P2 x0 x1 x2 x3 x4 x5) \to ((P3 x0 x1 x2 x3 x4 x5) \to ((P4 x0 x1 x2 x3 x4 x5) \to ((P5 x0 x1 x2 x3 x4 x5) \to (ex6_6 A0 A1 A2 A3 A4 A5 P0 P1 P2 P3 P4 P5)))))))))))).

inductive ex6_7 (A0:Set) (A1:Set) (A2:Set) (A3:Set) (A4:Set) (A5:Set) (A6:Set) (P0:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))) (P1:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))) (P2:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))) (P3:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))) (P4:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))) (P5:A0 \to (A1 \to (A2 \to (A3 \to (A4 \to (A5 \to (A6 \to Prop))))))): Prop \def
| ex6_7_intro: \forall (x0: A0).(\forall (x1: A1).(\forall (x2: A2).(\forall (x3: A3).(\forall (x4: A4).(\forall (x5: A5).(\forall (x6: A6).((P0 x0 x1 x2 x3 x4 x5 x6) \to ((P1 x0 x1 x2 x3 x4 x5 x6) \to ((P2 x0 x1 x2 x3 x4 x5 x6) \to ((P3 x0 x1 x2 x3 x4 x5 x6) \to ((P4 x0 x1 x2 x3 x4 x5 x6) \to ((P5 x0 x1 x2 x3 x4 x5 x6) \to (ex6_7 A0 A1 A2 A3 A4 A5 A6 P0 P1 P2 P3 P4 P5))))))))))))).

definition blt: nat \to (nat \to bool) \def let rec blt (m: nat) (n: nat): bool \def (match n with [O \Rightarrow false | (S n0) \Rightarrow (match m with [O \Rightarrow true | (S m0) \Rightarrow (blt m0 n0)])]) in blt.

axiom lt_blt: \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq bool (blt y x) true))) .

axiom le_bge: \forall (x: nat).(\forall (y: nat).((le x y) \to (eq bool (blt y x) false))) .

axiom blt_lt: \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) true) \to (lt y x))) .

axiom bge_le: \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) false) \to (le x y))) .

