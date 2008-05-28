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

include "Legacy-1/preamble.ma".

inductive eq (A: Set) (x: A): A \to Prop \def
| refl_equal: eq A x x.

inductive True: Prop \def
| I: True.

inductive land (A: Prop) (B: Prop): Prop \def
| conj: A \to (B \to (land A B)).

inductive or (A: Prop) (B: Prop): Prop \def
| or_introl: A \to (or A B)
| or_intror: B \to (or A B).

inductive ex (A: Set) (P: A \to Prop): Prop \def
| ex_intro: \forall (x: A).((P x) \to (ex A P)).

inductive ex2 (A: Set) (P: A \to Prop) (Q: A \to Prop): Prop \def
| ex_intro2: \forall (x: A).((P x) \to ((Q x) \to (ex2 A P Q))).

definition not:
 Prop \to Prop
\def
 \lambda (A: Prop).(A \to False).

inductive bool: Set \def
| true: bool
| false: bool.

inductive nat: Set \def
| O: nat
| S: nat \to nat.

inductive le (n: nat): nat \to Prop \def
| le_n: le n n
| le_S: \forall (m: nat).((le n m) \to (le n (S m))).

definition lt:
 nat \to (nat \to Prop)
\def
 \lambda (n: nat).(\lambda (m: nat).(le (S n) m)).

definition IsSucc:
 nat \to Prop
\def
 \lambda (n: nat).(match n with [O \Rightarrow False | (S _) \Rightarrow 
True]).

definition pred:
 nat \to nat
\def
 \lambda (n: nat).(match n with [O \Rightarrow O | (S u) \Rightarrow u]).

definition plus:
 nat \to (nat \to nat)
\def
 let rec plus (n: nat) on n: (nat \to nat) \def (\lambda (m: nat).(match n 
with [O \Rightarrow m | (S p) \Rightarrow (S (plus p m))])) in plus.

definition minus:
 nat \to (nat \to nat)
\def
 let rec minus (n: nat) on n: (nat \to nat) \def (\lambda (m: nat).(match n 
with [O \Rightarrow O | (S k) \Rightarrow (match m with [O \Rightarrow (S k) 
| (S l) \Rightarrow (minus k l)])])) in minus.

inductive Acc (A: Set) (R: A \to (A \to Prop)): A \to Prop \def
| Acc_intro: \forall (x: A).(((\forall (y: A).((R y x) \to (Acc A R y)))) \to 
(Acc A R x)).

definition well_founded:
 \forall (A: Set).(((A \to (A \to Prop))) \to Prop)
\def
 \lambda (A: Set).(\lambda (R: ((A \to (A \to Prop)))).(\forall (a: A).(Acc A 
R a))).

definition ltof:
 \forall (A: Set).(((A \to nat)) \to (A \to (A \to Prop)))
\def
 \lambda (A: Set).(\lambda (f: ((A \to nat))).(\lambda (a: A).(\lambda (b: 
A).(lt (f a) (f b))))).

