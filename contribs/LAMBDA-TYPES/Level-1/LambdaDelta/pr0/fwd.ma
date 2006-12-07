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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/fwd".

include "pr0/props.ma".

axiom pr0_gen_sort:
 \forall (x: T).(\forall (n: nat).((pr0 (TSort n) x) \to (eq T x (TSort n))))
.

axiom pr0_gen_lref:
 \forall (x: T).(\forall (n: nat).((pr0 (TLRef n) x) \to (eq T x (TLRef n))))
.

axiom pr0_gen_abst:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abst) u1 
t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))))))
.

axiom pr0_gen_appl:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Appl) u1 
t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2))))))))))))
.

axiom pr0_gen_cast:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Cast) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x)))))
.

axiom pr0_gen_abbr:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x))))))
.

axiom pr0_gen_void:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x))))))
.

axiom pr0_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr0 
(lift h d t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda 
(t2: T).(pr0 t1 t2)))))))
.

