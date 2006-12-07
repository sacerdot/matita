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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/fwd".

include "subst0/defs.ma".

include "lift/props.ma".

axiom subst0_gen_sort:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 
i v (TSort n) x) \to (\forall (P: Prop).P)))))
.

axiom subst0_gen_lref:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 
i v (TLRef n) x) \to (land (eq nat n i) (eq T x (lift (S n) O v)))))))
.

axiom subst0_gen_head:
 \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall 
(x: T).(\forall (i: nat).((subst0 i v (THead k u1 t1) x) \to (or3 (ex2 T 
(\lambda (u2: T).(eq T x (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 
u2))) (ex2 T (\lambda (t2: T).(eq T x (THead k u1 t2))) (\lambda (t2: 
T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))))))))
.

axiom subst0_gen_lift_lt:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst0 i (lift h d u) (lift h (S (plus i d)) t1) 
x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst0 i u t1 t2)))))))))
.

axiom subst0_gen_lift_false:
 \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst0 i u 
(lift h d t) x) \to (\forall (P: Prop).P)))))))))
.

axiom subst0_gen_lift_ge:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst0 i u (lift h d t1) x) \to ((le (plus d h) 
i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst0 (minus i h) u t1 t2))))))))))
.

