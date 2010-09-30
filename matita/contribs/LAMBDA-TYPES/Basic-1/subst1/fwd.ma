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

include "Basic-1/subst1/defs.ma".

include "Basic-1/subst0/props.ma".

theorem subst1_gen_sort:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 
i v (TSort n) x) \to (eq T x (TSort n))))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst1 i v (TSort n) x)).(subst1_ind i v (TSort n) (\lambda (t: T).(eq T 
t (TSort n))) (refl_equal T (TSort n)) (\lambda (t2: T).(\lambda (H0: (subst0 
i v (TSort n) t2)).(subst0_gen_sort v t2 i n H0 (eq T t2 (TSort n))))) x 
H))))).
(* COMMENTS
Initial nodes: 89
END *)

theorem subst1_gen_lref:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 
i v (TLRef n) x) \to (or (eq T x (TLRef n)) (land (eq nat n i) (eq T x (lift 
(S n) O v))))))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst1 i v (TLRef n) x)).(subst1_ind i v (TLRef n) (\lambda (t: T).(or 
(eq T t (TLRef n)) (land (eq nat n i) (eq T t (lift (S n) O v))))) (or_introl 
(eq T (TLRef n) (TLRef n)) (land (eq nat n i) (eq T (TLRef n) (lift (S n) O 
v))) (refl_equal T (TLRef n))) (\lambda (t2: T).(\lambda (H0: (subst0 i v 
(TLRef n) t2)).(land_ind (eq nat n i) (eq T t2 (lift (S n) O v)) (or (eq T t2 
(TLRef n)) (land (eq nat n i) (eq T t2 (lift (S n) O v)))) (\lambda (H1: (eq 
nat n i)).(\lambda (H2: (eq T t2 (lift (S n) O v))).(or_intror (eq T t2 
(TLRef n)) (land (eq nat n i) (eq T t2 (lift (S n) O v))) (conj (eq nat n i) 
(eq T t2 (lift (S n) O v)) H1 H2)))) (subst0_gen_lref v t2 i n H0)))) x 
H))))).
(* COMMENTS
Initial nodes: 305
END *)

theorem subst1_gen_head:
 \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall 
(x: T).(\forall (i: nat).((subst1 i v (THead k u1 t1) x) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst1 (s k i) v t1 t2))))))))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(x: T).(\lambda (i: nat).(\lambda (H: (subst1 i v (THead k u1 t1) 
x)).(subst1_ind i v (THead k u1 t1) (\lambda (t: T).(ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T t (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t2: T).(subst1 (s k i) v t1 
t2))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead k u1 
t1) (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(subst1 (s k i) v t1 t2))) u1 t1 (refl_equal 
T (THead k u1 t1)) (subst1_refl i v u1) (subst1_refl (s k i) v t1)) (\lambda 
(t2: T).(\lambda (H0: (subst0 i v (THead k u1 t1) t2)).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T t2 (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 
u2))) (ex2 T (\lambda (t3: T).(eq T t2 (THead k u1 t3))) (\lambda (t3: 
T).(subst0 (s k i) v t1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i) v t1 t3)))) (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) (\lambda 
(u2: T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst1 (s k i) v t1 t3)))) (\lambda (H1: (ex2 T (\lambda (u2: T).(eq T t2 
(THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T t2 (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 u2)) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst1 (s k i) v t1 t3)))) (\lambda (x0: T).(\lambda 
(H2: (eq T t2 (THead k x0 t1))).(\lambda (H3: (subst0 i v u1 
x0)).(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst1 (s k i) v t1 t3))) x0 t1 H2 (subst1_single i v u1 
x0 H3) (subst1_refl (s k i) v t1))))) H1)) (\lambda (H1: (ex2 T (\lambda (t3: 
T).(eq T t2 (THead k u1 t3))) (\lambda (t3: T).(subst0 (s k i) v t1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead k u1 t3))) (\lambda (t3: 
T).(subst0 (s k i) v t1 t3)) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead k u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst1 (s k i) v t1 t3)))) (\lambda (x0: 
T).(\lambda (H2: (eq T t2 (THead k u1 x0))).(\lambda (H3: (subst0 (s k i) v 
t1 x0)).(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst1 (s k i) v t1 t3))) u1 x0 H2 (subst1_refl i v u1) 
(subst1_single (s k i) v t1 x0 H3))))) H1)) (\lambda (H1: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s k i) v t1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i) v t1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst1 (s k i) v t1 t3)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H2: (eq T t2 (THead k x0 x1))).(\lambda (H3: (subst0 i v u1 x0)).(\lambda 
(H4: (subst0 (s k i) v t1 x1)).(ex3_2_intro T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst1 
i v u1 u2))) (\lambda (_: T).(\lambda (t3: T).(subst1 (s k i) v t1 t3))) x0 
x1 H2 (subst1_single i v u1 x0 H3) (subst1_single (s k i) v t1 x1 H4))))))) 
H1)) (subst0_gen_head k v u1 t1 t2 i H0)))) x H))))))).
(* COMMENTS
Initial nodes: 1199
END *)

theorem subst1_gen_lift_lt:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst1 i (lift h d u) (lift h (S (plus i d)) t1) 
x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst1 i u t1 t2)))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (subst1 i (lift h d u) (lift h (S 
(plus i d)) t1) x)).(subst1_ind i (lift h d u) (lift h (S (plus i d)) t1) 
(\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h (S (plus i d)) t2))) 
(\lambda (t2: T).(subst1 i u t1 t2)))) (ex_intro2 T (\lambda (t2: T).(eq T 
(lift h (S (plus i d)) t1) (lift h (S (plus i d)) t2))) (\lambda (t2: 
T).(subst1 i u t1 t2)) t1 (refl_equal T (lift h (S (plus i d)) t1)) 
(subst1_refl i u t1)) (\lambda (t2: T).(\lambda (H0: (subst0 i (lift h d u) 
(lift h (S (plus i d)) t1) t2)).(ex2_ind T (\lambda (t3: T).(eq T t2 (lift h 
(S (plus i d)) t3))) (\lambda (t3: T).(subst0 i u t1 t3)) (ex2 T (\lambda 
(t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst1 i u t1 
t3))) (\lambda (x0: T).(\lambda (H1: (eq T t2 (lift h (S (plus i d)) 
x0))).(\lambda (H2: (subst0 i u t1 x0)).(ex_intro2 T (\lambda (t3: T).(eq T 
t2 (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst1 i u t1 t3)) x0 H1 
(subst1_single i u t1 x0 H2))))) (subst0_gen_lift_lt u t1 t2 i h d H0)))) x 
H))))))).
(* COMMENTS
Initial nodes: 395
END *)

theorem subst1_gen_lift_eq:
 \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst1 i u 
(lift h d t) x) \to (eq T x (lift h d t))))))))))
\def
 \lambda (t: T).(\lambda (u: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (i: nat).(\lambda (H: (le d i)).(\lambda (H0: (lt i (plus d 
h))).(\lambda (H1: (subst1 i u (lift h d t) x)).(subst1_ind i u (lift h d t) 
(\lambda (t0: T).(eq T t0 (lift h d t))) (refl_equal T (lift h d t)) (\lambda 
(t2: T).(\lambda (H2: (subst0 i u (lift h d t) t2)).(subst0_gen_lift_false t 
u t2 h d i H H0 H2 (eq T t2 (lift h d t))))) x H1))))))))).
(* COMMENTS
Initial nodes: 141
END *)

theorem subst1_gen_lift_ge:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst1 i u (lift h d t1) x) \to ((le (plus d h) 
i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst1 (minus i h) u t1 t2))))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (subst1 i u (lift h d t1) 
x)).(\lambda (H0: (le (plus d h) i)).(subst1_ind i u (lift h d t1) (\lambda 
(t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h d t2))) (\lambda (t2: 
T).(subst1 (minus i h) u t1 t2)))) (ex_intro2 T (\lambda (t2: T).(eq T (lift 
h d t1) (lift h d t2))) (\lambda (t2: T).(subst1 (minus i h) u t1 t2)) t1 
(refl_equal T (lift h d t1)) (subst1_refl (minus i h) u t1)) (\lambda (t2: 
T).(\lambda (H1: (subst0 i u (lift h d t1) t2)).(ex2_ind T (\lambda (t3: 
T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(subst0 (minus i h) u t1 t3)) 
(ex2 T (\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(subst1 
(minus i h) u t1 t3))) (\lambda (x0: T).(\lambda (H2: (eq T t2 (lift h d 
x0))).(\lambda (H3: (subst0 (minus i h) u t1 x0)).(ex_intro2 T (\lambda (t3: 
T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(subst1 (minus i h) u t1 t3)) x0 
H2 (subst1_single (minus i h) u t1 x0 H3))))) (subst0_gen_lift_ge u t1 t2 i h 
d H1 H0)))) x H)))))))).
(* COMMENTS
Initial nodes: 355
END *)

