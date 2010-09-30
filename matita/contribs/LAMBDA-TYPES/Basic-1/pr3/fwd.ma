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

include "Basic-1/pr3/props.ma".

include "Basic-1/pr2/fwd.ma".

theorem pr3_gen_sort:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TSort n) x) \to 
(eq T x (TSort n)))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr3 c (TSort 
n) x)).(insert_eq T (TSort n) (\lambda (t: T).(pr3 c t x)) (\lambda (t: 
T).(eq T x t)) (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(pr3_ind c (\lambda 
(t: T).(\lambda (t0: T).((eq T t (TSort n)) \to (eq T t0 t)))) (\lambda (t: 
T).(\lambda (_: (eq T t (TSort n))).(refl_equal T t))) (\lambda (t2: 
T).(\lambda (t1: T).(\lambda (H1: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda 
(_: (pr3 c t2 t3)).(\lambda (H3: (((eq T t2 (TSort n)) \to (eq T t3 
t2)))).(\lambda (H4: (eq T t1 (TSort n))).(let H5 \def (eq_ind T t1 (\lambda 
(t: T).(pr2 c t t2)) H1 (TSort n) H4) in (eq_ind_r T (TSort n) (\lambda (t: 
T).(eq T t3 t)) (let H6 \def (eq_ind T t2 (\lambda (t: T).((eq T t (TSort n)) 
\to (eq T t3 t))) H3 (TSort n) (pr2_gen_sort c t2 n H5)) in (H6 (refl_equal T 
(TSort n)))) t1 H4))))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 253
END *)

theorem pr3_gen_abst:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: 
T).(pr3 (CHead c (Bind b) u) t1 t2))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Bind Abst) u1 t1) x)).(insert_eq T (THead (Bind Abst) u1 
t1) (\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 t2))))))) (\lambda (y: 
T).(\lambda (H0: (pr3 c y x)).(unintro T t1 (\lambda (t: T).((eq T y (THead 
(Bind Abst) u1 t)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) t t2)))))))) (unintro T u1 (\lambda (t: T).(\forall (x0: 
T).((eq T y (THead (Bind Abst) t x0)) \to (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c t u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x0 t2))))))))) (pr3_ind c 
(\lambda (t: T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: T).((eq T t 
(THead (Bind Abst) x0 x1)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T t0 (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x1 t2))))))))))) (\lambda (t: T).(\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H1: (eq T t (THead (Bind Abst) x0 
x1))).(ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T t (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
x1 t2))))) x0 x1 H1 (pr3_refl c x0) (\lambda (b: B).(\lambda (u: T).(pr3_refl 
(CHead c (Bind b) u) x1)))))))) (\lambda (t2: T).(\lambda (t3: T).(\lambda 
(H1: (pr2 c t3 t2)).(\lambda (t4: T).(\lambda (_: (pr3 c t2 t4)).(\lambda 
(H3: ((\forall (x0: T).(\forall (x1: T).((eq T t2 (THead (Bind Abst) x0 x1)) 
\to (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abst) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
x1 t5))))))))))).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t3 
(THead (Bind Abst) x0 x1))).(let H5 \def (eq_ind T t3 (\lambda (t: T).(pr2 c 
t t2)) H1 (THead (Bind Abst) x0 x1) H4) in (let H6 \def (pr2_gen_abst c x0 x1 
t2 H5) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead 
(Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead 
c (Bind b) u) x1 t5))))) (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
t4 (THead (Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) x1 t5)))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda 
(H7: (eq T t2 (THead (Bind Abst) x2 x3))).(\lambda (H8: (pr2 c x0 
x2)).(\lambda (H9: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x1 x3))))).(let H10 \def (eq_ind T t2 (\lambda (t: T).(\forall (x4: 
T).(\forall (x5: T).((eq T t (THead (Bind Abst) x4 x5)) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x4 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x5 
t5)))))))))) H3 (THead (Bind Abst) x2 x3) H7) in (let H11 \def (H10 x2 x3 
(refl_equal T (THead (Bind Abst) x2 x3))) in (ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abst) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x3 t5))))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5)))))) 
(\lambda (x4: T).(\lambda (x5: T).(\lambda (H12: (eq T t4 (THead (Bind Abst) 
x4 x5))).(\lambda (H13: (pr3 c x2 x4)).(\lambda (H14: ((\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x3 x5))))).(ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5))))) 
x4 x5 H12 (pr3_sing c x2 x0 H8 x4 H13) (\lambda (b: B).(\lambda (u: 
T).(pr3_sing (CHead c (Bind b) u) x3 x1 (H9 b u) x5 (H14 b u)))))))))) 
H11)))))))) H6)))))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 1261
END *)

theorem pr3_gen_cast:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 t2)))) (pr3 c 
t1 x))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Flat Cast) u1 t1) x)).(insert_eq T (THead (Flat Cast) u1 
t1) (\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 
t2)))) (pr3 c t1 x))) (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(unintro T 
t1 (\lambda (t: T).((eq T y (THead (Flat Cast) u1 t)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c t t2)))) (pr3 c t x)))) (unintro T u1 (\lambda (t: T).(\forall 
(x0: T).((eq T y (THead (Flat Cast) t x0)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c t u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c x0 
t2)))) (pr3 c x0 x))))) (pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall 
(x0: T).(\forall (x1: T).((eq T t (THead (Flat Cast) x0 x1)) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Flat Cast) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c x1 t2)))) (pr3 c x1 t0))))))) (\lambda (t: T).(\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H1: (eq T t (THead (Flat Cast) x0 
x1))).(eq_ind_r T (THead (Flat Cast) x0 x1) (\lambda (t0: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Flat Cast) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c x1 t2)))) (pr3 c x1 t0))) (or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T (THead (Flat Cast) x0 x1) (THead (Flat Cast) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 c x1 t2)))) (pr3 c x1 (THead (Flat Cast) x0 x1)) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Cast) 
x0 x1) (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c 
x0 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2))) x0 x1 (refl_equal T 
(THead (Flat Cast) x0 x1)) (pr3_refl c x0) (pr3_refl c x1))) t H1))))) 
(\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: 
T).(\lambda (H2: (pr3 c t2 t4)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: 
T).((eq T t2 (THead (Flat Cast) x0 x1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5)))) (pr3 c x1 t4))))))).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: 
(eq T t3 (THead (Flat Cast) x0 x1))).(let H5 \def (eq_ind T t3 (\lambda (t: 
T).(pr2 c t t2)) H1 (THead (Flat Cast) x0 x1) H4) in (let H6 \def 
(pr2_gen_cast c x0 x1 t2 H5) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T t2 (THead (Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr2 c x1 t5)))) (pr2 c 
x1 t2) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat 
Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4)) (\lambda (H7: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Flat Cast) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr2 c x1 t5))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T t2 (THead (Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr2 c x1 t5))) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4)) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H8: (eq T t2 (THead (Flat Cast) x2 x3))).(\lambda (H9: (pr2 
c x0 x2)).(\lambda (H10: (pr2 c x1 x3)).(let H11 \def (eq_ind T t2 (\lambda 
(t: T).(\forall (x4: T).(\forall (x5: T).((eq T t (THead (Flat Cast) x4 x5)) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat 
Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x4 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x5 t5)))) (pr3 c x5 t4)))))) H3 (THead (Flat Cast) 
x2 x3) H8) in (let H12 \def (H11 x2 x3 (refl_equal T (THead (Flat Cast) x2 
x3))) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x3 t5)))) (pr3 c x3 t4) (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4)) (\lambda (H13: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x3 
t5))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x3 t5))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5)))) (pr3 c x1 t4)) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H14: (eq T 
t4 (THead (Flat Cast) x4 x5))).(\lambda (H15: (pr3 c x2 x4)).(\lambda (H16: 
(pr3 c x3 x5)).(eq_ind_r T (THead (Flat Cast) x4 x5) (\lambda (t: T).(or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t (THead (Flat Cast) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 t))) (or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T (THead (Flat Cast) x4 x5) (THead 
(Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 (THead (Flat 
Cast) x4 x5)) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t5: T).(eq T (THead 
(Flat Cast) x4 x5) (THead (Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5))) x4 x5 
(refl_equal T (THead (Flat Cast) x4 x5)) (pr3_sing c x2 x0 H9 x4 H15) 
(pr3_sing c x3 x1 H10 x5 H16))) t4 H14)))))) H13)) (\lambda (H13: (pr3 c x3 
t4)).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4) (pr3_sing c 
x3 x1 H10 t4 H13))) H12)))))))) H7)) (\lambda (H7: (pr2 c x1 t2)).(or_intror 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4) (pr3_sing c t2 x1 H7 t4 
H2))) H6)))))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 2001
END *)

theorem pr3_gen_lift:
 \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).((pr3 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to 
(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr3 e t1 
t2))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H: (pr3 c (lift h d t1) x)).(insert_eq T (lift h d t1) 
(\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(\forall (e: C).((drop h d c e) 
\to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr3 e 
t1 t2)))))) (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(unintro T t1 (\lambda 
(t: T).((eq T y (lift h d t)) \to (\forall (e: C).((drop h d c e) \to (ex2 T 
(\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr3 e t t2))))))) 
(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (x0: T).((eq T t (lift h 
d x0)) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t2: T).(eq T 
t0 (lift h d t2))) (\lambda (t2: T).(pr3 e x0 t2))))))))) (\lambda (t: 
T).(\lambda (x0: T).(\lambda (H1: (eq T t (lift h d x0))).(\lambda (e: 
C).(\lambda (_: (drop h d c e)).(ex_intro2 T (\lambda (t2: T).(eq T t (lift h 
d t2))) (\lambda (t2: T).(pr3 e x0 t2)) x0 H1 (pr3_refl e x0))))))) (\lambda 
(t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: 
T).(\lambda (_: (pr3 c t2 t4)).(\lambda (H3: ((\forall (x0: T).((eq T t2 
(lift h d x0)) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t5: 
T).(eq T t4 (lift h d t5))) (\lambda (t5: T).(pr3 e x0 t5))))))))).(\lambda 
(x0: T).(\lambda (H4: (eq T t3 (lift h d x0))).(\lambda (e: C).(\lambda (H5: 
(drop h d c e)).(let H6 \def (eq_ind T t3 (\lambda (t: T).(pr2 c t t2)) H1 
(lift h d x0) H4) in (let H7 \def (pr2_gen_lift c x0 t2 h d H6 e H5) in 
(ex2_ind T (\lambda (t5: T).(eq T t2 (lift h d t5))) (\lambda (t5: T).(pr2 e 
x0 t5)) (ex2 T (\lambda (t5: T).(eq T t4 (lift h d t5))) (\lambda (t5: 
T).(pr3 e x0 t5))) (\lambda (x1: T).(\lambda (H8: (eq T t2 (lift h d 
x1))).(\lambda (H9: (pr2 e x0 x1)).(ex2_ind T (\lambda (t5: T).(eq T t4 (lift 
h d t5))) (\lambda (t5: T).(pr3 e x1 t5)) (ex2 T (\lambda (t5: T).(eq T t4 
(lift h d t5))) (\lambda (t5: T).(pr3 e x0 t5))) (\lambda (x2: T).(\lambda 
(H10: (eq T t4 (lift h d x2))).(\lambda (H11: (pr3 e x1 x2)).(ex_intro2 T 
(\lambda (t5: T).(eq T t4 (lift h d t5))) (\lambda (t5: T).(pr3 e x0 t5)) x2 
H10 (pr3_sing e x1 x0 H9 x2 H11))))) (H3 x1 H8 e H5))))) H7))))))))))))) y x 
H0)))) H)))))).
(* COMMENTS
Initial nodes: 689
END *)

theorem pr3_gen_lref:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TLRef n) x) \to 
(or (eq T x (TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T x (lift (S n) O v))))))))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr3 c (TLRef 
n) x)).(insert_eq T (TLRef n) (\lambda (t: T).(pr3 c t x)) (\lambda (t: 
T).(or (eq T x t) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T x (lift (S n) O v)))))))) (\lambda (y: T).(\lambda (H0: (pr3 c y 
x)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n)) \to (or 
(eq T t0 t) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T t0 (lift (S n) O v)))))))))) (\lambda (t: T).(\lambda (_: (eq T 
t (TLRef n))).(or_introl (eq T t t) (ex3_3 C T T (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: 
C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (v: T).(eq T t (lift (S n) O v)))))) (refl_equal T t)))) 
(\lambda (t2: T).(\lambda (t1: T).(\lambda (H1: (pr2 c t1 t2)).(\lambda (t3: 
T).(\lambda (H2: (pr3 c t2 t3)).(\lambda (H3: (((eq T t2 (TLRef n)) \to (or 
(eq T t3 t2) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T t3 (lift (S n) O v)))))))))).(\lambda (H4: (eq T t1 (TLRef 
n))).(let H5 \def (eq_ind T t1 (\lambda (t: T).(pr2 c t t2)) H1 (TLRef n) H4) 
in (eq_ind_r T (TLRef n) (\lambda (t: T).(or (eq T t3 t) (ex3_3 C T T 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead d (Bind 
Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T t3 (lift (S n) O 
v)))))))) (let H6 \def (pr2_gen_lref c t2 n H5) in (or_ind (eq T t2 (TLRef 
n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift (S n) O u))))) (or (eq T 
t3 (TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T t3 (lift (S n) O v))))))) (\lambda (H7: (eq T t2 (TLRef 
n))).(let H8 \def (eq_ind T t2 (\lambda (t: T).((eq T t (TLRef n)) \to (or 
(eq T t3 t) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T t3 (lift (S n) O v))))))))) H3 (TLRef n) H7) in (let H9 \def 
(eq_ind T t2 (\lambda (t: T).(pr3 c t t3)) H2 (TLRef n) H7) in (H8 
(refl_equal T (TLRef n)))))) (\lambda (H7: (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T t2 (lift (S n) O u)))))).(ex2_2_ind C T (\lambda (d: 
C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T t2 (lift (S n) O u)))) (or (eq T t3 (TLRef n)) 
(ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead 
d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u 
v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T t3 (lift (S n) O 
v))))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H8: (getl n c (CHead x0 
(Bind Abbr) x1))).(\lambda (H9: (eq T t2 (lift (S n) O x1))).(let H10 \def 
(eq_ind T t2 (\lambda (t: T).((eq T t (TLRef n)) \to (or (eq T t3 t) (ex3_3 C 
T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead d (Bind 
Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T t3 (lift (S n) O 
v))))))))) H3 (lift (S n) O x1) H9) in (let H11 \def (eq_ind T t2 (\lambda 
(t: T).(pr3 c t t3)) H2 (lift (S n) O x1) H9) in (let H12 \def (pr3_gen_lift 
c x1 t3 (S n) O H11 x0 (getl_drop Abbr c x0 x1 n H8)) in (ex2_ind T (\lambda 
(t4: T).(eq T t3 (lift (S n) O t4))) (\lambda (t4: T).(pr3 x0 x1 t4)) (or (eq 
T t3 (TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T t3 (lift (S n) O v))))))) (\lambda (x2: T).(\lambda (H13: (eq T 
t3 (lift (S n) O x2))).(\lambda (H14: (pr3 x0 x1 x2)).(or_intror (eq T t3 
(TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl 
n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: 
T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T t3 
(lift (S n) O v)))))) (ex3_3_intro C T T (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: 
C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (v: T).(eq T t3 (lift (S n) O v))))) x0 x1 x2 H8 H14 H13))))) 
H12)))))))) H7)) H6)) t1 H4))))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 1515
END *)

theorem pr3_gen_void:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) t1 t2)))))) (pr3 (CHead c (Bind Void) u1) t1 
(lift (S O) O x)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Bind Void) u1 t1) x)).(insert_eq T (THead (Bind Void) u1 
t1) (\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 t2)))))) (pr3 (CHead c 
(Bind Void) u1) t1 (lift (S O) O x)))) (\lambda (y: T).(\lambda (H0: (pr3 c y 
x)).(unintro T t1 (\lambda (t: T).((eq T y (THead (Bind Void) u1 t)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
t t2)))))) (pr3 (CHead c (Bind Void) u1) t (lift (S O) O x))))) (unintro T u1 
(\lambda (t: T).(\forall (x0: T).((eq T y (THead (Bind Void) t x0)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
x0 t2)))))) (pr3 (CHead c (Bind Void) t) x0 (lift (S O) O x)))))) (pr3_ind c 
(\lambda (t: T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: T).((eq T t 
(THead (Bind Void) x0 x1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T t0 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x1 t2)))))) (pr3 (CHead c (Bind Void) x0) x1 
(lift (S O) O t0)))))))) (\lambda (t: T).(\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H1: (eq T t (THead (Bind Void) x0 x1))).(eq_ind_r T (THead (Bind 
Void) x0 x1) (\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T t0 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x1 t2)))))) (pr3 (CHead c (Bind Void) x0) x1 
(lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead (Bind Void) x0 x1) (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t2)))))) (pr3 (CHead c 
(Bind Void) x0) x1 (lift (S O) O (THead (Bind Void) x0 x1))) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Bind Void) x0 x1) (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) x1 t2))))) x0 x1 (refl_equal T (THead (Bind Void) x0 x1)) 
(pr3_refl c x0) (\lambda (b: B).(\lambda (u: T).(pr3_refl (CHead c (Bind b) 
u) x1))))) t H1))))) (\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c 
t3 t2)).(\lambda (t4: T).(\lambda (H2: (pr3 c t2 t4)).(\lambda (H3: ((\forall 
(x0: T).(\forall (x1: T).((eq T t2 (THead (Bind Void) x0 x1)) \to (or (ex3_2 
T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5)))))) 
(pr3 (CHead c (Bind Void) x0) x1 (lift (S O) O t4)))))))).(\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H4: (eq T t3 (THead (Bind Void) x0 x1))).(let 
H5 \def (eq_ind T t3 (\lambda (t: T).(pr2 c t t2)) H1 (THead (Bind Void) x0 
x1) H4) in (let H6 \def (pr2_gen_void c x0 x1 t2 H5) in (or_ind (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Bind Void) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 t5)))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 (lift (S O) O 
t2)))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind 
Void) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
x1 t5)))))) (pr3 (CHead c (Bind Void) x0) x1 (lift (S O) O t4))) (\lambda 
(H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Bind Void) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x1 t5))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead 
(Bind Void) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead 
c (Bind b) u) x1 t5))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq 
T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) x1 t5)))))) (pr3 (CHead c (Bind Void) x0) x1 (lift (S O) 
O t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H8: (eq T t2 (THead (Bind 
Void) x2 x3))).(\lambda (H9: (pr2 c x0 x2)).(\lambda (H10: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 x3))))).(let H11 \def (eq_ind 
T t2 (\lambda (t: T).(\forall (x4: T).(\forall (x5: T).((eq T t (THead (Bind 
Void) x4 x5)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Bind Void) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x4 u2))) 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) x5 t5)))))) (pr3 (CHead c (Bind Void) x4) x5 (lift (S O) O 
t4))))))) H3 (THead (Bind Void) x2 x3) H8) in (let H12 \def (H11 x2 x3 
(refl_equal T (THead (Bind Void) x2 x3))) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x3 t5)))))) (pr3 (CHead c 
(Bind Void) x2) x3 (lift (S O) O t4)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5)))))) (pr3 (CHead c 
(Bind Void) x0) x1 (lift (S O) O t4))) (\lambda (H13: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x3 t5))))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x3 t5))))) 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
x1 t5)))))) (pr3 (CHead c (Bind Void) x0) x1 (lift (S O) O t4))) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H14: (eq T t4 (THead (Bind Void) x4 
x5))).(\lambda (H15: (pr3 c x2 x4)).(\lambda (H16: ((\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x3 x5))))).(or_introl (ex3_2 T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5)))))) (pr3 (CHead c 
(Bind Void) x0) x1 (lift (S O) O t4)) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5))))) x4 x5 H14 
(pr3_sing c x2 x0 H9 x4 H15) (\lambda (b: B).(\lambda (u: T).(pr3_sing (CHead 
c (Bind b) u) x3 x1 (H10 b u) x5 (H16 b u))))))))))) H13)) (\lambda (H13: 
(pr3 (CHead c (Bind Void) x2) x3 (lift (S O) O t4))).(or_intror (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Void) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x1 t5)))))) 
(pr3 (CHead c (Bind Void) x0) x1 (lift (S O) O t4)) (pr3_sing (CHead c (Bind 
Void) x0) x3 x1 (H10 Void x0) (lift (S O) O t4) (pr3_pr2_pr3_t c x2 x3 (lift 
(S O) O t4) (Bind Void) H13 x0 H9)))) H12)))))))) H7)) (\lambda (H7: 
((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 (lift (S O) O 
t2)))))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Bind Void) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) x1 t5)))))) (pr3 (CHead c (Bind Void) x0) x1 (lift (S O) O t4)) 
(pr3_sing (CHead c (Bind Void) x0) (lift (S O) O t2) x1 (H7 Void x0) (lift (S 
O) O t4) (pr3_lift (CHead c (Bind Void) x0) c (S O) O (drop_drop (Bind Void) 
O c c (drop_refl c) x0) t2 t4 H2)))) H6)))))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 2645
END *)

theorem pr3_gen_abbr:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) 
u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Bind Abbr) u1 t1) x)).(insert_eq T (THead (Bind Abbr) u1 
t1) (\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S 
O) O x)))) (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(unintro T t1 (\lambda 
(t: T).((eq T y (THead (Bind Abbr) u1 t)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) u1) t t2)))) (pr3 (CHead c (Bind Abbr) u1) t (lift (S O) 
O x))))) (unintro T u1 (\lambda (t: T).(\forall (x0: T).((eq T y (THead (Bind 
Abbr) t x0)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) t) x0 t2)))) (pr3 
(CHead c (Bind Abbr) t) x0 (lift (S O) O x)))))) (pr3_ind c (\lambda (t: 
T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: T).((eq T t (THead (Bind 
Abbr) x0 x1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 
(THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) x0) x1 t2)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t0)))))))) (\lambda (t: T).(\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H1: (eq T t (THead (Bind Abbr) x0 
x1))).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t0: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) x0) x1 t2)))) (pr3 (CHead c (Bind Abbr) x0) 
x1 (lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t2)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O (THead (Bind Abbr) x0 x1))) (ex3_2_intro T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t2)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t2))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 
x1)) (pr3_refl c x0) (pr3_refl (CHead c (Bind Abbr) x0) x1))) t H1))))) 
(\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: 
T).(\lambda (H2: (pr3 c t2 t4)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: 
T).((eq T t2 (THead (Bind Abbr) x0 x1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O t4)))))))).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t3 
(THead (Bind Abbr) x0 x1))).(let H5 \def (eq_ind T t3 (\lambda (t: T).(pr2 c 
t t2)) H1 (THead (Bind Abbr) x0 x1) H4) in (let H6 \def (pr2_gen_abbr c x0 x1 
t2 H5) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 
(THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) x1 t5))) (ex2 T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) x1 t5))) (ex3_2 T T (\lambda (y0: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: T).(\lambda (z: 
T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) x0) 
z t5)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 
(lift (S O) O t2)))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 
t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (H7: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Bind Abbr) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) x1 t5))) (ex2 T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: T).(pr2 (CHead 
c (Bind Abbr) u) x1 t5))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) x0) z 
t5))))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) x1 t5))) (ex2 T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) x1 t5))) (ex3_2 T T (\lambda (y0: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: T).(\lambda (z: 
T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) x0) 
z t5))))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H8: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (H9: (pr2 
c x0 x2)).(\lambda (H10: (or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) x1 x3))) (ex2 T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: T).(pr2 
(CHead c (Bind Abbr) u) x1 x3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: T).(\lambda (z: 
T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) x0) 
z x3)))))).(or3_ind (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x1 x3))) (ex2 T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: T).(pr2 (CHead c 
(Bind Abbr) u) x1 x3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) x0) z x3)))) 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c 
(Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (H11: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 x3))))).(let H12 \def (eq_ind 
T t2 (\lambda (t: T).(\forall (x4: T).(\forall (x5: T).((eq T t (THead (Bind 
Abbr) x4 x5)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x4 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x4) x5 t5)))) (pr3 
(CHead c (Bind Abbr) x4) x5 (lift (S O) O t4))))))) H3 (THead (Bind Abbr) x2 
x3) H8) in (let H13 \def (H12 x2 x3 (refl_equal T (THead (Bind Abbr) x2 x3))) 
in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind 
Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x2) x3 t5)))) (pr3 (CHead c 
(Bind Abbr) x2) x3 (lift (S O) O t4)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O t4))) (\lambda (H14: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x2) x3 
t5))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x2) x3 t5))) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c 
(Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H15: (eq T t4 (THead (Bind Abbr) x4 x5))).(\lambda (H16: (pr3 c 
x2 x4)).(\lambda (H17: (pr3 (CHead c (Bind Abbr) x2) x3 x5)).(eq_ind_r T 
(THead (Bind Abbr) x4 x5) (\lambda (t: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O t)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
(THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O (THead (Bind Abbr) x4 x5))) (ex3_2_intro T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T (THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 t5)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5))) x4 x5 (refl_equal T (THead (Bind Abbr) x4 
x5)) (pr3_sing c x2 x0 H9 x4 H16) (pr3_sing (CHead c (Bind Abbr) x0) x3 x1 
(H11 Abbr x0) x5 (pr3_pr2_pr3_t c x2 x3 x5 (Bind Abbr) H17 x0 H9)))) t4 
H15)))))) H14)) (\lambda (H14: (pr3 (CHead c (Bind Abbr) x2) x3 (lift (S O) O 
t4))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t4)) (pr3_sing (CHead c (Bind Abbr) 
x0) x3 x1 (H11 Abbr x0) (lift (S O) O t4) (pr3_pr2_pr3_t c x2 x3 (lift (S O) 
O t4) (Bind Abbr) H14 x0 H9)))) H13)))) (\lambda (H11: (ex2 T (\lambda (u: 
T).(pr0 x0 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) x1 
x3)))).(ex2_ind T (\lambda (u: T).(pr0 x0 u)) (\lambda (u: T).(pr2 (CHead c 
(Bind Abbr) u) x1 x3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 
t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (x4: 
T).(\lambda (H12: (pr0 x0 x4)).(\lambda (H13: (pr2 (CHead c (Bind Abbr) x4) 
x1 x3)).(let H14 \def (eq_ind T t2 (\lambda (t: T).(\forall (x5: T).(\forall 
(x6: T).((eq T t (THead (Bind Abbr) x5 x6)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x5 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x5) x6 t5)))) (pr3 (CHead c (Bind Abbr) x5) x6 (lift (S 
O) O t4))))))) H3 (THead (Bind Abbr) x2 x3) H8) in (let H15 \def (H14 x2 x3 
(refl_equal T (THead (Bind Abbr) x2 x3))) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x2) x3 t5)))) (pr3 (CHead c (Bind Abbr) x2) x3 (lift (S 
O) O t4)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (H16: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 (CHead c (Bind Abbr) x2) x3 t5))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x2) x3 t5))) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) 
x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda 
(x5: T).(\lambda (x6: T).(\lambda (H17: (eq T t4 (THead (Bind Abbr) x5 
x6))).(\lambda (H18: (pr3 c x2 x5)).(\lambda (H19: (pr3 (CHead c (Bind Abbr) 
x2) x3 x6)).(eq_ind_r T (THead (Bind Abbr) x5 x6) (\lambda (t: T).(or (ex3_2 
T T (\lambda (u2: T).(\lambda (t5: T).(eq T t (THead (Bind Abbr) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) 
x1 (lift (S O) O t)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T (THead (Bind Abbr) x5 x6) (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O (THead (Bind Abbr) x5 x6))) (ex3_2_intro T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T (THead (Bind Abbr) x5 x6) (THead (Bind Abbr) u2 t5)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5))) x5 x6 (refl_equal T (THead (Bind Abbr) x5 
x6)) (pr3_sing c x2 x0 H9 x5 H18) (pr3_t x3 x1 (CHead c (Bind Abbr) x0) 
(pr3_pr0_pr2_t x0 x4 H12 c x1 x3 (Bind Abbr) H13) x6 (pr3_pr2_pr3_t c x2 x3 
x6 (Bind Abbr) H19 x0 H9)))) t4 H17)))))) H16)) (\lambda (H16: (pr3 (CHead c 
(Bind Abbr) x2) x3 (lift (S O) O t4))).(or_intror (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O t4)) (pr3_t x3 x1 (CHead c (Bind Abbr) x0) (pr3_pr0_pr2_t x0 x4 H12 c x1 
x3 (Bind Abbr) H13) (lift (S O) O t4) (pr3_pr2_pr3_t c x2 x3 (lift (S O) O 
t4) (Bind Abbr) H16 x0 H9)))) H15)))))) H11)) (\lambda (H11: (ex3_2 T T 
(\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) x0) x1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) x0) z x3))))).(ex3_2_ind T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) x0) x1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) x0) z x3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq 
T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 
t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H12: (pr2 (CHead c (Bind Abbr) x0) x1 
x4)).(\lambda (H13: (pr0 x4 x5)).(\lambda (H14: (pr2 (CHead c (Bind Abbr) x0) 
x5 x3)).(let H15 \def (eq_ind T t2 (\lambda (t: T).(\forall (x6: T).(\forall 
(x7: T).((eq T t (THead (Bind Abbr) x6 x7)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x6 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x6) x7 t5)))) (pr3 (CHead c (Bind Abbr) x6) x7 (lift (S 
O) O t4))))))) H3 (THead (Bind Abbr) x2 x3) H8) in (let H16 \def (H15 x2 x3 
(refl_equal T (THead (Bind Abbr) x2 x3))) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x2) x3 t5)))) (pr3 (CHead c (Bind Abbr) x2) x3 (lift (S 
O) O t4)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda (H17: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 (CHead c (Bind Abbr) x2) x3 t5))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x2) x3 t5))) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) 
x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4))) (\lambda 
(x6: T).(\lambda (x7: T).(\lambda (H18: (eq T t4 (THead (Bind Abbr) x6 
x7))).(\lambda (H19: (pr3 c x2 x6)).(\lambda (H20: (pr3 (CHead c (Bind Abbr) 
x2) x3 x7)).(eq_ind_r T (THead (Bind Abbr) x6 x7) (\lambda (t: T).(or (ex3_2 
T T (\lambda (u2: T).(\lambda (t5: T).(eq T t (THead (Bind Abbr) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) 
x1 (lift (S O) O t)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T (THead (Bind Abbr) x6 x7) (THead (Bind Abbr) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S 
O) O (THead (Bind Abbr) x6 x7))) (ex3_2_intro T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T (THead (Bind Abbr) x6 x7) (THead (Bind Abbr) u2 t5)))) (\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 
(CHead c (Bind Abbr) x0) x1 t5))) x6 x7 (refl_equal T (THead (Bind Abbr) x6 
x7)) (pr3_sing c x2 x0 H9 x6 H19) (pr3_sing (CHead c (Bind Abbr) x0) x4 x1 
H12 x7 (pr3_sing (CHead c (Bind Abbr) x0) x5 x4 (pr2_free (CHead c (Bind 
Abbr) x0) x4 x5 H13) x7 (pr3_sing (CHead c (Bind Abbr) x0) x3 x5 H14 x7 
(pr3_pr2_pr3_t c x2 x3 x7 (Bind Abbr) H20 x0 H9)))))) t4 H18)))))) H17)) 
(\lambda (H17: (pr3 (CHead c (Bind Abbr) x2) x3 (lift (S O) O 
t4))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) x0) x1 t5)))) (pr3 
(CHead c (Bind Abbr) x0) x1 (lift (S O) O t4)) (pr3_sing (CHead c (Bind Abbr) 
x0) x4 x1 H12 (lift (S O) O t4) (pr3_sing (CHead c (Bind Abbr) x0) x5 x4 
(pr2_free (CHead c (Bind Abbr) x0) x4 x5 H13) (lift (S O) O t4) (pr3_sing 
(CHead c (Bind Abbr) x0) x3 x5 H14 (lift (S O) O t4) (pr3_pr2_pr3_t c x2 x3 
(lift (S O) O t4) (Bind Abbr) H17 x0 H9)))))) H16)))))))) H11)) H10)))))) 
H7)) (\lambda (H7: ((\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
x1 (lift (S O) O t2)))))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T t4 (THead (Bind Abbr) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 (CHead c (Bind Abbr) 
x0) x1 t5)))) (pr3 (CHead c (Bind Abbr) x0) x1 (lift (S O) O t4)) (pr3_sing 
(CHead c (Bind Abbr) x0) (lift (S O) O t2) x1 (H7 Abbr x0) (lift (S O) O t4) 
(pr3_lift (CHead c (Bind Abbr) x0) c (S O) O (drop_drop (Bind Abbr) O c c 
(drop_refl c) x0) t2 t4 H2)))) H6)))))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 5983
END *)

theorem pr3_gen_appl:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Flat Appl) u1 t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 t2)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u2 t2) x))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c u1 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) x))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Flat Appl) u1 t1) x)).(insert_eq T (THead (Flat Appl) u1 
t1) (\lambda (t: T).(pr3 c t x)) (\lambda (_: T).(or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 
t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) x))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
x))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))))) (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(unintro T t1 
(\lambda (t: T).((eq T y (THead (Flat Appl) u1 t)) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c t t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) x))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c t (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c t (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2)) x))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))))) (unintro T u1 (\lambda 
(t: T).(\forall (x0: T).((eq T y (THead (Flat Appl) t x0)) \to (or3 (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr3 c x0 t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) x))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))) (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x0 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c x0 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
x))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))))))) (pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall 
(x0: T).(\forall (x1: T).((eq T t (THead (Flat Appl) x0 x1)) \to (or3 (ex3_2 
T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 c x1 t2)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind Abbr) u2 t2) t0))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t0))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))))))))) 
(\lambda (t: T).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T t 
(THead (Flat Appl) x0 x1))).(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda 
(t0: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u2 t2) t0))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t0))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))))) 
(or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat 
Appl) x0 x1) (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 
c (THead (Bind Abbr) u2 t2) (THead (Flat Appl) x0 x1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
(THead (Flat Appl) x0 x1)))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T (THead (Flat Appl) x0 x1) (THead (Flat Appl) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 c x1 t2))) x0 x1 (refl_equal T (THead (Flat Appl) x0 
x1)) (pr3_refl c x0) (pr3_refl c x1))) t H1))))) (\lambda (t2: T).(\lambda 
(t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: T).(\lambda (H2: (pr3 c t2 
t4)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: T).((eq T t2 (THead (Flat 
Appl) x0 x1)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 
z2)))))))))))))).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t3 
(THead (Flat Appl) x0 x1))).(let H5 \def (eq_ind T t3 (\lambda (t: T).(pr2 c 
t t2)) H1 (THead (Flat Appl) x0 x1) H4) in (let H6 \def (pr2_gen_appl c x0 x1 
t2 H5) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr2 c x1 t5)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T x1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t5: T).(eq T t2 (THead (Bind Abbr) u2 t5)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead 
(Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (or3 (ex3_2 
T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Flat Appl) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr2 c x1 t5))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t2 (THead (Flat Appl) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr2 c x1 
t5))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat 
Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) 
t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 
c x0 u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x2: T).(\lambda (x3: T).(\lambda (H8: (eq T t2 (THead (Flat Appl) x2 
x3))).(\lambda (H9: (pr2 c x0 x2)).(\lambda (H10: (pr2 c x1 x3)).(let H11 
\def (eq_ind T t2 (\lambda (t: T).(\forall (x4: T).(\forall (x5: T).((eq T t 
(THead (Flat Appl) x4 x5)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x4 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x5 t5)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 
c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x4 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x5 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x5 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x4 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))))))) H3 
(THead (Flat Appl) x2 x3) H8) in (let H12 \def (eq_ind T t2 (\lambda (t: 
T).(pr3 c t t4)) H2 (THead (Flat Appl) x2 x3) H8) in (let H13 \def (H11 x2 x3 
(refl_equal T (THead (Flat Appl) x2 x3))) in (or3_ind (ex3_2 T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x3 
t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x3 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c x3 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
t4))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(H14: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat 
Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x3 t5))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x3 
t5))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat 
Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) 
t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 
c x0 u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H15: (eq T t4 (THead (Flat Appl) x4 
x5))).(\lambda (H16: (pr3 c x2 x4)).(\lambda (H17: (pr3 c x3 x5)).(eq_ind_r T 
(THead (Flat Appl) x4 x5) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t (THead (Flat Appl) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))) 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
t))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T (THead (Flat Appl) x4 x5) (THead (Flat Appl) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) (THead (Flat Appl) x4 
x5)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) (THead (Flat Appl) x4 x5)))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t5: T).(eq T (THead (Flat Appl) 
x4 x5) (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c 
x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5))) x4 x5 (refl_equal T 
(THead (Flat Appl) x4 x5)) (pr3_sing c x2 x0 H9 x4 H16) (pr3_sing c x3 x1 H10 
x5 H17))) t4 H15)))))) H14)) (\lambda (H14: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x3 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5))))))))).(ex4_4_ind T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 
c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x2 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x3 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5))))))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x4: T).(\lambda (x5: T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (H15: 
(pr3 c (THead (Bind Abbr) x6 x7) t4)).(\lambda (H16: (pr3 c x2 x6)).(\lambda 
(H17: (pr3 c x3 (THead (Bind Abst) x4 x5))).(\lambda (H18: ((\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) x5 x7))))).(or3_intro1 (ex3_2 T 
T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (ex4_4_intro 
T T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: 
T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 
t5))))))) x4 x5 x6 x7 H15 (pr3_sing c x2 x0 H9 x6 H16) (pr3_sing c x3 x1 H10 
(THead (Bind Abst) x4 x5) H17) H18)))))))))) H14)) (\lambda (H14: (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c x3 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x2 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x3 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2)) t4))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 
c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x4: B).(\lambda (x5: T).(\lambda (x6: T).(\lambda (x7: T).(\lambda (x8: 
T).(\lambda (x9: T).(\lambda (H15: (not (eq B x4 Abst))).(\lambda (H16: (pr3 
c x3 (THead (Bind x4) x5 x6))).(\lambda (H17: (pr3 c (THead (Bind x4) x9 
(THead (Flat Appl) (lift (S O) O x8) x7)) t4)).(\lambda (H18: (pr3 c x2 
x8)).(\lambda (H19: (pr3 c x5 x9)).(\lambda (H20: (pr3 (CHead c (Bind x4) x9) 
x6 x7)).(or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (ex6_6_intro 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))) 
x4 x5 x6 x7 x8 x9 H15 (pr3_sing c x3 x1 H10 (THead (Bind x4) x5 x6) H16) H17 
(pr3_sing c x2 x0 H9 x8 H18) H19 H20)))))))))))))) H14)) H13))))))))) H7)) 
(\lambda (H7: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Bind 
Abbr) u2 t5)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x0 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t5))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(eq T t2 (THead (Bind 
Abbr) u2 t5)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x0 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t5))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H8: (eq 
T x1 (THead (Bind Abst) x2 x3))).(\lambda (H9: (eq T t2 (THead (Bind Abbr) x4 
x5))).(\lambda (H10: (pr2 c x0 x4)).(\lambda (H11: ((\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) x3 x5))))).(eq_ind_r T (THead (Bind Abst) x2 
x3) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c t t5)))) (ex4_4 T T T T 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c 
(THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c t (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c t (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))))) (let H12 
\def (eq_ind T t2 (\lambda (t: T).(\forall (x6: T).(\forall (x7: T).((eq T t 
(THead (Flat Appl) x6 x7)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T t4 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x6 u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x7 t5)))) (ex4_4 T 
T T T (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 
c (THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x6 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x7 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x7 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x6 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))))))) H3 
(THead (Bind Abbr) x4 x5) H9) in (let H13 \def (eq_ind T t2 (\lambda (t: 
T).(pr3 c t t4)) H2 (THead (Bind Abbr) x4 x5) H9) in (or3_intro1 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c (THead (Bind Abst) x2 x3) t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) x2 x3) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) x2 x3) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (ex4_4_intro T T T T 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c 
(THead (Bind Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind Abst) x2 x3) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t5))))))) x2 x3 x4 x5 H13 (pr3_pr2 c x0 x4 H10) (pr3_refl c (THead (Bind 
Abst) x2 x3)) (\lambda (b: B).(\lambda (u: T).(pr3_pr2 (CHead c (Bind b) u) 
x3 x5 (H11 b u)))))))) x1 H8))))))))) H7)) (\lambda (H7: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T x1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))).(ex6_6_ind 
B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T x1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) 
t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 
c x0 u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c x1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c x1 (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x0 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x2: B).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (x6: 
T).(\lambda (x7: T).(\lambda (H8: (not (eq B x2 Abst))).(\lambda (H9: (eq T 
x1 (THead (Bind x2) x3 x4))).(\lambda (H10: (eq T t2 (THead (Bind x2) x7 
(THead (Flat Appl) (lift (S O) O x6) x5)))).(\lambda (H11: (pr2 c x0 
x6)).(\lambda (H12: (pr2 c x3 x7)).(\lambda (H13: (pr2 (CHead c (Bind x2) x7) 
x4 x5)).(eq_ind_r T (THead (Bind x2) x3 x4) (\lambda (t: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c t t5)))) (ex4_4 T T T T (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind Abbr) u2 t5) t4))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(pr3 c t (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c t (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))))) (let H14 \def (eq_ind T t2 
(\lambda (t: T).(\forall (x8: T).(\forall (x9: T).((eq T t (THead (Flat Appl) 
x8 x9)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead 
(Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x8 u2))) 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x9 t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x8 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c x9 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t5: T).(\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) z1 t5)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 
c x9 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c x8 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) y2) z1 z2))))))))))))) H3 
(THead (Bind x2) x7 (THead (Flat Appl) (lift (S O) O x6) x5)) H10) in (let 
H15 \def (eq_ind T t2 (\lambda (t: T).(pr3 c t t4)) H2 (THead (Bind x2) x7 
(THead (Flat Appl) (lift (S O) O x6) x5)) H10) in (or3_intro2 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Appl) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c (THead (Bind x2) x3 x4) t5)))) (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t5: T).(pr3 c (THead (Bind 
Abbr) u2 t5) t4))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))))) (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(pr3 c (THead (Bind x2) x3 x4) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
z1 t5)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(pr3 c (THead (Bind x2) x3 x4) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u2) z2)) t4))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 (CHead c (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(pr3 c 
(THead (Bind x2) x3 x4) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2)) 
t4))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 (CHead c (Bind b) 
y2) z1 z2))))))) x2 x3 x4 x5 x6 x7 H8 (pr3_refl c (THead (Bind x2) x3 x4)) 
H15 (pr3_pr2 c x0 x6 H11) (pr3_pr2 c x3 x7 H12) (pr3_pr2 (CHead c (Bind x2) 
x7) x4 x5 H13))))) x1 H9))))))))))))) H7)) H6)))))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 12691
END *)

theorem pr3_gen_bind:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (u1: 
T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind b) u1 t1) x) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind b) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind b) u1) t1 t2)))) (pr3 (CHead c (Bind 
b) u1) t1 (lift (S O) O x)))))))))
\def
 \lambda (b: B).(B_ind (\lambda (b0: B).((not (eq B b0 Abst)) \to (\forall 
(c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c (THead (Bind 
b0) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind b0) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind b0) u1) t1 t2)))) (pr3 
(CHead c (Bind b0) u1) t1 (lift (S O) O x)))))))))) (\lambda (_: (not (eq B 
Abbr Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: 
T).(\lambda (H0: (pr3 c (THead (Bind Abbr) u1 t1) x)).(let H1 \def 
(pr3_gen_abbr c u1 t1 x H0) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) 
u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x)) (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O x))) (\lambda (H2: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 
t2))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O x))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H3: (eq T x 
(THead (Bind Abbr) x0 x1))).(\lambda (H4: (pr3 c u1 x0)).(\lambda (H5: (pr3 
(CHead c (Bind Abbr) u1) t1 x1)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Abbr) u1) t1 t2)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S 
O) O x)) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2))) x0 x1 
H3 H4 H5))))))) H2)) (\lambda (H2: (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S 
O) O x))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Abbr) u1) t1 t2)))) (pr3 
(CHead c (Bind Abbr) u1) t1 (lift (S O) O x)) H2)) H1)))))))) (\lambda (H: 
(not (eq B Abst Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: 
T).(\lambda (x: T).(\lambda (_: (pr3 c (THead (Bind Abst) u1 t1) x)).(let H1 
\def (match (H (refl_equal B Abst)) in False return (\lambda (_: False).(or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr3 (CHead c (Bind Abst) u1) t1 t2)))) (pr3 (CHead c 
(Bind Abst) u1) t1 (lift (S O) O x)))) with []) in H1))))))) (\lambda (_: 
(not (eq B Void Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: 
T).(\lambda (x: T).(\lambda (H0: (pr3 c (THead (Bind Void) u1 t1) x)).(let H1 
\def (pr3_gen_void c u1 t1 x H0) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t1 t2)))))) (pr3 (CHead c 
(Bind Void) u1) t1 (lift (S O) O x)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) 
u1) t1 t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x))) (\lambda 
(H2: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) 
u) t1 t2))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T x 
(THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead 
c (Bind b0) u) t1 t2))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 
t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T x (THead (Bind Void) x0 
x1))).(\lambda (H4: (pr3 c u1 x0)).(\lambda (H5: ((\forall (b0: B).(\forall 
(u: T).(pr3 (CHead c (Bind b0) u) t1 x1))))).(or_introl (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 
(CHead c (Bind Void) u1) t1 t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S 
O) O x)) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 t2))) x0 x1 
H3 H4 (H5 Void u1)))))))) H2)) (\lambda (H2: (pr3 (CHead c (Bind Void) u1) t1 
(lift (S O) O x))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 (CHead c (Bind Void) u1) t1 
t2)))) (pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O x)) H2)) H1)))))))) b).
(* COMMENTS
Initial nodes: 1721
END *)

