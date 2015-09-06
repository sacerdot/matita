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

include "basic_1/pr3/defs.ma".

include "basic_1/pr2/fwd.ma".

implied let rec pr3_ind (c: C) (P: (T \to (T \to Prop))) (f: (\forall (t: 
T).(P t t))) (f0: (\forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to 
(\forall (t3: T).((pr3 c t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) (t: T) 
(t0: T) (p: pr3 c t t0) on p: P t t0 \def match p with [(pr3_refl t1) 
\Rightarrow (f t1) | (pr3_sing t2 t1 p0 t3 p1) \Rightarrow (f0 t2 t1 p0 t3 p1 
((pr3_ind c P f f0) t2 t3 p1))].

lemma pr3_gen_sort:
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

lemma pr3_gen_abst:
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

lemma pr3_gen_cast:
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

lemma pr3_gen_lift:
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

lemma pr3_gen_lref:
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

