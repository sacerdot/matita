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

include "Basic-1/pr2/defs.ma".

include "Basic-1/pr0/fwd.ma".

include "Basic-1/getl/drop.ma".

include "Basic-1/getl/clear.ma".

theorem pr2_gen_sort:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TSort n) x) \to 
(eq T x (TSort n)))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr2 c (TSort 
n) x)).(insert_eq T (TSort n) (\lambda (t: T).(pr2 c t x)) (\lambda (t: 
T).(eq T x t)) (\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda 
(_: C).(\lambda (t: T).(\lambda (t0: T).((eq T t (TSort n)) \to (eq T t0 
t))))) (\lambda (_: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H1: (pr0 
t1 t2)).(\lambda (H2: (eq T t1 (TSort n))).(let H3 \def (eq_ind T t1 (\lambda 
(t: T).(pr0 t t2)) H1 (TSort n) H2) in (eq_ind_r T (TSort n) (\lambda (t: 
T).(eq T t2 t)) (eq_ind_r T (TSort n) (\lambda (t: T).(eq T t (TSort n))) 
(refl_equal T (TSort n)) t2 (pr0_gen_sort t2 n H3)) t1 H2))))))) (\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: (getl 
i c0 (CHead d (Bind Abbr) u))).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H2: (pr0 t1 t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda 
(H4: (eq T t1 (TSort n))).(let H5 \def (eq_ind T t1 (\lambda (t0: T).(pr0 t0 
t2)) H2 (TSort n) H4) in (eq_ind_r T (TSort n) (\lambda (t0: T).(eq T t t0)) 
(let H6 \def (eq_ind T t2 (\lambda (t0: T).(subst0 i u t0 t)) H3 (TSort n) 
(pr0_gen_sort t2 n H5)) in (subst0_gen_sort u t i n H6 (eq T t (TSort n)))) 
t1 H4))))))))))))) c y x H0))) H)))).
(* COMMENTS
Initial nodes: 347
END *)

theorem pr2_gen_lref:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TLRef n) x) \to 
(or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c 
(CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T x (lift (S 
n) O u)))))))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr2 c (TLRef 
n) x)).(insert_eq T (TLRef n) (\lambda (t: T).(pr2 c t x)) (\lambda (t: 
T).(or (eq T x t) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c (CHead 
d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T x (lift (S n) O 
u))))))) (\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n)) \to (or (eq T t0 t) 
(ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c0 (CHead d (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(eq T t0 (lift (S n) O u)))))))))) 
(\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H1: (pr0 t1 
t2)).(\lambda (H2: (eq T t1 (TLRef n))).(let H3 \def (eq_ind T t1 (\lambda 
(t: T).(pr0 t t2)) H1 (TLRef n) H2) in (eq_ind_r T (TLRef n) (\lambda (t: 
T).(or (eq T t2 t) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c0 
(CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift (S 
n) O u))))))) (eq_ind_r T (TLRef n) (\lambda (t: T).(or (eq T t (TLRef n)) 
(ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c0 (CHead d (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(eq T t (lift (S n) O u))))))) 
(or_introl (eq T (TLRef n) (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: 
T).(getl n c0 (CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq 
T (TLRef n) (lift (S n) O u))))) (refl_equal T (TLRef n))) t2 (pr0_gen_lref 
t2 n H3)) t1 H2))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H2: (pr0 t1 t2)).(\lambda 
(t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda (H4: (eq T t1 (TLRef 
n))).(let H5 \def (eq_ind T t1 (\lambda (t0: T).(pr0 t0 t2)) H2 (TLRef n) H4) 
in (eq_ind_r T (TLRef n) (\lambda (t0: T).(or (eq T t t0) (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl n c0 (CHead d0 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(eq T t (lift (S n) O u0))))))) (let H6 \def (eq_ind T t2 
(\lambda (t0: T).(subst0 i u t0 t)) H3 (TLRef n) (pr0_gen_lref t2 n H5)) in 
(land_ind (eq nat n i) (eq T t (lift (S n) O u)) (or (eq T t (TLRef n)) 
(ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl n c0 (CHead d0 (Bind Abbr) 
u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t (lift (S n) O u0)))))) 
(\lambda (H7: (eq nat n i)).(\lambda (H8: (eq T t (lift (S n) O 
u))).(eq_ind_r T (lift (S n) O u) (\lambda (t0: T).(or (eq T t0 (TLRef n)) 
(ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl n c0 (CHead d0 (Bind Abbr) 
u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t0 (lift (S n) O u0))))))) (let 
H9 \def (eq_ind_r nat i (\lambda (n0: nat).(getl n0 c0 (CHead d (Bind Abbr) 
u))) H1 n H7) in (or_intror (eq T (lift (S n) O u) (TLRef n)) (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl n c0 (CHead d0 (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(eq T (lift (S n) O u) (lift (S n) O u0))))) 
(ex2_2_intro C T (\lambda (d0: C).(\lambda (u0: T).(getl n c0 (CHead d0 (Bind 
Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T (lift (S n) O u) (lift (S 
n) O u0)))) d u H9 (refl_equal T (lift (S n) O u))))) t H8))) 
(subst0_gen_lref u t i n H6))) t1 H4))))))))))))) c y x H0))) H)))).
(* COMMENTS
Initial nodes: 1003
END *)

theorem pr2_gen_abst:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t2))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Abst) u1 t1) x)).(insert_eq T (THead (Bind Abst) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))))))) (\lambda (y: 
T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abst) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t2)))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H1: 
(pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Bind Abst) u1 t1))).(let H3 \def 
(eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Bind Abst) u1 t1) H2) in 
(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c0 (Bind b) u) t1 t3)))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H4: (eq T t2 (THead (Bind Abst) x0 x1))).(\lambda (H5: (pr0 u1 
x0)).(\lambda (H6: (pr0 t1 x1)).(eq_ind_r T (THead (Bind Abst) x0 x1) 
(\lambda (t: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead 
c0 (Bind b) u) t1 t3))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))))) x0 x1 
(refl_equal T (THead (Bind Abst) x0 x1)) (pr2_free c0 u1 x0 H5) (\lambda (b: 
B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) t1 x1 H6)))) t2 H4)))))) 
(pr0_gen_abst u1 t1 t2 H3)))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 t2)).(\lambda 
(t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda (H4: (eq T t0 (THead (Bind 
Abst) u1 t1))).(let H5 \def (eq_ind T t0 (\lambda (t3: T).(pr0 t3 t2)) H2 
(THead (Bind Abst) u1 t1) H4) in (ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H6: (eq T t2 (THead 
(Bind Abst) x0 x1))).(\lambda (H7: (pr0 u1 x0)).(\lambda (H8: (pr0 t1 
x1)).(let H9 \def (eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 t)) H3 (THead 
(Bind Abst) x0 x1) H6) in (or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abst) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda 
(t3: T).(eq T t (THead (Bind Abst) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind 
Abst) i) u x1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 
u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 t3)))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3)))))) (\lambda (H10: (ex2 T (\lambda (u2: T).(eq T t (THead (Bind 
Abst) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T t (THead (Bind Abst) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3)))))) (\lambda (x2: T).(\lambda (H11: (eq T t (THead (Bind Abst) x2 
x1))).(\lambda (H12: (subst0 i u x0 x2)).(eq_ind_r T (THead (Bind Abst) x2 
x1) (\lambda (t3: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t4))))))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abst) x2 x1) (THead (Bind Abst) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x2 x1 (refl_equal T (THead (Bind Abst) x2 x1)) (pr2_delta c0 d 
u i H1 u1 x0 H7 x2 H12) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c0 
(Bind b) u0) t1 x1 H8)))) t H11)))) H10)) (\lambda (H10: (ex2 T (\lambda (t3: 
T).(eq T t (THead (Bind Abst) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind 
Abst) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Abst) 
x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 t3)) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\lambda (x2: T).(\lambda (H11: (eq T t (THead (Bind Abst) x0 
x2))).(\lambda (H12: (subst0 (s (Bind Abst) i) u x1 x2)).(eq_ind_r T (THead 
(Bind Abst) x0 x2) (\lambda (t3: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t4))))))) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind Abst) x0 x2) (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x0 x2 (refl_equal T (THead (Bind Abst) x0 x2)) (pr2_free c0 u1 
x0 H7) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u 
(S i) (getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H8 x2 
H12)))) t H11)))) H10)) (\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind 
Abst) i) u x1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u 
x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 
t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3)))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H11: (eq T t 
(THead (Bind Abst) x2 x3))).(\lambda (H12: (subst0 i u x0 x2)).(\lambda (H13: 
(subst0 (s (Bind Abst) i) u x1 x3)).(eq_ind_r T (THead (Bind Abst) x2 x3) 
(\lambda (t3: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 t4))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abst) x2 x3) (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))))) x2 x3 
(refl_equal T (THead (Bind Abst) x2 x3)) (pr2_delta c0 d u i H1 u1 x0 H7 x2 
H12) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u 
(S i) (getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H8 x3 
H13)))) t H11)))))) H10)) (subst0_gen_head (Bind Abst) u x0 x1 t i H9)))))))) 
(pr0_gen_abst u1 t1 t2 H5)))))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 2383
END *)

theorem pr2_gen_cast:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 t2)))) (pr2 c 
t1 x))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Flat Cast) u1 t1) x)).(insert_eq T (THead (Flat Cast) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 
t2)))) (pr2 c t1 x))) (\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq T t (THead (Flat Cast) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead 
(Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr2 c0 t1 t2)))) (pr2 c0 t1 t0)))))) 
(\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H1: (pr0 t0 
t2)).(\lambda (H2: (eq T t0 (THead (Flat Cast) u1 t1))).(let H3 \def (eq_ind 
T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Flat Cast) u1 t1) H2) in (or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t2)) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t2)) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t2 (THead (Flat Cast) 
x0 x1))).(\lambda (H6: (pr0 u1 x0)).(\lambda (H7: (pr0 t1 x1)).(eq_ind_r T 
(THead (Flat Cast) x0 x1) (\lambda (t: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Flat Cast) x0 x1) (THead (Flat Cast) u2 t3)))) (\lambda 
(u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr2 c0 t1 t3)))) (pr2 c0 t1 (THead (Flat Cast) x0 x1)) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat Cast) x0 x1) (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3))) x0 x1 (refl_equal T (THead 
(Flat Cast) x0 x1)) (pr2_free c0 u1 x0 H6) (pr2_free c0 t1 x1 H7))) t2 
H5)))))) H4)) (\lambda (H4: (pr0 t1 t2)).(or_intror (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t2) (pr2_free c0 t1 t2 H4))) (pr0_gen_cast u1 t1 t2 
H3)))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 t2)).(\lambda (t: T).(\lambda (H3: 
(subst0 i u t2 t)).(\lambda (H4: (eq T t0 (THead (Flat Cast) u1 t1))).(let H5 
\def (eq_ind T t0 (\lambda (t3: T).(pr0 t3 t2)) H2 (THead (Flat Cast) u1 t1) 
H4) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t)) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t)) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T t2 (THead (Flat Cast) 
x0 x1))).(\lambda (H8: (pr0 u1 x0)).(\lambda (H9: (pr0 t1 x1)).(let H10 \def 
(eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Flat Cast) x0 x1) 
H7) in (or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead (Flat Cast) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead 
(Flat Cast) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t)) (\lambda (H11: (ex2 T (\lambda (u2: 
T).(eq T t (THead (Flat Cast) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T t (THead (Flat Cast) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 
c0 t1 t)) (\lambda (x2: T).(\lambda (H12: (eq T t (THead (Flat Cast) x2 
x1))).(\lambda (H13: (subst0 i u x0 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3))) x2 x1 H12 
(pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (pr2_free c0 t1 x1 H9)))))) H11)) 
(\lambda (H11: (ex2 T (\lambda (t3: T).(eq T t (THead (Flat Cast) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3)))).(ex2_ind T (\lambda 
(t3: T).(eq T t (THead (Flat Cast) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat 
Cast) i) u x1 t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t)) 
(\lambda (x2: T).(\lambda (H12: (eq T t (THead (Flat Cast) x0 x2))).(\lambda 
(H13: (subst0 (s (Flat Cast) i) u x1 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (pr2 c0 t1 t) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3))) x0 x2 H12 
(pr2_free c0 u1 x0 H8) (pr2_delta c0 d u i H1 t1 x1 H9 x2 H13)))))) H11)) 
(\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat 
Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3))) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t)) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H12: (eq T t (THead (Flat Cast) x2 
x3))).(\lambda (H13: (subst0 i u x0 x2)).(\lambda (H14: (subst0 (s (Flat 
Cast) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3))) x2 x3 H12 (pr2_delta c0 d u i H1 u1 x0 
H8 x2 H13) (pr2_delta c0 d u i H1 t1 x1 H9 x3 H14)))))))) H11)) 
(subst0_gen_head (Flat Cast) u x0 x1 t i H10)))))))) H6)) (\lambda (H6: (pr0 
t1 t2)).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (pr2 c0 t1 t) 
(pr2_delta c0 d u i H1 t1 t2 H6 t H3))) (pr0_gen_cast u1 t1 t2 
H5)))))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 2659
END *)

theorem pr2_gen_csort:
 \forall (t1: T).(\forall (t2: T).(\forall (n: nat).((pr2 (CSort n) t1 t2) 
\to (pr0 t1 t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (n: nat).(\lambda (H: (pr2 (CSort 
n) t1 t2)).(insert_eq C (CSort n) (\lambda (c: C).(pr2 c t1 t2)) (\lambda (_: 
C).(pr0 t1 t2)) (\lambda (y: C).(\lambda (H0: (pr2 y t1 t2)).(pr2_ind 
(\lambda (c: C).(\lambda (t: T).(\lambda (t0: T).((eq C c (CSort n)) \to (pr0 
t t0))))) (\lambda (c: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: 
(pr0 t3 t4)).(\lambda (_: (eq C c (CSort n))).H1))))) (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 
t3 t4)).(\lambda (t: T).(\lambda (_: (subst0 i u t4 t)).(\lambda (H4: (eq C c 
(CSort n))).(let H5 \def (eq_ind C c (\lambda (c0: C).(getl i c0 (CHead d 
(Bind Abbr) u))) H1 (CSort n) H4) in (getl_gen_sort n i (CHead d (Bind Abbr) 
u) H5 (pr0 t3 t)))))))))))))) y t1 t2 H0))) H)))).
(* COMMENTS
Initial nodes: 221
END *)

theorem pr2_gen_appl:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Flat Appl) u1 t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 t2)))) (ex4_4 T 
T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead 
(Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Flat Appl) u1 t1) x)).(insert_eq T (THead (Flat Appl) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 
t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t2)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq T t (THead (Flat Appl) 
u1 t1)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr2 c0 t1 t2)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t2)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t0 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2))))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(H1: (pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Flat Appl) u1 t1))).(let H3 
\def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Flat Appl) u1 t1) 
H2) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (H4: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H6: (pr0 u1 
x0)).(\lambda (H7: (pr0 t1 x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) 
(\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2)))))))))) (or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Flat Appl) x0 x1) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) 
x0 x1) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Flat 
Appl) x0 x1) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Flat Appl) x0 x1) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3))) x0 x1 (refl_equal T (THead (Flat Appl) x0 x1)) (pr2_free c0 u1 x0 
H6) (pr2_free c0 t1 x1 H7))) t2 H5)))))) H4)) (\lambda (H4: (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2))))))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H5: (eq T t1 (THead (Bind Abst) x0 x1))).(\lambda (H6: (eq T t2 
(THead (Bind Abbr) x2 x3))).(\lambda (H7: (pr0 u1 x2)).(\lambda (H8: (pr0 x1 
x3)).(eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda (t: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (eq_ind_r T (THead (Bind 
Abst) x0 x1) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x3) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x2 x3) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x2 x3) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x3) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x2 x3) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) z1 t3))))))) x0 x1 x2 x3 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x2 x3)) (pr2_free c0 u1 x2 H7) (\lambda (b: 
B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) x1 x3 H8))))) t1 H5) t2 
H6))))))))) H4)) (\lambda (H4: (ex6_6 B T T T T T (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not 
(eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) 
y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead (Flat 
Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead (Flat Appl) (lift 
(S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2))))))))) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H5: (not (eq B x0 
Abst))).(\lambda (H6: (eq T t1 (THead (Bind x0) x1 x2))).(\lambda (H7: (eq T 
t2 (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)))).(\lambda 
(H8: (pr0 u1 x3)).(\lambda (H9: (pr0 x1 x4)).(\lambda (H10: (pr0 x2 
x5)).(eq_ind_r T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) 
x5)) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2)))))))))) (eq_ind_r T (THead (Bind x0) x1 x2) (\lambda (t: T).(or3 (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat 
Appl) (lift (S O) O x3) x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat 
Appl) (lift (S O) O x3) x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x5 x3 x4 H5 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5))) (pr2_free c0 
u1 x3 H8) (pr2_free c0 x1 x4 H9) (pr2_free (CHead c0 (Bind x0) x4) x2 x5 
H10))) t1 H6) t2 H7))))))))))))) H4)) (pr0_gen_appl u1 t1 t2 H3)))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H2: (pr0 t0 t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 
t)).(\lambda (H4: (eq T t0 (THead (Flat Appl) u1 t1))).(let H5 \def (eq_ind T 
t0 (\lambda (t3: T).(pr0 t3 t2)) H2 (THead (Flat Appl) u1 t1) H4) in (or3_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (H6: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H8: (pr0 u1 
x0)).(\lambda (H9: (pr0 t1 x1)).(let H10 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 t)) H3 (THead (Flat Appl) x0 x1) H7) in (or3_ind (ex2 T 
(\lambda (u2: T).(eq T t (THead (Flat Appl) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Flat Appl) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) i) u x1 t3)))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (H11: (ex2 T (\lambda (u2: 
T).(eq T t (THead (Flat Appl) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T t (THead (Flat Appl) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda (H12: (eq T t 
(THead (Flat Appl) x2 x1))).(\lambda (H13: (subst0 i u x0 x2)).(eq_ind_r T 
(THead (Flat Appl) x2 x1) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x1) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Flat Appl) x2 x1) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Flat Appl) x2 x1) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O 
u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Flat Appl) x2 x1) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3))) x2 x1 (refl_equal T (THead (Flat Appl) x2 x1)) (pr2_delta c0 d u i 
H1 u1 x0 H8 x2 H13) (pr2_free c0 t1 x1 H9))) t H12)))) H11)) (\lambda (H11: 
(ex2 T (\lambda (t3: T).(eq T t (THead (Flat Appl) x0 t3))) (\lambda (t3: 
T).(subst0 (s (Flat Appl) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T t 
(THead (Flat Appl) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 
t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda 
(H12: (eq T t (THead (Flat Appl) x0 x2))).(\lambda (H13: (subst0 (s (Flat 
Appl) i) u x1 x2)).(eq_ind_r T (THead (Flat Appl) x0 x2) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat 
Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t4: T).(pr2 c0 t1 t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) 
(or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat 
Appl) x0 x2) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x2) (THead (Bind Abbr) 
u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T (THead (Flat Appl) x0 x2) (THead (Bind b) y2 
(THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x2) (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3))) x0 x2 (refl_equal T (THead (Flat Appl) 
x0 x2)) (pr2_free c0 u1 x0 H8) (pr2_delta c0 d u i H1 t1 x1 H9 x2 H13))) t 
H12)))) H11)) (\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u 
x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3))) (or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H12: (eq T t (THead (Flat Appl) x2 x3))).(\lambda (H13: 
(subst0 i u x0 x2)).(\lambda (H14: (subst0 (s (Flat Appl) i) u x1 
x3)).(eq_ind_r T (THead (Flat Appl) x2 x3) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c0 t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T (THead (Flat Appl) x2 x3) (THead (Bind b) y2 
(THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 t1 t3))) x2 x3 (refl_equal T (THead (Flat Appl) 
x2 x3)) (pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (pr2_delta c0 d u i H1 t1 x1 
H9 x3 H14))) t H12)))))) H11)) (subst0_gen_head (Flat Appl) u x0 x1 t i 
H10)))))))) H6)) (\lambda (H6: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(pr0 z1 t3))))))).(ex4_4_ind T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T t1 (THead (Bind 
Abst) x0 x1))).(\lambda (H8: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda 
(H9: (pr0 u1 x2)).(\lambda (H10: (pr0 x1 x3)).(let H11 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Bind Abbr) x2 x3) H8) in 
(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c0 t3 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t3 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t 
(THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda 
(u2: T).(eq T t (THead (Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 i u x2 
u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x2 t3))) (\lambda 
(t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x3 t3)))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (H12: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 i u x2 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 
i u x2 u2)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind Abst) x0 x1) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x4: T).(\lambda 
(H13: (eq T t (THead (Bind Abbr) x4 x3))).(\lambda (H14: (subst0 i u x2 
x4)).(eq_ind_r T (THead (Bind Abbr) x4 x3) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c0 (THead (Bind Abst) x0 x1) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x4 x3) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x4 x3) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3))))))) x0 x1 x4 x3 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x4 x3)) (pr2_delta c0 d u i H1 u1 x2 H9 x4 
H14) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c0 (Bind b) u0) x1 x3 
H10))))) t H13)))) H12)) (\lambda (H12: (ex2 T (\lambda (t3: T).(eq T t 
(THead (Bind Abbr) x2 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x2 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3)) (or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (x4: T).(\lambda (H13: (eq T t (THead (Bind Abbr) 
x2 x4))).(\lambda (H14: (subst0 (s (Bind Abbr) i) u x3 x4)).(eq_ind_r T 
(THead (Bind Abbr) x2 x4) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x4) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x4) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x2 x4) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x4) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3))))))) x0 x1 x2 x4 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x2 x4)) (pr2_free c0 u1 x2 H9) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) 
(getl_clear_bind b (CHead c0 (Bind b) u0) c0 u0 (clear_bind b c0 u0) (CHead d 
(Bind Abbr) u) i H1) x1 x3 H10 x4 H14))))) t H13)))) H12)) (\lambda (H12: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 (THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H13: (eq T t 
(THead (Bind Abbr) x4 x5))).(\lambda (H14: (subst0 i u x2 x4)).(\lambda (H15: 
(subst0 (s (Bind Abbr) i) u x3 x5)).(eq_ind_r T (THead (Bind Abbr) x4 x5) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind Abst) x0 x1) 
t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x4 x5) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x4 x5) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3))))))) x0 x1 x4 x5 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x4 x5)) (pr2_delta c0 d u i H1 u1 x2 H9 x4 
H14) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u 
(S i) (getl_clear_bind b (CHead c0 (Bind b) u0) c0 u0 (clear_bind b c0 u0) 
(CHead d (Bind Abbr) u) i H1) x1 x3 H10 x5 H15))))) t H13)))))) H12)) 
(subst0_gen_head (Bind Abbr) u x2 x3 t i H11)) t1 H7)))))))))) H6)) (\lambda 
(H6: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) 
t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda 
(y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 
y1 v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))))))).(ex6_6_ind B T T T T 
T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x0: B).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H7: (not (eq B x0 Abst))).(\lambda (H8: (eq T t1 (THead (Bind 
x0) x1 x2))).(\lambda (H9: (eq T t2 (THead (Bind x0) x4 (THead (Flat Appl) 
(lift (S O) O x3) x5)))).(\lambda (H10: (pr0 u1 x3)).(\lambda (H11: (pr0 x1 
x4)).(\lambda (H12: (pr0 x2 x5)).(let H13 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 t)) H3 (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O 
x3) x5)) H9) in (eq_ind_r T (THead (Bind x0) x1 x2) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c0 t3 t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T t (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda 
(u2: T).(eq T t (THead (Bind x0) u2 (THead (Flat Appl) (lift (S O) O x3) 
x5)))) (\lambda (u2: T).(subst0 i u x4 u2))) (ex2 T (\lambda (t3: T).(eq T t 
(THead (Bind x0) x4 t3))) (\lambda (t3: T).(subst0 (s (Bind x0) i) u (THead 
(Flat Appl) (lift (S O) O x3) x5) t3))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind x0) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u x4 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind x0) 
i) u (THead (Flat Appl) (lift (S O) O x3) x5) t3)))) (or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (H14: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind x0) u2 (THead (Flat Appl) (lift (S O) O x3) x5)))) (\lambda (u2: 
T).(subst0 i u x4 u2)))).(ex2_ind T (\lambda (u2: T).(eq T t (THead (Bind x0) 
u2 (THead (Flat Appl) (lift (S O) O x3) x5)))) (\lambda (u2: T).(subst0 i u 
x4 u2)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x6: T).(\lambda 
(H15: (eq T t (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) 
x5)))).(\lambda (H16: (subst0 i u x4 x6)).(eq_ind_r T (THead (Bind x0) x6 
(THead (Flat Appl) (lift (S O) O x3) x5)) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x3) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x3 x6 H7 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) (lift 
(S O) O x3) x5))) (pr2_free c0 u1 x3 H10) (pr2_delta c0 d u i H1 x1 x4 H11 x6 
H16) (pr2_free (CHead c0 (Bind x0) x6) x2 x5 H12))) t H15)))) H14)) (\lambda 
(H14: (ex2 T (\lambda (t3: T).(eq T t (THead (Bind x0) x4 t3))) (\lambda (t3: 
T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind x0) x4 t3))) (\lambda 
(t3: T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x6: T).(\lambda 
(H15: (eq T t (THead (Bind x0) x4 x6))).(\lambda (H16: (subst0 (s (Bind x0) 
i) u (THead (Flat Appl) (lift (S O) O x3) x5) x6)).(eq_ind_r T (THead (Bind 
x0) x4 x6) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) 
x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda (u2: T).(eq T x6 (THead (Flat 
Appl) u2 x5))) (\lambda (u2: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) 
u2))) (ex2 T (\lambda (t3: T).(eq T x6 (THead (Flat Appl) (lift (S O) O x3) 
t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x6 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) 
O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind 
x0) i)) u x5 t3)))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 x6) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (H17: (ex2 T 
(\lambda (u2: T).(eq T x6 (THead (Flat Appl) u2 x5))) (\lambda (u2: 
T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x6 (THead (Flat Appl) u2 x5))) (\lambda (u2: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda (H18: (eq T 
x6 (THead (Flat Appl) x7 x5))).(\lambda (H19: (subst0 (s (Bind x0) i) u (lift 
(S O) O x3) x7)).(eq_ind_r T (THead (Flat Appl) x7 x5) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) x4 t3) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: T).(eq T x7 
(lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) i) (S O)) u 
x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
x0) x4 (THead (Flat Appl) x7 x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) x7 x5)) (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) x7 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (x8: T).(\lambda (H20: (eq T x7 (lift (S O) O 
x8))).(\lambda (H21: (subst0 (minus (s (Bind x0) i) (S O)) u x3 x8)).(let H22 
\def (eq_ind nat (minus (s (Bind x0) i) (S O)) (\lambda (n: nat).(subst0 n u 
x3 x8)) H21 i (s_arith1 x0 i)) in (eq_ind_r T (lift (S O) O x8) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) t3 x5)) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x5)) (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) t3 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x8) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) (lift (S O) O x8) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x8) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) (lift (S O) O x8) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x8 x4 H7 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x4 (THead (Flat Appl) (lift 
(S O) O x8) x5))) (pr2_delta c0 d u i H1 u1 x3 H10 x8 H22) (pr2_free c0 x1 x4 
H11) (pr2_free (CHead c0 (Bind x0) x4) x2 x5 H12))) x7 H20))))) 
(subst0_gen_lift_ge u x3 x7 (s (Bind x0) i) (S O) O H19 (le_n_S O i (le_O_n 
i)))) x6 H18)))) H17)) (\lambda (H17: (ex2 T (\lambda (t3: T).(eq T x6 (THead 
(Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) 
(s (Bind x0) i)) u x5 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x6 (THead 
(Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) 
(s (Bind x0) i)) u x5 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 x6) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda 
(H18: (eq T x6 (THead (Flat Appl) (lift (S O) O x3) x7))).(\lambda (H19: 
(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 x7)).(eq_ind_r T (THead (Flat 
Appl) (lift (S O) O x3) x7) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T (THead (Bind x0) x4 t3) (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x3) x7)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x7 x3 x4 H7 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7))) (pr2_free c0 
u1 x3 H10) (pr2_free c0 x1 x4 H11) (pr2_delta (CHead c0 (Bind x0) x4) d u (S 
i) (getl_clear_bind x0 (CHead c0 (Bind x0) x4) c0 x4 (clear_bind x0 c0 x4) 
(CHead d (Bind Abbr) u) i H1) x2 x5 H12 x7 H19))) x6 H18)))) H17)) (\lambda 
(H17: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x6 (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u 
(lift (S O) O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x6 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2))) (\lambda (_: T).(\lambda 
(t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda (x8: 
T).(\lambda (H18: (eq T x6 (THead (Flat Appl) x7 x8))).(\lambda (H19: (subst0 
(s (Bind x0) i) u (lift (S O) O x3) x7)).(\lambda (H20: (subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 x8)).(eq_ind_r T (THead (Flat Appl) x7 x8) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T 
(THead (Bind x0) x4 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: 
T).(eq T x7 (lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) 
i) (S O)) u x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x9: T).(\lambda 
(H21: (eq T x7 (lift (S O) O x9))).(\lambda (H22: (subst0 (minus (s (Bind x0) 
i) (S O)) u x3 x9)).(let H23 \def (eq_ind nat (minus (s (Bind x0) i) (S O)) 
(\lambda (n: nat).(subst0 n u x3 x9)) H22 i (s_arith1 x0 i)) in (eq_ind_r T 
(lift (S O) O x9) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x8)) (THead (Flat 
Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) t3 x8)) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x8)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x9) x8)) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) (lift (S O) O x9) x8)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x9) x8)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) (lift (S O) O x9) x8)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))) x0 x1 x2 x8 x9 x4 H7 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x4 (THead (Flat Appl) (lift 
(S O) O x9) x8))) (pr2_delta c0 d u i H1 u1 x3 H10 x9 H23) (pr2_free c0 x1 x4 
H11) (pr2_delta (CHead c0 (Bind x0) x4) d u (S i) (getl_clear_bind x0 (CHead 
c0 (Bind x0) x4) c0 x4 (clear_bind x0 c0 x4) (CHead d (Bind Abbr) u) i H1) x2 
x5 H12 x8 H20))) x7 H21))))) (subst0_gen_lift_ge u x3 x7 (s (Bind x0) i) (S 
O) O H19 (le_n_S O i (le_O_n i)))) x6 H18)))))) H17)) (subst0_gen_head (Flat 
Appl) u (lift (S O) O x3) x5 x6 (s (Bind x0) i) H16)) t H15)))) H14)) 
(\lambda (H14: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind x0) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x4 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) 
(lift (S O) O x3) x5) t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Bind x0) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u x4 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind x0) 
i) u (THead (Flat Appl) (lift (S O) O x3) x5) t3))) (or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (x6: T).(\lambda (x7: T).(\lambda (H15: (eq T t 
(THead (Bind x0) x6 x7))).(\lambda (H16: (subst0 i u x4 x6)).(\lambda (H17: 
(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
x7)).(eq_ind_r T (THead (Bind x0) x6 x7) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda (u2: T).(eq T x7 (THead (Flat 
Appl) u2 x5))) (\lambda (u2: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) 
u2))) (ex2 T (\lambda (t3: T).(eq T x7 (THead (Flat Appl) (lift (S O) O x3) 
t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x7 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) 
O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind 
x0) i)) u x5 t3)))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 x7) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (H18: (ex2 T 
(\lambda (u2: T).(eq T x7 (THead (Flat Appl) u2 x5))) (\lambda (u2: 
T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x7 (THead (Flat Appl) u2 x5))) (\lambda (u2: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x8: T).(\lambda (H19: (eq T 
x7 (THead (Flat Appl) x8 x5))).(\lambda (H20: (subst0 (s (Bind x0) i) u (lift 
(S O) O x3) x8)).(eq_ind_r T (THead (Flat Appl) x8 x5) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) x6 t3) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: T).(eq T x8 
(lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) i) (S O)) u 
x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
x0) x6 (THead (Flat Appl) x8 x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) x8 x5)) (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) x8 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2))))))))) (\lambda (x9: T).(\lambda (H21: (eq T x8 (lift (S O) O 
x9))).(\lambda (H22: (subst0 (minus (s (Bind x0) i) (S O)) u x3 x9)).(let H23 
\def (eq_ind nat (minus (s (Bind x0) i) (S O)) (\lambda (n: nat).(subst0 n u 
x3 x9)) H22 i (s_arith1 x0 i)) in (eq_ind_r T (lift (S O) O x9) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) t3 x5)) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x5)) (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) t3 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x9) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x9) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x9) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x9) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x9 x6 H7 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) (lift 
(S O) O x9) x5))) (pr2_delta c0 d u i H1 u1 x3 H10 x9 H23) (pr2_delta c0 d u 
i H1 x1 x4 H11 x6 H16) (pr2_free (CHead c0 (Bind x0) x6) x2 x5 H12))) x8 
H21))))) (subst0_gen_lift_ge u x3 x8 (s (Bind x0) i) (S O) O H20 (le_n_S O i 
(le_O_n i)))) x7 H19)))) H18)) (\lambda (H18: (ex2 T (\lambda (t3: T).(eq T 
x7 (THead (Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s 
(Flat Appl) (s (Bind x0) i)) u x5 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x7 
(THead (Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Flat Appl) u2 t3)))) (\lambda 
(u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 x7) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2))))))))) (\lambda (x8: T).(\lambda (H19: (eq T x7 (THead (Flat Appl) (lift 
(S O) O x3) x8))).(\lambda (H20: (subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 
x8)).(eq_ind_r T (THead (Flat Appl) (lift (S O) O x3) x8) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) 
t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T (THead (Bind x0) x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 (THead (Flat 
Appl) (lift (S O) O x3) x8)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x8 x3 x6 H7 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8))) (pr2_free c0 
u1 x3 H10) (pr2_delta c0 d u i H1 x1 x4 H11 x6 H16) (pr2_delta (CHead c0 
(Bind x0) x6) d u (S i) (getl_clear_bind x0 (CHead c0 (Bind x0) x6) c0 x6 
(clear_bind x0 c0 x6) (CHead d (Bind Abbr) u) i H1) x2 x5 H12 x8 H20))) x7 
H19)))) H18)) (\lambda (H18: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T x7 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x7 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) 
u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) 
i)) u x5 t3))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind x0) x6 x7) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) 
x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x8: T).(\lambda 
(x9: T).(\lambda (H19: (eq T x7 (THead (Flat Appl) x8 x9))).(\lambda (H20: 
(subst0 (s (Bind x0) i) u (lift (S O) O x3) x8)).(\lambda (H21: (subst0 (s 
(Flat Appl) (s (Bind x0) i)) u x5 x9)).(eq_ind_r T (THead (Flat Appl) x8 x9) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T 
(THead (Bind x0) x6 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: 
T).(eq T x8 (lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) 
i) (S O)) u x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c0 (Bind b) y2) z1 z2))))))))) (\lambda (x10: T).(\lambda 
(H22: (eq T x8 (lift (S O) O x10))).(\lambda (H23: (subst0 (minus (s (Bind 
x0) i) (S O)) u x3 x10)).(let H24 \def (eq_ind nat (minus (s (Bind x0) i) (S 
O)) (\lambda (n: nat).(subst0 n u x3 x10)) H23 i (s_arith1 x0 i)) in 
(eq_ind_r T (lift (S O) O x10) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x9)) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c0 (THead (Bind x0) x1 x2) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) t3 x9)) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t4)))))))) (ex6_6 B T 
T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x9)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c0 
y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) y2) z1 
z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x10) x9)) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr2 c0 (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x10) x9)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x10) x9)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c0 (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x10) x9)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c0 y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c0 (Bind b) y2) z1 z2))))))) x0 x1 x2 x9 x10 x6 H7 (refl_equal T 
(THead (Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) 
(lift (S O) O x10) x9))) (pr2_delta c0 d u i H1 u1 x3 H10 x10 H24) (pr2_delta 
c0 d u i H1 x1 x4 H11 x6 H16) (pr2_delta (CHead c0 (Bind x0) x6) d u (S i) 
(getl_clear_bind x0 (CHead c0 (Bind x0) x6) c0 x6 (clear_bind x0 c0 x6) 
(CHead d (Bind Abbr) u) i H1) x2 x5 H12 x9 H21))) x8 H22))))) 
(subst0_gen_lift_ge u x3 x8 (s (Bind x0) i) (S O) O H20 (le_n_S O i (le_O_n 
i)))) x7 H19)))))) H18)) (subst0_gen_head (Flat Appl) u (lift (S O) O x3) x5 
x7 (s (Bind x0) i) H17)) t H15)))))) H14)) (subst0_gen_head (Bind x0) u x4 
(THead (Flat Appl) (lift (S O) O x3) x5) t i H13)) t1 H8)))))))))))))) H6)) 
(pr0_gen_appl u1 t1 t2 H5)))))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 38859
END *)

theorem pr2_gen_abbr:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t2))) (ex3_2 T 
T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Abbr) u1 t1) x)).(insert_eq T (THead (Bind Abbr) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
t2))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))) 
(\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t2))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t2))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t2)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t0))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H1: 
(pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Bind Abbr) u1 t1))).(let H3 \def 
(eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Bind Abbr) u1 t1) H2) in 
(or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O t2)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind 
b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O t2))))) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3)))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3)))))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) 
u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t2 (THead (Bind Abbr) 
x0 x1))).(\lambda (H6: (pr0 u1 x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 
x1))))).(or_ind (pr0 t1 x1) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda 
(y0: T).(subst0 O x0 y0 x1))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2))))) (\lambda (H7: (pr0 t1 
x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t)))))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 x1)) 
(pr2_free c0 u1 x0 H6) (or3_intro0 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 x1))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x1)))) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead 
c0 (Bind b) u) t1 x1 H7)))))) t2 H5)) (\lambda (H_x0: (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1)))).(ex2_ind T (\lambda 
(y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1)) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t2))))) (\lambda (x2: T).(\lambda (H7: (pr0 t1 x2)).(\lambda (H8: (subst0 O 
x0 x2 x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: T).(or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t)))))) (ex2_ind T (\lambda (t: T).(subst0 O u1 x2 t)) (\lambda (t: T).(pr0 t 
x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1)))))) 
(\lambda (x3: T).(\lambda (_: (subst0 O u1 x2 x3)).(\lambda (_: (pr0 x3 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 x1)) 
(pr2_free c0 u1 x0 H6) (or3_intro1 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 x1))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x1)))) (ex_intro2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1)) x0 H6 (pr2_delta (CHead c0 (Bind 
Abbr) x0) c0 x0 O (getl_refl Abbr c0 x0) t1 x2 H7 x1 H8)))))))) 
(pr0_subst0_back x0 x2 x1 O H8 u1 H6)) t2 H5)))) H_x0)) H_x)))))) H4)) 
(\lambda (H4: (pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) 
u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2)))) 
(\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) t1 (lift (S 
O) O t2) H4))))) (pr0_gen_abbr u1 t1 t2 H3)))))))) (\lambda (c0: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d 
(Bind Abbr) u))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 
t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda (H4: (eq T t0 
(THead (Bind Abbr) u1 t1))).(let H5 \def (eq_ind T t0 (\lambda (t3: T).(pr0 
t3 t2)) H2 (THead (Bind Abbr) u1 t1) H4) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3))))))) (pr0 t1 (lift (S O) O t2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: 
T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) 
(ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 
y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda 
(z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (H6: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3)))))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3)))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Bind Abbr) x0 x1))).(\lambda (H8: (pr0 u1 
x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O x0 y0 x1))))).(or_ind (pr0 t1 x1) (ex2 T (\lambda 
(y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H9: (pr0 t1 x1)).(let H10 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Bind Abbr) x0 x1) H7) in 
(or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda 
(u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind 
Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H11: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T 
t (THead (Bind Abbr) x2 x1))).(\lambda (H13: (subst0 i u x0 x2)).(or_introl 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x2 x1 H12 
(pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (or3_intro0 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 x1))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x1))) (ex3_2 T T 
(\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z x1)))) (\lambda (b: B).(\lambda (u0: 
T).(pr2_free (CHead c0 (Bind b) u0) t1 x1 H9))))))))) H11)) (\lambda (H11: 
(ex2 T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x0 t3))) (\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T t 
(THead (Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T 
t (THead (Bind Abbr) x0 x2))).(\lambda (H13: (subst0 (s (Bind Abbr) i) u x1 
x2)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x0 x2 H12 
(pr2_free c0 u1 x0 H8) (or3_intro0 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 x2))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x2))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x2)))) (\lambda (b: B).(\lambda (u0: T).(pr2_delta 
(CHead c0 (Bind b) u0) d u (S i) (getl_head (Bind b) i c0 (CHead d (Bind 
Abbr) u) H1 u0) t1 x1 H9 x2 H13))))))))) H11)) (\lambda (H11: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq T t 
(THead (Bind Abbr) x2 x3))).(\lambda (H13: (subst0 i u x0 x2)).(\lambda (H14: 
(subst0 (s (Bind Abbr) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x2 x3 H12 (pr2_delta c0 d u i H1 u1 x0 H8 x2 
H13) (or3_intro0 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) 
t1 x3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z x3)))) 
(\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) 
(getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x3 
H14))))))))))) H11)) (subst0_gen_head (Bind Abbr) u x0 x1 t i H10)))) 
(\lambda (H_x0: (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 
O x0 y0 x1)))).(ex2_ind T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O x0 y0 x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) 
(\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H9: (pr0 
t1 x2)).(\lambda (H10: (subst0 O x0 x2 x1)).(let H11 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Bind Abbr) x0 x1) H7) in 
(or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda 
(u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind 
Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H12: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x3: T).(\lambda (H13: (eq T 
t (THead (Bind Abbr) x3 x1))).(\lambda (H14: (subst0 i u x0 x3)).(ex2_ind T 
(\lambda (t3: T).(subst0 O u1 x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x4: T).(\lambda (_: (subst0 
O u1 x2 x4)).(\lambda (_: (pr0 x4 x1)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x3 x1 H13 (pr2_delta c0 d u i H1 u1 x0 H8 x3 
H14) (or3_intro1 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) 
t1 x1))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x1))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z x1)))) 
(ex_intro2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x1)) x0 H8 (pr2_delta (CHead c0 (Bind Abbr) x0) c0 x0 O 
(getl_refl Abbr c0 x0) t1 x2 H9 x1 H10)))))))) (pr0_subst0_back x0 x2 x1 O 
H10 u1 H8))))) H12)) (\lambda (H12: (ex2 T (\lambda (t3: T).(eq T t (THead 
(Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x3: T).(\lambda (H13: (eq T t (THead (Bind Abbr) x0 x3))).(\lambda 
(H14: (subst0 (s (Bind Abbr) i) u x1 x3)).(ex2_ind T (\lambda (t3: T).(subst0 
O u1 x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x4: T).(\lambda (H15: (subst0 O u1 x2 x4)).(\lambda (H16: (pr0 x4 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x0 x3 H13 
(pr2_free c0 u1 x0 H8) (or3_intro2 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 x3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x3)))) (ex3_2_intro T T (\lambda (y0: T).(\lambda (_: 
T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: 
T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) 
u1) z x3))) x4 x1 (pr2_delta (CHead c0 (Bind Abbr) u1) c0 u1 O (getl_refl 
Abbr c0 u1) t1 x2 H9 x4 H15) H16 (pr2_delta (CHead c0 (Bind Abbr) u1) d u (S 
i) (getl_head (Bind Abbr) i c0 (CHead d (Bind Abbr) u) H1 u1) x1 x1 (pr0_refl 
x1) x3 H14)))))))) (pr0_subst0_back x0 x2 x1 O H10 u1 H8))))) H12)) (\lambda 
(H12: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H13: (eq T t 
(THead (Bind Abbr) x3 x4))).(\lambda (H14: (subst0 i u x0 x3)).(\lambda (H15: 
(subst0 (s (Bind Abbr) i) u x1 x4)).(ex2_ind T (\lambda (t3: T).(subst0 O u1 
x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x5: T).(\lambda (H16: (subst0 O u1 x2 x5)).(\lambda (H17: (pr0 x5 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x3 x4 H13 
(pr2_delta c0 d u i H1 u1 x0 H8 x3 H14) (or3_intro2 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 x4))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x4))) (ex3_2 T T 
(\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z x4)))) (ex3_2_intro T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x4))) x5 x1 (pr2_delta (CHead c0 (Bind Abbr) u1) c0 u1 O 
(getl_refl Abbr c0 u1) t1 x2 H9 x5 H16) H17 (pr2_delta (CHead c0 (Bind Abbr) 
u1) d u (S i) (getl_head (Bind Abbr) i c0 (CHead d (Bind Abbr) u) H1 u1) x1 
x1 (pr0_refl x1) x4 H15)))))))) (pr0_subst0_back x0 x2 x1 O H10 u1 H8))))))) 
H12)) (subst0_gen_head (Bind Abbr) u x0 x1 t i H11)))))) H_x0)) H_x)))))) 
H6)) (\lambda (H6: (pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) 
(getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 (lift (S O) O t2) 
H6 (lift (S O) O t) (subst0_lift_ge_S t2 t u i H3 O (le_O_n i))))))) 
(pr0_gen_abbr u1 t1 t2 H5)))))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 11671
END *)

theorem pr2_gen_void:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Void) u1 t1) x)).(insert_eq T (THead (Bind Void) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))) 
(\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq T t (THead (Bind Void) u1 t1)) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t2)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift 
(S O) O t0))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H1: (pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Bind Void) u1 
t1))).(let H3 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Bind 
Void) u1 t1) H2) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind 
b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) 
t1 (lift (S O) O t2))))) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead 
c0 (Bind b) u) t1 (lift (S O) O t2))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T t2 (THead (Bind Void) x0 x1))).(\lambda (H6: (pr0 u1 
x0)).(\lambda (H7: (pr0 t1 x1)).(eq_ind_r T (THead (Bind Void) x0 x1) 
(\lambda (t: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead 
c0 (Bind b) u) t1 (lift (S O) O t)))))) (or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Void) x0 x1) (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O (THead (Bind Void) x0 x1))))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Void) x0 x1) (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3))))) x0 x1 (refl_equal T (THead (Bind Void) x0 x1)) (pr2_free c0 u1 
x0 H6) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) t1 x1 
H7))))) t2 H5)))))) H4)) (\lambda (H4: (pr0 t1 (lift (S O) O t2))).(or_intror 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O t2)))) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 
(Bind b) u) t1 (lift (S O) O t2) H4))))) (pr0_gen_void u1 t1 t2 H3)))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H2: (pr0 t0 t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 
t)).(\lambda (H4: (eq T t0 (THead (Bind Void) u1 t1))).(let H5 \def (eq_ind T 
t0 (\lambda (t3: T).(pr0 t3 t2)) H2 (THead (Bind Void) u1 t1) H4) in (or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Bind Void) x0 x1))).(\lambda (H8: (pr0 u1 
x0)).(\lambda (H9: (pr0 t1 x1)).(let H10 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 t)) H3 (THead (Bind Void) x0 x1) H7) in (or3_ind (ex2 T 
(\lambda (u2: T).(eq T t (THead (Bind Void) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind Void) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Void) i) u x1 t3)))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (H11: (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Void) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T (\lambda (u2: T).(eq T t 
(THead (Bind Void) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)) (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T t (THead (Bind 
Void) x2 x1))).(\lambda (H13: (subst0 i u x0 x2)).(or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))))) x2 x1 H12 (pr2_delta c0 d u i H1 u1 x0 H8 
x2 H13) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c0 (Bind b) u0) t1 
x1 H9)))))))) H11)) (\lambda (H11: (ex2 T (\lambda (t3: T).(eq T t (THead 
(Bind Void) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Void) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3)) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x2: T).(\lambda (H12: (eq T t (THead (Bind Void) x0 x2))).(\lambda 
(H13: (subst0 (s (Bind Void) i) u x1 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x0 x2 H12 (pr2_free c0 u1 x0 H8) (\lambda (b: B).(\lambda (u0: 
T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head (Bind b) i c0 
(CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x2 H13)))))))) H11)) (\lambda (H11: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq T t 
(THead (Bind Void) x2 x3))).(\lambda (H13: (subst0 i u x0 x2)).(\lambda (H14: 
(subst0 (s (Bind Void) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x2 x3 H12 (pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head 
(Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x3 H14)))))))))) H11)) 
(subst0_gen_head (Bind Void) u x0 x1 t i H10)))))))) H6)) (\lambda (H6: (pr0 
t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head 
(Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 (lift (S O) O t2) H6 (lift (S 
O) O t) (subst0_lift_ge_S t2 t u i H3 O (le_O_n i))))))) (pr0_gen_void u1 t1 
t2 H5)))))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 3467
END *)

theorem pr2_gen_lift:
 \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).((pr2 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to 
(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr2 e t1 
t2))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H: (pr2 c (lift h d t1) x)).(insert_eq T (lift h d t1) 
(\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(\forall (e: C).((drop h d c e) 
\to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr2 e 
t1 t2)))))) (\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq T t (lift h d t1)) \to (\forall (e: 
C).((drop h d c0 e) \to (ex2 T (\lambda (t2: T).(eq T t0 (lift h d t2))) 
(\lambda (t2: T).(pr2 e t1 t2))))))))) (\lambda (c0: C).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (H1: (pr0 t0 t2)).(\lambda (H2: (eq T t0 (lift h 
d t1))).(\lambda (e: C).(\lambda (_: (drop h d c0 e)).(let H4 \def (eq_ind T 
t0 (\lambda (t: T).(pr0 t t2)) H1 (lift h d t1) H2) in (ex2_ind T (\lambda 
(t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(pr0 t1 t3)) (ex2 T 
(\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (x0: T).(\lambda (H5: (eq T t2 (lift h d x0))).(\lambda (H6: (pr0 t1 
x0)).(eq_ind_r T (lift h d x0) (\lambda (t: T).(ex2 T (\lambda (t3: T).(eq T 
t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3)))) (ex_intro2 T (\lambda 
(t3: T).(eq T (lift h d x0) (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3)) 
x0 (refl_equal T (lift h d x0)) (pr2_free e t1 x0 H6)) t2 H5)))) 
(pr0_gen_lift t1 t2 h d H4)))))))))) (\lambda (c0: C).(\lambda (d0: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d0 (Bind 
Abbr) u))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 
t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda (H4: (eq T t0 
(lift h d t1))).(\lambda (e: C).(\lambda (H5: (drop h d c0 e)).(let H6 \def 
(eq_ind T t0 (\lambda (t3: T).(pr0 t3 t2)) H2 (lift h d t1) H4) in (ex2_ind T 
(\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(pr0 t1 t3)) (ex2 
T (\lambda (t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (x0: T).(\lambda (H7: (eq T t2 (lift h d x0))).(\lambda (H8: (pr0 t1 
x0)).(let H9 \def (eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 t)) H3 (lift h 
d x0) H7) in (lt_le_e i d (ex2 T (\lambda (t3: T).(eq T t (lift h d t3))) 
(\lambda (t3: T).(pr2 e t1 t3))) (\lambda (H10: (lt i d)).(let H11 \def 
(eq_ind nat d (\lambda (n: nat).(subst0 i u (lift h n x0) t)) H9 (S (plus i 
(minus d (S i)))) (lt_plus_minus i d H10)) in (let H12 \def (eq_ind nat d 
(\lambda (n: nat).(drop h n c0 e)) H5 (S (plus i (minus d (S i)))) 
(lt_plus_minus i d H10)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift h (minus d (S i)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind Abbr) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (minus d (S i)) d0 e0))) (ex2 T (\lambda (t3: T).(eq T t (lift h d 
t3))) (\lambda (t3: T).(pr2 e t1 t3))) (\lambda (x1: T).(\lambda (x2: 
C).(\lambda (H13: (eq T u (lift h (minus d (S i)) x1))).(\lambda (H14: (getl 
i e (CHead x2 (Bind Abbr) x1))).(\lambda (_: (drop h (minus d (S i)) d0 
x2)).(let H16 \def (eq_ind T u (\lambda (t3: T).(subst0 i t3 (lift h (S (plus 
i (minus d (S i)))) x0) t)) H11 (lift h (minus d (S i)) x1) H13) in (ex2_ind 
T (\lambda (t3: T).(eq T t (lift h (S (plus i (minus d (S i)))) t3))) 
(\lambda (t3: T).(subst0 i x1 x0 t3)) (ex2 T (\lambda (t3: T).(eq T t (lift h 
d t3))) (\lambda (t3: T).(pr2 e t1 t3))) (\lambda (x3: T).(\lambda (H17: (eq 
T t (lift h (S (plus i (minus d (S i)))) x3))).(\lambda (H18: (subst0 i x1 x0 
x3)).(let H19 \def (eq_ind_r nat (S (plus i (minus d (S i)))) (\lambda (n: 
nat).(eq T t (lift h n x3))) H17 d (lt_plus_minus i d H10)) in (ex_intro2 T 
(\lambda (t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3)) x3 
H19 (pr2_delta e x2 x1 i H14 t1 x0 H8 x3 H18)))))) (subst0_gen_lift_lt x1 x0 
t i h (minus d (S i)) H16)))))))) (getl_drop_conf_lt Abbr c0 d0 u i H1 e h 
(minus d (S i)) H12))))) (\lambda (H10: (le d i)).(lt_le_e i (plus d h) (ex2 
T (\lambda (t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (H11: (lt i (plus d h))).(subst0_gen_lift_false x0 u t h d i H10 H11 
H9 (ex2 T (\lambda (t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 
t3))))) (\lambda (H11: (le (plus d h) i)).(ex2_ind T (\lambda (t3: T).(eq T t 
(lift h d t3))) (\lambda (t3: T).(subst0 (minus i h) u x0 t3)) (ex2 T 
(\lambda (t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (x1: T).(\lambda (H12: (eq T t (lift h d x1))).(\lambda (H13: 
(subst0 (minus i h) u x0 x1)).(ex_intro2 T (\lambda (t3: T).(eq T t (lift h d 
t3))) (\lambda (t3: T).(pr2 e t1 t3)) x1 H12 (pr2_delta e d0 u (minus i h) 
(getl_drop_conf_ge i (CHead d0 (Bind Abbr) u) c0 H1 e h d H5 H11) t1 x0 H8 x1 
H13))))) (subst0_gen_lift_ge u x0 t i h d H9 H11)))))))))) (pr0_gen_lift t1 
t2 h d H6)))))))))))))))) c y x H0))) H)))))).
(* COMMENTS
Initial nodes: 1579
END *)

