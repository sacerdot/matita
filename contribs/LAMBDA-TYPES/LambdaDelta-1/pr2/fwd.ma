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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/pr2/fwd".

include "pr2/defs.ma".

include "pr0/fwd.ma".

include "getl/drop.ma".

include "getl/clear.ma".

theorem pr2_gen_sort:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TSort n) x) \to 
(eq T x (TSort n)))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr2 c (TSort 
n) x)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 c) \to ((eq T t 
(TSort n)) \to ((eq T t0 x) \to (eq T x (TSort n))))))))) with [(pr2_free c0 
t1 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: (eq T t1 
(TSort n))).(\lambda (H3: (eq T t2 x)).(eq_ind C c (\lambda (_: C).((eq T t1 
(TSort n)) \to ((eq T t2 x) \to ((pr0 t1 t2) \to (eq T x (TSort n)))))) 
(\lambda (H4: (eq T t1 (TSort n))).(eq_ind T (TSort n) (\lambda (t: T).((eq T 
t2 x) \to ((pr0 t t2) \to (eq T x (TSort n))))) (\lambda (H5: (eq T t2 
x)).(eq_ind T x (\lambda (t: T).((pr0 (TSort n) t) \to (eq T x (TSort n)))) 
(\lambda (H6: (pr0 (TSort n) x)).(let H7 \def (eq_ind T x (\lambda (t: 
T).(pr2 c (TSort n) t)) H (TSort n) (pr0_gen_sort x n H6)) in (eq_ind_r T 
(TSort n) (\lambda (t: T).(eq T t (TSort n))) (refl_equal T (TSort n)) x 
(pr0_gen_sort x n H6)))) t2 (sym_eq T t2 x H5))) t1 (sym_eq T t1 (TSort n) 
H4))) c0 (sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u i H0 t1 t2 H1 t 
H2) \Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq T t1 (TSort 
n))).(\lambda (H5: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T t1 (TSort 
n)) \to ((eq T t x) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t1 t2) 
\to ((subst0 i u t2 t) \to (eq T x (TSort n)))))))) (\lambda (H6: (eq T t1 
(TSort n))).(eq_ind T (TSort n) (\lambda (t0: T).((eq T t x) \to ((getl i c 
(CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) \to (eq T x 
(TSort n))))))) (\lambda (H7: (eq T t x)).(eq_ind T x (\lambda (t0: T).((getl 
i c (CHead d (Bind Abbr) u)) \to ((pr0 (TSort n) t2) \to ((subst0 i u t2 t0) 
\to (eq T x (TSort n)))))) (\lambda (_: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (H9: (pr0 (TSort n) t2)).(\lambda (H10: (subst0 i u t2 x)).(let 
H11 \def (eq_ind T t2 (\lambda (t0: T).(subst0 i u t0 x)) H10 (TSort n) 
(pr0_gen_sort t2 n H9)) in (subst0_gen_sort u x i n H11 (eq T x (TSort 
n))))))) t (sym_eq T t x H7))) t1 (sym_eq T t1 (TSort n) H6))) c0 (sym_eq C 
c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 (refl_equal C c) (refl_equal T (TSort 
n)) (refl_equal T x)))))).

theorem pr2_gen_lref:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr2 c (TLRef n) x) \to 
(or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c 
(CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T x (lift (S 
n) O u)))))))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr2 c (TLRef 
n) x)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 c) \to ((eq T t 
(TLRef n)) \to ((eq T t0 x) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda 
(d: C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T x (lift (S n) O u))))))))))))) with [(pr2_free c0 t1 
t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: (eq T t1 (TLRef 
n))).(\lambda (H3: (eq T t2 x)).(eq_ind C c (\lambda (_: C).((eq T t1 (TLRef 
n)) \to ((eq T t2 x) \to ((pr0 t1 t2) \to (or (eq T x (TLRef n)) (ex2_2 C T 
(\lambda (d: C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda 
(_: C).(\lambda (u: T).(eq T x (lift (S n) O u)))))))))) (\lambda (H4: (eq T 
t1 (TLRef n))).(eq_ind T (TLRef n) (\lambda (t: T).((eq T t2 x) \to ((pr0 t 
t2) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: 
T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T 
x (lift (S n) O u))))))))) (\lambda (H5: (eq T t2 x)).(eq_ind T x (\lambda 
(t: T).((pr0 (TLRef n) t) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T x (lift (S n) O u)))))))) (\lambda (H6: (pr0 (TLRef 
n) x)).(let H7 \def (eq_ind T x (\lambda (t: T).(pr2 c (TLRef n) t)) H (TLRef 
n) (pr0_gen_lref x n H6)) in (eq_ind_r T (TLRef n) (\lambda (t: T).(or (eq T 
t (TLRef n)) (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c (CHead d 
(Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t (lift (S n) O 
u))))))) (or_introl (eq T (TLRef n) (TLRef n)) (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl n c (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T (TLRef n) (lift (S n) O u))))) (refl_equal T (TLRef 
n))) x (pr0_gen_lref x n H6)))) t2 (sym_eq T t2 x H5))) t1 (sym_eq T t1 
(TLRef n) H4))) c0 (sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u i H0 
t1 t2 H1 t H2) \Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq T t1 
(TLRef n))).(\lambda (H5: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T t1 
(TLRef n)) \to ((eq T t x) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 
t1 t2) \to ((subst0 i u t2 t) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl n c (CHead d0 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(eq T x (lift (S n) O u0)))))))))))) (\lambda (H6: (eq T 
t1 (TLRef n))).(eq_ind T (TLRef n) (\lambda (t0: T).((eq T t x) \to ((getl i 
c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) \to (or 
(eq T x (TLRef n)) (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl n c 
(CHead d0 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T x (lift 
(S n) O u0))))))))))) (\lambda (H7: (eq T t x)).(eq_ind T x (\lambda (t0: 
T).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 (TLRef n) t2) \to ((subst0 i 
u t2 t0) \to (or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d0: C).(\lambda (u0: 
T).(getl n c (CHead d0 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: 
T).(eq T x (lift (S n) O u0)))))))))) (\lambda (H8: (getl i c (CHead d (Bind 
Abbr) u))).(\lambda (H9: (pr0 (TLRef n) t2)).(\lambda (H10: (subst0 i u t2 
x)).(let H11 \def (eq_ind T t2 (\lambda (t0: T).(subst0 i u t0 x)) H10 (TLRef 
n) (pr0_gen_lref t2 n H9)) in (and_ind (eq nat n i) (eq T x (lift (S n) O u)) 
(or (eq T x (TLRef n)) (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl n c 
(CHead d0 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T x (lift 
(S n) O u0)))))) (\lambda (H12: (eq nat n i)).(\lambda (H13: (eq T x (lift (S 
n) O u))).(let H14 \def (eq_ind_r nat i (\lambda (n0: nat).(getl n0 c (CHead 
d (Bind Abbr) u))) H8 n H12) in (let H15 \def (eq_ind T x (\lambda (t0: 
T).(pr2 c (TLRef n) t0)) H (lift (S n) O u) H13) in (eq_ind_r T (lift (S n) O 
u) (\lambda (t0: T).(or (eq T t0 (TLRef n)) (ex2_2 C T (\lambda (d0: 
C).(\lambda (u0: T).(getl n c (CHead d0 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(eq T t0 (lift (S n) O u0))))))) (or_intror (eq T (lift 
(S n) O u) (TLRef n)) (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl n c 
(CHead d0 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T (lift (S 
n) O u) (lift (S n) O u0))))) (ex2_2_intro C T (\lambda (d0: C).(\lambda (u0: 
T).(getl n c (CHead d0 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: 
T).(eq T (lift (S n) O u) (lift (S n) O u0)))) d u H14 (refl_equal T (lift (S 
n) O u)))) x H13))))) (subst0_gen_lref u x i n H11)))))) t (sym_eq T t x 
H7))) t1 (sym_eq T t1 (TLRef n) H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 
H2))))]) in (H0 (refl_equal C c) (refl_equal T (TLRef n)) (refl_equal T 
x)))))).

theorem pr2_gen_abst:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t2))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Abst) u1 t1) x)).(let H0 \def (match H in pr2 return 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t 
t0)).((eq C c0 c) \to ((eq T t (THead (Bind Abst) u1 t1)) \to ((eq T t0 x) 
\to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
t1 t2))))))))))))) with [(pr2_free c0 t0 t2 H0) \Rightarrow (\lambda (H1: (eq 
C c0 c)).(\lambda (H2: (eq T t0 (THead (Bind Abst) u1 t1))).(\lambda (H3: (eq 
T t2 x)).(eq_ind C c (\lambda (_: C).((eq T t0 (THead (Bind Abst) u1 t1)) \to 
((eq T t2 x) \to ((pr0 t0 t2) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3)))))))))) (\lambda (H4: (eq T t0 (THead 
(Bind Abst) u1 t1))).(eq_ind T (THead (Bind Abst) u1 t1) (\lambda (t: T).((eq 
T t2 x) \to ((pr0 t t2) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 t3))))))))) (\lambda (H5: (eq T t2 x)).(eq_ind T x 
(\lambda (t: T).((pr0 (THead (Bind Abst) u1 t1) t) \to (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))))) (\lambda (H6: 
(pr0 (THead (Bind Abst) u1 t1) x)).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T x (THead (Bind Abst) x0 
x1))).(\lambda (H8: (pr0 u1 x0)).(\lambda (H9: (pr0 t1 x1)).(let H10 \def 
(eq_ind T x (\lambda (t: T).(pr2 c (THead (Bind Abst) u1 t1) t)) H (THead 
(Bind Abst) x0 x1) H7) in (eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t: 
T).(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abst) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
t1 t3))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abst) x0 x1) (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) t1 t3))))) x0 x1 (refl_equal T (THead (Bind 
Abst) x0 x1)) (pr2_free c u1 x0 H8) (\lambda (b: B).(\lambda (u: T).(pr2_free 
(CHead c (Bind b) u) t1 x1 H9)))) x H7))))))) (pr0_gen_abst u1 t1 x H6))) t2 
(sym_eq T t2 x H5))) t0 (sym_eq T t0 (THead (Bind Abst) u1 t1) H4))) c0 
(sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u i H0 t0 t2 H1 t H2) 
\Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq T t0 (THead (Bind 
Abst) u1 t1))).(\lambda (H5: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T 
t0 (THead (Bind Abst) u1 t1)) \to ((eq T t x) \to ((getl i c1 (CHead d (Bind 
Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) \to (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))))))))) (\lambda 
(H6: (eq T t0 (THead (Bind Abst) u1 t1))).(eq_ind T (THead (Bind Abst) u1 t1) 
(\lambda (t3: T).((eq T t x) \to ((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 t3 t2) \to ((subst0 i u t2 t) \to (ex3_2 T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T x (THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t4))))))))))) (\lambda (H7: (eq T t 
x)).(eq_ind T x (\lambda (t3: T).((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 (THead (Bind Abst) u1 t1) t2) \to ((subst0 i u t2 t3) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Bind Abst) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t4)))))))))) (\lambda (H8: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H9: 
(pr0 (THead (Bind Abst) u1 t1) t2)).(\lambda (H10: (subst0 i u t2 
x)).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H11: (eq T t2 (THead (Bind Abst) x0 x1))).(\lambda (H12: (pr0 u1 
x0)).(\lambda (H13: (pr0 t1 x1)).(let H14 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 x)) H10 (THead (Bind Abst) x0 x1) H11) in (or3_ind (ex2 T 
(\lambda (u2: T).(eq T x (THead (Bind Abst) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T x (THead (Bind Abst) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abst) i) u x1 t3)))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\lambda (H15: (ex2 T (\lambda 
(u2: T).(eq T x (THead (Bind Abst) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead (Bind Abst) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\lambda (x2: T).(\lambda 
(H16: (eq T x (THead (Bind Abst) x2 x1))).(\lambda (H17: (subst0 i u x0 
x2)).(let H18 \def (eq_ind T x (\lambda (t3: T).(pr2 c (THead (Bind Abst) u1 
t1) t3)) H (THead (Bind Abst) x2 x1) H16) in (eq_ind_r T (THead (Bind Abst) 
x2 x1) (\lambda (t3: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Bind Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c (Bind b) u0) t1 t4))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abst) x2 x1) (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))))) x2 x1 
(refl_equal T (THead (Bind Abst) x2 x1)) (pr2_delta c d u i H8 u1 x0 H12 x2 
H17) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c (Bind b) u0) t1 x1 
H13)))) x H16))))) H15)) (\lambda (H15: (ex2 T (\lambda (t3: T).(eq T x 
(THead (Bind Abst) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T x (THead (Bind Abst) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abst) i) u x1 t3)) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\lambda (x2: 
T).(\lambda (H16: (eq T x (THead (Bind Abst) x0 x2))).(\lambda (H17: (subst0 
(s (Bind Abst) i) u x1 x2)).(let H18 \def (eq_ind T x (\lambda (t3: T).(pr2 c 
(THead (Bind Abst) u1 t1) t3)) H (THead (Bind Abst) x0 x2) H16) in (eq_ind_r 
T (THead (Bind Abst) x0 x2) (\lambda (t3: T).(ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abst) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t4))))))) (ex3_2_intro 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abst) x0 x2) (THead 
(Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c (Bind b) u0) t1 t3))))) x0 x2 (refl_equal T (THead (Bind Abst) x0 x2)) 
(pr2_free c u1 x0 H12) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c 
(Bind b) u0) d u (S i) (getl_head (Bind b) i c (CHead d (Bind Abbr) u) H8 u0) 
t1 x1 H13 x2 H17)))) x H16))))) H15)) (\lambda (H15: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abst) i) u x1 t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abst) i) u x1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H16: (eq T x (THead (Bind Abst) x2 x3))).(\lambda (H17: (subst0 
i u x0 x2)).(\lambda (H18: (subst0 (s (Bind Abst) i) u x1 x3)).(let H19 \def 
(eq_ind T x (\lambda (t3: T).(pr2 c (THead (Bind Abst) u1 t1) t3)) H (THead 
(Bind Abst) x2 x3) H16) in (eq_ind_r T (THead (Bind Abst) x2 x3) (\lambda 
(t3: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abst) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t4))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind Abst) x2 x3) (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))))) x2 x3 
(refl_equal T (THead (Bind Abst) x2 x3)) (pr2_delta c d u i H8 u1 x0 H12 x2 
H17) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c (Bind b) u0) d u (S 
i) (getl_head (Bind b) i c (CHead d (Bind Abbr) u) H8 u0) t1 x1 H13 x3 
H18)))) x H16))))))) H15)) (subst0_gen_head (Bind Abst) u x0 x1 x i 
H14)))))))) (pr0_gen_abst u1 t1 t2 H9))))) t (sym_eq T t x H7))) t0 (sym_eq T 
t0 (THead (Bind Abst) u1 t1) H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) 
in (H0 (refl_equal C c) (refl_equal T (THead (Bind Abst) u1 t1)) (refl_equal 
T x))))))).

theorem pr2_gen_cast:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr2 c t1 t2)))) (pr2 c 
t1 x))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Flat Cast) u1 t1) x)).(let H0 \def (match H in pr2 return 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t 
t0)).((eq C c0 c) \to ((eq T t (THead (Flat Cast) u1 t1)) \to ((eq T t0 x) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat 
Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr2 c t1 t2)))) (pr2 c t1 x))))))))) with [(pr2_free c0 
t0 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: (eq T t0 
(THead (Flat Cast) u1 t1))).(\lambda (H3: (eq T t2 x)).(eq_ind C c (\lambda 
(_: C).((eq T t0 (THead (Flat Cast) u1 t1)) \to ((eq T t2 x) \to ((pr0 t0 t2) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)))))) (\lambda (H4: (eq T t0 
(THead (Flat Cast) u1 t1))).(eq_ind T (THead (Flat Cast) u1 t1) (\lambda (t: 
T).((eq T t2 x) \to ((pr0 t t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c 
t1 x))))) (\lambda (H5: (eq T t2 x)).(eq_ind T x (\lambda (t: T).((pr0 (THead 
(Flat Cast) u1 t1) t) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)))) 
(\lambda (H6: (pr0 (THead (Flat Cast) u1 t1) x)).(or_ind (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (H7: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H8: (eq T x (THead (Flat Cast) x0 x1))).(\lambda (H9: (pr0 u1 
x0)).(\lambda (H10: (pr0 t1 x1)).(let H11 \def (eq_ind T x (\lambda (t: 
T).(pr2 c (THead (Flat Cast) u1 t1) t)) H (THead (Flat Cast) x0 x1) H8) in 
(eq_ind_r T (THead (Flat Cast) x0 x1) (\lambda (t: T).(or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (pr2 c t1 t))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Flat Cast) x0 x1) (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (pr2 c t1 (THead (Flat Cast) x0 x1)) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Cast) x0 x1) (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3))) x0 x1 (refl_equal T (THead (Flat Cast) x0 
x1)) (pr2_free c u1 x0 H9) (pr2_free c t1 x1 H10))) x H8))))))) H7)) (\lambda 
(H7: (pr0 t1 x)).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x) 
(pr2_free c t1 x H7))) (pr0_gen_cast u1 t1 x H6))) t2 (sym_eq T t2 x H5))) t0 
(sym_eq T t0 (THead (Flat Cast) u1 t1) H4))) c0 (sym_eq C c0 c H1) H2 H3 
H0)))) | (pr2_delta c0 d u i H0 t0 t2 H1 t H2) \Rightarrow (\lambda (H3: (eq 
C c0 c)).(\lambda (H4: (eq T t0 (THead (Flat Cast) u1 t1))).(\lambda (H5: (eq 
T t x)).(eq_ind C c (\lambda (c1: C).((eq T t0 (THead (Flat Cast) u1 t1)) \to 
((eq T t x) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to 
((subst0 i u t2 t) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)))))))) 
(\lambda (H6: (eq T t0 (THead (Flat Cast) u1 t1))).(eq_ind T (THead (Flat 
Cast) u1 t1) (\lambda (t3: T).((eq T t x) \to ((getl i c (CHead d (Bind Abbr) 
u)) \to ((pr0 t3 t2) \to ((subst0 i u t2 t) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T x (THead (Flat Cast) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c t1 
t4)))) (pr2 c t1 x))))))) (\lambda (H7: (eq T t x)).(eq_ind T x (\lambda (t3: 
T).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 (THead (Flat Cast) u1 t1) 
t2) \to ((subst0 i u t2 t3) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T x (THead (Flat Cast) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c t1 t4)))) (pr2 c t1 
x)))))) (\lambda (H8: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H9: (pr0 
(THead (Flat Cast) u1 t1) t2)).(\lambda (H10: (subst0 i u t2 x)).(or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (pr2 c t1 x)) (\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H12: (eq T t2 (THead (Flat Cast) x0 
x1))).(\lambda (H13: (pr0 u1 x0)).(\lambda (H14: (pr0 t1 x1)).(let H15 \def 
(eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 x)) H10 (THead (Flat Cast) x0 
x1) H12) in (or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead (Flat Cast) u2 
x1))) (\lambda (u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T x 
(THead (Flat Cast) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 
t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (H16: (ex2 T (\lambda (u2: 
T).(eq T x (THead (Flat Cast) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead (Flat Cast) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c 
t1 x)) (\lambda (x2: T).(\lambda (H17: (eq T x (THead (Flat Cast) x2 
x1))).(\lambda (H18: (subst0 i u x0 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (pr2 c t1 x) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3))) x2 x1 H17 (pr2_delta c 
d u i H8 u1 x0 H13 x2 H18) (pr2_free c t1 x1 H14)))))) H16)) (\lambda (H16: 
(ex2 T (\lambda (t3: T).(eq T x (THead (Flat Cast) x0 t3))) (\lambda (t3: 
T).(subst0 (s (Flat Cast) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x 
(THead (Flat Cast) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 
t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (x2: T).(\lambda 
(H17: (eq T x (THead (Flat Cast) x0 x2))).(\lambda (H18: (subst0 (s (Flat 
Cast) i) u x1 x2)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3))) x0 x2 H17 (pr2_free c u1 x0 H13) 
(pr2_delta c d u i H8 t1 x1 H14 x2 H18)))))) H16)) (\lambda (H16: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Flat Cast) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (pr2 c t1 x)) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H17: (eq T x (THead (Flat Cast) x2 x3))).(\lambda (H18: (subst0 
i u x0 x2)).(\lambda (H19: (subst0 (s (Flat Cast) i) u x1 x3)).(or_introl 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (pr2 c t1 x) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3))) x2 x3 H17 (pr2_delta c d u i H8 u1 x0 H13 x2 H18) (pr2_delta c d u i H8 
t1 x1 H14 x3 H19)))))))) H16)) (subst0_gen_head (Flat Cast) u x0 x1 x i 
H15)))))))) H11)) (\lambda (H11: (pr0 t1 t2)).(or_intror (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (pr2 c t1 x) (pr2_delta c d u i H8 t1 t2 H11 x H10))) (pr0_gen_cast u1 
t1 t2 H9))))) t (sym_eq T t x H7))) t0 (sym_eq T t0 (THead (Flat Cast) u1 t1) 
H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 (refl_equal C c) 
(refl_equal T (THead (Flat Cast) u1 t1)) (refl_equal T x))))))).

theorem pr2_gen_csort:
 \forall (t1: T).(\forall (t2: T).(\forall (n: nat).((pr2 (CSort n) t1 t2) 
\to (pr0 t1 t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (n: nat).(\lambda (H: (pr2 (CSort 
n) t1 t2)).(let H0 \def (match H in pr2 return (\lambda (c: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c t t0)).((eq C c (CSort n)) \to ((eq T 
t t1) \to ((eq T t0 t2) \to (pr0 t1 t2)))))))) with [(pr2_free c t0 t3 H0) 
\Rightarrow (\lambda (H1: (eq C c (CSort n))).(\lambda (H2: (eq T t0 
t1)).(\lambda (H3: (eq T t3 t2)).(eq_ind C (CSort n) (\lambda (_: C).((eq T 
t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (pr0 t1 t2))))) (\lambda (H4: 
(eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to 
(pr0 t1 t2)))) (\lambda (H5: (eq T t3 t2)).(eq_ind T t2 (\lambda (t: T).((pr0 
t1 t) \to (pr0 t1 t2))) (\lambda (H6: (pr0 t1 t2)).H6) t3 (sym_eq T t3 t2 
H5))) t0 (sym_eq T t0 t1 H4))) c (sym_eq C c (CSort n) H1) H2 H3 H0)))) | 
(pr2_delta c d u i H0 t0 t3 H1 t H2) \Rightarrow (\lambda (H3: (eq C c (CSort 
n))).(\lambda (H4: (eq T t0 t1)).(\lambda (H5: (eq T t t2)).(eq_ind C (CSort 
n) (\lambda (c0: C).((eq T t0 t1) \to ((eq T t t2) \to ((getl i c0 (CHead d 
(Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i u t3 t) \to (pr0 t1 t2))))))) 
(\lambda (H6: (eq T t0 t1)).(eq_ind T t1 (\lambda (t4: T).((eq T t t2) \to 
((getl i (CSort n) (CHead d (Bind Abbr) u)) \to ((pr0 t4 t3) \to ((subst0 i u 
t3 t) \to (pr0 t1 t2)))))) (\lambda (H7: (eq T t t2)).(eq_ind T t2 (\lambda 
(t4: T).((getl i (CSort n) (CHead d (Bind Abbr) u)) \to ((pr0 t1 t3) \to 
((subst0 i u t3 t4) \to (pr0 t1 t2))))) (\lambda (H8: (getl i (CSort n) 
(CHead d (Bind Abbr) u))).(\lambda (_: (pr0 t1 t3)).(\lambda (_: (subst0 i u 
t3 t2)).(getl_gen_sort n i (CHead d (Bind Abbr) u) H8 (pr0 t1 t2))))) t 
(sym_eq T t t2 H7))) t0 (sym_eq T t0 t1 H6))) c (sym_eq C c (CSort n) H3) H4 
H5 H0 H1 H2))))]) in (H0 (refl_equal C (CSort n)) (refl_equal T t1) 
(refl_equal T t2)))))).

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
(H: (pr2 c (THead (Flat Appl) u1 t1) x)).(let H0 \def (match H in pr2 return 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t 
t0)).((eq C c0 c) \to ((eq T t (THead (Flat Appl) u1 t1)) \to ((eq T t0 x) 
\to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Flat 
Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr2 c t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t2)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))))))))) with [(pr2_free c0 
t0 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: (eq T t0 
(THead (Flat Appl) u1 t1))).(\lambda (H3: (eq T t2 x)).(eq_ind C c (\lambda 
(_: C).((eq T t0 (THead (Flat Appl) u1 t1)) \to ((eq T t2 x) \to ((pr0 t0 t2) 
\to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))))))) (\lambda (H4: (eq T t0 
(THead (Flat Appl) u1 t1))).(eq_ind T (THead (Flat Appl) u1 t1) (\lambda (t: 
T).((eq T t2 x) \to ((pr0 t t2) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T 
T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T 
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
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))))) (\lambda 
(H5: (eq T t2 x)).(eq_ind T x (\lambda (t: T).((pr0 (THead (Flat Appl) u1 t1) 
t) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))))) (\lambda (H6: (pr0 (THead 
(Flat Appl) u1 t1) x)).(or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (H7: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
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
y2) z1 z2))))))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H8: (eq T x 
(THead (Flat Appl) x0 x1))).(\lambda (H9: (pr0 u1 x0)).(\lambda (H10: (pr0 t1 
x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x1) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x1) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Flat Appl) x0 x1) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x1) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3))) x0 x1 (refl_equal T (THead (Flat Appl) x0 
x1)) (pr2_free c u1 x0 H9) (pr2_free c t1 x1 H10))) x H8)))))) H7)) (\lambda 
(H7: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))).(ex4_4_ind T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H8: (eq T t1 (THead (Bind 
Abst) x0 x1))).(\lambda (H9: (eq T x (THead (Bind Abbr) x2 x3))).(\lambda 
(H10: (pr0 u1 x2)).(\lambda (H11: (pr0 x1 x3)).(eq_ind_r T (THead (Bind Abbr) 
x2 x3) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead 
(Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (eq_ind_r 
T (THead (Bind Abst) x0 x1) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x3) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T 
T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq 
T t (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x2 x3) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x3) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind Abbr) x2 x3) (THead 
(Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex4_4_intro 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind Abst) x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x2 x3) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t3))))))) x0 x1 x2 x3 (refl_equal T 
(THead (Bind Abst) x0 x1)) (refl_equal T (THead (Bind Abbr) x2 x3)) (pr2_free 
c u1 x2 H10) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c (Bind b) u) 
x1 x3 H11))))) t1 H8) x H9))))))))) H7)) (\lambda (H7: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not 
(eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) 
y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) v2 (THead (Flat 
Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T 
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
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda 
(x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H8: (not (eq B x0 Abst))).(\lambda (H9: (eq T 
t1 (THead (Bind x0) x1 x2))).(\lambda (H10: (eq T x (THead (Bind x0) x4 
(THead (Flat Appl) (lift (S O) O x3) x5)))).(\lambda (H11: (pr0 u1 
x3)).(\lambda (H12: (pr0 x1 x4)).(\lambda (H13: (pr0 x2 x5)).(eq_ind_r T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (\lambda (t: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (eq_ind_r T (THead (Bind 
x0) x1 x2) (\lambda (t: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x3) x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x5 x3 x4 H8 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5))) (pr2_free c u1 
x3 H11) (pr2_free c x1 x4 H12) (pr2_free (CHead c (Bind x0) x4) x2 x5 H13))) 
t1 H9) x H10))))))))))))) H7)) (pr0_gen_appl u1 t1 x H6))) t2 (sym_eq T t2 x 
H5))) t0 (sym_eq T t0 (THead (Flat Appl) u1 t1) H4))) c0 (sym_eq C c0 c H1) 
H2 H3 H0)))) | (pr2_delta c0 d u i H0 t0 t2 H1 t H2) \Rightarrow (\lambda 
(H3: (eq C c0 c)).(\lambda (H4: (eq T t0 (THead (Flat Appl) u1 t1))).(\lambda 
(H5: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T t0 (THead (Flat Appl) u1 
t1)) \to ((eq T t x) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t0 
t2) \to ((subst0 i u t2 t) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2))))))))))))))) (\lambda (H6: (eq T t0 (THead (Flat Appl) u1 t1))).(eq_ind 
T (THead (Flat Appl) u1 t1) (\lambda (t3: T).((eq T t x) \to ((getl i c 
(CHead d (Bind Abbr) u)) \to ((pr0 t3 t2) \to ((subst0 i u t2 t) \to (or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T x (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))))))) (\lambda (H7: (eq T t 
x)).(eq_ind T x (\lambda (t3: T).((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 (THead (Flat Appl) u1 t1) t2) \to ((subst0 i u t2 t3) \to (or3 (ex3_2 T 
T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T x 
(THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))))))) (\lambda (H8: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (H9: (pr0 (THead (Flat Appl) u1 t1) 
t2)).(\lambda (H10: (subst0 i u t2 x)).(or3_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) 
(\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H12: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H13: 
(pr0 u1 x0)).(\lambda (H14: (pr0 t1 x1)).(let H15 \def (eq_ind T t2 (\lambda 
(t3: T).(subst0 i u t3 x)) H10 (THead (Flat Appl) x0 x1) H12) in (or3_ind 
(ex2 T (\lambda (u2: T).(eq T x (THead (Flat Appl) u2 x1))) (\lambda (u2: 
T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T x (THead (Flat Appl) x0 
t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3)))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (H16: (ex2 T 
(\lambda (u2: T).(eq T x (THead (Flat Appl) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead (Flat Appl) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda (H17: (eq T x 
(THead (Flat Appl) x2 x1))).(\lambda (H18: (subst0 i u x0 x2)).(eq_ind_r T 
(THead (Flat Appl) x2 x1) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c t1 
t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x1) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Flat Appl) x2 x1) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Flat Appl) x2 x1) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O 
u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Flat Appl) x2 x1) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3))) x2 x1 (refl_equal T (THead (Flat Appl) x2 x1)) (pr2_delta c d u i H8 u1 
x0 H13 x2 H18) (pr2_free c t1 x1 H14))) x H17)))) H16)) (\lambda (H16: (ex2 T 
(\lambda (t3: T).(eq T x (THead (Flat Appl) x0 t3))) (\lambda (t3: T).(subst0 
(s (Flat Appl) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x (THead 
(Flat Appl) x0 t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3)) 
(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda 
(H17: (eq T x (THead (Flat Appl) x0 x2))).(\lambda (H18: (subst0 (s (Flat 
Appl) i) u x1 x2)).(eq_ind_r T (THead (Flat Appl) x0 x2) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat 
Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda 
(_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) 
(or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat 
Appl) x0 x2) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T 
T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x2) (THead (Bind Abbr) 
u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T (THead (Flat Appl) x0 x2) (THead (Bind b) y2 
(THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x0 x2) (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3))) x0 x2 (refl_equal T (THead (Flat Appl) x0 
x2)) (pr2_free c u1 x0 H13) (pr2_delta c d u i H8 t1 x1 H14 x2 H18))) x 
H17)))) H16)) (\lambda (H16: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u 
x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 
t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) 
(\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) i) u x1 t3))) (or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H17: (eq T x (THead (Flat Appl) x2 x3))).(\lambda (H18: 
(subst0 i u x0 x2)).(\lambda (H19: (subst0 (s (Flat Appl) i) u x1 
x3)).(eq_ind_r T (THead (Flat Appl) x2 x3) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c t1 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro0 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T (THead (Flat Appl) x2 x3) (THead (Bind b) y2 
(THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex3_2_intro T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Flat Appl) x2 x3) (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3))) x2 x3 (refl_equal T (THead (Flat Appl) x2 
x3)) (pr2_delta c d u i H8 u1 x0 H13 x2 H18) (pr2_delta c d u i H8 t1 x1 H14 
x3 H19))) x H17)))))) H16)) (subst0_gen_head (Flat Appl) u x0 x1 x i 
H15)))))))) H11)) (\lambda (H11: (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))))).(ex4_4_ind T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))) (or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq T t1 (THead 
(Bind Abst) x0 x1))).(\lambda (H13: (eq T t2 (THead (Bind Abbr) x2 
x3))).(\lambda (H14: (pr0 u1 x2)).(\lambda (H15: (pr0 x1 x3)).(let H16 \def 
(eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 x)) H10 (THead (Bind Abbr) x2 
x3) H13) in (eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c t3 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T x (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda 
(u2: T).(eq T x (THead (Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 i u x2 
u2))) (ex2 T (\lambda (t3: T).(eq T x (THead (Bind Abbr) x2 t3))) (\lambda 
(t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x3 t3)))) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (H17: (ex2 T (\lambda (u2: T).(eq T x (THead 
(Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 i u x2 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T x (THead (Bind Abbr) u2 x3))) (\lambda (u2: T).(subst0 
i u x2 u2)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind Abst) x0 x1) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x4: T).(\lambda 
(H18: (eq T x (THead (Bind Abbr) x4 x3))).(\lambda (H19: (subst0 i u x2 
x4)).(eq_ind_r T (THead (Bind Abbr) x4 x3) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c (THead (Bind Abst) x0 x1) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x4 x3) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x4 x3) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x3) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3))))))) x0 x1 x4 x3 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x4 x3)) (pr2_delta c d u i H8 u1 x2 H14 x4 
H19) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c (Bind b) u0) x1 x3 
H15))))) x H18)))) H17)) (\lambda (H17: (ex2 T (\lambda (t3: T).(eq T x 
(THead (Bind Abbr) x2 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T x (THead (Bind Abbr) x2 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3)) (or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (x4: T).(\lambda (H18: (eq T x (THead (Bind Abbr) 
x2 x4))).(\lambda (H19: (subst0 (s (Bind Abbr) i) u x3 x4)).(eq_ind_r T 
(THead (Bind Abbr) x2 x4) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind Abst) x0 x1) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x2 x4) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x4) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x2 x4) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x2 x4) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3))))))) x0 x1 x2 x4 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x2 x4)) (pr2_free c u1 x2 H14) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c (Bind b) u0) d u (S i) 
(getl_clear_bind b (CHead c (Bind b) u0) c u0 (clear_bind b c u0) (CHead d 
(Bind Abbr) u) i H8) x1 x3 H15 x4 H19))))) x H18)))) H17)) (\lambda (H17: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x2 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x3 t3))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c (THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) 
x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) 
O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H18: (eq T x 
(THead (Bind Abbr) x4 x5))).(\lambda (H19: (subst0 i u x2 x4)).(\lambda (H20: 
(subst0 (s (Bind Abbr) i) u x3 x5)).(eq_ind_r T (THead (Bind Abbr) x4 x5) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind Abst) x0 x1) t4)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind Abst) x0 x1) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
Abst) x0 x1) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind Abbr) x4 x5) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind Abst) x0 x1) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind 
Abbr) x4 x5) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) x0 x1) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) x4 x5) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3))))))) x0 x1 x4 x5 (refl_equal T (THead (Bind Abst) x0 x1)) 
(refl_equal T (THead (Bind Abbr) x4 x5)) (pr2_delta c d u i H8 u1 x2 H14 x4 
H19) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c (Bind b) u0) d u (S 
i) (getl_clear_bind b (CHead c (Bind b) u0) c u0 (clear_bind b c u0) (CHead d 
(Bind Abbr) u) i H8) x1 x3 H15 x5 H20))))) x H18)))))) H17)) (subst0_gen_head 
(Bind Abbr) u x2 x3 x i H16)) t1 H12)))))))))) H11)) (\lambda (H11: (ex6_6 B 
T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T 
t2 (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
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
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x0: B).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H12: (not (eq B x0 Abst))).(\lambda (H13: (eq T t1 (THead (Bind 
x0) x1 x2))).(\lambda (H14: (eq T t2 (THead (Bind x0) x4 (THead (Flat Appl) 
(lift (S O) O x3) x5)))).(\lambda (H15: (pr0 u1 x3)).(\lambda (H16: (pr0 x1 
x4)).(\lambda (H17: (pr0 x2 x5)).(let H18 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 x)) H10 (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x3) x5)) H14) in (eq_ind_r T (THead (Bind x0) x1 x2) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c t3 t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T x (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t3 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda 
(u2: T).(eq T x (THead (Bind x0) u2 (THead (Flat Appl) (lift (S O) O x3) 
x5)))) (\lambda (u2: T).(subst0 i u x4 u2))) (ex2 T (\lambda (t3: T).(eq T x 
(THead (Bind x0) x4 t3))) (\lambda (t3: T).(subst0 (s (Bind x0) i) u (THead 
(Flat Appl) (lift (S O) O x3) x5) t3))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind x0) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u x4 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind x0) 
i) u (THead (Flat Appl) (lift (S O) O x3) x5) t3)))) (or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (H19: (ex2 T (\lambda (u2: T).(eq T x (THead 
(Bind x0) u2 (THead (Flat Appl) (lift (S O) O x3) x5)))) (\lambda (u2: 
T).(subst0 i u x4 u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead (Bind x0) 
u2 (THead (Flat Appl) (lift (S O) O x3) x5)))) (\lambda (u2: T).(subst0 i u 
x4 u2)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x6: T).(\lambda 
(H20: (eq T x (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) 
x5)))).(\lambda (H21: (subst0 i u x4 x6)).(eq_ind_r T (THead (Bind x0) x6 
(THead (Flat Appl) (lift (S O) O x3) x5)) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x3) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x3) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x3) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x3 x6 H12 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) (lift 
(S O) O x3) x5))) (pr2_free c u1 x3 H15) (pr2_delta c d u i H8 x1 x4 H16 x6 
H21) (pr2_free (CHead c (Bind x0) x6) x2 x5 H17))) x H20)))) H19)) (\lambda 
(H19: (ex2 T (\lambda (t3: T).(eq T x (THead (Bind x0) x4 t3))) (\lambda (t3: 
T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T x (THead (Bind x0) x4 t3))) (\lambda 
(t3: T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T x (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x6: T).(\lambda 
(H20: (eq T x (THead (Bind x0) x4 x6))).(\lambda (H21: (subst0 (s (Bind x0) 
i) u (THead (Flat Appl) (lift (S O) O x3) x5) x6)).(eq_ind_r T (THead (Bind 
x0) x4 x6) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind x0) 
x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda (u2: T).(eq T x6 (THead (Flat 
Appl) u2 x5))) (\lambda (u2: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) 
u2))) (ex2 T (\lambda (t3: T).(eq T x6 (THead (Flat Appl) (lift (S O) O x3) 
t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x6 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) 
O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind 
x0) i)) u x5 t3)))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 x6) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (H22: (ex2 T 
(\lambda (u2: T).(eq T x6 (THead (Flat Appl) u2 x5))) (\lambda (u2: 
T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x6 (THead (Flat Appl) u2 x5))) (\lambda (u2: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda (H23: (eq T x6 
(THead (Flat Appl) x7 x5))).(\lambda (H24: (subst0 (s (Bind x0) i) u (lift (S 
O) O x3) x7)).(eq_ind_r T (THead (Flat Appl) x7 x5) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) x4 t3) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: T).(eq T x7 
(lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) i) (S O)) u 
x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
x0) x4 (THead (Flat Appl) x7 x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) x7 x5)) (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) x7 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (x8: T).(\lambda (H25: (eq T x7 (lift (S O) O 
x8))).(\lambda (H26: (subst0 (minus (s (Bind x0) i) (S O)) u x3 x8)).(let H27 
\def (eq_ind nat (minus (s (Bind x0) i) (S O)) (\lambda (n: nat).(subst0 n u 
x3 x8)) H26 i (s_arith1 x0 i)) in (eq_ind_r T (lift (S O) O x8) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) t3 x5)) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x5)) (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) t3 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x8) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) (lift (S O) O x8) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x8) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) (lift (S O) O x8) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x8 x4 H12 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x4 (THead (Flat Appl) (lift 
(S O) O x8) x5))) (pr2_delta c d u i H8 u1 x3 H15 x8 H27) (pr2_free c x1 x4 
H16) (pr2_free (CHead c (Bind x0) x4) x2 x5 H17))) x7 H25))))) 
(subst0_gen_lift_ge u x3 x7 (s (Bind x0) i) (S O) O H24 (le_n_S O i (le_O_n 
i)))) x6 H23)))) H22)) (\lambda (H22: (ex2 T (\lambda (t3: T).(eq T x6 (THead 
(Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) 
(s (Bind x0) i)) u x5 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x6 (THead 
(Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) 
(s (Bind x0) i)) u x5 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 x6) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda 
(H23: (eq T x6 (THead (Flat Appl) (lift (S O) O x3) x7))).(\lambda (H24: 
(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 x7)).(eq_ind_r T (THead (Flat 
Appl) (lift (S O) O x3) x7) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T (THead (Bind x0) x4 t3) (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x3) x7)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x7 x3 x4 H12 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x7))) (pr2_free c u1 
x3 H15) (pr2_free c x1 x4 H16) (pr2_delta (CHead c (Bind x0) x4) d u (S i) 
(getl_clear_bind x0 (CHead c (Bind x0) x4) c x4 (clear_bind x0 c x4) (CHead d 
(Bind Abbr) u) i H8) x2 x5 H17 x7 H24))) x6 H23)))) H22)) (\lambda (H22: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x6 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) 
O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind 
x0) i)) u x5 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x6 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 x6) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 x6) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x4 x6) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x7: T).(\lambda (x8: 
T).(\lambda (H23: (eq T x6 (THead (Flat Appl) x7 x8))).(\lambda (H24: (subst0 
(s (Bind x0) i) u (lift (S O) O x3) x7)).(\lambda (H25: (subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 x8)).(eq_ind_r T (THead (Flat Appl) x7 x8) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T 
(THead (Bind x0) x4 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: 
T).(eq T x7 (lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) 
i) (S O)) u x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) x7 x8)) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x9: T).(\lambda 
(H26: (eq T x7 (lift (S O) O x9))).(\lambda (H27: (subst0 (minus (s (Bind x0) 
i) (S O)) u x3 x9)).(let H28 \def (eq_ind nat (minus (s (Bind x0) i) (S O)) 
(\lambda (n: nat).(subst0 n u x3 x9)) H27 i (s_arith1 x0 i)) in (eq_ind_r T 
(lift (S O) O x9) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x8)) (THead (Flat 
Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) t3 x8)) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) t3 x8)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x9) x8)) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x4 (THead (Flat Appl) (lift (S O) O x9) x8)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) 
O x9) x8)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x4 (THead 
(Flat Appl) (lift (S O) O x9) x8)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) x0 x1 x2 x8 x9 x4 H12 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x4 (THead (Flat Appl) (lift 
(S O) O x9) x8))) (pr2_delta c d u i H8 u1 x3 H15 x9 H28) (pr2_free c x1 x4 
H16) (pr2_delta (CHead c (Bind x0) x4) d u (S i) (getl_clear_bind x0 (CHead c 
(Bind x0) x4) c x4 (clear_bind x0 c x4) (CHead d (Bind Abbr) u) i H8) x2 x5 
H17 x8 H25))) x7 H26))))) (subst0_gen_lift_ge u x3 x7 (s (Bind x0) i) (S O) O 
H24 (le_n_S O i (le_O_n i)))) x6 H23)))))) H22)) (subst0_gen_head (Flat Appl) 
u (lift (S O) O x3) x5 x6 (s (Bind x0) i) H21)) x H20)))) H19)) (\lambda 
(H19: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind x0) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x4 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) 
O x3) x5) t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind x0) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x4 
u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind x0) i) u (THead (Flat 
Appl) (lift (S O) O x3) x5) t3))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) 
x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T x (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (x6: T).(\lambda (x7: T).(\lambda (H20: (eq T x 
(THead (Bind x0) x6 x7))).(\lambda (H21: (subst0 i u x4 x6)).(\lambda (H22: 
(subst0 (s (Bind x0) i) u (THead (Flat Appl) (lift (S O) O x3) x5) 
x7)).(eq_ind_r T (THead (Bind x0) x6 x7) (\lambda (t3: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t3 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_ind (ex2 T (\lambda (u2: T).(eq T x7 (THead (Flat 
Appl) u2 x5))) (\lambda (u2: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) 
u2))) (ex2 T (\lambda (t3: T).(eq T x7 (THead (Flat Appl) (lift (S O) O x3) 
t3))) (\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x7 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) 
O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind 
x0) i)) u x5 t3)))) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 x7) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (H23: (ex2 T 
(\lambda (u2: T).(eq T x7 (THead (Flat Appl) u2 x5))) (\lambda (u2: 
T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x7 (THead (Flat Appl) u2 x5))) (\lambda (u2: T).(subst0 (s 
(Bind x0) i) u (lift (S O) O x3) u2)) (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x8: T).(\lambda (H24: (eq T x7 
(THead (Flat Appl) x8 x5))).(\lambda (H25: (subst0 (s (Bind x0) i) u (lift (S 
O) O x3) x8)).(eq_ind_r T (THead (Flat Appl) x8 x5) (\lambda (t3: T).(or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) x6 t3) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: T).(eq T x8 
(lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) i) (S O)) u 
x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
x0) x6 (THead (Flat Appl) x8 x5)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) x8 x5)) (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) x8 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2))))))))) (\lambda (x9: T).(\lambda (H26: (eq T x8 (lift (S O) O 
x9))).(\lambda (H27: (subst0 (minus (s (Bind x0) i) (S O)) u x3 x9)).(let H28 
\def (eq_ind nat (minus (s (Bind x0) i) (S O)) (\lambda (n: nat).(subst0 n u 
x3 x9)) H27 i (s_arith1 x0 i)) in (eq_ind_r T (lift (S O) O x9) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) t3 x5)) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x5)) (THead (Bind 
Abbr) u2 t4)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t4)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) t3 x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x9) x5)) (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x9) x5)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x9) x5)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x9) x5)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) x0 x1 x2 x5 x9 x6 H12 (refl_equal T (THead 
(Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) (lift 
(S O) O x9) x5))) (pr2_delta c d u i H8 u1 x3 H15 x9 H28) (pr2_delta c d u i 
H8 x1 x4 H16 x6 H21) (pr2_free (CHead c (Bind x0) x6) x2 x5 H17))) x8 
H26))))) (subst0_gen_lift_ge u x3 x8 (s (Bind x0) i) (S O) O H25 (le_n_S O i 
(le_O_n i)))) x7 H24)))) H23)) (\lambda (H23: (ex2 T (\lambda (t3: T).(eq T 
x7 (THead (Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s 
(Flat Appl) (s (Bind x0) i)) u x5 t3)))).(ex2_ind T (\lambda (t3: T).(eq T x7 
(THead (Flat Appl) (lift (S O) O x3) t3))) (\lambda (t3: T).(subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Flat Appl) u2 t3)))) (\lambda 
(u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 
c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 x7) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) 
(\lambda (x8: T).(\lambda (H24: (eq T x7 (THead (Flat Appl) (lift (S O) O x3) 
x8))).(\lambda (H25: (subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 
x8)).(eq_ind_r T (THead (Flat Appl) (lift (S O) O x3) x8) (\lambda (t3: 
T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c 
u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) 
t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: 
T).(eq T (THead (Bind x0) x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (or3_intro2 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 (THead (Flat 
Appl) (lift (S O) O x3) x8)) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) (THead (Bind b) 
y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) (ex6_6_intro B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))) 
x0 x1 x2 x8 x3 x6 H12 (refl_equal T (THead (Bind x0) x1 x2)) (refl_equal T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x3) x8))) (pr2_free c u1 
x3 H15) (pr2_delta c d u i H8 x1 x4 H16 x6 H21) (pr2_delta (CHead c (Bind x0) 
x6) d u (S i) (getl_clear_bind x0 (CHead c (Bind x0) x6) c x6 (clear_bind x0 
c x6) (CHead d (Bind Abbr) u) i H8) x2 x5 H17 x8 H25))) x7 H24)))) H23)) 
(\lambda (H23: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x7 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 (s (Bind x0) 
i) u (lift (S O) O x3) u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s 
(Flat Appl) (s (Bind x0) i)) u x5 t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x7 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 (s (Bind x0) i) u (lift (S O) O x3) u2))) (\lambda 
(_: T).(\lambda (t3: T).(subst0 (s (Flat Appl) (s (Bind x0) i)) u x5 t3))) 
(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 
x7) (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 x7) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda 
(y2: T).(eq T (THead (Bind x0) x6 x7) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x8: T).(\lambda (x9: 
T).(\lambda (H24: (eq T x7 (THead (Flat Appl) x8 x9))).(\lambda (H25: (subst0 
(s (Bind x0) i) u (lift (S O) O x3) x8)).(\lambda (H26: (subst0 (s (Flat 
Appl) (s (Bind x0) i)) u x5 x9)).(eq_ind_r T (THead (Flat Appl) x8 x9) 
(\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T 
(THead (Bind x0) x6 t3) (THead (Flat Appl) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(pr2 c 
(THead (Bind x0) x1 x2) t4)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t4: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind Abbr) u2 t4)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 t3) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))))) (ex2_ind T (\lambda (t3: 
T).(eq T x8 (lift (S O) O t3))) (\lambda (t3: T).(subst0 (minus (s (Bind x0) 
i) (S O)) u x3 t3)) (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 
x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))) (\lambda (_: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) x8 x9)) (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))) (\lambda (x10: T).(\lambda 
(H27: (eq T x8 (lift (S O) O x10))).(\lambda (H28: (subst0 (minus (s (Bind 
x0) i) (S O)) u x3 x10)).(let H29 \def (eq_ind nat (minus (s (Bind x0) i) (S 
O)) (\lambda (n: nat).(subst0 n u x3 x10)) H28 i (s_arith1 x0 i)) in 
(eq_ind_r T (lift (S O) O x10) (\lambda (t3: T).(or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x9)) 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t4: T).(pr2 c (THead (Bind x0) x1 x2) t4)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t4: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) t3 x9)) (THead (Bind Abbr) u2 t4)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t4: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t4)))))))) (ex6_6 B T T 
T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) t3 x9)) 
(THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) O x10) x9)) (THead (Flat 
Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr2 c (THead (Bind x0) x1 x2) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind x0) x1 x2) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind x0) 
x6 (THead (Flat Appl) (lift (S O) O x10) x9)) (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead (Flat Appl) (lift (S O) 
O x10) x9)) (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) 
z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) 
y2) z1 z2)))))))) (ex6_6_intro B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind x0) x1 x2) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T (THead (Bind x0) x6 (THead 
(Flat Appl) (lift (S O) O x10) x9)) (THead (Bind b) y2 (THead (Flat Appl) 
(lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) x0 x1 x2 x9 x10 x6 H12 (refl_equal T 
(THead (Bind x0) x1 x2)) (refl_equal T (THead (Bind x0) x6 (THead (Flat Appl) 
(lift (S O) O x10) x9))) (pr2_delta c d u i H8 u1 x3 H15 x10 H29) (pr2_delta 
c d u i H8 x1 x4 H16 x6 H21) (pr2_delta (CHead c (Bind x0) x6) d u (S i) 
(getl_clear_bind x0 (CHead c (Bind x0) x6) c x6 (clear_bind x0 c x6) (CHead d 
(Bind Abbr) u) i H8) x2 x5 H17 x9 H26))) x8 H27))))) (subst0_gen_lift_ge u x3 
x8 (s (Bind x0) i) (S O) O H25 (le_n_S O i (le_O_n i)))) x7 H24)))))) H23)) 
(subst0_gen_head (Flat Appl) u (lift (S O) O x3) x5 x7 (s (Bind x0) i) H22)) 
x H20)))))) H19)) (subst0_gen_head (Bind x0) u x4 (THead (Flat Appl) (lift (S 
O) O x3) x5) x i H18)) t1 H13)))))))))))))) H11)) (pr0_gen_appl u1 t1 t2 
H9))))) t (sym_eq T t x H7))) t0 (sym_eq T t0 (THead (Flat Appl) u1 t1) H6))) 
c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 (refl_equal C c) 
(refl_equal T (THead (Flat Appl) u1 t1)) (refl_equal T x))))))).

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
(H: (pr2 c (THead (Bind Abbr) u1 t1) x)).(let H0 \def (match H in pr2 return 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t 
t0)).((eq C c0 c) \to ((eq T t (THead (Bind Abbr) u1 t1)) \to ((eq T t0 x) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) t1 t2))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c (Bind Abbr) u) t1 t2))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O 
x)))))))))))) with [(pr2_free c0 t0 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 
c)).(\lambda (H2: (eq T t0 (THead (Bind Abbr) u1 t1))).(\lambda (H3: (eq T t2 
x)).(eq_ind C c (\lambda (_: C).((eq T t0 (THead (Bind Abbr) u1 t1)) \to ((eq 
T t2 x) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) t1 (lift (S O) O x))))))))) (\lambda (H4: (eq T t0 (THead (Bind 
Abbr) u1 t1))).(eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (t: T).((eq T t2 
x) \to ((pr0 t t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c 
(Bind b) u) t1 (lift (S O) O x)))))))) (\lambda (H5: (eq T t2 x)).(eq_ind T x 
(\lambda (t: T).((pr0 (THead (Bind Abbr) u1 t1) t) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c 
(Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda 
(_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))))) 
(\lambda (H6: (pr0 (THead (Bind Abbr) u1 t1) x)).(or_ind (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t3))))))) (pr0 t1 (lift (S O) O x)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T 
T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))) (\lambda (H7: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 
O u2 y t3)))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O u2 y t3)))))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H8: (eq T x (THead (Bind Abbr) x0 
x1))).(\lambda (H9: (pr0 u1 x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T 
(\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O x0 y x1))))).(or_ind 
(pr0 t1 x1) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O x0 y 
x1))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O 
x))))) (\lambda (H10: (pr0 t1 x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) 
(\lambda (t: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: 
T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) 
z t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
(lift (S O) O t)))))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O (THead (Bind 
Abbr) x0 x1))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3))))))) x0 x1 
(refl_equal T (THead (Bind Abbr) x0 x1)) (pr2_free c u1 x0 H9) (or3_intro0 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 x1))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
x1))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z x1)))) (\lambda (b: 
B).(\lambda (u: T).(pr2_free (CHead c (Bind b) u) t1 x1 H10)))))) x H8)) 
(\lambda (H_x0: (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O 
x0 y x1)))).(ex2_ind T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O 
x0 y x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: 
T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) 
z t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
(lift (S O) O x))))) (\lambda (x2: T).(\lambda (H10: (pr0 t1 x2)).(\lambda 
(H11: (subst0 O x0 x2 x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: 
T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O 
t)))))) (ex2_ind T (\lambda (t: T).(subst0 O u1 x2 t)) (\lambda (t: T).(pr0 t 
x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T 
T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1)))))) 
(\lambda (x3: T).(\lambda (_: (subst0 O u1 x2 x3)).(\lambda (_: (pr0 x3 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T 
T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3))))))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 x1)) 
(pr2_free c u1 x0 H9) (or3_intro1 (\forall (b: B).(\forall (u: T).(pr2 (CHead 
c (Bind b) u) t1 x1))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) t1 x1))) (ex3_2 T T (\lambda (y: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: 
T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) 
z x1)))) (ex_intro2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c (Bind Abbr) u) t1 x1)) x0 H9 (pr2_delta (CHead c (Bind Abbr) x0) c x0 O 
(getl_refl Abbr c x0) t1 x2 H10 x1 H11)))))))) (pr0_subst0_back x0 x2 x1 O 
H11 u1 H9)) x H8)))) H_x0)) H_x)))))) H7)) (\lambda (H7: (pr0 t1 (lift (S O) 
O x))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: 
T).(pr2 (CHead c (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda 
(_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: 
T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) 
z t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
(lift (S O) O x)))) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c (Bind 
b) u) t1 (lift (S O) O x) H7))))) (pr0_gen_abbr u1 t1 x H6))) t2 (sym_eq T t2 
x H5))) t0 (sym_eq T t0 (THead (Bind Abbr) u1 t1) H4))) c0 (sym_eq C c0 c H1) 
H2 H3 H0)))) | (pr2_delta c0 d u i H0 t0 t2 H1 t H2) \Rightarrow (\lambda 
(H3: (eq C c0 c)).(\lambda (H4: (eq T t0 (THead (Bind Abbr) u1 t1))).(\lambda 
(H5: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T t0 (THead (Bind Abbr) u1 
t1)) \to ((eq T t x) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t0 
t2) \to ((subst0 i u t2 t) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))))))))) (\lambda (H6: (eq 
T t0 (THead (Bind Abbr) u1 t1))).(eq_ind T (THead (Bind Abbr) u1 t1) (\lambda 
(t3: T).((eq T t x) \to ((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t3 t2) 
\to ((subst0 i u t2 t) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t4: 
T).(eq T x (THead (Bind Abbr) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(or3 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t4))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t4))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t4)))))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))))))))) (\lambda (H7: (eq 
T t x)).(eq_ind T x (\lambda (t3: T).((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 (THead (Bind Abbr) u1 t1) t2) \to ((subst0 i u t2 t3) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Bind Abbr) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t4: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t4))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c 
(Bind Abbr) u0) t1 t4))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t4)))))))) 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O 
x))))))))) (\lambda (H8: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H9: 
(pr0 (THead (Bind Abbr) u1 t1) t2)).(\lambda (H10: (subst0 i u t2 x)).(or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t3))))))) (pr0 t1 (lift (S O) O t2)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (H11: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t3)))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t3)))))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H12: (eq T t2 (THead (Bind Abbr) 
x0 x1))).(\lambda (H13: (pr0 u1 x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T 
(\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O x0 y x1))))).(or_ind 
(pr0 t1 x1) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O x0 y 
x1))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (H14: (pr0 t1 x1)).(let H15 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 x)) H10 (THead (Bind Abbr) x0 x1) H12) in 
(or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead (Bind Abbr) u2 x1))) (\lambda 
(u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T x (THead (Bind 
Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O 
x))))) (\lambda (H16: (ex2 T (\lambda (u2: T).(eq T x (THead (Bind Abbr) u2 
x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T (\lambda (u2: T).(eq 
T x (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (x2: T).(\lambda (H17: (eq T x (THead (Bind 
Abbr) x2 x1))).(\lambda (H18: (subst0 i u x0 x2)).(or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O 
x)))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3))))))) x2 x1 H17 (pr2_delta c d u i H8 u1 x0 H13 x2 H18) (or3_intro0 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 x1))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 x1))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z x1)))) (\lambda (b: 
B).(\lambda (u0: T).(pr2_free (CHead c (Bind b) u0) t1 x1 H14))))))))) H16)) 
(\lambda (H16: (ex2 T (\lambda (t3: T).(eq T x (THead (Bind Abbr) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))).(ex2_ind T (\lambda 
(t3: T).(eq T x (THead (Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind 
Abbr) i) u x1 t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c 
(Bind b) u0) t1 (lift (S O) O x))))) (\lambda (x2: T).(\lambda (H17: (eq T x 
(THead (Bind Abbr) x0 x2))).(\lambda (H18: (subst0 (s (Bind Abbr) i) u x1 
x2)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c 
(Bind b) u0) t1 (lift (S O) O x)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3))))))) x0 x2 H17 
(pr2_free c u1 x0 H13) (or3_intro0 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) t1 x2))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 x2))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z x2)))) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c 
(Bind b) u0) d u (S i) (getl_head (Bind b) i c (CHead d (Bind Abbr) u) H8 u0) 
t1 x1 H14 x2 H18))))))))) H16)) (\lambda (H16: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x1 t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x1 t3))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (H17: (eq T x (THead (Bind Abbr) 
x2 x3))).(\lambda (H18: (subst0 i u x0 x2)).(\lambda (H19: (subst0 (s (Bind 
Abbr) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3))))))) x2 
x3 H17 (pr2_delta c d u i H8 u1 x0 H13 x2 H18) (or3_intro0 (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 x3))) (ex2 T (\lambda (u0: 
T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 x3))) 
(ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 
y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z x3)))) (\lambda (b: B).(\lambda (u0: 
T).(pr2_delta (CHead c (Bind b) u0) d u (S i) (getl_head (Bind b) i c (CHead 
d (Bind Abbr) u) H8 u0) t1 x1 H14 x3 H19))))))))))) H16)) (subst0_gen_head 
(Bind Abbr) u x0 x1 x i H15)))) (\lambda (H_x0: (ex2 T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O x0 y x1)))).(ex2_ind T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O x0 y x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x2: T).(\lambda (H14: (pr0 t1 x2)).(\lambda (H15: (subst0 O x0 x2 
x1)).(let H16 \def (eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 x)) H10 
(THead (Bind Abbr) x0 x1) H12) in (or3_ind (ex2 T (\lambda (u2: T).(eq T x 
(THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2))) (ex2 T 
(\lambda (t3: T).(eq T x (THead (Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 
(s (Bind Abbr) i) u x1 t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u 
x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3)))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (H17: (ex2 T (\lambda (u2: T).(eq T x (THead 
(Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T x (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c 
(Bind b) u0) t1 (lift (S O) O x))))) (\lambda (x3: T).(\lambda (H18: (eq T x 
(THead (Bind Abbr) x3 x1))).(\lambda (H19: (subst0 i u x0 x3)).(ex2_ind T 
(\lambda (t3: T).(subst0 O u1 x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (x4: T).(\lambda (_: (subst0 O u1 x2 
x4)).(\lambda (_: (pr0 x4 x1)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3))))))) x3 x1 H18 (pr2_delta c d u i H8 u1 x0 H13 x3 H19) (or3_intro1 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 x1))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 x1))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z x1)))) (ex_intro2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 x1)) x0 H13 (pr2_delta (CHead c (Bind Abbr) x0) c x0 O (getl_refl Abbr c 
x0) t1 x2 H14 x1 H15)))))))) (pr0_subst0_back x0 x2 x1 O H15 u1 H13))))) 
H17)) (\lambda (H17: (ex2 T (\lambda (t3: T).(eq T x (THead (Bind Abbr) x0 
t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))).(ex2_ind T 
(\lambda (t3: T).(eq T x (THead (Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 
(s (Bind Abbr) i) u x1 t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) (\lambda (x3: 
T).(\lambda (H18: (eq T x (THead (Bind Abbr) x0 x3))).(\lambda (H19: (subst0 
(s (Bind Abbr) i) u x1 x3)).(ex2_ind T (\lambda (t3: T).(subst0 O u1 x2 t3)) 
(\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) (\lambda (x4: 
T).(\lambda (H20: (subst0 O u1 x2 x4)).(\lambda (H21: (pr0 x4 x1)).(or_introl 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x)))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) 
(\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda 
(y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3))))))) x0 x3 H18 (pr2_free c u1 x0 H13) (or3_intro2 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 x3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 x3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z x3)))) (ex3_2_intro T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z x3))) x4 x1 (pr2_delta (CHead c (Bind 
Abbr) u1) c u1 O (getl_refl Abbr c u1) t1 x2 H14 x4 H20) H21 (pr2_delta 
(CHead c (Bind Abbr) u1) d u (S i) (getl_head (Bind Abbr) i c (CHead d (Bind 
Abbr) u) H8 u1) x1 x1 (pr0_refl x1) x3 H19)))))))) (pr0_subst0_back x0 x2 x1 
O H15 u1 H13))))) H17)) (\lambda (H17: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind 
Abbr) i) u x1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u 
x0 u2))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 
(CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: 
T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 
y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
(lift (S O) O x))))) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H18: (eq T x 
(THead (Bind Abbr) x3 x4))).(\lambda (H19: (subst0 i u x0 x3)).(\lambda (H20: 
(subst0 (s (Bind Abbr) i) u x1 x4)).(ex2_ind T (\lambda (t3: T).(subst0 O u1 
x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x5: T).(\lambda (H21: (subst0 O u1 x2 x5)).(\lambda (H22: (pr0 x5 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c 
(Bind b) u0) t1 (lift (S O) O x)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3))))))) x3 x4 H18 
(pr2_delta c d u i H8 u1 x0 H13 x3 H19) (or3_intro2 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 x4))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c (Bind Abbr) u0) t1 x4))) (ex3_2 T T 
(\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z x4)))) (ex3_2_intro T T (\lambda (y: 
T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: 
T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c 
(Bind Abbr) u1) z x4))) x5 x1 (pr2_delta (CHead c (Bind Abbr) u1) c u1 O 
(getl_refl Abbr c u1) t1 x2 H14 x5 H21) H22 (pr2_delta (CHead c (Bind Abbr) 
u1) d u (S i) (getl_head (Bind Abbr) i c (CHead d (Bind Abbr) u) H8 u1) x1 x1 
(pr0_refl x1) x4 H20)))))))) (pr0_subst0_back x0 x2 x1 O H15 u1 H13))))))) 
H17)) (subst0_gen_head (Bind Abbr) u x0 x1 x i H16)))))) H_x0)) H_x)))))) 
H11)) (\lambda (H11: (pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 
(CHead c (Bind Abbr) u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O 
x)))) (\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c (Bind b) u0) d u 
(S i) (getl_head (Bind b) i c (CHead d (Bind Abbr) u) H8 u0) t1 (lift (S O) O 
t2) H11 (lift (S O) O x) (subst0_lift_ge_S t2 x u i H10 O (le_O_n i))))))) 
(pr0_gen_abbr u1 t1 t2 H9))))) t (sym_eq T t x H7))) t0 (sym_eq T t0 (THead 
(Bind Abbr) u1 t1) H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 
(refl_equal C c) (refl_equal T (THead (Bind Abbr) u1 t1)) (refl_equal T 
x))))))).

theorem pr2_gen_void:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Void) u1 t1) x)).(let H0 \def (match H in pr2 return 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t 
t0)).((eq C c0 c) \to ((eq T t (THead (Bind Void) u1 t1)) \to ((eq T t0 x) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
t1 t2)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
(lift (S O) O x)))))))))))) with [(pr2_free c0 t0 t2 H0) \Rightarrow (\lambda 
(H1: (eq C c0 c)).(\lambda (H2: (eq T t0 (THead (Bind Void) u1 t1))).(\lambda 
(H3: (eq T t2 x)).(eq_ind C c (\lambda (_: C).((eq T t0 (THead (Bind Void) u1 
t1)) \to ((eq T t2 x) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x))))))))) 
(\lambda (H4: (eq T t0 (THead (Bind Void) u1 t1))).(eq_ind T (THead (Bind 
Void) u1 t1) (\lambda (t: T).((eq T t2 x) \to ((pr0 t t2) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O 
x)))))))) (\lambda (H5: (eq T t2 x)).(eq_ind T x (\lambda (t: T).((pr0 (THead 
(Bind Void) u1 t1) t) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 (lift (S O) O x))))))) (\lambda (H6: (pr0 (THead 
(Bind Void) u1 t1) x)).(or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) 
O x)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) 
t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 
(lift (S O) O x))))) (\lambda (H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead 
c (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind 
b) u) t1 (lift (S O) O x))))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H8: 
(eq T x (THead (Bind Void) x0 x1))).(\lambda (H9: (pr0 u1 x0)).(\lambda (H10: 
(pr0 t1 x1)).(eq_ind_r T (THead (Bind Void) x0 x1) (\lambda (t: T).(or (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O 
t)))))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Void) x0 x1) (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O (THead (Bind Void) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Void) 
x0 x1) (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3))))) x0 x1 (refl_equal T (THead (Bind 
Void) x0 x1)) (pr2_free c u1 x0 H9) (\lambda (b: B).(\lambda (u: T).(pr2_free 
(CHead c (Bind b) u) t1 x1 H10))))) x H8)))))) H7)) (\lambda (H7: (pr0 t1 
(lift (S O) O x))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) t1 (lift (S O) O x)))) (\lambda (b: B).(\lambda (u: 
T).(pr2_free (CHead c (Bind b) u) t1 (lift (S O) O x) H7))))) (pr0_gen_void 
u1 t1 x H6))) t2 (sym_eq T t2 x H5))) t0 (sym_eq T t0 (THead (Bind Void) u1 
t1) H4))) c0 (sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u i H0 t0 t2 
H1 t H2) \Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq T t0 (THead 
(Bind Void) u1 t1))).(\lambda (H5: (eq T t x)).(eq_ind C c (\lambda (c1: 
C).((eq T t0 (THead (Bind Void) u1 t1)) \to ((eq T t x) \to ((getl i c1 
(CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) 
t1 (lift (S O) O x))))))))))) (\lambda (H6: (eq T t0 (THead (Bind Void) u1 
t1))).(eq_ind T (THead (Bind Void) u1 t1) (\lambda (t3: T).((eq T t x) \to 
((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t3 t2) \to ((subst0 i u t2 t) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T x (THead (Bind 
Void) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t4: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t4)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) 
t1 (lift (S O) O x)))))))))) (\lambda (H7: (eq T t x)).(eq_ind T x (\lambda 
(t3: T).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 (THead (Bind Void) u1 
t1) t2) \to ((subst0 i u t2 t3) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T x (THead (Bind Void) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t4: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t4)))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))))))) (\lambda (H8: (getl 
i c (CHead d (Bind Abbr) u))).(\lambda (H9: (pr0 (THead (Bind Void) u1 t1) 
t2)).(\lambda (H10: (subst0 i u t2 x)).(or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) (\lambda (H11: (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H12: (eq T t2 (THead (Bind Void) 
x0 x1))).(\lambda (H13: (pr0 u1 x0)).(\lambda (H14: (pr0 t1 x1)).(let H15 
\def (eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 x)) H10 (THead (Bind Void) 
x0 x1) H12) in (or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead (Bind Void) u2 
x1))) (\lambda (u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T x 
(THead (Bind Void) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 
t3))) (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift 
(S O) O x))))) (\lambda (H16: (ex2 T (\lambda (u2: T).(eq T x (THead (Bind 
Void) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x (THead (Bind Void) u2 x1))) (\lambda (u2: T).(subst0 i u x0 
u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) 
t1 (lift (S O) O x))))) (\lambda (x2: T).(\lambda (H17: (eq T x (THead (Bind 
Void) x2 x1))).(\lambda (H18: (subst0 i u x0 x2)).(or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift 
(S O) O x)))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c (Bind b) u0) t1 t3))))) x2 x1 H17 (pr2_delta c d u i H8 u1 x0 H13 x2 H18) 
(\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c (Bind b) u0) t1 x1 
H14)))))))) H16)) (\lambda (H16: (ex2 T (\lambda (t3: T).(eq T x (THead (Bind 
Void) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T x (THead (Bind Void) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3)) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x))))) 
(\lambda (x2: T).(\lambda (H17: (eq T x (THead (Bind Void) x0 x2))).(\lambda 
(H18: (subst0 (s (Bind Void) i) u x1 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t3))))) x0 x2 H17 (pr2_free c u1 x0 H13) (\lambda (b: B).(\lambda (u0: 
T).(pr2_delta (CHead c (Bind b) u0) d u (S i) (getl_head (Bind b) i c (CHead 
d (Bind Abbr) u) H8 u0) t1 x1 H14 x2 H18)))))))) H16)) (\lambda (H16: (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift 
(S O) O x))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H17: (eq T x 
(THead (Bind Void) x2 x3))).(\lambda (H18: (subst0 i u x0 x2)).(\lambda (H19: 
(subst0 (s (Bind Void) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) 
u0) t1 t3))))) x2 x3 H17 (pr2_delta c d u i H8 u1 x0 H13 x2 H18) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c (Bind b) u0) d u (S i) (getl_head 
(Bind b) i c (CHead d (Bind Abbr) u) H8 u0) t1 x1 H14 x3 H19)))))))))) H16)) 
(subst0_gen_head (Bind Void) u x0 x1 x i H15)))))))) H11)) (\lambda (H11: 
(pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c (Bind b) u0) t1 (lift (S O) O x)))) (\lambda (b: B).(\lambda 
(u0: T).(pr2_delta (CHead c (Bind b) u0) d u (S i) (getl_head (Bind b) i c 
(CHead d (Bind Abbr) u) H8 u0) t1 (lift (S O) O t2) H11 (lift (S O) O x) 
(subst0_lift_ge_S t2 x u i H10 O (le_O_n i))))))) (pr0_gen_void u1 t1 t2 
H9))))) t (sym_eq T t x H7))) t0 (sym_eq T t0 (THead (Bind Void) u1 t1) H6))) 
c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 (refl_equal C c) 
(refl_equal T (THead (Bind Void) u1 t1)) (refl_equal T x))))))).

theorem pr2_gen_lift:
 \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).((pr2 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to 
(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr2 e t1 
t2))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H: (pr2 c (lift h d t1) x)).(\lambda (e: C).(\lambda (H0: 
(drop h d c e)).(let H1 \def (match H in pr2 return (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 c) \to ((eq T t 
(lift h d t1)) \to ((eq T t0 x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d 
t2))) (\lambda (t2: T).(pr2 e t1 t2)))))))))) with [(pr2_free c0 t0 t2 H1) 
\Rightarrow (\lambda (H2: (eq C c0 c)).(\lambda (H3: (eq T t0 (lift h d 
t1))).(\lambda (H4: (eq T t2 x)).(eq_ind C c (\lambda (_: C).((eq T t0 (lift 
h d t1)) \to ((eq T t2 x) \to ((pr0 t0 t2) \to (ex2 T (\lambda (t3: T).(eq T 
x (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))))))) (\lambda (H5: (eq T t0 
(lift h d t1))).(eq_ind T (lift h d t1) (\lambda (t: T).((eq T t2 x) \to 
((pr0 t t2) \to (ex2 T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: 
T).(pr2 e t1 t3)))))) (\lambda (H6: (eq T t2 x)).(eq_ind T x (\lambda (t: 
T).((pr0 (lift h d t1) t) \to (ex2 T (\lambda (t3: T).(eq T x (lift h d t3))) 
(\lambda (t3: T).(pr2 e t1 t3))))) (\lambda (H7: (pr0 (lift h d t1) 
x)).(ex2_ind T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr0 
t1 t3)) (ex2 T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 
e t1 t3))) (\lambda (x0: T).(\lambda (H8: (eq T x (lift h d x0))).(\lambda 
(H9: (pr0 t1 x0)).(eq_ind_r T (lift h d x0) (\lambda (t: T).(ex2 T (\lambda 
(t3: T).(eq T t (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3)))) (ex_intro2 
T (\lambda (t3: T).(eq T (lift h d x0) (lift h d t3))) (\lambda (t3: T).(pr2 
e t1 t3)) x0 (refl_equal T (lift h d x0)) (pr2_free e t1 x0 H9)) x H8)))) 
(pr0_gen_lift t1 x h d H7))) t2 (sym_eq T t2 x H6))) t0 (sym_eq T t0 (lift h 
d t1) H5))) c0 (sym_eq C c0 c H2) H3 H4 H1)))) | (pr2_delta c0 d0 u i H1 t0 
t2 H2 t H3) \Rightarrow (\lambda (H4: (eq C c0 c)).(\lambda (H5: (eq T t0 
(lift h d t1))).(\lambda (H6: (eq T t x)).(eq_ind C c (\lambda (c1: C).((eq T 
t0 (lift h d t1)) \to ((eq T t x) \to ((getl i c1 (CHead d0 (Bind Abbr) u)) 
\to ((pr0 t0 t2) \to ((subst0 i u t2 t) \to (ex2 T (\lambda (t3: T).(eq T x 
(lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))))))))) (\lambda (H7: (eq T t0 
(lift h d t1))).(eq_ind T (lift h d t1) (\lambda (t3: T).((eq T t x) \to 
((getl i c (CHead d0 (Bind Abbr) u)) \to ((pr0 t3 t2) \to ((subst0 i u t2 t) 
\to (ex2 T (\lambda (t4: T).(eq T x (lift h d t4))) (\lambda (t4: T).(pr2 e 
t1 t4)))))))) (\lambda (H8: (eq T t x)).(eq_ind T x (\lambda (t3: T).((getl i 
c (CHead d0 (Bind Abbr) u)) \to ((pr0 (lift h d t1) t2) \to ((subst0 i u t2 
t3) \to (ex2 T (\lambda (t4: T).(eq T x (lift h d t4))) (\lambda (t4: T).(pr2 
e t1 t4))))))) (\lambda (H9: (getl i c (CHead d0 (Bind Abbr) u))).(\lambda 
(H10: (pr0 (lift h d t1) t2)).(\lambda (H11: (subst0 i u t2 x)).(ex2_ind T 
(\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(pr0 t1 t3)) (ex2 
T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (x0: T).(\lambda (H12: (eq T t2 (lift h d x0))).(\lambda (H13: (pr0 
t1 x0)).(let H14 \def (eq_ind T t2 (\lambda (t3: T).(subst0 i u t3 x)) H11 
(lift h d x0) H12) in (lt_le_e i d (ex2 T (\lambda (t3: T).(eq T x (lift h d 
t3))) (\lambda (t3: T).(pr2 e t1 t3))) (\lambda (H15: (lt i d)).(let H16 \def 
(eq_ind nat d (\lambda (n: nat).(drop h n c e)) H0 (S (plus i (minus d (S 
i)))) (lt_plus_minus i d H15)) in (let H17 \def (eq_ind nat d (\lambda (n: 
nat).(subst0 i u (lift h n x0) x)) H14 (S (plus i (minus d (S i)))) 
(lt_plus_minus i d H15)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift h (minus d (S i)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind Abbr) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (minus d (S i)) d0 e0))) (ex2 T (\lambda (t3: T).(eq T x (lift h d 
t3))) (\lambda (t3: T).(pr2 e t1 t3))) (\lambda (x1: T).(\lambda (x2: 
C).(\lambda (H18: (eq T u (lift h (minus d (S i)) x1))).(\lambda (H19: (getl 
i e (CHead x2 (Bind Abbr) x1))).(\lambda (_: (drop h (minus d (S i)) d0 
x2)).(let H21 \def (eq_ind T u (\lambda (t3: T).(subst0 i t3 (lift h (S (plus 
i (minus d (S i)))) x0) x)) H17 (lift h (minus d (S i)) x1) H18) in (ex2_ind 
T (\lambda (t3: T).(eq T x (lift h (S (plus i (minus d (S i)))) t3))) 
(\lambda (t3: T).(subst0 i x1 x0 t3)) (ex2 T (\lambda (t3: T).(eq T x (lift h 
d t3))) (\lambda (t3: T).(pr2 e t1 t3))) (\lambda (x3: T).(\lambda (H22: (eq 
T x (lift h (S (plus i (minus d (S i)))) x3))).(\lambda (H23: (subst0 i x1 x0 
x3)).(let H24 \def (eq_ind_r nat (S (plus i (minus d (S i)))) (\lambda (n: 
nat).(eq T x (lift h n x3))) H22 d (lt_plus_minus i d H15)) in (ex_intro2 T 
(\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3)) x3 
H24 (pr2_delta e x2 x1 i H19 t1 x0 H13 x3 H23)))))) (subst0_gen_lift_lt x1 x0 
x i h (minus d (S i)) H21)))))))) (getl_drop_conf_lt Abbr c d0 u i H9 e h 
(minus d (S i)) H16))))) (\lambda (H15: (le d i)).(lt_le_e i (plus d h) (ex2 
T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (H16: (lt i (plus d h))).(subst0_gen_lift_false x0 u x h d i H15 H16 
H14 (ex2 T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 e 
t1 t3))))) (\lambda (H16: (le (plus d h) i)).(ex2_ind T (\lambda (t3: T).(eq 
T x (lift h d t3))) (\lambda (t3: T).(subst0 (minus i h) u x0 t3)) (ex2 T 
(\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr2 e t1 t3))) 
(\lambda (x1: T).(\lambda (H17: (eq T x (lift h d x1))).(\lambda (H18: 
(subst0 (minus i h) u x0 x1)).(ex_intro2 T (\lambda (t3: T).(eq T x (lift h d 
t3))) (\lambda (t3: T).(pr2 e t1 t3)) x1 H17 (pr2_delta e d0 u (minus i h) 
(getl_drop_conf_ge i (CHead d0 (Bind Abbr) u) c H9 e h d H0 H16) t1 x0 H13 x1 
H18))))) (subst0_gen_lift_ge u x0 x i h d H14 H16)))))))))) (pr0_gen_lift t1 
t2 h d H10))))) t (sym_eq T t x H8))) t0 (sym_eq T t0 (lift h d t1) H7))) c0 
(sym_eq C c0 c H4) H5 H6 H1 H2 H3))))]) in (H1 (refl_equal C c) (refl_equal T 
(lift h d t1)) (refl_equal T x)))))))))).

