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

include "Basic-1/ty3/pr3.ma".

theorem ty3_cred_pr2:
 \forall (g: G).(\forall (c: C).(\forall (v1: T).(\forall (v2: T).((pr2 c v1 
v2) \to (\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c 
(Bind b) v1) t1 t2) \to (ty3 g (CHead c (Bind b) v2) t1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(H: (pr2 c v1 v2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c0 (Bind 
b) t) t1 t2) \to (ty3 g (CHead c0 (Bind b) t0) t1 t2)))))))) (\lambda (c0: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (b: 
B).(\lambda (t0: T).(\lambda (t3: T).(\lambda (H1: (ty3 g (CHead c0 (Bind b) 
t1) t0 t3)).(ty3_sred_wcpr0_pr0 g (CHead c0 (Bind b) t1) t0 t3 H1 (CHead c0 
(Bind b) t2) (wcpr0_comp c0 c0 (wcpr0_refl c0) t1 t2 H0 (Bind b)) t0 
(pr0_refl t0)))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H1: (pr0 t1 t2)).(\lambda 
(t: T).(\lambda (H2: (subst0 i u t2 t)).(\lambda (b: B).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H3: (ty3 g (CHead c0 (Bind b) t1) t0 
t3)).(ty3_csubst0 g (CHead c0 (Bind b) t2) t0 t3 (ty3_sred_wcpr0_pr0 g (CHead 
c0 (Bind b) t1) t0 t3 H3 (CHead c0 (Bind b) t2) (wcpr0_comp c0 c0 (wcpr0_refl 
c0) t1 t2 H1 (Bind b)) t0 (pr0_refl t0)) d u (S i) (getl_clear_bind b (CHead 
c0 (Bind b) t2) c0 t2 (clear_bind b c0 t2) (CHead d (Bind Abbr) u) i H0) 
(CHead c0 (Bind b) t) (csubst0_snd_bind b i u t2 t H2 c0)))))))))))))))) c v1 
v2 H))))).
(* COMMENTS
Initial nodes: 383
END *)

theorem ty3_cred_pr3:
 \forall (g: G).(\forall (c: C).(\forall (v1: T).(\forall (v2: T).((pr3 c v1 
v2) \to (\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c 
(Bind b) v1) t1 t2) \to (ty3 g (CHead c (Bind b) v2) t1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(H: (pr3 c v1 v2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (b: 
B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind b) t) t1 t2) \to 
(ty3 g (CHead c (Bind b) t0) t1 t2))))))) (\lambda (t: T).(\lambda (b: 
B).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (ty3 g (CHead c (Bind b) 
t) t1 t2)).H0))))) (\lambda (t2: T).(\lambda (t1: T).(\lambda (H0: (pr2 c t1 
t2)).(\lambda (t3: T).(\lambda (_: (pr3 c t2 t3)).(\lambda (H2: ((\forall (b: 
B).(\forall (t4: T).(\forall (t5: T).((ty3 g (CHead c (Bind b) t2) t4 t5) \to 
(ty3 g (CHead c (Bind b) t3) t4 t5))))))).(\lambda (b: B).(\lambda (t0: 
T).(\lambda (t4: T).(\lambda (H3: (ty3 g (CHead c (Bind b) t1) t0 t4)).(H2 b 
t0 t4 (ty3_cred_pr2 g c t1 t2 H0 b t0 t4 H3)))))))))))) v1 v2 H))))).
(* COMMENTS
Initial nodes: 215
END *)

theorem ty3_gen_lift:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((ty3 g c (lift h d t1) x) \to (\forall (e: C).((drop 
h d c e) \to (ex2 T (\lambda (t2: T).(pc3 c (lift h d t2) x)) (\lambda (t2: 
T).(ty3 g e t1 t2)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (x: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (ty3 g c (lift h d t1) x)).(insert_eq T 
(lift h d t1) (\lambda (t: T).(ty3 g c t x)) (\lambda (_: T).(\forall (e: 
C).((drop h d c e) \to (ex2 T (\lambda (t2: T).(pc3 c (lift h d t2) x)) 
(\lambda (t2: T).(ty3 g e t1 t2)))))) (\lambda (y: T).(\lambda (H0: (ty3 g c 
y x)).(unintro nat d (\lambda (n: nat).((eq T y (lift h n t1)) \to (\forall 
(e: C).((drop h n c e) \to (ex2 T (\lambda (t2: T).(pc3 c (lift h n t2) x)) 
(\lambda (t2: T).(ty3 g e t1 t2))))))) (unintro T t1 (\lambda (t: T).(\forall 
(x0: nat).((eq T y (lift h x0 t)) \to (\forall (e: C).((drop h x0 c e) \to 
(ex2 T (\lambda (t2: T).(pc3 c (lift h x0 t2) x)) (\lambda (t2: T).(ty3 g e t 
t2)))))))) (ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (x0: T).(\forall (x1: nat).((eq T t (lift h x1 x0)) \to (\forall 
(e: C).((drop h x1 c0 e) \to (ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) 
t0)) (\lambda (t2: T).(ty3 g e x0 t2))))))))))) (\lambda (c0: C).(\lambda 
(t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda (_: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (\forall (e: 
C).((drop h x1 c0 e) \to (ex2 T (\lambda (t3: T).(pc3 c0 (lift h x1 t3) t)) 
(\lambda (t3: T).(ty3 g e x0 t3)))))))))).(\lambda (u: T).(\lambda (t3: 
T).(\lambda (H3: (ty3 g c0 u t3)).(\lambda (H4: ((\forall (x0: T).(\forall 
(x1: nat).((eq T u (lift h x1 x0)) \to (\forall (e: C).((drop h x1 c0 e) \to 
(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) t3)) (\lambda (t4: T).(ty3 g e 
x0 t4)))))))))).(\lambda (H5: (pc3 c0 t3 t2)).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H6: (eq T u (lift h x1 x0))).(\lambda (e: C).(\lambda (H7: 
(drop h x1 c0 e)).(let H8 \def (eq_ind T u (\lambda (t0: T).(\forall (x2: 
T).(\forall (x3: nat).((eq T t0 (lift h x3 x2)) \to (\forall (e0: C).((drop h 
x3 c0 e0) \to (ex2 T (\lambda (t4: T).(pc3 c0 (lift h x3 t4) t3)) (\lambda 
(t4: T).(ty3 g e0 x2 t4))))))))) H4 (lift h x1 x0) H6) in (let H9 \def 
(eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 t3)) H3 (lift h x1 x0) H6) in (let 
H10 \def (H8 x0 x1 (refl_equal T (lift h x1 x0)) e H7) in (ex2_ind T (\lambda 
(t4: T).(pc3 c0 (lift h x1 t4) t3)) (\lambda (t4: T).(ty3 g e x0 t4)) (ex2 T 
(\lambda (t4: T).(pc3 c0 (lift h x1 t4) t2)) (\lambda (t4: T).(ty3 g e x0 
t4))) (\lambda (x2: T).(\lambda (H11: (pc3 c0 (lift h x1 x2) t3)).(\lambda 
(H12: (ty3 g e x0 x2)).(ex_intro2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) 
t2)) (\lambda (t4: T).(ty3 g e x0 t4)) x2 (pc3_t t3 c0 (lift h x1 x2) H11 t2 
H5) H12)))) H10))))))))))))))))))) (\lambda (c0: C).(\lambda (m: 
nat).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H1: (eq T (TSort m) (lift 
h x1 x0))).(\lambda (e: C).(\lambda (_: (drop h x1 c0 e)).(eq_ind_r T (TSort 
m) (\lambda (t: T).(ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (TSort 
(next g m)))) (\lambda (t2: T).(ty3 g e t t2)))) (ex_intro2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (TSort (next g m)))) (\lambda (t2: T).(ty3 g e 
(TSort m) t2)) (TSort (next g m)) (eq_ind_r T (TSort (next g m)) (\lambda (t: 
T).(pc3 c0 t (TSort (next g m)))) (pc3_refl c0 (TSort (next g m))) (lift h x1 
(TSort (next g m))) (lift_sort (next g m) h x1)) (ty3_sort g e m)) x0 
(lift_gen_sort h x1 m x0 H1))))))))) (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d0: C).(\lambda (u: T).(\lambda (H1: (getl n c0 (CHead d0 (Bind 
Abbr) u))).(\lambda (t: T).(\lambda (H2: (ty3 g d0 u t)).(\lambda (H3: 
((\forall (x0: T).(\forall (x1: nat).((eq T u (lift h x1 x0)) \to (\forall 
(e: C).((drop h x1 d0 e) \to (ex2 T (\lambda (t2: T).(pc3 d0 (lift h x1 t2) 
t)) (\lambda (t2: T).(ty3 g e x0 t2)))))))))).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H4: (eq T (TLRef n) (lift h x1 x0))).(\lambda (e: C).(\lambda 
(H5: (drop h x1 c0 e)).(let H_x \def (lift_gen_lref x0 x1 h n H4) in (let H6 
\def H_x in (or_ind (land (lt n x1) (eq T x0 (TLRef n))) (land (le (plus x1 
h) n) (eq T x0 (TLRef (minus n h)))) (ex2 T (\lambda (t2: T).(pc3 c0 (lift h 
x1 t2) (lift (S n) O t))) (\lambda (t2: T).(ty3 g e x0 t2))) (\lambda (H7: 
(land (lt n x1) (eq T x0 (TLRef n)))).(land_ind (lt n x1) (eq T x0 (TLRef n)) 
(ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O t))) (\lambda 
(t2: T).(ty3 g e x0 t2))) (\lambda (H8: (lt n x1)).(\lambda (H9: (eq T x0 
(TLRef n))).(eq_ind_r T (TLRef n) (\lambda (t0: T).(ex2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (lift (S n) O t))) (\lambda (t2: T).(ty3 g e t0 
t2)))) (let H10 \def (eq_ind nat x1 (\lambda (n0: nat).(drop h n0 c0 e)) H5 
(S (plus n (minus x1 (S n)))) (lt_plus_minus n x1 H8)) in (ex3_2_ind T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h (minus x1 (S n)) v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl n e (CHead e0 (Bind Abbr) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h (minus x1 (S n)) d0 e0))) (ex2 T 
(\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O t))) (\lambda (t2: 
T).(ty3 g e (TLRef n) t2))) (\lambda (x2: T).(\lambda (x3: C).(\lambda (H11: 
(eq T u (lift h (minus x1 (S n)) x2))).(\lambda (H12: (getl n e (CHead x3 
(Bind Abbr) x2))).(\lambda (H13: (drop h (minus x1 (S n)) d0 x3)).(let H14 
\def (eq_ind T u (\lambda (t0: T).(\forall (x4: T).(\forall (x5: nat).((eq T 
t0 (lift h x5 x4)) \to (\forall (e0: C).((drop h x5 d0 e0) \to (ex2 T 
(\lambda (t2: T).(pc3 d0 (lift h x5 t2) t)) (\lambda (t2: T).(ty3 g e0 x4 
t2))))))))) H3 (lift h (minus x1 (S n)) x2) H11) in (let H15 \def (eq_ind T u 
(\lambda (t0: T).(ty3 g d0 t0 t)) H2 (lift h (minus x1 (S n)) x2) H11) in 
(let H16 \def (H14 x2 (minus x1 (S n)) (refl_equal T (lift h (minus x1 (S n)) 
x2)) x3 H13) in (ex2_ind T (\lambda (t2: T).(pc3 d0 (lift h (minus x1 (S n)) 
t2) t)) (\lambda (t2: T).(ty3 g x3 x2 t2)) (ex2 T (\lambda (t2: T).(pc3 c0 
(lift h x1 t2) (lift (S n) O t))) (\lambda (t2: T).(ty3 g e (TLRef n) t2))) 
(\lambda (x4: T).(\lambda (H17: (pc3 d0 (lift h (minus x1 (S n)) x4) 
t)).(\lambda (H18: (ty3 g x3 x2 x4)).(eq_ind_r nat (plus (S n) (minus x1 (S 
n))) (\lambda (n0: nat).(ex2 T (\lambda (t2: T).(pc3 c0 (lift h n0 t2) (lift 
(S n) O t))) (\lambda (t2: T).(ty3 g e (TLRef n) t2)))) (ex_intro2 T (\lambda 
(t2: T).(pc3 c0 (lift h (plus (S n) (minus x1 (S n))) t2) (lift (S n) O t))) 
(\lambda (t2: T).(ty3 g e (TLRef n) t2)) (lift (S n) O x4) (eq_ind_r T (lift 
(S n) O (lift h (minus x1 (S n)) x4)) (\lambda (t0: T).(pc3 c0 t0 (lift (S n) 
O t))) (pc3_lift c0 d0 (S n) O (getl_drop Abbr c0 d0 u n H1) (lift h (minus 
x1 (S n)) x4) t H17) (lift h (plus (S n) (minus x1 (S n))) (lift (S n) O x4)) 
(lift_d x4 h (S n) (minus x1 (S n)) O (le_O_n (minus x1 (S n))))) (ty3_abbr g 
n e x3 x2 H12 x4 H18)) x1 (le_plus_minus (S n) x1 H8))))) H16))))))))) 
(getl_drop_conf_lt Abbr c0 d0 u n H1 e h (minus x1 (S n)) H10))) x0 H9))) 
H7)) (\lambda (H7: (land (le (plus x1 h) n) (eq T x0 (TLRef (minus n 
h))))).(land_ind (le (plus x1 h) n) (eq T x0 (TLRef (minus n h))) (ex2 T 
(\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O t))) (\lambda (t2: 
T).(ty3 g e x0 t2))) (\lambda (H8: (le (plus x1 h) n)).(\lambda (H9: (eq T x0 
(TLRef (minus n h)))).(eq_ind_r T (TLRef (minus n h)) (\lambda (t0: T).(ex2 T 
(\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O t))) (\lambda (t2: 
T).(ty3 g e t0 t2)))) (ex_intro2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) 
(lift (S n) O t))) (\lambda (t2: T).(ty3 g e (TLRef (minus n h)) t2)) (lift 
(S (minus n h)) O t) (eq_ind_r T (lift (plus h (S (minus n h))) O t) (\lambda 
(t0: T).(pc3 c0 t0 (lift (S n) O t))) (eq_ind nat (S (plus h (minus n h))) 
(\lambda (n0: nat).(pc3 c0 (lift n0 O t) (lift (S n) O t))) (eq_ind nat n 
(\lambda (n0: nat).(pc3 c0 (lift (S n0) O t) (lift (S n) O t))) (pc3_refl c0 
(lift (S n) O t)) (plus h (minus n h)) (le_plus_minus h n (le_trans h (plus 
x1 h) n (le_plus_r x1 h) H8))) (plus h (S (minus n h))) (plus_n_Sm h (minus n 
h))) (lift h x1 (lift (S (minus n h)) O t)) (lift_free t (S (minus n h)) h O 
x1 (le_trans x1 (S (minus n h)) (plus O (S (minus n h))) (le_S_minus x1 h n 
H8) (le_n (plus O (S (minus n h))))) (le_O_n x1))) (ty3_abbr g (minus n h) e 
d0 u (getl_drop_conf_ge n (CHead d0 (Bind Abbr) u) c0 H1 e h x1 H5 H8) t H2)) 
x0 H9))) H7)) H6)))))))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda 
(d0: C).(\lambda (u: T).(\lambda (H1: (getl n c0 (CHead d0 (Bind Abst) 
u))).(\lambda (t: T).(\lambda (H2: (ty3 g d0 u t)).(\lambda (H3: ((\forall 
(x0: T).(\forall (x1: nat).((eq T u (lift h x1 x0)) \to (\forall (e: 
C).((drop h x1 d0 e) \to (ex2 T (\lambda (t2: T).(pc3 d0 (lift h x1 t2) t)) 
(\lambda (t2: T).(ty3 g e x0 t2)))))))))).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H4: (eq T (TLRef n) (lift h x1 x0))).(\lambda (e: C).(\lambda 
(H5: (drop h x1 c0 e)).(let H_x \def (lift_gen_lref x0 x1 h n H4) in (let H6 
\def H_x in (or_ind (land (lt n x1) (eq T x0 (TLRef n))) (land (le (plus x1 
h) n) (eq T x0 (TLRef (minus n h)))) (ex2 T (\lambda (t2: T).(pc3 c0 (lift h 
x1 t2) (lift (S n) O u))) (\lambda (t2: T).(ty3 g e x0 t2))) (\lambda (H7: 
(land (lt n x1) (eq T x0 (TLRef n)))).(land_ind (lt n x1) (eq T x0 (TLRef n)) 
(ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O u))) (\lambda 
(t2: T).(ty3 g e x0 t2))) (\lambda (H8: (lt n x1)).(\lambda (H9: (eq T x0 
(TLRef n))).(eq_ind_r T (TLRef n) (\lambda (t0: T).(ex2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (lift (S n) O u))) (\lambda (t2: T).(ty3 g e t0 
t2)))) (let H10 \def (eq_ind nat x1 (\lambda (n0: nat).(drop h n0 c0 e)) H5 
(S (plus n (minus x1 (S n)))) (lt_plus_minus n x1 H8)) in (ex3_2_ind T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h (minus x1 (S n)) v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl n e (CHead e0 (Bind Abst) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h (minus x1 (S n)) d0 e0))) (ex2 T 
(\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O u))) (\lambda (t2: 
T).(ty3 g e (TLRef n) t2))) (\lambda (x2: T).(\lambda (x3: C).(\lambda (H11: 
(eq T u (lift h (minus x1 (S n)) x2))).(\lambda (H12: (getl n e (CHead x3 
(Bind Abst) x2))).(\lambda (H13: (drop h (minus x1 (S n)) d0 x3)).(let H14 
\def (eq_ind T u (\lambda (t0: T).(\forall (x4: T).(\forall (x5: nat).((eq T 
t0 (lift h x5 x4)) \to (\forall (e0: C).((drop h x5 d0 e0) \to (ex2 T 
(\lambda (t2: T).(pc3 d0 (lift h x5 t2) t)) (\lambda (t2: T).(ty3 g e0 x4 
t2))))))))) H3 (lift h (minus x1 (S n)) x2) H11) in (let H15 \def (eq_ind T u 
(\lambda (t0: T).(ty3 g d0 t0 t)) H2 (lift h (minus x1 (S n)) x2) H11) in 
(eq_ind_r T (lift h (minus x1 (S n)) x2) (\lambda (t0: T).(ex2 T (\lambda 
(t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O t0))) (\lambda (t2: T).(ty3 g e 
(TLRef n) t2)))) (let H16 \def (H14 x2 (minus x1 (S n)) (refl_equal T (lift h 
(minus x1 (S n)) x2)) x3 H13) in (ex2_ind T (\lambda (t2: T).(pc3 d0 (lift h 
(minus x1 (S n)) t2) t)) (\lambda (t2: T).(ty3 g x3 x2 t2)) (ex2 T (\lambda 
(t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O (lift h (minus x1 (S n)) x2)))) 
(\lambda (t2: T).(ty3 g e (TLRef n) t2))) (\lambda (x4: T).(\lambda (_: (pc3 
d0 (lift h (minus x1 (S n)) x4) t)).(\lambda (H18: (ty3 g x3 x2 
x4)).(eq_ind_r nat (plus (S n) (minus x1 (S n))) (\lambda (n0: nat).(ex2 T 
(\lambda (t2: T).(pc3 c0 (lift h n0 t2) (lift (S n) O (lift h (minus n0 (S 
n)) x2)))) (\lambda (t2: T).(ty3 g e (TLRef n) t2)))) (ex_intro2 T (\lambda 
(t2: T).(pc3 c0 (lift h (plus (S n) (minus x1 (S n))) t2) (lift (S n) O (lift 
h (minus (plus (S n) (minus x1 (S n))) (S n)) x2)))) (\lambda (t2: T).(ty3 g 
e (TLRef n) t2)) (lift (S n) O x2) (eq_ind_r T (lift (S n) O (lift h (minus 
x1 (S n)) x2)) (\lambda (t0: T).(pc3 c0 t0 (lift (S n) O (lift h (minus (plus 
(S n) (minus x1 (S n))) (S n)) x2)))) (eq_ind nat x1 (\lambda (n0: nat).(pc3 
c0 (lift (S n) O (lift h (minus x1 (S n)) x2)) (lift (S n) O (lift h (minus 
n0 (S n)) x2)))) (pc3_refl c0 (lift (S n) O (lift h (minus x1 (S n)) x2))) 
(plus (S n) (minus x1 (S n))) (le_plus_minus (S n) x1 H8)) (lift h (plus (S 
n) (minus x1 (S n))) (lift (S n) O x2)) (lift_d x2 h (S n) (minus x1 (S n)) O 
(le_O_n (minus x1 (S n))))) (ty3_abst g n e x3 x2 H12 x4 H18)) x1 
(le_plus_minus (S n) x1 H8))))) H16)) u H11)))))))) (getl_drop_conf_lt Abst 
c0 d0 u n H1 e h (minus x1 (S n)) H10))) x0 H9))) H7)) (\lambda (H7: (land 
(le (plus x1 h) n) (eq T x0 (TLRef (minus n h))))).(land_ind (le (plus x1 h) 
n) (eq T x0 (TLRef (minus n h))) (ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 
t2) (lift (S n) O u))) (\lambda (t2: T).(ty3 g e x0 t2))) (\lambda (H8: (le 
(plus x1 h) n)).(\lambda (H9: (eq T x0 (TLRef (minus n h)))).(eq_ind_r T 
(TLRef (minus n h)) (\lambda (t0: T).(ex2 T (\lambda (t2: T).(pc3 c0 (lift h 
x1 t2) (lift (S n) O u))) (\lambda (t2: T).(ty3 g e t0 t2)))) (ex_intro2 T 
(\lambda (t2: T).(pc3 c0 (lift h x1 t2) (lift (S n) O u))) (\lambda (t2: 
T).(ty3 g e (TLRef (minus n h)) t2)) (lift (S (minus n h)) O u) (eq_ind_r T 
(lift (plus h (S (minus n h))) O u) (\lambda (t0: T).(pc3 c0 t0 (lift (S n) O 
u))) (eq_ind nat (S (plus h (minus n h))) (\lambda (n0: nat).(pc3 c0 (lift n0 
O u) (lift (S n) O u))) (eq_ind nat n (\lambda (n0: nat).(pc3 c0 (lift (S n0) 
O u) (lift (S n) O u))) (pc3_refl c0 (lift (S n) O u)) (plus h (minus n h)) 
(le_plus_minus h n (le_trans h (plus x1 h) n (le_plus_r x1 h) H8))) (plus h 
(S (minus n h))) (plus_n_Sm h (minus n h))) (lift h x1 (lift (S (minus n h)) 
O u)) (lift_free u (S (minus n h)) h O x1 (le_trans x1 (S (minus n h)) (plus 
O (S (minus n h))) (le_S_minus x1 h n H8) (le_n (plus O (S (minus n h))))) 
(le_O_n x1))) (ty3_abst g (minus n h) e d0 u (getl_drop_conf_ge n (CHead d0 
(Bind Abst) u) c0 H1 e h x1 H5 H8) t H2)) x0 H9))) H7)) H6)))))))))))))))) 
(\lambda (c0: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H1: (ty3 g c0 u 
t)).(\lambda (H2: ((\forall (x0: T).(\forall (x1: nat).((eq T u (lift h x1 
x0)) \to (\forall (e: C).((drop h x1 c0 e) \to (ex2 T (\lambda (t2: T).(pc3 
c0 (lift h x1 t2) t)) (\lambda (t2: T).(ty3 g e x0 t2)))))))))).(\lambda (b: 
B).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H3: (ty3 g (CHead c0 (Bind b) 
u) t2 t3)).(\lambda (H4: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift 
h x1 x0)) \to (\forall (e: C).((drop h x1 (CHead c0 (Bind b) u) e) \to (ex2 T 
(\lambda (t4: T).(pc3 (CHead c0 (Bind b) u) (lift h x1 t4) t3)) (\lambda (t4: 
T).(ty3 g e x0 t4)))))))))).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H5: 
(eq T (THead (Bind b) u t2) (lift h x1 x0))).(\lambda (e: C).(\lambda (H6: 
(drop h x1 c0 e)).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 
(THead (Bind b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u (lift h x1 
y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) z)))) (ex2 T 
(\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind b) u t3))) (\lambda (t4: 
T).(ty3 g e x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T x0 
(THead (Bind b) x2 x3))).(\lambda (H8: (eq T u (lift h x1 x2))).(\lambda (H9: 
(eq T t2 (lift h (S x1) x3))).(eq_ind_r T (THead (Bind b) x2 x3) (\lambda 
(t0: T).(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind b) u 
t3))) (\lambda (t4: T).(ty3 g e t0 t4)))) (let H10 \def (eq_ind T t2 (\lambda 
(t0: T).(\forall (x4: T).(\forall (x5: nat).((eq T t0 (lift h x5 x4)) \to 
(\forall (e0: C).((drop h x5 (CHead c0 (Bind b) u) e0) \to (ex2 T (\lambda 
(t4: T).(pc3 (CHead c0 (Bind b) u) (lift h x5 t4) t3)) (\lambda (t4: T).(ty3 
g e0 x4 t4))))))))) H4 (lift h (S x1) x3) H9) in (let H11 \def (eq_ind T t2 
(\lambda (t0: T).(ty3 g (CHead c0 (Bind b) u) t0 t3)) H3 (lift h (S x1) x3) 
H9) in (let H12 \def (eq_ind T u (\lambda (t0: T).(ty3 g (CHead c0 (Bind b) 
t0) (lift h (S x1) x3) t3)) H11 (lift h x1 x2) H8) in (let H13 \def (eq_ind T 
u (\lambda (t0: T).(\forall (x4: T).(\forall (x5: nat).((eq T (lift h (S x1) 
x3) (lift h x5 x4)) \to (\forall (e0: C).((drop h x5 (CHead c0 (Bind b) t0) 
e0) \to (ex2 T (\lambda (t4: T).(pc3 (CHead c0 (Bind b) t0) (lift h x5 t4) 
t3)) (\lambda (t4: T).(ty3 g e0 x4 t4))))))))) H10 (lift h x1 x2) H8) in (let 
H14 \def (eq_ind T u (\lambda (t0: T).(\forall (x4: T).(\forall (x5: 
nat).((eq T t0 (lift h x5 x4)) \to (\forall (e0: C).((drop h x5 c0 e0) \to 
(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x5 t4) t)) (\lambda (t4: T).(ty3 g e0 
x4 t4))))))))) H2 (lift h x1 x2) H8) in (let H15 \def (eq_ind T u (\lambda 
(t0: T).(ty3 g c0 t0 t)) H1 (lift h x1 x2) H8) in (eq_ind_r T (lift h x1 x2) 
(\lambda (t0: T).(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind 
b) t0 t3))) (\lambda (t4: T).(ty3 g e (THead (Bind b) x2 x3) t4)))) (let H16 
\def (H14 x2 x1 (refl_equal T (lift h x1 x2)) e H6) in (ex2_ind T (\lambda 
(t4: T).(pc3 c0 (lift h x1 t4) t)) (\lambda (t4: T).(ty3 g e x2 t4)) (ex2 T 
(\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind b) (lift h x1 x2) t3))) 
(\lambda (t4: T).(ty3 g e (THead (Bind b) x2 x3) t4))) (\lambda (x4: 
T).(\lambda (_: (pc3 c0 (lift h x1 x4) t)).(\lambda (H18: (ty3 g e x2 
x4)).(let H19 \def (H13 x3 (S x1) (refl_equal T (lift h (S x1) x3)) (CHead e 
(Bind b) x2) (drop_skip_bind h x1 c0 e H6 b x2)) in (ex2_ind T (\lambda (t4: 
T).(pc3 (CHead c0 (Bind b) (lift h x1 x2)) (lift h (S x1) t4) t3)) (\lambda 
(t4: T).(ty3 g (CHead e (Bind b) x2) x3 t4)) (ex2 T (\lambda (t4: T).(pc3 c0 
(lift h x1 t4) (THead (Bind b) (lift h x1 x2) t3))) (\lambda (t4: T).(ty3 g e 
(THead (Bind b) x2 x3) t4))) (\lambda (x5: T).(\lambda (H20: (pc3 (CHead c0 
(Bind b) (lift h x1 x2)) (lift h (S x1) x5) t3)).(\lambda (H21: (ty3 g (CHead 
e (Bind b) x2) x3 x5)).(ex_ind T (\lambda (t0: T).(ty3 g (CHead e (Bind b) 
x2) x5 t0)) (ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind b) 
(lift h x1 x2) t3))) (\lambda (t4: T).(ty3 g e (THead (Bind b) x2 x3) t4))) 
(\lambda (x6: T).(\lambda (_: (ty3 g (CHead e (Bind b) x2) x5 x6)).(ex_intro2 
T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Bind b) (lift h x1 x2) 
t3))) (\lambda (t4: T).(ty3 g e (THead (Bind b) x2 x3) t4)) (THead (Bind b) 
x2 x5) (eq_ind_r T (THead (Bind b) (lift h x1 x2) (lift h (S x1) x5)) 
(\lambda (t0: T).(pc3 c0 t0 (THead (Bind b) (lift h x1 x2) t3))) (pc3_head_2 
c0 (lift h x1 x2) (lift h (S x1) x5) t3 (Bind b) H20) (lift h x1 (THead (Bind 
b) x2 x5)) (lift_bind b x2 x5 h x1)) (ty3_bind g e x2 x4 H18 b x3 x5 H21)))) 
(ty3_correct g (CHead e (Bind b) x2) x3 x5 H21))))) H19))))) H16)) u 
H8))))))) x0 H7)))))) (lift_gen_bind b u t2 x0 h x1 H5))))))))))))))))) 
(\lambda (c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (H1: (ty3 g c0 w 
u)).(\lambda (H2: ((\forall (x0: T).(\forall (x1: nat).((eq T w (lift h x1 
x0)) \to (\forall (e: C).((drop h x1 c0 e) \to (ex2 T (\lambda (t2: T).(pc3 
c0 (lift h x1 t2) u)) (\lambda (t2: T).(ty3 g e x0 t2)))))))))).(\lambda (v: 
T).(\lambda (t: T).(\lambda (H3: (ty3 g c0 v (THead (Bind Abst) u 
t))).(\lambda (H4: ((\forall (x0: T).(\forall (x1: nat).((eq T v (lift h x1 
x0)) \to (\forall (e: C).((drop h x1 c0 e) \to (ex2 T (\lambda (t2: T).(pc3 
c0 (lift h x1 t2) (THead (Bind Abst) u t))) (\lambda (t2: T).(ty3 g e x0 
t2)))))))))).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H5: (eq T (THead 
(Flat Appl) w v) (lift h x1 x0))).(\lambda (e: C).(\lambda (H6: (drop h x1 c0 
e)).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Flat 
Appl) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T w (lift h x1 y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T v (lift h x1 z)))) (ex2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (THead (Flat Appl) w (THead (Bind Abst) u t)))) 
(\lambda (t2: T).(ty3 g e x0 t2))) (\lambda (x2: T).(\lambda (x3: T).(\lambda 
(H7: (eq T x0 (THead (Flat Appl) x2 x3))).(\lambda (H8: (eq T w (lift h x1 
x2))).(\lambda (H9: (eq T v (lift h x1 x3))).(eq_ind_r T (THead (Flat Appl) 
x2 x3) (\lambda (t0: T).(ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (THead 
(Flat Appl) w (THead (Bind Abst) u t)))) (\lambda (t2: T).(ty3 g e t0 t2)))) 
(let H10 \def (eq_ind T v (\lambda (t0: T).(\forall (x4: T).(\forall (x5: 
nat).((eq T t0 (lift h x5 x4)) \to (\forall (e0: C).((drop h x5 c0 e0) \to 
(ex2 T (\lambda (t2: T).(pc3 c0 (lift h x5 t2) (THead (Bind Abst) u t))) 
(\lambda (t2: T).(ty3 g e0 x4 t2))))))))) H4 (lift h x1 x3) H9) in (let H11 
\def (eq_ind T v (\lambda (t0: T).(ty3 g c0 t0 (THead (Bind Abst) u t))) H3 
(lift h x1 x3) H9) in (let H12 \def (eq_ind T w (\lambda (t0: T).(\forall 
(x4: T).(\forall (x5: nat).((eq T t0 (lift h x5 x4)) \to (\forall (e0: 
C).((drop h x5 c0 e0) \to (ex2 T (\lambda (t2: T).(pc3 c0 (lift h x5 t2) u)) 
(\lambda (t2: T).(ty3 g e0 x4 t2))))))))) H2 (lift h x1 x2) H8) in (let H13 
\def (eq_ind T w (\lambda (t0: T).(ty3 g c0 t0 u)) H1 (lift h x1 x2) H8) in 
(eq_ind_r T (lift h x1 x2) (\lambda (t0: T).(ex2 T (\lambda (t2: T).(pc3 c0 
(lift h x1 t2) (THead (Flat Appl) t0 (THead (Bind Abst) u t)))) (\lambda (t2: 
T).(ty3 g e (THead (Flat Appl) x2 x3) t2)))) (let H14 \def (H12 x2 x1 
(refl_equal T (lift h x1 x2)) e H6) in (ex2_ind T (\lambda (t2: T).(pc3 c0 
(lift h x1 t2) u)) (\lambda (t2: T).(ty3 g e x2 t2)) (ex2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (THead (Flat Appl) (lift h x1 x2) (THead (Bind 
Abst) u t)))) (\lambda (t2: T).(ty3 g e (THead (Flat Appl) x2 x3) t2))) 
(\lambda (x4: T).(\lambda (H15: (pc3 c0 (lift h x1 x4) u)).(\lambda (H16: 
(ty3 g e x2 x4)).(let H17 \def (H10 x3 x1 (refl_equal T (lift h x1 x3)) e H6) 
in (ex2_ind T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (THead (Bind Abst) u 
t))) (\lambda (t2: T).(ty3 g e x3 t2)) (ex2 T (\lambda (t2: T).(pc3 c0 (lift 
h x1 t2) (THead (Flat Appl) (lift h x1 x2) (THead (Bind Abst) u t)))) 
(\lambda (t2: T).(ty3 g e (THead (Flat Appl) x2 x3) t2))) (\lambda (x5: 
T).(\lambda (H18: (pc3 c0 (lift h x1 x5) (THead (Bind Abst) u t))).(\lambda 
(H19: (ty3 g e x3 x5)).(ex3_2_ind T T (\lambda (u1: T).(\lambda (t2: T).(pr3 
e x5 (THead (Bind Abst) u1 t2)))) (\lambda (u1: T).(\lambda (_: T).(pr3 c0 u 
(lift h x1 u1)))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u0: T).(pr3 (CHead c0 (Bind b) u0) t (lift h (S x1) t2)))))) (ex2 T (\lambda 
(t2: T).(pc3 c0 (lift h x1 t2) (THead (Flat Appl) (lift h x1 x2) (THead (Bind 
Abst) u t)))) (\lambda (t2: T).(ty3 g e (THead (Flat Appl) x2 x3) t2))) 
(\lambda (x6: T).(\lambda (x7: T).(\lambda (H20: (pr3 e x5 (THead (Bind Abst) 
x6 x7))).(\lambda (H21: (pr3 c0 u (lift h x1 x6))).(\lambda (H22: ((\forall 
(b: B).(\forall (u0: T).(pr3 (CHead c0 (Bind b) u0) t (lift h (S x1) 
x7)))))).(ex_ind T (\lambda (t0: T).(ty3 g e x5 t0)) (ex2 T (\lambda (t2: 
T).(pc3 c0 (lift h x1 t2) (THead (Flat Appl) (lift h x1 x2) (THead (Bind 
Abst) u t)))) (\lambda (t2: T).(ty3 g e (THead (Flat Appl) x2 x3) t2))) 
(\lambda (x8: T).(\lambda (H23: (ty3 g e x5 x8)).(let H_y \def (ty3_sred_pr3 
e x5 (THead (Bind Abst) x6 x7) H20 g x8 H23) in (ex3_2_ind T T (\lambda (t2: 
T).(\lambda (_: T).(pc3 e (THead (Bind Abst) x6 t2) x8))) (\lambda (_: 
T).(\lambda (t0: T).(ty3 g e x6 t0))) (\lambda (t2: T).(\lambda (_: T).(ty3 g 
(CHead e (Bind Abst) x6) x7 t2))) (ex2 T (\lambda (t2: T).(pc3 c0 (lift h x1 
t2) (THead (Flat Appl) (lift h x1 x2) (THead (Bind Abst) u t)))) (\lambda 
(t2: T).(ty3 g e (THead (Flat Appl) x2 x3) t2))) (\lambda (x9: T).(\lambda 
(x10: T).(\lambda (_: (pc3 e (THead (Bind Abst) x6 x9) x8)).(\lambda (H25: 
(ty3 g e x6 x10)).(\lambda (H26: (ty3 g (CHead e (Bind Abst) x6) x7 
x9)).(ex_intro2 T (\lambda (t2: T).(pc3 c0 (lift h x1 t2) (THead (Flat Appl) 
(lift h x1 x2) (THead (Bind Abst) u t)))) (\lambda (t2: T).(ty3 g e (THead 
(Flat Appl) x2 x3) t2)) (THead (Flat Appl) x2 (THead (Bind Abst) x6 x7)) 
(eq_ind_r T (THead (Flat Appl) (lift h x1 x2) (lift h x1 (THead (Bind Abst) 
x6 x7))) (\lambda (t0: T).(pc3 c0 t0 (THead (Flat Appl) (lift h x1 x2) (THead 
(Bind Abst) u t)))) (pc3_thin_dx c0 (lift h x1 (THead (Bind Abst) x6 x7)) 
(THead (Bind Abst) u t) (eq_ind_r T (THead (Bind Abst) (lift h x1 x6) (lift h 
(S x1) x7)) (\lambda (t0: T).(pc3 c0 t0 (THead (Bind Abst) u t))) 
(pc3_head_21 c0 (lift h x1 x6) u (pc3_pr3_x c0 (lift h x1 x6) u H21) (Bind 
Abst) (lift h (S x1) x7) t (pc3_pr3_x (CHead c0 (Bind Abst) (lift h x1 x6)) 
(lift h (S x1) x7) t (H22 Abst (lift h x1 x6)))) (lift h x1 (THead (Bind 
Abst) x6 x7)) (lift_bind Abst x6 x7 h x1)) (lift h x1 x2) Appl) (lift h x1 
(THead (Flat Appl) x2 (THead (Bind Abst) x6 x7))) (lift_flat Appl x2 (THead 
(Bind Abst) x6 x7) h x1)) (ty3_appl g e x2 x6 (ty3_conv g e x6 x10 H25 x2 x4 
H16 (pc3_gen_lift c0 x4 x6 h x1 (pc3_t u c0 (lift h x1 x4) H15 (lift h x1 x6) 
(pc3_pr3_r c0 u (lift h x1 x6) H21)) e H6)) x3 x7 (ty3_conv g e (THead (Bind 
Abst) x6 x7) (THead (Bind Abst) x6 x9) (ty3_bind g e x6 x10 H25 Abst x7 x9 
H26) x3 x5 H19 (pc3_pr3_r e x5 (THead (Bind Abst) x6 x7) H20))))))))) 
(ty3_gen_bind g Abst e x6 x7 x8 H_y))))) (ty3_correct g e x3 x5 H19))))))) 
(pc3_gen_lift_abst c0 x5 t u h x1 H18 e H6))))) H17))))) H14)) w H8))))) x0 
H7)))))) (lift_gen_flat Appl w v x0 h x1 H5)))))))))))))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (ty3 g c0 t2 t3)).(\lambda 
(H2: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to 
(\forall (e: C).((drop h x1 c0 e) \to (ex2 T (\lambda (t4: T).(pc3 c0 (lift h 
x1 t4) t3)) (\lambda (t4: T).(ty3 g e x0 t4)))))))))).(\lambda (t0: 
T).(\lambda (H3: (ty3 g c0 t3 t0)).(\lambda (H4: ((\forall (x0: T).(\forall 
(x1: nat).((eq T t3 (lift h x1 x0)) \to (\forall (e: C).((drop h x1 c0 e) \to 
(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) t0)) (\lambda (t4: T).(ty3 g e 
x0 t4)))))))))).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H5: (eq T 
(THead (Flat Cast) t3 t2) (lift h x1 x0))).(\lambda (e: C).(\lambda (H6: 
(drop h x1 c0 e)).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 
(THead (Flat Cast) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T t3 (lift h 
x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h x1 z)))) (ex2 T 
(\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Flat Cast) t0 t3))) (\lambda 
(t4: T).(ty3 g e x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq 
T x0 (THead (Flat Cast) x2 x3))).(\lambda (H8: (eq T t3 (lift h x1 
x2))).(\lambda (H9: (eq T t2 (lift h x1 x3))).(eq_ind_r T (THead (Flat Cast) 
x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead 
(Flat Cast) t0 t3))) (\lambda (t4: T).(ty3 g e t t4)))) (let H10 \def (eq_ind 
T t3 (\lambda (t: T).(\forall (x4: T).(\forall (x5: nat).((eq T t (lift h x5 
x4)) \to (\forall (e0: C).((drop h x5 c0 e0) \to (ex2 T (\lambda (t4: T).(pc3 
c0 (lift h x5 t4) t0)) (\lambda (t4: T).(ty3 g e0 x4 t4))))))))) H4 (lift h 
x1 x2) H8) in (let H11 \def (eq_ind T t3 (\lambda (t: T).(ty3 g c0 t t0)) H3 
(lift h x1 x2) H8) in (let H12 \def (eq_ind T t3 (\lambda (t: T).(\forall 
(x4: T).(\forall (x5: nat).((eq T t2 (lift h x5 x4)) \to (\forall (e0: 
C).((drop h x5 c0 e0) \to (ex2 T (\lambda (t4: T).(pc3 c0 (lift h x5 t4) t)) 
(\lambda (t4: T).(ty3 g e0 x4 t4))))))))) H2 (lift h x1 x2) H8) in (let H13 
\def (eq_ind T t3 (\lambda (t: T).(ty3 g c0 t2 t)) H1 (lift h x1 x2) H8) in 
(eq_ind_r T (lift h x1 x2) (\lambda (t: T).(ex2 T (\lambda (t4: T).(pc3 c0 
(lift h x1 t4) (THead (Flat Cast) t0 t))) (\lambda (t4: T).(ty3 g e (THead 
(Flat Cast) x2 x3) t4)))) (let H14 \def (eq_ind T t2 (\lambda (t: T).(ty3 g 
c0 t (lift h x1 x2))) H13 (lift h x1 x3) H9) in (let H15 \def (eq_ind T t2 
(\lambda (t: T).(\forall (x4: T).(\forall (x5: nat).((eq T t (lift h x5 x4)) 
\to (\forall (e0: C).((drop h x5 c0 e0) \to (ex2 T (\lambda (t4: T).(pc3 c0 
(lift h x5 t4) (lift h x1 x2))) (\lambda (t4: T).(ty3 g e0 x4 t4))))))))) H12 
(lift h x1 x3) H9) in (let H16 \def (H15 x3 x1 (refl_equal T (lift h x1 x3)) 
e H6) in (ex2_ind T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (lift h x1 x2))) 
(\lambda (t4: T).(ty3 g e x3 t4)) (ex2 T (\lambda (t4: T).(pc3 c0 (lift h x1 
t4) (THead (Flat Cast) t0 (lift h x1 x2)))) (\lambda (t4: T).(ty3 g e (THead 
(Flat Cast) x2 x3) t4))) (\lambda (x4: T).(\lambda (H17: (pc3 c0 (lift h x1 
x4) (lift h x1 x2))).(\lambda (H18: (ty3 g e x3 x4)).(let H19 \def (H10 x2 x1 
(refl_equal T (lift h x1 x2)) e H6) in (ex2_ind T (\lambda (t4: T).(pc3 c0 
(lift h x1 t4) t0)) (\lambda (t4: T).(ty3 g e x2 t4)) (ex2 T (\lambda (t4: 
T).(pc3 c0 (lift h x1 t4) (THead (Flat Cast) t0 (lift h x1 x2)))) (\lambda 
(t4: T).(ty3 g e (THead (Flat Cast) x2 x3) t4))) (\lambda (x5: T).(\lambda 
(H20: (pc3 c0 (lift h x1 x5) t0)).(\lambda (H21: (ty3 g e x2 x5)).(ex_intro2 
T (\lambda (t4: T).(pc3 c0 (lift h x1 t4) (THead (Flat Cast) t0 (lift h x1 
x2)))) (\lambda (t4: T).(ty3 g e (THead (Flat Cast) x2 x3) t4)) (THead (Flat 
Cast) x5 x2) (eq_ind_r T (THead (Flat Cast) (lift h x1 x5) (lift h x1 x2)) 
(\lambda (t: T).(pc3 c0 t (THead (Flat Cast) t0 (lift h x1 x2)))) (pc3_head_1 
c0 (lift h x1 x5) t0 H20 (Flat Cast) (lift h x1 x2)) (lift h x1 (THead (Flat 
Cast) x5 x2)) (lift_flat Cast x5 x2 h x1)) (ty3_cast g e x3 x2 (ty3_conv g e 
x2 x5 H21 x3 x4 H18 (pc3_gen_lift c0 x4 x2 h x1 H17 e H6)) x5 H21))))) 
H19))))) H16)))) t3 H8))))) x0 H7)))))) (lift_gen_flat Cast t3 t2 x0 h x1 
H5))))))))))))))) c y x H0))))) H))))))).
(* COMMENTS
Initial nodes: 9781
END *)

theorem ty3_tred:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((pr3 c t1 t2) \to (ty3 g c u t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).(ex_ind T 
(\lambda (t: T).(ty3 g c t1 t)) (ty3 g c u t2) (\lambda (x: T).(\lambda (H1: 
(ty3 g c t1 x)).(let H_y \def (ty3_sred_pr3 c t1 t2 H0 g x H1) in (ty3_conv g 
c t2 x H_y u t1 H (pc3_pr3_r c t1 t2 H0))))) (ty3_correct g c u t1 H)))))))).
(* COMMENTS
Initial nodes: 121
END *)

theorem ty3_sconv_pc3:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to ((pc3 c u1 
u2) \to (pc3 c t1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(\lambda (H1: (pc3 c u1 u2)).(let H2 \def H1 in (ex2_ind T (\lambda 
(t: T).(pr3 c u1 t)) (\lambda (t: T).(pr3 c u2 t)) (pc3 c t1 t2) (\lambda (x: 
T).(\lambda (H3: (pr3 c u1 x)).(\lambda (H4: (pr3 c u2 x)).(let H_y \def 
(ty3_sred_pr3 c u2 x H4 g t2 H0) in (let H_y0 \def (ty3_sred_pr3 c u1 x H3 g 
t1 H) in (ty3_unique g c x t1 H_y0 t2 H_y)))))) H2)))))))))).
(* COMMENTS
Initial nodes: 141
END *)

theorem ty3_sred_back:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t0: T).((ty3 g c 
t1 t0) \to (\forall (t2: T).((pr3 c t1 t2) \to (\forall (t: T).((ty3 g c t2 
t) \to (ty3 g c t1 t)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t0: T).(\lambda 
(H: (ty3 g c t1 t0)).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).(\lambda 
(t: T).(\lambda (H1: (ty3 g c t2 t)).(ex_ind T (\lambda (t3: T).(ty3 g c t 
t3)) (ty3 g c t1 t) (\lambda (x: T).(\lambda (H2: (ty3 g c t x)).(ty3_conv g 
c t x H2 t1 t0 H (ty3_unique g c t2 t0 (ty3_sred_pr3 c t1 t2 H0 g t0 H) t 
H1)))) (ty3_correct g c t2 t H1)))))))))).
(* COMMENTS
Initial nodes: 137
END *)

theorem ty3_sconv:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to ((pc3 c u1 
u2) \to (ty3 g c u1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(\lambda (H1: (pc3 c u1 u2)).(let H2 \def H1 in (ex2_ind T (\lambda 
(t: T).(pr3 c u1 t)) (\lambda (t: T).(pr3 c u2 t)) (ty3 g c u1 t2) (\lambda 
(x: T).(\lambda (H3: (pr3 c u1 x)).(\lambda (H4: (pr3 c u2 x)).(ty3_sred_back 
g c u1 t1 H x H3 t2 (ty3_sred_pr3 c u2 x H4 g t2 H0))))) H2)))))))))).
(* COMMENTS
Initial nodes: 129
END *)

