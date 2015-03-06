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

include "basic_1/pr0/fwd.ma".

include "basic_1/subst0/props.ma".

theorem pr0_lift:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (h: nat).(\forall 
(d: nat).(pr0 (lift h d t1) (lift h d t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(pr0_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t) 
(lift h d t0)))))) (\lambda (t: T).(\lambda (h: nat).(\lambda (d: 
nat).(pr0_refl (lift h d t))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda 
(_: (pr0 u1 u2)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 
(lift h d u1) (lift h d u2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(_: (pr0 t3 t4)).(\lambda (H3: ((\forall (h: nat).(\forall (d: nat).(pr0 
(lift h d t3) (lift h d t4)))))).(\lambda (k: K).(\lambda (h: nat).(\lambda 
(d: nat).(eq_ind_r T (THead k (lift h d u1) (lift h (s k d) t3)) (\lambda (t: 
T).(pr0 t (lift h d (THead k u2 t4)))) (eq_ind_r T (THead k (lift h d u2) 
(lift h (s k d) t4)) (\lambda (t: T).(pr0 (THead k (lift h d u1) (lift h (s k 
d) t3)) t)) (pr0_comp (lift h d u1) (lift h d u2) (H1 h d) (lift h (s k d) 
t3) (lift h (s k d) t4) (H3 h (s k d)) k) (lift h d (THead k u2 t4)) 
(lift_head k u2 t4 h d)) (lift h d (THead k u1 t3)) (lift_head k u1 t3 h 
d))))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: 
(pr0 v1 v2)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h 
d v1) (lift h d v2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 
t3 t4)).(\lambda (H3: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) 
(lift h d t4)))))).(\lambda (h: nat).(\lambda (d: nat).(eq_ind_r T (THead 
(Flat Appl) (lift h d v1) (lift h (s (Flat Appl) d) (THead (Bind Abst) u 
t3))) (\lambda (t: T).(pr0 t (lift h d (THead (Bind Abbr) v2 t4)))) (eq_ind_r 
T (THead (Bind Abst) (lift h (s (Flat Appl) d) u) (lift h (s (Bind Abst) (s 
(Flat Appl) d)) t3)) (\lambda (t: T).(pr0 (THead (Flat Appl) (lift h d v1) t) 
(lift h d (THead (Bind Abbr) v2 t4)))) (eq_ind_r T (THead (Bind Abbr) (lift h 
d v2) (lift h (s (Bind Abbr) d) t4)) (\lambda (t: T).(pr0 (THead (Flat Appl) 
(lift h d v1) (THead (Bind Abst) (lift h (s (Flat Appl) d) u) (lift h (s 
(Bind Abst) (s (Flat Appl) d)) t3))) t)) (pr0_beta (lift h (s (Flat Appl) d) 
u) (lift h d v1) (lift h d v2) (H1 h d) (lift h (s (Bind Abst) (s (Flat Appl) 
d)) t3) (lift h (s (Bind Abbr) d) t4) (H3 h (s (Bind Abbr) d))) (lift h d 
(THead (Bind Abbr) v2 t4)) (lift_head (Bind Abbr) v2 t4 h d)) (lift h (s 
(Flat Appl) d) (THead (Bind Abst) u t3)) (lift_head (Bind Abst) u t3 h (s 
(Flat Appl) d))) (lift h d (THead (Flat Appl) v1 (THead (Bind Abst) u t3))) 
(lift_head (Flat Appl) v1 (THead (Bind Abst) u t3) h d))))))))))))) (\lambda 
(b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(\lambda (H2: ((\forall (h: nat).(\forall (d: 
nat).(pr0 (lift h d v1) (lift h d v2)))))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (_: (pr0 u1 u2)).(\lambda (H4: ((\forall (h: nat).(\forall (d: 
nat).(pr0 (lift h d u1) (lift h d u2)))))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (pr0 t3 t4)).(\lambda (H6: ((\forall (h: nat).(\forall (d: 
nat).(pr0 (lift h d t3) (lift h d t4)))))).(\lambda (h: nat).(\lambda (d: 
nat).(eq_ind_r T (THead (Flat Appl) (lift h d v1) (lift h (s (Flat Appl) d) 
(THead (Bind b) u1 t3))) (\lambda (t: T).(pr0 t (lift h d (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4))))) (eq_ind_r T (THead (Bind b) 
(lift h (s (Flat Appl) d) u1) (lift h (s (Bind b) (s (Flat Appl) d)) t3)) 
(\lambda (t: T).(pr0 (THead (Flat Appl) (lift h d v1) t) (lift h d (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))))) (eq_ind_r T (THead 
(Bind b) (lift h d u2) (lift h (s (Bind b) d) (THead (Flat Appl) (lift (S O) 
O v2) t4))) (\lambda (t: T).(pr0 (THead (Flat Appl) (lift h d v1) (THead 
(Bind b) (lift h (s (Flat Appl) d) u1) (lift h (s (Bind b) (s (Flat Appl) d)) 
t3))) t)) (eq_ind_r T (THead (Flat Appl) (lift h (s (Bind b) d) (lift (S O) O 
v2)) (lift h (s (Flat Appl) (s (Bind b) d)) t4)) (\lambda (t: T).(pr0 (THead 
(Flat Appl) (lift h d v1) (THead (Bind b) (lift h (s (Flat Appl) d) u1) (lift 
h (s (Bind b) (s (Flat Appl) d)) t3))) (THead (Bind b) (lift h d u2) t))) 
(eq_ind nat (plus (S O) d) (\lambda (n: nat).(pr0 (THead (Flat Appl) (lift h 
d v1) (THead (Bind b) (lift h d u1) (lift h n t3))) (THead (Bind b) (lift h d 
u2) (THead (Flat Appl) (lift h n (lift (S O) O v2)) (lift h n t4))))) 
(eq_ind_r T (lift (S O) O (lift h d v2)) (\lambda (t: T).(pr0 (THead (Flat 
Appl) (lift h d v1) (THead (Bind b) (lift h d u1) (lift h (plus (S O) d) 
t3))) (THead (Bind b) (lift h d u2) (THead (Flat Appl) t (lift h (plus (S O) 
d) t4))))) (pr0_upsilon b H0 (lift h d v1) (lift h d v2) (H2 h d) (lift h d 
u1) (lift h d u2) (H4 h d) (lift h (plus (S O) d) t3) (lift h (plus (S O) d) 
t4) (H6 h (plus (S O) d))) (lift h (plus (S O) d) (lift (S O) O v2)) (lift_d 
v2 h (S O) d O (le_O_n d))) (S d) (refl_equal nat (S d))) (lift h (s (Bind b) 
d) (THead (Flat Appl) (lift (S O) O v2) t4)) (lift_head (Flat Appl) (lift (S 
O) O v2) t4 h (s (Bind b) d))) (lift h d (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4))) (lift_head (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4) h d)) (lift h (s (Flat Appl) d) (THead (Bind b) u1 t3)) 
(lift_head (Bind b) u1 t3 h (s (Flat Appl) d))) (lift h d (THead (Flat Appl) 
v1 (THead (Bind b) u1 t3))) (lift_head (Flat Appl) v1 (THead (Bind b) u1 t3) 
h d)))))))))))))))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 
u2)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d u1) 
(lift h d u2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 
t4)).(\lambda (H3: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) 
(lift h d t4)))))).(\lambda (w: T).(\lambda (H4: (subst0 O u2 t4 w)).(\lambda 
(h: nat).(\lambda (d: nat).(eq_ind_r T (THead (Bind Abbr) (lift h d u1) (lift 
h (s (Bind Abbr) d) t3)) (\lambda (t: T).(pr0 t (lift h d (THead (Bind Abbr) 
u2 w)))) (eq_ind_r T (THead (Bind Abbr) (lift h d u2) (lift h (s (Bind Abbr) 
d) w)) (\lambda (t: T).(pr0 (THead (Bind Abbr) (lift h d u1) (lift h (s (Bind 
Abbr) d) t3)) t)) (pr0_delta (lift h d u1) (lift h d u2) (H1 h d) (lift h (S 
d) t3) (lift h (S d) t4) (H3 h (S d)) (lift h (S d) w) (let d' \def (S d) in 
(eq_ind nat (minus (S d) (S O)) (\lambda (n: nat).(subst0 O (lift h n u2) 
(lift h d' t4) (lift h d' w))) (subst0_lift_lt t4 w u2 O H4 (S d) (le_n_S O d 
(le_O_n d)) h) d (eq_ind nat d (\lambda (n: nat).(eq nat n d)) (le_antisym d 
d (le_n d) (le_n d)) (minus d O) (minus_n_O d))))) (lift h d (THead (Bind 
Abbr) u2 w)) (lift_head (Bind Abbr) u2 w h d)) (lift h d (THead (Bind Abbr) 
u1 t3)) (lift_head (Bind Abbr) u1 t3 h d)))))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (pr0 t3 t4)).(\lambda (H2: ((\forall (h: nat).(\forall (d: 
nat).(pr0 (lift h d t3) (lift h d t4)))))).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (d: nat).(eq_ind_r T (THead (Bind b) (lift h d u) (lift h (s 
(Bind b) d) (lift (S O) O t3))) (\lambda (t: T).(pr0 t (lift h d t4))) 
(eq_ind nat (plus (S O) d) (\lambda (n: nat).(pr0 (THead (Bind b) (lift h d 
u) (lift h n (lift (S O) O t3))) (lift h d t4))) (eq_ind_r T (lift (S O) O 
(lift h d t3)) (\lambda (t: T).(pr0 (THead (Bind b) (lift h d u) t) (lift h d 
t4))) (pr0_zeta b H0 (lift h d t3) (lift h d t4) (H2 h d) (lift h d u)) (lift 
h (plus (S O) d) (lift (S O) O t3)) (lift_d t3 h (S O) d O (le_O_n d))) (S d) 
(refl_equal nat (S d))) (lift h d (THead (Bind b) u (lift (S O) O t3))) 
(lift_head (Bind b) u (lift (S O) O t3) h d))))))))))) (\lambda (t3: 
T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (H1: ((\forall (h: 
nat).(\forall (d: nat).(pr0 (lift h d t3) (lift h d t4)))))).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (d: nat).(eq_ind_r T (THead (Flat Cast) (lift h 
d u) (lift h (s (Flat Cast) d) t3)) (\lambda (t: T).(pr0 t (lift h d t4))) 
(pr0_tau (lift h (s (Flat Cast) d) t3) (lift h d t4) (H1 h d) (lift h d u)) 
(lift h d (THead (Flat Cast) u t3)) (lift_head (Flat Cast) u t3 h d))))))))) 
t1 t2 H))).

theorem pr0_gen_abbr:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abbr) u1 t1) x)).(insert_eq T (THead (Bind Abbr) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda 
(y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S 
O) O x)))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O t0)))))) (\lambda (t: 
T).(\lambda (H1: (eq T t (THead (Bind Abbr) u1 t1))).(let H2 \def (f_equal T 
T (\lambda (e: T).e) t (THead (Bind Abbr) u1 t1) H1) in (eq_ind_r T (THead 
(Bind Abbr) u1 t1) (\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t2))))))) (pr0 
t1 (lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t2))))))) (pr0 t1 (lift (S O) O (THead (Bind Abbr) u1 t1))) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Bind Abbr) u1 t1) (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2)))))) u1 t1 (refl_equal T (THead (Bind 
Abbr) u1 t1)) (pr0_refl u1) (or_introl (pr0 t1 t1) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u1 y0 t1))) (pr0_refl t1)))) t 
H2)))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda 
(H2: (((eq T u0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 
t2))))))) (pr0 t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H3: (pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u0 t0) (THead (Bind 
Abbr) u1 t1))).(let H6 \def (f_equal T K (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k u0 t0) (THead (Bind Abbr) u1 t1) H5) in ((let H7 
\def (f_equal T T (\lambda (e: T).(match e with [(TSort _) \Rightarrow u0 | 
(TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) (THead k u0 t0) 
(THead (Bind Abbr) u1 t1) H5) in ((let H8 \def (f_equal T T (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | 
(THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Bind Abbr) u1 t1) H5) 
in (\lambda (H9: (eq T u0 u1)).(\lambda (H10: (eq K k (Bind Abbr))).(eq_ind_r 
K (Bind Abbr) (\lambda (k0: K).(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead k0 u2 t2) (THead (Bind Abbr) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 
t3))))))) (pr0 t1 (lift (S O) O (THead k0 u2 t2))))) (let H11 \def (eq_ind T 
t0 (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O t2))))) H4 t1 H8) in (let 
H12 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in (let H13 \def 
(eq_ind T u0 (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O u2))))) H2 
u1 H9) in (let H14 \def (eq_ind T u0 (\lambda (t: T).(pr0 t u2)) H1 u1 H9) in 
(or_introl (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) u2 t2) (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 
t1 (lift (S O) O (THead (Bind Abbr) u2 t2))) (ex3_2_intro T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 t2) (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3)))))) u2 t2 (refl_equal T (THead (Bind 
Abbr) u2 t2)) H14 (or_introl (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2))) H12))))))) k H10)))) H7)) 
H6)))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: 
(pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O 
v2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H5: (eq T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (THead (Bind Abbr) u1 t1))).(let H6 \def 
(eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: 
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead k _ _) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat 
_) \Rightarrow True])])) I (THead (Bind Abbr) u1 t1) H5) in (False_ind (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S 
O) O (THead (Bind Abbr) v2 t2)))) H6)))))))))))) (\lambda (b: B).(\lambda (_: 
(not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 
v2)).(\lambda (_: (((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead 
(Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 t1 (lift (S 
O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq 
T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Bind Abbr) u1 
t1))).(let H9 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 
t1) H8) in (False_ind (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind 
Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t2))))) H9))))))))))))))))) 
(\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: 
(((eq T u0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 
t2))))))) (pr0 t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H3: (pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (w: T).(\lambda (H5: (subst0 O u2 t2 w)).(\lambda (H6: (eq 
T (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1))).(let H7 \def (f_equal 
T T (\lambda (e: T).(match e with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) (THead (Bind Abbr) u0 t0) 
(THead (Bind Abbr) u1 t1) H6) in ((let H8 \def (f_equal T T (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | 
(THead _ _ t) \Rightarrow t])) (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) 
u1 t1) H6) in (\lambda (H9: (eq T u0 u1)).(let H10 \def (eq_ind T t0 (\lambda 
(t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 
t3))))))) (pr0 t1 (lift (S O) O t2))))) H4 t1 H8) in (let H11 \def (eq_ind T 
t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in (let H12 \def (eq_ind T u0 
(\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O u2))))) H2 u1 H9) in (let 
H13 \def (eq_ind T u0 (\lambda (t: T).(pr0 t u2)) H1 u1 H9) in (or_introl 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) 
(THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S 
O) O (THead (Bind Abbr) u2 w))) (ex3_2_intro T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u3 t3)))) (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or 
(pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O 
u3 y0 t3)))))) u2 w (refl_equal T (THead (Bind Abbr) u2 w)) H13 (or_intror 
(pr0 t1 w) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 
y0 w))) (ex_intro2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O 
u2 y0 w)) t2 H11 H5)))))))))) H7))))))))))))) (\lambda (b: B).(\lambda (H1: 
(not (eq B b Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 
t2)).(\lambda (H3: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (u: 
T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead (Bind 
Abbr) u1 t1))).(let H5 \def (f_equal T B (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) 
\Rightarrow (match k with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 t1) H4) in 
((let H6 \def (f_equal T T (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t _) \Rightarrow t])) 
(THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 t1) H4) in ((let 
H7 \def (f_equal T T (\lambda (e: T).(match e with [(TSort _) \Rightarrow 
(lref_map (\lambda (x0: nat).(plus x0 (S O))) O t0) | (TLRef _) \Rightarrow 
(lref_map (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 
t1) H4) in (\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b Abbr)).(let H10 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H1 Abbr H9) in (let 
H11 \def (eq_ind_r T t1 (\lambda (t: T).((eq T t0 (THead (Bind Abbr) u1 t)) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t t3) (ex2 T (\lambda (y0: T).(pr0 t y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t (lift (S O) O t2))))) H3 
(lift (S O) O t0) H7) in (eq_ind T (lift (S O) O t0) (\lambda (t: T).(or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t t3) (ex2 T (\lambda (y0: T).(pr0 t y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t (lift (S O) O t2)))) 
(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 (lift (S O) O t0) t3) (ex2 T (\lambda (y0: 
T).(pr0 (lift (S O) O t0) y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) 
(pr0 (lift (S O) O t0) (lift (S O) O t2)) (pr0_lift t0 t2 H2 (S O) O)) t1 
H7)))))) H6)) H5)))))))))) (\lambda (t0: T).(\lambda (t2: T).(\lambda (_: 
(pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t0) (THead 
(Bind Abbr) u1 t1))).(let H4 \def (eq_ind T (THead (Flat Cast) u t0) (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
False | (THead k _ _) \Rightarrow (match k with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 t1) H3) in (False_ind 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O t2))) 
H4)))))))) y x H0))) H)))).

theorem pr0_gen_void:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Void) u1 t1) x)).(insert_eq T (THead (Bind Void) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) 
O x)))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O t0)))))) (\lambda (t: T).(\lambda 
(H1: (eq T t (THead (Bind Void) u1 t1))).(let H2 \def (f_equal T T (\lambda 
(e: T).e) t (THead (Bind Void) u1 t1) H1) in (eq_ind_r T (THead (Bind Void) 
u1 t1) (\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T t0 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead 
(Bind Void) u1 t1) (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O (THead (Bind Void) u1 t1))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T (THead (Bind Void) u1 t1) (THead (Bind Void) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 (refl_equal T (THead (Bind Void) u1 
t1)) (pr0_refl u1) (pr0_refl t1))) t H2)))) (\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: (pr0 t0 
t2)).(\lambda (H4: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (k: K).(\lambda 
(H5: (eq T (THead k u0 t0) (THead (Bind Void) u1 t1))).(let H6 \def (f_equal 
T K (\lambda (e: T).(match e with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Bind 
Void) u1 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) 
\Rightarrow t])) (THead k u0 t0) (THead (Bind Void) u1 t1) H5) in ((let H8 
\def (f_equal T T (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k u0 t0) 
(THead (Bind Void) u1 t1) H5) in (\lambda (H9: (eq T u0 u1)).(\lambda (H10: 
(eq K k (Bind Void))).(eq_ind_r K (Bind Void) (\lambda (k0: K).(or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Bind Void) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O (THead k0 u2 t2))))) 
(let H11 \def (eq_ind T t0 (\lambda (t: T).((eq T t (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2))))) H4 t1 
H8) in (let H12 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in 
(let H13 \def (eq_ind T u0 (\lambda (t: T).((eq T t (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O u2))))) H2 u1 
H9) in (let H14 \def (eq_ind T u0 (\lambda (t: T).(pr0 t u2)) H1 u1 H9) in 
(or_introl (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind 
Void) u2 t2) (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O (THead (Bind Void) u2 t2))) (ex3_2_intro T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Bind Void) u2 t2) (THead (Bind Void) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T (THead (Bind Void) u2 
t2)) H14 H12)))))) k H10)))) H7)) H6)))))))))))) (\lambda (u: T).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 
(THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T v2 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O v2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H5: (eq T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t0)) (THead (Bind Void) u1 t1))).(let H6 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: 
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead k _ _) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat 
_) \Rightarrow True])])) I (THead (Bind Void) u1 t1) H5) in (False_ind (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O (THead 
(Bind Abbr) v2 t2)))) H6)))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B 
b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 
v2)).(\lambda (_: (((eq T v1 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: T).(\lambda 
(u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead (Bind Void) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq T (THead (Flat Appl) 
v1 (THead (Bind b) u0 t0)) (THead (Bind Void) u1 t1))).(let H9 \def (eq_ind T 
(THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (\lambda (ee: T).(match ee with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Void) u1 t1) H8) in (False_ind (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2))))) 
H9))))))))))))))))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (_: (pr0 u0 
u2)).(\lambda (_: (((eq T u0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Bind Void) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda 
(t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t2 w)).(\lambda (H6: (eq T 
(THead (Bind Abbr) u0 t0) (THead (Bind Void) u1 t1))).(let H7 \def (eq_ind T 
(THead (Bind Abbr) u0 t0) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k with [(Bind b) \Rightarrow (match b with [Abbr \Rightarrow True | 
Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])])) I (THead (Bind Void) u1 t1) H6) in (False_ind (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind 
Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O (THead (Bind Abbr) 
u2 w)))) H7))))))))))))) (\lambda (b: B).(\lambda (H1: (not (eq B b 
Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 t2)).(\lambda 
(H3: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (u: T).(\lambda (H4: (eq T 
(THead (Bind b) u (lift (S O) O t0)) (THead (Bind Void) u1 t1))).(let H5 \def 
(f_equal T B (\lambda (e: T).(match e with [(TSort _) \Rightarrow b | (TLRef 
_) \Rightarrow b | (THead k _ _) \Rightarrow (match k with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead (Bind b) u (lift (S O) O 
t0)) (THead (Bind Void) u1 t1) H4) in ((let H6 \def (f_equal T T (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead 
_ t _) \Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind 
Void) u1 t1) H4) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow (lref_map (\lambda (x0: nat).(plus x0 (S O))) O t0) | 
(TLRef _) \Rightarrow (lref_map (\lambda (x0: nat).(plus x0 (S O))) O t0) | 
(THead _ _ t) \Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead 
(Bind Void) u1 t1) H4) in (\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b 
Void)).(let H10 \def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H1 
Void H9) in (let H11 \def (eq_ind_r T t1 (\lambda (t: T).((eq T t0 (THead 
(Bind Void) u1 t)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t t3)))) (pr0 t (lift (S O) O 
t2))))) H3 (lift (S O) O t0) H7) in (eq_ind T (lift (S O) O t0) (\lambda (t: 
T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))) (pr0 t (lift (S O) O t2)))) (or_intror 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 (lift (S O) O t0) t3)))) (pr0 (lift (S O) O t0) 
(lift (S O) O t2)) (pr0_lift t0 t2 H2 (S O) O)) t1 H7)))))) H6)) H5)))))))))) 
(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: 
(((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (u: T).(\lambda (H3: (eq T 
(THead (Flat Cast) u t0) (THead (Bind Void) u1 t1))).(let H4 \def (eq_ind T 
(THead (Flat Cast) u t0) (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I 
(THead (Bind Void) u1 t1) H3) in (False_ind (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2))) H4)))))))) y x H0))) H)))).

