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

include "Basic-1/pr0/defs.ma".

include "Basic-1/subst0/subst0.ma".

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
(le_O_n d)) h) d (eq_ind nat d (\lambda (n: nat).(eq nat n d)) (refl_equal 
nat d) (minus d O) (minus_n_O d))))) (lift h d (THead (Bind Abbr) u2 w)) 
(lift_head (Bind Abbr) u2 w h d)) (lift h d (THead (Bind Abbr) u1 t3)) 
(lift_head (Bind Abbr) u1 t3 h d)))))))))))))) (\lambda (b: B).(\lambda (H0: 
(not (eq B b Abst))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 
t4)).(\lambda (H2: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) 
(lift h d t4)))))).(\lambda (u: T).(\lambda (h: nat).(\lambda (d: 
nat).(eq_ind_r T (THead (Bind b) (lift h d u) (lift h (s (Bind b) d) (lift (S 
O) O t3))) (\lambda (t: T).(pr0 t (lift h d t4))) (eq_ind nat (plus (S O) d) 
(\lambda (n: nat).(pr0 (THead (Bind b) (lift h d u) (lift h n (lift (S O) O 
t3))) (lift h d t4))) (eq_ind_r T (lift (S O) O (lift h d t3)) (\lambda (t: 
T).(pr0 (THead (Bind b) (lift h d u) t) (lift h d t4))) (pr0_zeta b H0 (lift 
h d t3) (lift h d t4) (H2 h d) (lift h d u)) (lift h (plus (S O) d) (lift (S 
O) O t3)) (lift_d t3 h (S O) d O (le_O_n d))) (S d) (refl_equal nat (S d))) 
(lift h d (THead (Bind b) u (lift (S O) O t3))) (lift_head (Bind b) u (lift 
(S O) O t3) h d))))))))))) (\lambda (t3: T).(\lambda (t4: T).(\lambda (_: 
(pr0 t3 t4)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h 
d t3) (lift h d t4)))))).(\lambda (u: T).(\lambda (h: nat).(\lambda (d: 
nat).(eq_ind_r T (THead (Flat Cast) (lift h d u) (lift h (s (Flat Cast) d) 
t3)) (\lambda (t: T).(pr0 t (lift h d t4))) (pr0_tau (lift h (s (Flat Cast) 
d) t3) (lift h d t4) (H1 h d) (lift h d u)) (lift h d (THead (Flat Cast) u 
t3)) (lift_head (Flat Cast) u t3 h d))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 2845
END *)

theorem pr0_subst0_back:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst0 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u1 u2) \to (ex2 T (\lambda (t: 
T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t t2)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u2 t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (u1: T).((pr0 u1 t) \to (ex2 T 
(\lambda (t4: T).(subst0 n u1 t0 t4)) (\lambda (t4: T).(pr0 t4 t3))))))))) 
(\lambda (v: T).(\lambda (i0: nat).(\lambda (u1: T).(\lambda (H0: (pr0 u1 
v)).(ex_intro2 T (\lambda (t: T).(subst0 i0 u1 (TLRef i0) t)) (\lambda (t: 
T).(pr0 t (lift (S i0) O v))) (lift (S i0) O u1) (subst0_lref u1 i0) 
(pr0_lift u1 v H0 (S i0) O)))))) (\lambda (v: T).(\lambda (u3: T).(\lambda 
(u1: T).(\lambda (i0: nat).(\lambda (_: (subst0 i0 v u1 u3)).(\lambda (H1: 
((\forall (u4: T).((pr0 u4 v) \to (ex2 T (\lambda (t: T).(subst0 i0 u4 u1 t)) 
(\lambda (t: T).(pr0 t u3))))))).(\lambda (t: T).(\lambda (k: K).(\lambda 
(u0: T).(\lambda (H2: (pr0 u0 v)).(ex2_ind T (\lambda (t0: T).(subst0 i0 u0 
u1 t0)) (\lambda (t0: T).(pr0 t0 u3)) (ex2 T (\lambda (t0: T).(subst0 i0 u0 
(THead k u1 t) t0)) (\lambda (t0: T).(pr0 t0 (THead k u3 t)))) (\lambda (x: 
T).(\lambda (H3: (subst0 i0 u0 u1 x)).(\lambda (H4: (pr0 x u3)).(ex_intro2 T 
(\lambda (t0: T).(subst0 i0 u0 (THead k u1 t) t0)) (\lambda (t0: T).(pr0 t0 
(THead k u3 t))) (THead k x t) (subst0_fst u0 x u1 i0 H3 t k) (pr0_comp x u3 
H4 t t (pr0_refl t) k))))) (H1 u0 H2)))))))))))) (\lambda (k: K).(\lambda (v: 
T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (i0: nat).(\lambda (_: (subst0 
(s k i0) v t4 t3)).(\lambda (H1: ((\forall (u1: T).((pr0 u1 v) \to (ex2 T 
(\lambda (t: T).(subst0 (s k i0) u1 t4 t)) (\lambda (t: T).(pr0 t 
t3))))))).(\lambda (u: T).(\lambda (u1: T).(\lambda (H2: (pr0 u1 v)).(ex2_ind 
T (\lambda (t: T).(subst0 (s k i0) u1 t4 t)) (\lambda (t: T).(pr0 t t3)) (ex2 
T (\lambda (t: T).(subst0 i0 u1 (THead k u t4) t)) (\lambda (t: T).(pr0 t 
(THead k u t3)))) (\lambda (x: T).(\lambda (H3: (subst0 (s k i0) u1 t4 
x)).(\lambda (H4: (pr0 x t3)).(ex_intro2 T (\lambda (t: T).(subst0 i0 u1 
(THead k u t4) t)) (\lambda (t: T).(pr0 t (THead k u t3))) (THead k u x) 
(subst0_snd k u1 x t4 i0 H3 u) (pr0_comp u u (pr0_refl u) x t3 H4 k))))) (H1 
u1 H2)))))))))))) (\lambda (v: T).(\lambda (u1: T).(\lambda (u3: T).(\lambda 
(i0: nat).(\lambda (_: (subst0 i0 v u1 u3)).(\lambda (H1: ((\forall (u4: 
T).((pr0 u4 v) \to (ex2 T (\lambda (t: T).(subst0 i0 u4 u1 t)) (\lambda (t: 
T).(pr0 t u3))))))).(\lambda (k: K).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (subst0 (s k i0) v t3 t4)).(\lambda (H3: ((\forall (u4: 
T).((pr0 u4 v) \to (ex2 T (\lambda (t: T).(subst0 (s k i0) u4 t3 t)) (\lambda 
(t: T).(pr0 t t4))))))).(\lambda (u0: T).(\lambda (H4: (pr0 u0 v)).(ex2_ind T 
(\lambda (t: T).(subst0 (s k i0) u0 t3 t)) (\lambda (t: T).(pr0 t t4)) (ex2 T 
(\lambda (t: T).(subst0 i0 u0 (THead k u1 t3) t)) (\lambda (t: T).(pr0 t 
(THead k u3 t4)))) (\lambda (x: T).(\lambda (H5: (subst0 (s k i0) u0 t3 
x)).(\lambda (H6: (pr0 x t4)).(ex2_ind T (\lambda (t: T).(subst0 i0 u0 u1 t)) 
(\lambda (t: T).(pr0 t u3)) (ex2 T (\lambda (t: T).(subst0 i0 u0 (THead k u1 
t3) t)) (\lambda (t: T).(pr0 t (THead k u3 t4)))) (\lambda (x0: T).(\lambda 
(H7: (subst0 i0 u0 u1 x0)).(\lambda (H8: (pr0 x0 u3)).(ex_intro2 T (\lambda 
(t: T).(subst0 i0 u0 (THead k u1 t3) t)) (\lambda (t: T).(pr0 t (THead k u3 
t4))) (THead k x0 x) (subst0_both u0 u1 x0 i0 H7 k t3 x H5) (pr0_comp x0 u3 
H8 x t4 H6 k))))) (H1 u0 H4))))) (H3 u0 H4))))))))))))))) i u2 t1 t2 H))))).
(* COMMENTS
Initial nodes: 979
END *)

theorem pr0_subst0_fwd:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst0 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u2 u1) \to (ex2 T (\lambda (t: 
T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t2 t)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u2 t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (u1: T).((pr0 t u1) \to (ex2 T 
(\lambda (t4: T).(subst0 n u1 t0 t4)) (\lambda (t4: T).(pr0 t3 t4))))))))) 
(\lambda (v: T).(\lambda (i0: nat).(\lambda (u1: T).(\lambda (H0: (pr0 v 
u1)).(ex_intro2 T (\lambda (t: T).(subst0 i0 u1 (TLRef i0) t)) (\lambda (t: 
T).(pr0 (lift (S i0) O v) t)) (lift (S i0) O u1) (subst0_lref u1 i0) 
(pr0_lift v u1 H0 (S i0) O)))))) (\lambda (v: T).(\lambda (u3: T).(\lambda 
(u1: T).(\lambda (i0: nat).(\lambda (_: (subst0 i0 v u1 u3)).(\lambda (H1: 
((\forall (u4: T).((pr0 v u4) \to (ex2 T (\lambda (t: T).(subst0 i0 u4 u1 t)) 
(\lambda (t: T).(pr0 u3 t))))))).(\lambda (t: T).(\lambda (k: K).(\lambda 
(u0: T).(\lambda (H2: (pr0 v u0)).(ex2_ind T (\lambda (t0: T).(subst0 i0 u0 
u1 t0)) (\lambda (t0: T).(pr0 u3 t0)) (ex2 T (\lambda (t0: T).(subst0 i0 u0 
(THead k u1 t) t0)) (\lambda (t0: T).(pr0 (THead k u3 t) t0))) (\lambda (x: 
T).(\lambda (H3: (subst0 i0 u0 u1 x)).(\lambda (H4: (pr0 u3 x)).(ex_intro2 T 
(\lambda (t0: T).(subst0 i0 u0 (THead k u1 t) t0)) (\lambda (t0: T).(pr0 
(THead k u3 t) t0)) (THead k x t) (subst0_fst u0 x u1 i0 H3 t k) (pr0_comp u3 
x H4 t t (pr0_refl t) k))))) (H1 u0 H2)))))))))))) (\lambda (k: K).(\lambda 
(v: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (i0: nat).(\lambda (_: 
(subst0 (s k i0) v t4 t3)).(\lambda (H1: ((\forall (u1: T).((pr0 v u1) \to 
(ex2 T (\lambda (t: T).(subst0 (s k i0) u1 t4 t)) (\lambda (t: T).(pr0 t3 
t))))))).(\lambda (u: T).(\lambda (u1: T).(\lambda (H2: (pr0 v u1)).(ex2_ind 
T (\lambda (t: T).(subst0 (s k i0) u1 t4 t)) (\lambda (t: T).(pr0 t3 t)) (ex2 
T (\lambda (t: T).(subst0 i0 u1 (THead k u t4) t)) (\lambda (t: T).(pr0 
(THead k u t3) t))) (\lambda (x: T).(\lambda (H3: (subst0 (s k i0) u1 t4 
x)).(\lambda (H4: (pr0 t3 x)).(ex_intro2 T (\lambda (t: T).(subst0 i0 u1 
(THead k u t4) t)) (\lambda (t: T).(pr0 (THead k u t3) t)) (THead k u x) 
(subst0_snd k u1 x t4 i0 H3 u) (pr0_comp u u (pr0_refl u) t3 x H4 k))))) (H1 
u1 H2)))))))))))) (\lambda (v: T).(\lambda (u1: T).(\lambda (u3: T).(\lambda 
(i0: nat).(\lambda (_: (subst0 i0 v u1 u3)).(\lambda (H1: ((\forall (u4: 
T).((pr0 v u4) \to (ex2 T (\lambda (t: T).(subst0 i0 u4 u1 t)) (\lambda (t: 
T).(pr0 u3 t))))))).(\lambda (k: K).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (subst0 (s k i0) v t3 t4)).(\lambda (H3: ((\forall (u4: 
T).((pr0 v u4) \to (ex2 T (\lambda (t: T).(subst0 (s k i0) u4 t3 t)) (\lambda 
(t: T).(pr0 t4 t))))))).(\lambda (u0: T).(\lambda (H4: (pr0 v u0)).(ex2_ind T 
(\lambda (t: T).(subst0 (s k i0) u0 t3 t)) (\lambda (t: T).(pr0 t4 t)) (ex2 T 
(\lambda (t: T).(subst0 i0 u0 (THead k u1 t3) t)) (\lambda (t: T).(pr0 (THead 
k u3 t4) t))) (\lambda (x: T).(\lambda (H5: (subst0 (s k i0) u0 t3 
x)).(\lambda (H6: (pr0 t4 x)).(ex2_ind T (\lambda (t: T).(subst0 i0 u0 u1 t)) 
(\lambda (t: T).(pr0 u3 t)) (ex2 T (\lambda (t: T).(subst0 i0 u0 (THead k u1 
t3) t)) (\lambda (t: T).(pr0 (THead k u3 t4) t))) (\lambda (x0: T).(\lambda 
(H7: (subst0 i0 u0 u1 x0)).(\lambda (H8: (pr0 u3 x0)).(ex_intro2 T (\lambda 
(t: T).(subst0 i0 u0 (THead k u1 t3) t)) (\lambda (t: T).(pr0 (THead k u3 t4) 
t)) (THead k x0 x) (subst0_both u0 u1 x0 i0 H7 k t3 x H5) (pr0_comp u3 x0 H8 
t4 x H6 k))))) (H1 u0 H4))))) (H3 u0 H4))))))))))))))) i u2 t1 t2 H))))).
(* COMMENTS
Initial nodes: 979
END *)

theorem pr0_subst0:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (v1: T).(\forall 
(w1: T).(\forall (i: nat).((subst0 i v1 t1 w1) \to (\forall (v2: T).((pr0 v1 
v2) \to (or (pr0 w1 t2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 t2 w2))))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(pr0_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (v1: T).(\forall (w1: T).(\forall (i: 
nat).((subst0 i v1 t w1) \to (\forall (v2: T).((pr0 v1 v2) \to (or (pr0 w1 
t0) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t0 
w2)))))))))))) (\lambda (t: T).(\lambda (v1: T).(\lambda (w1: T).(\lambda (i: 
nat).(\lambda (H0: (subst0 i v1 t w1)).(\lambda (v2: T).(\lambda (H1: (pr0 v1 
v2)).(or_intror (pr0 w1 t) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 t w2))) (ex2_sym T (subst0 i v2 t) (pr0 w1) (pr0_subst0_fwd 
v1 t w1 i H0 v2 H1)))))))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: 
(pr0 u1 u2)).(\lambda (H1: ((\forall (v1: T).(\forall (w1: T).(\forall (i: 
nat).((subst0 i v1 u1 w1) \to (\forall (v2: T).((pr0 v1 v2) \to (or (pr0 w1 
u2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 u2 
w2)))))))))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 
t4)).(\lambda (H3: ((\forall (v1: T).(\forall (w1: T).(\forall (i: 
nat).((subst0 i v1 t3 w1) \to (\forall (v2: T).((pr0 v1 v2) \to (or (pr0 w1 
t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2)))))))))))).(\lambda (k: K).(\lambda (v1: T).(\lambda (w1: T).(\lambda (i: 
nat).(\lambda (H4: (subst0 i v1 (THead k u1 t3) w1)).(\lambda (v2: 
T).(\lambda (H5: (pr0 v1 v2)).(or3_ind (ex2 T (\lambda (u3: T).(eq T w1 
(THead k u3 t3))) (\lambda (u3: T).(subst0 i v1 u1 u3))) (ex2 T (\lambda (t5: 
T).(eq T w1 (THead k u1 t5))) (\lambda (t5: T).(subst0 (s k i) v1 t3 t5))) 
(ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead k u3 t5)))) 
(\lambda (u3: T).(\lambda (_: T).(subst0 i v1 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i) v1 t3 t5)))) (or (pr0 w1 (THead k u2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 (THead k 
u2 t4) w2)))) (\lambda (H6: (ex2 T (\lambda (u3: T).(eq T w1 (THead k u3 
t3))) (\lambda (u3: T).(subst0 i v1 u1 u3)))).(ex2_ind T (\lambda (u3: T).(eq 
T w1 (THead k u3 t3))) (\lambda (u3: T).(subst0 i v1 u1 u3)) (or (pr0 w1 
(THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x: T).(\lambda (H7: (eq T w1 
(THead k x t3))).(\lambda (H8: (subst0 i v1 u1 x)).(eq_ind_r T (THead k x t3) 
(\lambda (t: T).(or (pr0 t (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 t 
w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))))) (or_ind (pr0 x u2) 
(ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v2 u2 w2))) 
(or (pr0 (THead k x t3) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead 
k x t3) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda 
(H9: (pr0 x u2)).(or_introl (pr0 (THead k x t3) (THead k u2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead k x t3) w2)) (\lambda (w2: T).(subst0 i v2 
(THead k u2 t4) w2))) (pr0_comp x u2 H9 t3 t4 H2 k))) (\lambda (H9: (ex2 T 
(\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v2 u2 w2)))).(ex2_ind 
T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v2 u2 w2)) (or (pr0 
(THead k x t3) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x t3) 
w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x0: 
T).(\lambda (H10: (pr0 x x0)).(\lambda (H11: (subst0 i v2 u2 x0)).(or_intror 
(pr0 (THead k x t3) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x 
t3) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead k x t3) w2)) (\lambda (w2: T).(subst0 i v2 
(THead k u2 t4) w2)) (THead k x0 t4) (pr0_comp x x0 H10 t3 t4 H2 k) 
(subst0_fst v2 x0 u2 i H11 t4 k)))))) H9)) (H1 v1 x i H8 v2 H5)) w1 H7)))) 
H6)) (\lambda (H6: (ex2 T (\lambda (t5: T).(eq T w1 (THead k u1 t5))) 
(\lambda (t5: T).(subst0 (s k i) v1 t3 t5)))).(ex2_ind T (\lambda (t5: T).(eq 
T w1 (THead k u1 t5))) (\lambda (t5: T).(subst0 (s k i) v1 t3 t5)) (or (pr0 
w1 (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x: T).(\lambda (H7: (eq T w1 
(THead k u1 x))).(\lambda (H8: (subst0 (s k i) v1 t3 x)).(eq_ind_r T (THead k 
u1 x) (\lambda (t: T).(or (pr0 t (THead k u2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))))) (or_ind 
(pr0 x t4) (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s k 
i) v2 t4 w2))) (or (pr0 (THead k u1 x) (THead k u2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead k u1 x) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) 
w2)))) (\lambda (H9: (pr0 x t4)).(or_introl (pr0 (THead k u1 x) (THead k u2 
t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k u1 x) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead k u2 t4) w2))) (pr0_comp u1 u2 H0 x t4 H9 k))) 
(\lambda (H9: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s 
k i) v2 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: 
T).(subst0 (s k i) v2 t4 w2)) (or (pr0 (THead k u1 x) (THead k u2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead k u1 x) w2)) (\lambda (w2: T).(subst0 i v2 
(THead k u2 t4) w2)))) (\lambda (x0: T).(\lambda (H10: (pr0 x x0)).(\lambda 
(H11: (subst0 (s k i) v2 t4 x0)).(or_intror (pr0 (THead k u1 x) (THead k u2 
t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k u1 x) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead k u2 t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 
(THead k u1 x) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)) (THead 
k u2 x0) (pr0_comp u1 u2 H0 x x0 H10 k) (subst0_snd k v2 x0 t4 i H11 u2)))))) 
H9)) (H3 v1 x (s k i) H8 v2 H5)) w1 H7)))) H6)) (\lambda (H6: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead k u3 t5)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i v1 u1 u3))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s k i) v1 t3 t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda 
(t5: T).(eq T w1 (THead k u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 
i v1 u1 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i) v1 t3 t5))) 
(or (pr0 w1 (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda 
(w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T w1 (THead k x0 x1))).(\lambda (H8: (subst0 i v1 u1 
x0)).(\lambda (H9: (subst0 (s k i) v1 t3 x1)).(eq_ind_r T (THead k x0 x1) 
(\lambda (t: T).(or (pr0 t (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 t 
w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))))) (or_ind (pr0 x1 
t4) (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s k i) v2 
t4 w2))) (or (pr0 (THead k x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) 
w2)))) (\lambda (H10: (pr0 x1 t4)).(or_ind (pr0 x0 u2) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 u2 w2))) (or (pr0 (THead k x0 
x1) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (H11: (pr0 x0 
u2)).(or_introl (pr0 (THead k x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) 
w2))) (pr0_comp x0 u2 H11 x1 t4 H10 k))) (\lambda (H11: (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 u2 w2)))).(ex2_ind T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 u2 w2)) (or (pr0 (THead k 
x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x: T).(\lambda 
(H12: (pr0 x0 x)).(\lambda (H13: (subst0 i v2 u2 x)).(or_intror (pr0 (THead k 
x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))) (ex_intro2 T (\lambda 
(w2: T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 
t4) w2)) (THead k x t4) (pr0_comp x0 x H12 x1 t4 H10 k) (subst0_fst v2 x u2 i 
H13 t4 k)))))) H11)) (H1 v1 x0 i H8 v2 H5))) (\lambda (H10: (ex2 T (\lambda 
(w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s k i) v2 t4 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s k i) v2 t4 w2)) (or 
(pr0 (THead k x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k 
x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x: 
T).(\lambda (H11: (pr0 x1 x)).(\lambda (H12: (subst0 (s k i) v2 t4 
x)).(or_ind (pr0 x0 u2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v2 u2 w2))) (or (pr0 (THead k x0 x1) (THead k u2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 
(THead k u2 t4) w2)))) (\lambda (H13: (pr0 x0 u2)).(or_intror (pr0 (THead k 
x0 x1) (THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2))) (ex_intro2 T (\lambda 
(w2: T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 
t4) w2)) (THead k u2 x) (pr0_comp x0 u2 H13 x1 x H11 k) (subst0_snd k v2 x t4 
i H12 u2)))) (\lambda (H13: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v2 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) 
(\lambda (w2: T).(subst0 i v2 u2 w2)) (or (pr0 (THead k x0 x1) (THead k u2 
t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead k u2 t4) w2)))) (\lambda (x2: T).(\lambda (H14: (pr0 
x0 x2)).(\lambda (H15: (subst0 i v2 u2 x2)).(or_intror (pr0 (THead k x0 x1) 
(THead k u2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead k x0 x1) w2)) (\lambda 
(w2: T).(subst0 i v2 (THead k u2 t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 
(THead k x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead k u2 t4) w2)) 
(THead k x2 x) (pr0_comp x0 x2 H14 x1 x H11 k) (subst0_both v2 u2 x2 i H15 k 
t4 x H12)))))) H13)) (H1 v1 x0 i H8 v2 H5))))) H10)) (H3 v1 x1 (s k i) H9 v2 
H5)) w1 H7)))))) H6)) (subst0_gen_head k v1 u1 t3 w1 i H4))))))))))))))))) 
(\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H0: (pr0 v1 
v2)).(\lambda (H1: ((\forall (v3: T).(\forall (w1: T).(\forall (i: 
nat).((subst0 i v3 v1 w1) \to (\forall (v4: T).((pr0 v3 v4) \to (or (pr0 w1 
v2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v4 v2 
w2)))))))))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 
t4)).(\lambda (H3: ((\forall (v3: T).(\forall (w1: T).(\forall (i: 
nat).((subst0 i v3 t3 w1) \to (\forall (v4: T).((pr0 v3 v4) \to (or (pr0 w1 
t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v4 t4 
w2)))))))))))).(\lambda (v0: T).(\lambda (w1: T).(\lambda (i: nat).(\lambda 
(H4: (subst0 i v0 (THead (Flat Appl) v1 (THead (Bind Abst) u t3)) 
w1)).(\lambda (v3: T).(\lambda (H5: (pr0 v0 v3)).(or3_ind (ex2 T (\lambda 
(u2: T).(eq T w1 (THead (Flat Appl) u2 (THead (Bind Abst) u t3)))) (\lambda 
(u2: T).(subst0 i v0 v1 u2))) (ex2 T (\lambda (t5: T).(eq T w1 (THead (Flat 
Appl) v1 t5))) (\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 (THead (Bind 
Abst) u t3) t5))) (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T w1 
(THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 v1 
u2))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 (THead 
(Bind Abst) u t3) t5)))) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2)))) (\lambda (H6: (ex2 T (\lambda (u2: T).(eq T w1 (THead 
(Flat Appl) u2 (THead (Bind Abst) u t3)))) (\lambda (u2: T).(subst0 i v0 v1 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T w1 (THead (Flat Appl) u2 (THead 
(Bind Abst) u t3)))) (\lambda (u2: T).(subst0 i v0 v1 u2)) (or (pr0 w1 (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (x: T).(\lambda 
(H7: (eq T w1 (THead (Flat Appl) x (THead (Bind Abst) u t3)))).(\lambda (H8: 
(subst0 i v0 v1 x)).(eq_ind_r T (THead (Flat Appl) x (THead (Bind Abst) u 
t3)) (\lambda (t: T).(or (pr0 t (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda 
(w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2))))) (or_ind (pr0 x v2) (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: 
T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat Appl) x (THead (Bind Abst) u 
t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x (THead (Bind Abst) u t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2)))) (\lambda (H9: (pr0 x v2)).(or_introl (pr0 (THead 
(Flat Appl) x (THead (Bind Abst) u t3)) (THead (Bind Abbr) v2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x (THead (Bind Abst) u t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (pr0_beta u x 
v2 H9 t3 t4 H2))) (\lambda (H9: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda 
(w2: T).(subst0 i v3 v2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) 
(\lambda (w2: T).(subst0 i v3 v2 w2)) (or (pr0 (THead (Flat Appl) x (THead 
(Bind Abst) u t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x (THead (Bind Abst) u t3)) w2)) (\lambda (w2: T).(subst0 
i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (x0: T).(\lambda (H10: (pr0 x 
x0)).(\lambda (H11: (subst0 i v3 v2 x0)).(or_intror (pr0 (THead (Flat Appl) x 
(THead (Bind Abst) u t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x (THead (Bind Abst) u t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x (THead (Bind Abst) u t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)) (THead (Bind Abbr) x0 t4) 
(pr0_beta u x x0 H10 t3 t4 H2) (subst0_fst v3 x0 v2 i H11 t4 (Bind 
Abbr))))))) H9)) (H1 v0 x i H8 v3 H5)) w1 H7)))) H6)) (\lambda (H6: (ex2 T 
(\lambda (t5: T).(eq T w1 (THead (Flat Appl) v1 t5))) (\lambda (t5: 
T).(subst0 (s (Flat Appl) i) v0 (THead (Bind Abst) u t3) t5)))).(ex2_ind T 
(\lambda (t5: T).(eq T w1 (THead (Flat Appl) v1 t5))) (\lambda (t5: 
T).(subst0 (s (Flat Appl) i) v0 (THead (Bind Abst) u t3) t5)) (or (pr0 w1 
(THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (x: T).(\lambda 
(H7: (eq T w1 (THead (Flat Appl) v1 x))).(\lambda (H8: (subst0 (s (Flat Appl) 
i) v0 (THead (Bind Abst) u t3) x)).(or3_ind (ex2 T (\lambda (u2: T).(eq T x 
(THead (Bind Abst) u2 t3))) (\lambda (u2: T).(subst0 (s (Flat Appl) i) v0 u 
u2))) (ex2 T (\lambda (t5: T).(eq T x (THead (Bind Abst) u t5))) (\lambda 
(t5: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T x (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u u2))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 
t3 t5)))) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 
w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) 
(\lambda (H9: (ex2 T (\lambda (u2: T).(eq T x (THead (Bind Abst) u2 t3))) 
(\lambda (u2: T).(subst0 (s (Flat Appl) i) v0 u u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T x (THead (Bind Abst) u2 t3))) (\lambda (u2: T).(subst0 (s (Flat 
Appl) i) v0 u u2)) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2)))) (\lambda (x0: T).(\lambda (H10: (eq T x (THead (Bind Abst) x0 
t3))).(\lambda (_: (subst0 (s (Flat Appl) i) v0 u x0)).(let H12 \def (eq_ind 
T x (\lambda (t: T).(eq T w1 (THead (Flat Appl) v1 t))) H7 (THead (Bind Abst) 
x0 t3) H10) in (eq_ind_r T (THead (Flat Appl) v1 (THead (Bind Abst) x0 t3)) 
(\lambda (t: T).(or (pr0 t (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2))))) (or_introl (pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 t3)) 
(THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) x0 t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2))) (pr0_beta x0 v1 v2 H0 t3 t4 H2)) w1 H12))))) H9)) (\lambda 
(H9: (ex2 T (\lambda (t5: T).(eq T x (THead (Bind Abst) u t5))) (\lambda (t5: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5)))).(ex2_ind T (\lambda 
(t5: T).(eq T x (THead (Bind Abst) u t5))) (\lambda (t5: T).(subst0 (s (Bind 
Abst) (s (Flat Appl) i)) v0 t3 t5)) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2)))) (\lambda (x0: T).(\lambda (H10: (eq T x (THead 
(Bind Abst) u x0))).(\lambda (H11: (subst0 (s (Bind Abst) (s (Flat Appl) i)) 
v0 t3 x0)).(let H12 \def (eq_ind T x (\lambda (t: T).(eq T w1 (THead (Flat 
Appl) v1 t))) H7 (THead (Bind Abst) u x0) H10) in (eq_ind_r T (THead (Flat 
Appl) v1 (THead (Bind Abst) u x0)) (\lambda (t: T).(or (pr0 t (THead (Bind 
Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind Abbr) v2 t4) w2))))) (or_ind (pr0 x0 t4) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 
t4 w2))) (or (pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u x0)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead 
(Bind Abst) u x0)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)))) (\lambda (H13: (pr0 x0 t4)).(or_introl (pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) u x0)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u x0)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (pr0_beta u v1 v2 H0 x0 t4 
H13))) (\lambda (H13: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2)))).(ex2_ind T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) 
i)) v3 t4 w2)) (or (pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u x0)) 
(THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) u x0)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2)))) (\lambda (x1: T).(\lambda (H14: (pr0 x0 x1)).(\lambda 
(H15: (subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 t4 x1)).(or_intror (pr0 
(THead (Flat Appl) v1 (THead (Bind Abst) u x0)) (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u x0)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (ex_intro2 
T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u x0)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)) (THead (Bind 
Abbr) v2 x1) (pr0_beta u v1 v2 H0 x0 x1 H14) (subst0_snd (Bind Abbr) v3 x1 t4 
i H15 v2)))))) H13)) (H3 v0 x0 (s (Bind Abst) (s (Flat Appl) i)) H11 v3 H5)) 
w1 H12))))) H9)) (\lambda (H9: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T x (THead (Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 (s (Flat Appl) i) v0 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T x (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u u2))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 
t3 t5))) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 
w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H10: (eq T x (THead (Bind Abst) 
x0 x1))).(\lambda (_: (subst0 (s (Flat Appl) i) v0 u x0)).(\lambda (H12: 
(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 x1)).(let H13 \def (eq_ind T 
x (\lambda (t: T).(eq T w1 (THead (Flat Appl) v1 t))) H7 (THead (Bind Abst) 
x0 x1) H10) in (eq_ind_r T (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) 
(\lambda (t: T).(or (pr0 t (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2))))) (or_ind (pr0 x1 t4) (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda 
(w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2))) (or (pr0 (THead 
(Flat Appl) v1 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) v2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H14: 
(pr0 x1 t4)).(or_introl (pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) 
(THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2))) (pr0_beta x0 v1 v2 H0 x1 t4 H14))) (\lambda (H14: (ex2 T 
(\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s 
(Flat Appl) i)) v3 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x1 w2)) 
(\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2)) (or 
(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) (THead (Bind Abbr) v2 
t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 
x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) 
(\lambda (x2: T).(\lambda (H15: (pr0 x1 x2)).(\lambda (H16: (subst0 (s (Bind 
Abst) (s (Flat Appl) i)) v3 t4 x2)).(or_intror (pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) x0 x1)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) x0 x1)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)) (THead (Bind Abbr) v2 x2) 
(pr0_beta x0 v1 v2 H0 x1 x2 H15) (subst0_snd (Bind Abbr) v3 x2 t4 i H16 
v2)))))) H14)) (H3 v0 x1 (s (Bind Abst) (s (Flat Appl) i)) H12 v3 H5)) w1 
H13))))))) H9)) (subst0_gen_head (Bind Abst) v0 u t3 x (s (Flat Appl) i) 
H8))))) H6)) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T 
w1 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 
v1 u2))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 (THead 
(Bind Abst) u t3) t5))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T w1 (THead (Flat Appl) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i v0 v1 u2))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Flat 
Appl) i) v0 (THead (Bind Abst) u t3) t5))) (or (pr0 w1 (THead (Bind Abbr) v2 
t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind Abbr) v2 t4) w2)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H7: (eq T w1 (THead (Flat Appl) x0 x1))).(\lambda (H8: (subst0 i v0 v1 
x0)).(\lambda (H9: (subst0 (s (Flat Appl) i) v0 (THead (Bind Abst) u t3) 
x1)).(or3_ind (ex2 T (\lambda (u2: T).(eq T x1 (THead (Bind Abst) u2 t3))) 
(\lambda (u2: T).(subst0 (s (Flat Appl) i) v0 u u2))) (ex2 T (\lambda (t5: 
T).(eq T x1 (THead (Bind Abst) u t5))) (\lambda (t5: T).(subst0 (s (Bind 
Abst) (s (Flat Appl) i)) v0 t3 t5))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t5: T).(eq T x1 (THead (Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 (s (Flat Appl) i) v0 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5)))) (or (pr0 w1 (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H10: (ex2 T 
(\lambda (u2: T).(eq T x1 (THead (Bind Abst) u2 t3))) (\lambda (u2: 
T).(subst0 (s (Flat Appl) i) v0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T x1 
(THead (Bind Abst) u2 t3))) (\lambda (u2: T).(subst0 (s (Flat Appl) i) v0 u 
u2)) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 w1 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda 
(x: T).(\lambda (H11: (eq T x1 (THead (Bind Abst) x t3))).(\lambda (_: 
(subst0 (s (Flat Appl) i) v0 u x)).(let H13 \def (eq_ind T x1 (\lambda (t: 
T).(eq T w1 (THead (Flat Appl) x0 t))) H7 (THead (Bind Abst) x t3) H11) in 
(eq_ind_r T (THead (Flat Appl) x0 (THead (Bind Abst) x t3)) (\lambda (t: 
T).(or (pr0 t (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 t w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))))) (or_ind (pr0 
x0 v2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x t3)) (THead (Bind 
Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
Abst) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2)))) (\lambda (H14: (pr0 x0 v2)).(or_introl (pr0 (THead (Flat Appl) x0 
(THead (Bind Abst) x t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (pr0_beta x x0 v2 H14 t3 t4 
H2))) (\lambda (H14: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v3 v2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v3 v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind 
Abst) x t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead 
(Flat Appl) x0 (THead (Bind Abst) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind Abbr) v2 t4) w2)))) (\lambda (x2: T).(\lambda (H15: (pr0 x0 
x2)).(\lambda (H16: (subst0 i v3 v2 x2)).(or_intror (pr0 (THead (Flat Appl) 
x0 (THead (Bind Abst) x t3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)) (THead (Bind Abbr) x2 t4) 
(pr0_beta x x0 x2 H15 t3 t4 H2) (subst0_fst v3 x2 v2 i H16 t4 (Bind 
Abbr))))))) H14)) (H1 v0 x0 i H8 v3 H5)) w1 H13))))) H10)) (\lambda (H10: 
(ex2 T (\lambda (t5: T).(eq T x1 (THead (Bind Abst) u t5))) (\lambda (t5: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5)))).(ex2_ind T (\lambda 
(t5: T).(eq T x1 (THead (Bind Abst) u t5))) (\lambda (t5: T).(subst0 (s (Bind 
Abst) (s (Flat Appl) i)) v0 t3 t5)) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2)))) (\lambda (x: T).(\lambda (H11: (eq T x1 (THead 
(Bind Abst) u x))).(\lambda (H12: (subst0 (s (Bind Abst) (s (Flat Appl) i)) 
v0 t3 x)).(let H13 \def (eq_ind T x1 (\lambda (t: T).(eq T w1 (THead (Flat 
Appl) x0 t))) H7 (THead (Bind Abst) u x) H11) in (eq_ind_r T (THead (Flat 
Appl) x0 (THead (Bind Abst) u x)) (\lambda (t: T).(or (pr0 t (THead (Bind 
Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind Abbr) v2 t4) w2))))) (or_ind (pr0 x t4) (ex2 T (\lambda (w2: 
T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 
t4 w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead (Bind 
Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2)))) (\lambda (H14: (pr0 x t4)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat 
Appl) x0 (THead (Bind Abst) u x)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda 
(w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) w2)) (\lambda 
(w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H15: (pr0 x0 
v2)).(or_introl (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2))) (pr0_beta u x0 v2 H15 x t4 H14))) (\lambda (H15: (ex2 T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)) (or (pr0 
(THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda 
(x2: T).(\lambda (H16: (pr0 x0 x2)).(\lambda (H17: (subst0 i v3 v2 
x2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)) (THead (Bind Abbr) x2 t4) (pr0_beta u x0 x2 H16 x t4 H14) 
(subst0_fst v3 x2 v2 i H17 t4 (Bind Abbr))))))) H15)) (H1 v0 x0 i H8 v3 H5))) 
(\lambda (H14: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 
(s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2)))).(ex2_ind T (\lambda (w2: 
T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 
t4 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead (Bind 
Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2)))) (\lambda (x2: T).(\lambda (H15: (pr0 x x2)).(\lambda (H16: (subst0 (s 
(Bind Abst) (s (Flat Appl) i)) v3 t4 x2)).(or_ind (pr0 x0 v2) (ex2 T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead 
(Flat Appl) x0 (THead (Bind Abst) u x)) (THead (Bind Abbr) v2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H17: 
(pr0 x0 v2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) 
(THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 
(THead (Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 
(THead (Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind 
Abbr) v2 t4) w2)) (THead (Bind Abbr) v2 x2) (pr0_beta u x0 v2 H17 x x2 H15) 
(subst0_snd (Bind Abbr) v3 x2 t4 i H16 v2)))) (\lambda (H17: (ex2 T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)) (or (pr0 
(THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda 
(x3: T).(\lambda (H18: (pr0 x0 x3)).(\lambda (H19: (subst0 i v3 v2 
x3)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) u x)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) u x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)) (THead (Bind Abbr) x3 x2) (pr0_beta u x0 x3 H18 x x2 H15) 
(subst0_both v3 v2 x3 i H19 (Bind Abbr) t4 x2 H16)))))) H17)) (H1 v0 x0 i H8 
v3 H5))))) H14)) (H3 v0 x (s (Bind Abst) (s (Flat Appl) i)) H12 v3 H5)) w1 
H13))))) H10)) (\lambda (H10: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T x1 (THead (Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 (s (Flat Appl) i) v0 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 t5))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T x1 (THead (Bind Abst) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u u2))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 
t3 t5))) (or (pr0 w1 (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 
w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (H11: (eq T x1 (THead (Bind Abst) 
x2 x3))).(\lambda (_: (subst0 (s (Flat Appl) i) v0 u x2)).(\lambda (H13: 
(subst0 (s (Bind Abst) (s (Flat Appl) i)) v0 t3 x3)).(let H14 \def (eq_ind T 
x1 (\lambda (t: T).(eq T w1 (THead (Flat Appl) x0 t))) H7 (THead (Bind Abst) 
x2 x3) H11) in (eq_ind_r T (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) 
(\lambda (t: T).(or (pr0 t (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) 
w2))))) (or_ind (pr0 x3 t4) (ex2 T (\lambda (w2: T).(pr0 x3 w2)) (\lambda 
(w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2))) (or (pr0 (THead 
(Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead (Bind Abbr) v2 t4)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H15: 
(pr0 x3 t4)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) 
(\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda (H16: (pr0 x0 
v2)).(or_introl (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2))) (pr0_beta x2 x0 v2 H16 x3 t4 H15))) (\lambda (H16: (ex2 T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2)) (or (pr0 
(THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda 
(x: T).(\lambda (H17: (pr0 x0 x)).(\lambda (H18: (subst0 i v3 v2 
x)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)) (THead (Bind Abbr) x t4) (pr0_beta x2 x0 x H17 x3 t4 H15) 
(subst0_fst v3 x v2 i H18 t4 (Bind Abbr))))))) H16)) (H1 v0 x0 i H8 v3 H5))) 
(\lambda (H15: (ex2 T (\lambda (w2: T).(pr0 x3 w2)) (\lambda (w2: T).(subst0 
(s (Bind Abst) (s (Flat Appl) i)) v3 t4 w2)))).(ex2_ind T (\lambda (w2: 
T).(pr0 x3 w2)) (\lambda (w2: T).(subst0 (s (Bind Abst) (s (Flat Appl) i)) v3 
t4 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)))) (\lambda (x: T).(\lambda (H16: (pr0 x3 x)).(\lambda (H17: (subst0 
(s (Bind Abst) (s (Flat Appl) i)) v3 t4 x)).(or_ind (pr0 x0 v2) (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 
(THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead (Bind Abbr) v2 t4)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 t4) w2)))) (\lambda 
(H18: (pr0 x0 v2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) 
x2 x3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2)) (THead (Bind Abbr) v2 x) (pr0_beta x2 x0 v2 H18 x3 x 
H16) (subst0_snd (Bind Abbr) v3 x t4 i H17 v2)))) (\lambda (H18: (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) x2 x3)) (THead 
(Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind Abbr) v2 
t4) w2)))) (\lambda (x4: T).(\lambda (H19: (pr0 x0 x4)).(\lambda (H20: 
(subst0 i v3 v2 x4)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind Abst) 
x2 x3)) (THead (Bind Abbr) v2 t4)) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind Abst) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind Abbr) v2 t4) w2)) (THead (Bind Abbr) x4 x) (pr0_beta x2 x0 x4 H19 x3 x 
H16) (subst0_both v3 v2 x4 i H20 (Bind Abbr) t4 x H17)))))) H18)) (H1 v0 x0 i 
H8 v3 H5))))) H15)) (H3 v0 x3 (s (Bind Abst) (s (Flat Appl) i)) H13 v3 H5)) 
w1 H14))))))) H10)) (subst0_gen_head (Bind Abst) v0 u t3 x1 (s (Flat Appl) i) 
H9))))))) H6)) (subst0_gen_head (Flat Appl) v0 v1 (THead (Bind Abst) u t3) w1 
i H4))))))))))))))))) (\lambda (b: B).(\lambda (H0: (not (eq B b 
Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H1: (pr0 v1 v2)).(\lambda 
(H2: ((\forall (v3: T).(\forall (w1: T).(\forall (i: nat).((subst0 i v3 v1 
w1) \to (\forall (v4: T).((pr0 v3 v4) \to (or (pr0 w1 v2) (ex2 T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v4 v2 w2)))))))))))).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (H3: (pr0 u1 u2)).(\lambda (H4: ((\forall 
(v3: T).(\forall (w1: T).(\forall (i: nat).((subst0 i v3 u1 w1) \to (\forall 
(v4: T).((pr0 v3 v4) \to (or (pr0 w1 u2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) 
(\lambda (w2: T).(subst0 i v4 u2 w2)))))))))))).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H5: (pr0 t3 t4)).(\lambda (H6: ((\forall (v3: T).(\forall 
(w1: T).(\forall (i: nat).((subst0 i v3 t3 w1) \to (\forall (v4: T).((pr0 v3 
v4) \to (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v4 t4 w2)))))))))))).(\lambda (v0: T).(\lambda (w1: T).(\lambda 
(i: nat).(\lambda (H7: (subst0 i v0 (THead (Flat Appl) v1 (THead (Bind b) u1 
t3)) w1)).(\lambda (v3: T).(\lambda (H8: (pr0 v0 v3)).(or3_ind (ex2 T 
(\lambda (u3: T).(eq T w1 (THead (Flat Appl) u3 (THead (Bind b) u1 t3)))) 
(\lambda (u3: T).(subst0 i v0 v1 u3))) (ex2 T (\lambda (t5: T).(eq T w1 
(THead (Flat Appl) v1 t5))) (\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 
(THead (Bind b) u1 t3) t5))) (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq 
T w1 (THead (Flat Appl) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i 
v0 v1 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 
(THead (Bind b) u1 t3) t5)))) (or (pr0 w1 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda 
(w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4)) w2)))) (\lambda (H9: (ex2 T (\lambda (u3: T).(eq T w1 (THead (Flat Appl) 
u3 (THead (Bind b) u1 t3)))) (\lambda (u3: T).(subst0 i v0 v1 u3)))).(ex2_ind 
T (\lambda (u3: T).(eq T w1 (THead (Flat Appl) u3 (THead (Bind b) u1 t3)))) 
(\lambda (u3: T).(subst0 i v0 v1 u3)) (or (pr0 w1 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x: T).(\lambda (H10: (eq T w1 (THead (Flat 
Appl) x (THead (Bind b) u1 t3)))).(\lambda (H11: (subst0 i v0 v1 
x)).(eq_ind_r T (THead (Flat Appl) x (THead (Bind b) u1 t3)) (\lambda (t: 
T).(or (pr0 t (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) 
(ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2))))) (or_ind (pr0 x 
v2) (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2))) (or (pr0 (THead (Flat Appl) x (THead (Bind b) u1 t3)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x (THead (Bind b) u1 t3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (H12: (pr0 x v2)).(or_introl (pr0 (THead (Flat Appl) x (THead (Bind 
b) u1 t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 
T (\lambda (w2: T).(pr0 (THead (Flat Appl) x (THead (Bind b) u1 t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2))) (pr0_upsilon b H0 x v2 H12 u1 u2 H3 t3 t4 H5))) (\lambda 
(H12: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x (THead (Bind b) u1 t3)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x (THead (Bind b) u1 t3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x0: T).(\lambda (H13: (pr0 x x0)).(\lambda (H14: (subst0 i v3 v2 
x0)).(or_intror (pr0 (THead (Flat Appl) x (THead (Bind b) u1 t3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x (THead (Bind b) u1 t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x (THead (Bind b) 
u1 t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O x0) t4)) (pr0_upsilon b H0 x x0 H13 u1 u2 H3 t3 t4 H5) (subst0_snd 
(Bind b) v3 (THead (Flat Appl) (lift (S O) O x0) t4) (THead (Flat Appl) (lift 
(S O) O v2) t4) i (subst0_fst v3 (lift (S O) O x0) (lift (S O) O v2) (s (Bind 
b) i) (subst0_lift_ge_s v2 x0 v3 i H14 O (le_O_n i) b) t4 (Flat Appl)) 
u2)))))) H12)) (H2 v0 x i H11 v3 H8)) w1 H10)))) H9)) (\lambda (H9: (ex2 T 
(\lambda (t5: T).(eq T w1 (THead (Flat Appl) v1 t5))) (\lambda (t5: 
T).(subst0 (s (Flat Appl) i) v0 (THead (Bind b) u1 t3) t5)))).(ex2_ind T 
(\lambda (t5: T).(eq T w1 (THead (Flat Appl) v1 t5))) (\lambda (t5: 
T).(subst0 (s (Flat Appl) i) v0 (THead (Bind b) u1 t3) t5)) (or (pr0 w1 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x: T).(\lambda (H10: (eq 
T w1 (THead (Flat Appl) v1 x))).(\lambda (H11: (subst0 (s (Flat Appl) i) v0 
(THead (Bind b) u1 t3) x)).(or3_ind (ex2 T (\lambda (u3: T).(eq T x (THead 
(Bind b) u3 t3))) (\lambda (u3: T).(subst0 (s (Flat Appl) i) v0 u1 u3))) (ex2 
T (\lambda (t5: T).(eq T x (THead (Bind b) u1 t5))) (\lambda (t5: T).(subst0 
(s (Bind b) (s (Flat Appl) i)) v0 t3 t5))) (ex3_2 T T (\lambda (u3: 
T).(\lambda (t5: T).(eq T x (THead (Bind b) u3 t5)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 t5)))) (or 
(pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H12: (ex2 T 
(\lambda (u3: T).(eq T x (THead (Bind b) u3 t3))) (\lambda (u3: T).(subst0 (s 
(Flat Appl) i) v0 u1 u3)))).(ex2_ind T (\lambda (u3: T).(eq T x (THead (Bind 
b) u3 t3))) (\lambda (u3: T).(subst0 (s (Flat Appl) i) v0 u1 u3)) (or (pr0 w1 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x0: T).(\lambda (H13: (eq 
T x (THead (Bind b) x0 t3))).(\lambda (H14: (subst0 (s (Flat Appl) i) v0 u1 
x0)).(let H15 \def (eq_ind T x (\lambda (t: T).(eq T w1 (THead (Flat Appl) v1 
t))) H10 (THead (Bind b) x0 t3) H13) in (eq_ind_r T (THead (Flat Appl) v1 
(THead (Bind b) x0 t3)) (\lambda (t: T).(or (pr0 t (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 t w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2))))) (or_ind (pr0 x0 u2) (ex2 T (\lambda (w2: T).(pr0 x0 
w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 w2))) (or (pr0 (THead 
(Flat Appl) v1 (THead (Bind b) x0 t3)) (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 
(THead (Bind b) x0 t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H16: (pr0 x0 
u2)).(or_introl (pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 t3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (pr0_upsilon b H0 v1 v2 H1 x0 u2 H16 t3 t4 H5))) (\lambda (H16: (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 
u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 
(s (Flat Appl) i) v3 u2 w2)) (or (pr0 (THead (Flat Appl) v1 (THead (Bind b) 
x0 t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x1: T).(\lambda (H17: (pr0 x0 x1)).(\lambda 
(H18: (subst0 (s (Flat Appl) i) v3 u2 x1)).(or_intror (pr0 (THead (Flat Appl) 
v1 (THead (Bind b) x0 t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) 
O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind 
b) x0 t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead 
(Flat Appl) v1 (THead (Bind b) x0 t3)) w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead 
(Bind b) x1 (THead (Flat Appl) (lift (S O) O v2) t4)) (pr0_upsilon b H0 v1 v2 
H1 x0 x1 H17 t3 t4 H5) (subst0_fst v3 x1 u2 i H18 (THead (Flat Appl) (lift (S 
O) O v2) t4) (Bind b))))))) H16)) (H4 v0 x0 (s (Flat Appl) i) H14 v3 H8)) w1 
H15))))) H12)) (\lambda (H12: (ex2 T (\lambda (t5: T).(eq T x (THead (Bind b) 
u1 t5))) (\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 
t5)))).(ex2_ind T (\lambda (t5: T).(eq T x (THead (Bind b) u1 t5))) (\lambda 
(t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 t5)) (or (pr0 w1 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x0: T).(\lambda (H13: (eq T x 
(THead (Bind b) u1 x0))).(\lambda (H14: (subst0 (s (Bind b) (s (Flat Appl) 
i)) v0 t3 x0)).(let H15 \def (eq_ind T x (\lambda (t: T).(eq T w1 (THead 
(Flat Appl) v1 t))) H10 (THead (Bind b) u1 x0) H13) in (eq_ind_r T (THead 
(Flat Appl) v1 (THead (Bind b) u1 x0)) (\lambda (t: T).(or (pr0 t (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2))))) (or_ind (pr0 x0 t4) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 
w2))) (or (pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 x0)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) v1 (THead (Bind b) u1 x0)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (H16: (pr0 x0 t4)).(or_introl (pr0 (THead (Flat Appl) v1 (THead 
(Bind b) u1 x0)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 
x0)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2))) (pr0_upsilon b H0 v1 v2 H1 u1 u2 H3 x0 t4 H16))) 
(\lambda (H16: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 
(s (Bind b) (s (Flat Appl) i)) v3 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 
x0 w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 w2)) 
(or (pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 x0)) (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) v1 (THead (Bind b) u1 x0)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x1: T).(\lambda (H17: (pr0 x0 x1)).(\lambda (H18: (subst0 (s (Bind 
b) (s (Flat Appl) i)) v3 t4 x1)).(or_intror (pr0 (THead (Flat Appl) v1 (THead 
(Bind b) u1 x0)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 
x0)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) v1 (THead (Bind b) u1 x0)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) x1)) (pr0_upsilon b H0 v1 v2 H1 u1 u2 H3 
x0 x1 H17) (subst0_snd (Bind b) v3 (THead (Flat Appl) (lift (S O) O v2) x1) 
(THead (Flat Appl) (lift (S O) O v2) t4) i (subst0_snd (Flat Appl) v3 x1 t4 
(s (Bind b) i) H18 (lift (S O) O v2)) u2)))))) H16)) (H6 v0 x0 (s (Bind b) (s 
(Flat Appl) i)) H14 v3 H8)) w1 H15))))) H12)) (\lambda (H12: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T x (THead (Bind b) u3 t5)))) (\lambda 
(u3: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 
t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T x (THead (Bind 
b) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u1 
u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) 
v0 t3 t5))) (or (pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4))) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H13: (eq T x (THead (Bind b) x0 
x1))).(\lambda (H14: (subst0 (s (Flat Appl) i) v0 u1 x0)).(\lambda (H15: 
(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 x1)).(let H16 \def (eq_ind T x 
(\lambda (t: T).(eq T w1 (THead (Flat Appl) v1 t))) H10 (THead (Bind b) x0 
x1) H13) in (eq_ind_r T (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) 
(\lambda (t: T).(or (pr0 t (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) 
O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2))))) (or_ind 
(pr0 x1 t4) (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s 
(Bind b) (s (Flat Appl) i)) v3 t4 w2))) (or (pr0 (THead (Flat Appl) v1 (THead 
(Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 
x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (H17: (pr0 x1 t4)).(or_ind (pr0 x0 u2) 
(ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) 
i) v3 u2 w2))) (or (pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (H18: (pr0 x0 u2)).(or_introl (pr0 (THead (Flat Appl) v1 
(THead (Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) 
x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2))) (pr0_upsilon b H0 v1 v2 H1 x0 u2 H18 x1 t4 
H17))) (\lambda (H18: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 (s (Flat Appl) i) v3 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 
w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 w2)) (or (pr0 (THead 
(Flat Appl) v1 (THead (Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 
(THead (Bind b) x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x2: T).(\lambda 
(H19: (pr0 x0 x2)).(\lambda (H20: (subst0 (s (Flat Appl) i) v3 u2 
x2)).(or_intror (pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind 
b) x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) (pr0_upsilon b H0 v1 v2 H1 x0 x2 H19 x1 t4 H17) (subst0_fst 
v3 x2 u2 i H20 (THead (Flat Appl) (lift (S O) O v2) t4) (Bind b))))))) H18)) 
(H4 v0 x0 (s (Flat Appl) i) H14 v3 H8))) (\lambda (H17: (ex2 T (\lambda (w2: 
T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s 
(Bind b) (s (Flat Appl) i)) v3 t4 w2)) (or (pr0 (THead (Flat Appl) v1 (THead 
(Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 
x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (x2: T).(\lambda (H18: (pr0 x1 
x2)).(\lambda (H19: (subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 x2)).(or_ind 
(pr0 x0 u2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s 
(Flat Appl) i) v3 u2 w2))) (or (pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 
x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (H20: (pr0 x0 u2)).(or_intror (pr0 (THead (Flat 
Appl) v1 (THead (Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead 
(Bind b) x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) v1 (THead (Bind b) x0 x1)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) x2)) (pr0_upsilon b H0 v1 v2 
H1 x0 u2 H20 x1 x2 H18) (subst0_snd (Bind b) v3 (THead (Flat Appl) (lift (S 
O) O v2) x2) (THead (Flat Appl) (lift (S O) O v2) t4) i (subst0_snd (Flat 
Appl) v3 x2 t4 (s (Bind b) i) H19 (lift (S O) O v2)) u2)))) (\lambda (H20: 
(ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) 
i) v3 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 (s (Flat Appl) i) v3 u2 w2)) (or (pr0 (THead (Flat Appl) v1 (THead 
(Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 
x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (x3: T).(\lambda (H21: (pr0 x0 
x3)).(\lambda (H22: (subst0 (s (Flat Appl) i) v3 u2 x3)).(or_intror (pr0 
(THead (Flat Appl) v1 (THead (Bind b) x0 x1)) (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) 
v1 (THead (Bind b) x0 x1)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) v1 (THead (Bind b) x0 x1)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)) (THead (Bind b) x3 (THead (Flat Appl) (lift (S O) O v2) x2)) 
(pr0_upsilon b H0 v1 v2 H1 x0 x3 H21 x1 x2 H18) (subst0_both v3 u2 x3 i H22 
(Bind b) (THead (Flat Appl) (lift (S O) O v2) t4) (THead (Flat Appl) (lift (S 
O) O v2) x2) (subst0_snd (Flat Appl) v3 x2 t4 (s (Bind b) i) H19 (lift (S O) 
O v2)))))))) H20)) (H4 v0 x0 (s (Flat Appl) i) H14 v3 H8))))) H17)) (H6 v0 x1 
(s (Bind b) (s (Flat Appl) i)) H15 v3 H8)) w1 H16))))))) H12)) 
(subst0_gen_head (Bind b) v0 u1 t3 x (s (Flat Appl) i) H11))))) H9)) (\lambda 
(H9: (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead (Flat Appl) 
u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i v0 v1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 (THead (Bind b) u1 t3) 
t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead 
(Flat Appl) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i v0 v1 u3))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s (Flat Appl) i) v0 (THead (Bind b) 
u1 t3) t5))) (or (pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4))) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H10: (eq T w1 (THead (Flat Appl) x0 
x1))).(\lambda (H11: (subst0 i v0 v1 x0)).(\lambda (H12: (subst0 (s (Flat 
Appl) i) v0 (THead (Bind b) u1 t3) x1)).(or3_ind (ex2 T (\lambda (u3: T).(eq 
T x1 (THead (Bind b) u3 t3))) (\lambda (u3: T).(subst0 (s (Flat Appl) i) v0 
u1 u3))) (ex2 T (\lambda (t5: T).(eq T x1 (THead (Bind b) u1 t5))) (\lambda 
(t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 t5))) (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T x1 (THead (Bind b) u3 t5)))) (\lambda 
(u3: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 t5)))) (or 
(pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H13: (ex2 T 
(\lambda (u3: T).(eq T x1 (THead (Bind b) u3 t3))) (\lambda (u3: T).(subst0 
(s (Flat Appl) i) v0 u1 u3)))).(ex2_ind T (\lambda (u3: T).(eq T x1 (THead 
(Bind b) u3 t3))) (\lambda (u3: T).(subst0 (s (Flat Appl) i) v0 u1 u3)) (or 
(pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x: T).(\lambda 
(H14: (eq T x1 (THead (Bind b) x t3))).(\lambda (H15: (subst0 (s (Flat Appl) 
i) v0 u1 x)).(let H16 \def (eq_ind T x1 (\lambda (t: T).(eq T w1 (THead (Flat 
Appl) x0 t))) H10 (THead (Bind b) x t3) H14) in (eq_ind_r T (THead (Flat 
Appl) x0 (THead (Bind b) x t3)) (\lambda (t: T).(or (pr0 t (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 t 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2))))) (or_ind (pr0 x u2) (ex2 T (\lambda (w2: 
T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 w2))) (or 
(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H17: 
(pr0 x u2)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) 
x t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (H18: (pr0 x0 v2)).(or_introl (pr0 (THead (Flat 
Appl) x0 (THead (Bind b) x t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2))) (pr0_upsilon b H0 x0 v2 H18 x u2 H17 
t3 t4 H5))) (\lambda (H18: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v3 v2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v3 v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x 
t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x2: T).(\lambda (H19: (pr0 x0 x2)).(\lambda 
(H20: (subst0 i v3 v2 x2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 
T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 
(THead (Bind b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O x2) t4)) (pr0_upsilon b H0 x0 x2 H19 x u2 H17 t3 t4 
H5) (subst0_snd (Bind b) v3 (THead (Flat Appl) (lift (S O) O x2) t4) (THead 
(Flat Appl) (lift (S O) O v2) t4) i (subst0_fst v3 (lift (S O) O x2) (lift (S 
O) O v2) (s (Bind b) i) (subst0_lift_ge_s v2 x2 v3 i H20 O (le_O_n i) b) t4 
(Flat Appl)) u2)))))) H18)) (H2 v0 x0 i H11 v3 H8))) (\lambda (H17: (ex2 T 
(\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s 
(Flat Appl) i) v3 u2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x 
t3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x2: T).(\lambda (H18: (pr0 x x2)).(\lambda 
(H19: (subst0 (s (Flat Appl) i) v3 u2 x2)).(or_ind (pr0 x0 v2) (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 
(THead (Flat Appl) x0 (THead (Bind b) x t3)) (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) 
x0 (THead (Bind b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H20: (pr0 x0 
v2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) (pr0_upsilon b H0 x0 v2 H20 x x2 H18 t3 t4 H5) (subst0_fst 
v3 x2 u2 i H19 (THead (Flat Appl) (lift (S O) O v2) t4) (Bind b))))) (\lambda 
(H20: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x3: T).(\lambda (H21: (pr0 x0 x3)).(\lambda (H22: (subst0 i v3 v2 
x3)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x t3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x t3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x2 (THead (Flat Appl) (lift 
(S O) O x3) t4)) (pr0_upsilon b H0 x0 x3 H21 x x2 H18 t3 t4 H5) (subst0_both 
v3 u2 x2 i H19 (Bind b) (THead (Flat Appl) (lift (S O) O v2) t4) (THead (Flat 
Appl) (lift (S O) O x3) t4) (subst0_fst v3 (lift (S O) O x3) (lift (S O) O 
v2) (s (Bind b) i) (subst0_lift_ge_s v2 x3 v3 i H22 O (le_O_n i) b) t4 (Flat 
Appl)))))))) H20)) (H2 v0 x0 i H11 v3 H8))))) H17)) (H4 v0 x (s (Flat Appl) 
i) H15 v3 H8)) w1 H16))))) H13)) (\lambda (H13: (ex2 T (\lambda (t5: T).(eq T 
x1 (THead (Bind b) u1 t5))) (\lambda (t5: T).(subst0 (s (Bind b) (s (Flat 
Appl) i)) v0 t3 t5)))).(ex2_ind T (\lambda (t5: T).(eq T x1 (THead (Bind b) 
u1 t5))) (\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 t5)) 
(or (pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) 
(ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (x: 
T).(\lambda (H14: (eq T x1 (THead (Bind b) u1 x))).(\lambda (H15: (subst0 (s 
(Bind b) (s (Flat Appl) i)) v0 t3 x)).(let H16 \def (eq_ind T x1 (\lambda (t: 
T).(eq T w1 (THead (Flat Appl) x0 t))) H10 (THead (Bind b) u1 x) H14) in 
(eq_ind_r T (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (\lambda (t: T).(or 
(pr0 t (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2))))) (or_ind (pr0 x t4) (ex2 T 
(\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat 
Appl) i)) v3 t4 w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda 
(w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (H17: (pr0 x t4)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat 
Appl) x0 (THead (Bind b) u1 x)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind b) u1 x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H18: (pr0 x0 
v2)).(or_introl (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (pr0_upsilon b H0 x0 v2 H18 u1 u2 H3 x t4 H17))) (\lambda (H18: (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x2: T).(\lambda (H19: (pr0 x0 x2)).(\lambda (H20: (subst0 i v3 v2 
x2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) u1 x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O x2) t4)) (pr0_upsilon b H0 x0 x2 H19 u1 u2 H3 x t4 H17) (subst0_snd 
(Bind b) v3 (THead (Flat Appl) (lift (S O) O x2) t4) (THead (Flat Appl) (lift 
(S O) O v2) t4) i (subst0_fst v3 (lift (S O) O x2) (lift (S O) O v2) (s (Bind 
b) i) (subst0_lift_ge_s v2 x2 v3 i H20 O (le_O_n i) b) t4 (Flat Appl)) 
u2)))))) H18)) (H2 v0 x0 i H11 v3 H8))) (\lambda (H17: (ex2 T (\lambda (w2: 
T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s 
(Bind b) (s (Flat Appl) i)) v3 t4 w2)) (or (pr0 (THead (Flat Appl) x0 (THead 
(Bind b) u1 x)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) 
w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (x2: T).(\lambda (H18: (pr0 x 
x2)).(\lambda (H19: (subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 x2)).(or_ind 
(pr0 x0 v2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i 
v3 v2 w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (H20: (pr0 x0 v2)).(or_intror (pr0 (THead (Flat Appl) x0 
(THead (Bind b) u1 x)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) 
u1 x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead 
(Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) x2)) (pr0_upsilon b H0 x0 v2 
H20 u1 u2 H3 x x2 H18) (subst0_snd (Bind b) v3 (THead (Flat Appl) (lift (S O) 
O v2) x2) (THead (Flat Appl) (lift (S O) O v2) t4) i (subst0_snd (Flat Appl) 
v3 x2 t4 (s (Bind b) i) H19 (lift (S O) O v2)) u2)))) (\lambda (H20: (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x3: T).(\lambda (H21: (pr0 x0 x3)).(\lambda (H22: (subst0 i v3 v2 
x3)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) u1 x)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) u1 x)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O x3) x2)) (pr0_upsilon b H0 x0 x3 H21 u1 u2 H3 x x2 H18) (subst0_snd 
(Bind b) v3 (THead (Flat Appl) (lift (S O) O x3) x2) (THead (Flat Appl) (lift 
(S O) O v2) t4) i (subst0_both v3 (lift (S O) O v2) (lift (S O) O x3) (s 
(Bind b) i) (subst0_lift_ge_s v2 x3 v3 i H22 O (le_O_n i) b) (Flat Appl) t4 
x2 H19) u2)))))) H20)) (H2 v0 x0 i H11 v3 H8))))) H17)) (H6 v0 x (s (Bind b) 
(s (Flat Appl) i)) H15 v3 H8)) w1 H16))))) H13)) (\lambda (H13: (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T x1 (THead (Bind b) u3 t5)))) (\lambda 
(u3: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) v0 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 
t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T x1 (THead 
(Bind b) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 (s (Flat Appl) i) 
v0 u1 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind b) (s (Flat 
Appl) i)) v0 t3 t5))) (or (pr0 w1 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H14: (eq T x1 (THead (Bind 
b) x2 x3))).(\lambda (H15: (subst0 (s (Flat Appl) i) v0 u1 x2)).(\lambda 
(H16: (subst0 (s (Bind b) (s (Flat Appl) i)) v0 t3 x3)).(let H17 \def (eq_ind 
T x1 (\lambda (t: T).(eq T w1 (THead (Flat Appl) x0 t))) H10 (THead (Bind b) 
x2 x3) H14) in (eq_ind_r T (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) 
(\lambda (t: T).(or (pr0 t (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) 
O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v3 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2))))) (or_ind 
(pr0 x3 t4) (ex2 T (\lambda (w2: T).(pr0 x3 w2)) (\lambda (w2: T).(subst0 (s 
(Bind b) (s (Flat Appl) i)) v3 t4 w2))) (or (pr0 (THead (Flat Appl) x0 (THead 
(Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 
x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (H18: (pr0 x3 t4)).(or_ind (pr0 x2 u2) 
(ex2 T (\lambda (w2: T).(pr0 x2 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) 
i) v3 u2 w2))) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (H19: (pr0 x2 u2)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat 
Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead 
(Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H20: (pr0 x0 
v2)).(or_introl (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (pr0_upsilon b H0 x0 v2 H20 x2 u2 H19 x3 t4 H18))) (\lambda (H20: (ex2 
T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x: T).(\lambda (H21: (pr0 x0 x)).(\lambda (H22: (subst0 i v3 v2 
x)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O x) t4)) (pr0_upsilon b H0 x0 x H21 x2 u2 H19 x3 t4 H18) (subst0_snd 
(Bind b) v3 (THead (Flat Appl) (lift (S O) O x) t4) (THead (Flat Appl) (lift 
(S O) O v2) t4) i (subst0_fst v3 (lift (S O) O x) (lift (S O) O v2) (s (Bind 
b) i) (subst0_lift_ge_s v2 x v3 i H22 O (le_O_n i) b) t4 (Flat Appl)) 
u2)))))) H20)) (H2 v0 x0 i H11 v3 H8))) (\lambda (H19: (ex2 T (\lambda (w2: 
T).(pr0 x2 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x2 w2)) (\lambda (w2: T).(subst0 (s 
(Flat Appl) i) v3 u2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 
x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x: T).(\lambda (H20: (pr0 x2 x)).(\lambda 
(H21: (subst0 (s (Flat Appl) i) v3 u2 x)).(or_ind (pr0 x0 v2) (ex2 T (\lambda 
(w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead 
(Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 
(THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H22: (pr0 x0 
v2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x (THead (Flat Appl) (lift 
(S O) O v2) t4)) (pr0_upsilon b H0 x0 v2 H22 x2 x H20 x3 t4 H18) (subst0_fst 
v3 x u2 i H21 (THead (Flat Appl) (lift (S O) O v2) t4) (Bind b))))) (\lambda 
(H22: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x4: T).(\lambda (H23: (pr0 x0 x4)).(\lambda (H24: (subst0 i v3 v2 
x4)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x (THead (Flat Appl) (lift 
(S O) O x4) t4)) (pr0_upsilon b H0 x0 x4 H23 x2 x H20 x3 t4 H18) (subst0_both 
v3 u2 x i H21 (Bind b) (THead (Flat Appl) (lift (S O) O v2) t4) (THead (Flat 
Appl) (lift (S O) O x4) t4) (subst0_fst v3 (lift (S O) O x4) (lift (S O) O 
v2) (s (Bind b) i) (subst0_lift_ge_s v2 x4 v3 i H24 O (le_O_n i) b) t4 (Flat 
Appl)))))))) H22)) (H2 v0 x0 i H11 v3 H8))))) H19)) (H4 v0 x2 (s (Flat Appl) 
i) H15 v3 H8))) (\lambda (H18: (ex2 T (\lambda (w2: T).(pr0 x3 w2)) (\lambda 
(w2: T).(subst0 (s (Bind b) (s (Flat Appl) i)) v3 t4 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x3 w2)) (\lambda (w2: T).(subst0 (s (Bind b) (s (Flat 
Appl) i)) v3 t4 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda 
(w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2)))) (\lambda (x: T).(\lambda (H19: (pr0 x3 x)).(\lambda (H20: (subst0 (s 
(Bind b) (s (Flat Appl) i)) v3 t4 x)).(or_ind (pr0 x2 u2) (ex2 T (\lambda 
(w2: T).(pr0 x2 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) i) v3 u2 w2))) 
(or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (H21: (pr0 x2 u2)).(or_ind (pr0 x0 v2) (ex2 T (\lambda (w2: T).(pr0 
x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) (or (pr0 (THead (Flat Appl) x0 
(THead (Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) 
x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)))) (\lambda (H22: (pr0 x0 v2)).(or_intror 
(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
x)) (pr0_upsilon b H0 x0 v2 H22 x2 u2 H21 x3 x H19) (subst0_snd (Bind b) v3 
(THead (Flat Appl) (lift (S O) O v2) x) (THead (Flat Appl) (lift (S O) O v2) 
t4) i (subst0_snd (Flat Appl) v3 x t4 (s (Bind b) i) H20 (lift (S O) O v2)) 
u2)))) (\lambda (H22: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v3 v2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v3 v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) 
x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2)))) (\lambda (x4: T).(\lambda (H23: (pr0 x0 x4)).(\lambda 
(H24: (subst0 i v3 v2 x4)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 
T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) 
(\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 
(THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O x4) x)) (pr0_upsilon b H0 x0 x4 H23 x2 u2 H21 x3 x 
H19) (subst0_snd (Bind b) v3 (THead (Flat Appl) (lift (S O) O x4) x) (THead 
(Flat Appl) (lift (S O) O v2) t4) i (subst0_both v3 (lift (S O) O v2) (lift 
(S O) O x4) (s (Bind b) i) (subst0_lift_ge_s v2 x4 v3 i H24 O (le_O_n i) b) 
(Flat Appl) t4 x H20) u2)))))) H22)) (H2 v0 x0 i H11 v3 H8))) (\lambda (H21: 
(ex2 T (\lambda (w2: T).(pr0 x2 w2)) (\lambda (w2: T).(subst0 (s (Flat Appl) 
i) v3 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x2 w2)) (\lambda (w2: 
T).(subst0 (s (Flat Appl) i) v3 u2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead 
(Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 
x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2)))) (\lambda (x4: T).(\lambda (H22: (pr0 x2 
x4)).(\lambda (H23: (subst0 (s (Flat Appl) i) v3 u2 x4)).(or_ind (pr0 x0 v2) 
(ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 w2))) 
(or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (H24: (pr0 x0 v2)).(or_intror (pr0 (THead (Flat Appl) x0 (THead 
(Bind b) x2 x3)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4))) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 
x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat 
Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x4 
(THead (Flat Appl) (lift (S O) O v2) x)) (pr0_upsilon b H0 x0 v2 H24 x2 x4 
H22 x3 x H19) (subst0_both v3 u2 x4 i H23 (Bind b) (THead (Flat Appl) (lift 
(S O) O v2) t4) (THead (Flat Appl) (lift (S O) O v2) x) (subst0_snd (Flat 
Appl) v3 x t4 (s (Bind b) i) H20 (lift (S O) O v2)))))) (\lambda (H24: (ex2 T 
(\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 v2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v3 
v2 w2)) (or (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i 
v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) w2)))) 
(\lambda (x5: T).(\lambda (H25: (pr0 x0 x5)).(\lambda (H26: (subst0 i v3 v2 
x5)).(or_intror (pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Appl) x0 (THead (Bind b) x2 x3)) w2)) (\lambda (w2: 
T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Appl) x0 (THead (Bind 
b) x2 x3)) w2)) (\lambda (w2: T).(subst0 i v3 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) w2)) (THead (Bind b) x4 (THead (Flat Appl) (lift 
(S O) O x5) x)) (pr0_upsilon b H0 x0 x5 H25 x2 x4 H22 x3 x H19) (subst0_both 
v3 u2 x4 i H23 (Bind b) (THead (Flat Appl) (lift (S O) O v2) t4) (THead (Flat 
Appl) (lift (S O) O x5) x) (subst0_both v3 (lift (S O) O v2) (lift (S O) O 
x5) (s (Bind b) i) (subst0_lift_ge_s v2 x5 v3 i H26 O (le_O_n i) b) (Flat 
Appl) t4 x H20))))))) H24)) (H2 v0 x0 i H11 v3 H8))))) H21)) (H4 v0 x2 (s 
(Flat Appl) i) H15 v3 H8))))) H18)) (H6 v0 x3 (s (Bind b) (s (Flat Appl) i)) 
H16 v3 H8)) w1 H17))))))) H13)) (subst0_gen_head (Bind b) v0 u1 t3 x1 (s 
(Flat Appl) i) H12))))))) H9)) (subst0_gen_head (Flat Appl) v0 v1 (THead 
(Bind b) u1 t3) w1 i H7)))))))))))))))))))))) (\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H0: (pr0 u1 u2)).(\lambda (H1: ((\forall (v1: T).(\forall (w1: 
T).(\forall (i: nat).((subst0 i v1 u1 w1) \to (\forall (v2: T).((pr0 v1 v2) 
\to (or (pr0 w1 u2) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 u2 w2)))))))))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H2: (pr0 t3 t4)).(\lambda (H3: ((\forall (v1: T).(\forall (w1: T).(\forall 
(i: nat).((subst0 i v1 t3 w1) \to (\forall (v2: T).((pr0 v1 v2) \to (or (pr0 
w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2)))))))))))).(\lambda (w: T).(\lambda (H4: (subst0 O u2 t4 w)).(\lambda 
(v1: T).(\lambda (w1: T).(\lambda (i: nat).(\lambda (H5: (subst0 i v1 (THead 
(Bind Abbr) u1 t3) w1)).(\lambda (v2: T).(\lambda (H6: (pr0 v1 v2)).(or3_ind 
(ex2 T (\lambda (u3: T).(eq T w1 (THead (Bind Abbr) u3 t3))) (\lambda (u3: 
T).(subst0 i v1 u1 u3))) (ex2 T (\lambda (t5: T).(eq T w1 (THead (Bind Abbr) 
u1 t5))) (\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 t5))) (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead (Bind Abbr) u3 t5)))) 
(\lambda (u3: T).(\lambda (_: T).(subst0 i v1 u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 t5)))) (or (pr0 w1 (THead 
(Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (H7: (ex2 T (\lambda 
(u3: T).(eq T w1 (THead (Bind Abbr) u3 t3))) (\lambda (u3: T).(subst0 i v1 u1 
u3)))).(ex2_ind T (\lambda (u3: T).(eq T w1 (THead (Bind Abbr) u3 t3))) 
(\lambda (u3: T).(subst0 i v1 u1 u3)) (or (pr0 w1 (THead (Bind Abbr) u2 w)) 
(ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 (THead 
(Bind Abbr) u2 w) w2)))) (\lambda (x: T).(\lambda (H8: (eq T w1 (THead (Bind 
Abbr) x t3))).(\lambda (H9: (subst0 i v1 u1 x)).(eq_ind_r T (THead (Bind 
Abbr) x t3) (\lambda (t: T).(or (pr0 t (THead (Bind Abbr) u2 w)) (ex2 T 
(\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) 
u2 w) w2))))) (or_ind (pr0 x u2) (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda 
(w2: T).(subst0 i v2 u2 w2))) (or (pr0 (THead (Bind Abbr) x t3) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (H10: 
(pr0 x u2)).(or_introl (pr0 (THead (Bind Abbr) x t3) (THead (Bind Abbr) u2 
w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (pr0_delta x u2 H10 t3 t4 H2 w 
H4))) (\lambda (H10: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: 
T).(subst0 i v2 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda 
(w2: T).(subst0 i v2 u2 w2)) (or (pr0 (THead (Bind Abbr) x t3) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x0: 
T).(\lambda (H11: (pr0 x x0)).(\lambda (H12: (subst0 i v2 u2 x0)).(ex2_ind T 
(\lambda (t: T).(subst0 O x0 t4 t)) (\lambda (t: T).(subst0 (S (plus i O)) v2 
w t)) (or (pr0 (THead (Bind Abbr) x t3) (THead (Bind Abbr) u2 w)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x1: T).(\lambda (H13: (subst0 
O x0 t4 x1)).(\lambda (H14: (subst0 (S (plus i O)) v2 w x1)).(let H15 \def 
(f_equal nat nat S (plus i O) i (sym_eq nat i (plus i O) (plus_n_O i))) in 
(let H16 \def (eq_ind nat (S (plus i O)) (\lambda (n: nat).(subst0 n v2 w 
x1)) H14 (S i) H15) in (or_intror (pr0 (THead (Bind Abbr) x t3) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x t3) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)) (THead (Bind Abbr) x0 x1) (pr0_delta x x0 
H11 t3 t4 H2 x1 H13) (subst0_both v2 u2 x0 i H12 (Bind Abbr) w x1 H16)))))))) 
(subst0_subst0_back t4 w u2 O H4 x0 v2 i H12))))) H10)) (H1 v1 x i H9 v2 H6)) 
w1 H8)))) H7)) (\lambda (H7: (ex2 T (\lambda (t5: T).(eq T w1 (THead (Bind 
Abbr) u1 t5))) (\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 
t5)))).(ex2_ind T (\lambda (t5: T).(eq T w1 (THead (Bind Abbr) u1 t5))) 
(\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 t5)) (or (pr0 w1 (THead 
(Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x: T).(\lambda (H8: 
(eq T w1 (THead (Bind Abbr) u1 x))).(\lambda (H9: (subst0 (s (Bind Abbr) i) 
v1 t3 x)).(eq_ind_r T (THead (Bind Abbr) u1 x) (\lambda (t: T).(or (pr0 t 
(THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))))) (or_ind (pr0 x t4) (ex2 T 
(\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind Abbr) i) v2 t4 
w2))) (or (pr0 (THead (Bind Abbr) u1 x) (THead (Bind Abbr) u2 w)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) u1 x) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (H10: (pr0 x t4)).(or_introl 
(pr0 (THead (Bind Abbr) u1 x) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Bind Abbr) u1 x) w2)) (\lambda (w2: T).(subst0 i v2 (THead 
(Bind Abbr) u2 w) w2))) (pr0_delta u1 u2 H0 x t4 H10 w H4))) (\lambda (H10: 
(ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Bind Abbr) 
i) v2 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: 
T).(subst0 (s (Bind Abbr) i) v2 t4 w2)) (or (pr0 (THead (Bind Abbr) u1 x) 
(THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) u1 
x) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) 
(\lambda (x0: T).(\lambda (H11: (pr0 x x0)).(\lambda (H12: (subst0 (s (Bind 
Abbr) i) v2 t4 x0)).(ex2_ind T (\lambda (t: T).(subst0 O u2 x0 t)) (\lambda 
(t: T).(subst0 (s (Bind Abbr) i) v2 w t)) (or (pr0 (THead (Bind Abbr) u1 x) 
(THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) u1 
x) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) 
(\lambda (x1: T).(\lambda (H13: (subst0 O u2 x0 x1)).(\lambda (H14: (subst0 
(s (Bind Abbr) i) v2 w x1)).(or_intror (pr0 (THead (Bind Abbr) u1 x) (THead 
(Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) u1 x) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) u1 x) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)) (THead (Bind Abbr) u2 x1) (pr0_delta u1 u2 
H0 x x0 H11 x1 H13) (subst0_snd (Bind Abbr) v2 x1 w i H14 u2)))))) 
(subst0_confluence_neq t4 x0 v2 (s (Bind Abbr) i) H12 w u2 O H4 (sym_not_eq 
nat O (S i) (O_S i))))))) H10)) (H3 v1 x (s (Bind Abbr) i) H9 v2 H6)) w1 
H8)))) H7)) (\lambda (H7: (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T 
w1 (THead (Bind Abbr) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i v1 
u1 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 
t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T w1 (THead 
(Bind Abbr) u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i v1 u1 u3))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s (Bind Abbr) i) v1 t3 t5))) (or 
(pr0 w1 (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H8: (eq T w1 (THead (Bind Abbr) x0 
x1))).(\lambda (H9: (subst0 i v1 u1 x0)).(\lambda (H10: (subst0 (s (Bind 
Abbr) i) v1 t3 x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: T).(or 
(pr0 t (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda 
(w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))))) (or_ind (pr0 x1 t4) 
(ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 (s (Bind Abbr) 
i) v2 t4 w2))) (or (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (H11: (pr0 x1 
t4)).(or_ind (pr0 x0 u2) (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v2 u2 w2))) (or (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (H12: 
(pr0 x0 u2)).(or_introl (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 
w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: 
T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (pr0_delta x0 u2 H12 x1 t4 H11 
w H4))) (\lambda (H12: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: 
T).(subst0 i v2 u2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda 
(w2: T).(subst0 i v2 u2 w2)) (or (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x: 
T).(\lambda (H13: (pr0 x0 x)).(\lambda (H14: (subst0 i v2 u2 x)).(ex2_ind T 
(\lambda (t: T).(subst0 O x t4 t)) (\lambda (t: T).(subst0 (S (plus i O)) v2 
w t)) (or (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x2: T).(\lambda (H15: (subst0 
O x t4 x2)).(\lambda (H16: (subst0 (S (plus i O)) v2 w x2)).(let H17 \def 
(f_equal nat nat S (plus i O) i (sym_eq nat i (plus i O) (plus_n_O i))) in 
(let H18 \def (eq_ind nat (S (plus i O)) (\lambda (n: nat).(subst0 n v2 w 
x2)) H16 (S i) H17) in (or_intror (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)) (THead (Bind Abbr) x x2) (pr0_delta x0 x 
H13 x1 t4 H11 x2 H15) (subst0_both v2 u2 x i H14 (Bind Abbr) w x2 H18)))))))) 
(subst0_subst0_back t4 w u2 O H4 x v2 i H14))))) H12)) (H1 v1 x0 i H9 v2 
H6))) (\lambda (H11: (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: 
T).(subst0 (s (Bind Abbr) i) v2 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x1 
w2)) (\lambda (w2: T).(subst0 (s (Bind Abbr) i) v2 t4 w2)) (or (pr0 (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 
(THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind 
Abbr) u2 w) w2)))) (\lambda (x: T).(\lambda (H12: (pr0 x1 x)).(\lambda (H13: 
(subst0 (s (Bind Abbr) i) v2 t4 x)).(or_ind (pr0 x0 u2) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 u2 w2))) (or (pr0 (THead (Bind 
Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead 
(Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 
w) w2)))) (\lambda (H14: (pr0 x0 u2)).(ex2_ind T (\lambda (t: T).(subst0 O u2 
x t)) (\lambda (t: T).(subst0 (s (Bind Abbr) i) v2 w t)) (or (pr0 (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 
(THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind 
Abbr) u2 w) w2)))) (\lambda (x2: T).(\lambda (H15: (subst0 O u2 x 
x2)).(\lambda (H16: (subst0 (s (Bind Abbr) i) v2 w x2)).(or_intror (pr0 
(THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead 
(Bind Abbr) u2 w) w2))) (ex_intro2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) 
x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)) 
(THead (Bind Abbr) u2 x2) (pr0_delta x0 u2 H14 x1 x H12 x2 H15) (subst0_snd 
(Bind Abbr) v2 x2 w i H16 u2)))))) (subst0_confluence_neq t4 x v2 (s (Bind 
Abbr) i) H13 w u2 O H4 (sym_not_eq nat O (S i) (O_S i))))) (\lambda (H14: 
(ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 u2 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 
u2 w2)) (or (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda (x2: T).(\lambda (H15: (pr0 x0 
x2)).(\lambda (H16: (subst0 i v2 u2 x2)).(ex2_ind T (\lambda (t: T).(subst0 O 
x2 t4 t)) (\lambda (t: T).(subst0 (S (plus i O)) v2 w t)) (or (pr0 (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 
(THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind 
Abbr) u2 w) w2)))) (\lambda (x3: T).(\lambda (H17: (subst0 O x2 t4 
x3)).(\lambda (H18: (subst0 (S (plus i O)) v2 w x3)).(let H19 \def (f_equal 
nat nat S (plus i O) i (sym_eq nat i (plus i O) (plus_n_O i))) in (let H20 
\def (eq_ind nat (S (plus i O)) (\lambda (n: nat).(subst0 n v2 w x3)) H18 (S 
i) H19) in (ex2_ind T (\lambda (t: T).(subst0 (s (Bind Abbr) i) v2 x3 t)) 
(\lambda (t: T).(subst0 O x2 x t)) (or (pr0 (THead (Bind Abbr) x0 x1) (THead 
(Bind Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) 
w2)) (\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2)))) (\lambda 
(x4: T).(\lambda (H21: (subst0 (s (Bind Abbr) i) v2 x3 x4)).(\lambda (H22: 
(subst0 O x2 x x4)).(or_intror (pr0 (THead (Bind Abbr) x0 x1) (THead (Bind 
Abbr) u2 w)) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 (THead (Bind Abbr) u2 w) w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Bind Abbr) x0 x1) w2)) (\lambda (w2: T).(subst0 
i v2 (THead (Bind Abbr) u2 w) w2)) (THead (Bind Abbr) x2 x4) (pr0_delta x0 x2 
H15 x1 x H12 x4 H22) (subst0_both v2 u2 x2 i H16 (Bind Abbr) w x4 
(subst0_trans x3 w v2 (s (Bind Abbr) i) H20 x4 H21))))))) 
(subst0_confluence_neq t4 x3 x2 O H17 x v2 (s (Bind Abbr) i) H13 (O_S 
i)))))))) (subst0_subst0_back t4 w u2 O H4 x2 v2 i H16))))) H14)) (H1 v1 x0 i 
H9 v2 H6))))) H11)) (H3 v1 x1 (s (Bind Abbr) i) H10 v2 H6)) w1 H8)))))) H7)) 
(subst0_gen_head (Bind Abbr) v1 u1 t3 w1 i H5)))))))))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H1: (pr0 t3 t4)).(\lambda (H2: ((\forall (v1: T).(\forall (w1: 
T).(\forall (i: nat).((subst0 i v1 t3 w1) \to (\forall (v2: T).((pr0 v1 v2) 
\to (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)))))))))))).(\lambda (u: T).(\lambda (v1: T).(\lambda 
(w1: T).(\lambda (i: nat).(\lambda (H3: (subst0 i v1 (THead (Bind b) u (lift 
(S O) O t3)) w1)).(\lambda (v2: T).(\lambda (H4: (pr0 v1 v2)).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T w1 (THead (Bind b) u2 (lift (S O) O t3)))) (\lambda 
(u2: T).(subst0 i v1 u u2))) (ex2 T (\lambda (t5: T).(eq T w1 (THead (Bind b) 
u t5))) (\lambda (t5: T).(subst0 (s (Bind b) i) v1 (lift (S O) O t3) t5))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T w1 (THead (Bind b) u2 
t5)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s (Bind b) i) v1 (lift (S O) O t3) t5)))) (or 
(pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i 
v2 t4 w2)))) (\lambda (H5: (ex2 T (\lambda (u2: T).(eq T w1 (THead (Bind b) 
u2 (lift (S O) O t3)))) (\lambda (u2: T).(subst0 i v1 u u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T w1 (THead (Bind b) u2 (lift (S O) O t3)))) (\lambda 
(u2: T).(subst0 i v1 u u2)) (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 
w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (x: T).(\lambda (H6: 
(eq T w1 (THead (Bind b) x (lift (S O) O t3)))).(\lambda (_: (subst0 i v1 u 
x)).(eq_ind_r T (THead (Bind b) x (lift (S O) O t3)) (\lambda (t: T).(or (pr0 
t t4) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2))))) (or_introl (pr0 (THead (Bind b) x (lift (S O) O t3)) t4) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind b) x (lift (S O) O t3)) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2))) (pr0_zeta b H0 t3 t4 H1 x)) w1 H6)))) H5)) (\lambda 
(H5: (ex2 T (\lambda (t5: T).(eq T w1 (THead (Bind b) u t5))) (\lambda (t5: 
T).(subst0 (s (Bind b) i) v1 (lift (S O) O t3) t5)))).(ex2_ind T (\lambda 
(t5: T).(eq T w1 (THead (Bind b) u t5))) (\lambda (t5: T).(subst0 (s (Bind b) 
i) v1 (lift (S O) O t3) t5)) (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 
w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (x: T).(\lambda (H6: 
(eq T w1 (THead (Bind b) u x))).(\lambda (H7: (subst0 (s (Bind b) i) v1 (lift 
(S O) O t3) x)).(ex2_ind T (\lambda (t5: T).(eq T x (lift (S O) O t5))) 
(\lambda (t5: T).(subst0 (minus (s (Bind b) i) (S O)) v1 t3 t5)) (or (pr0 w1 
t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2)))) (\lambda (x0: T).(\lambda (H8: (eq T x (lift (S O) O x0))).(\lambda 
(H9: (subst0 (minus (s (Bind b) i) (S O)) v1 t3 x0)).(let H10 \def (eq_ind T 
x (\lambda (t: T).(eq T w1 (THead (Bind b) u t))) H6 (lift (S O) O x0) H8) in 
(eq_ind_r T (THead (Bind b) u (lift (S O) O x0)) (\lambda (t: T).(or (pr0 t 
t4) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2))))) (let H11 \def (eq_ind_r nat (minus i O) (\lambda (n: nat).(subst0 n 
v1 t3 x0)) H9 i (minus_n_O i)) in (or_ind (pr0 x0 t4) (ex2 T (\lambda (w2: 
T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (or (pr0 (THead (Bind 
b) u (lift (S O) O x0)) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind b) u 
(lift (S O) O x0)) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda 
(H12: (pr0 x0 t4)).(or_introl (pr0 (THead (Bind b) u (lift (S O) O x0)) t4) 
(ex2 T (\lambda (w2: T).(pr0 (THead (Bind b) u (lift (S O) O x0)) w2)) 
(\lambda (w2: T).(subst0 i v2 t4 w2))) (pr0_zeta b H0 x0 t4 H12 u))) (\lambda 
(H12: (ex2 T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x0 w2)) (\lambda (w2: T).(subst0 i v2 
t4 w2)) (or (pr0 (THead (Bind b) u (lift (S O) O x0)) t4) (ex2 T (\lambda 
(w2: T).(pr0 (THead (Bind b) u (lift (S O) O x0)) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)))) (\lambda (x1: T).(\lambda (H13: (pr0 x0 
x1)).(\lambda (H14: (subst0 i v2 t4 x1)).(or_intror (pr0 (THead (Bind b) u 
(lift (S O) O x0)) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind b) u (lift 
(S O) O x0)) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (ex_intro2 T 
(\lambda (w2: T).(pr0 (THead (Bind b) u (lift (S O) O x0)) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)) x1 (pr0_zeta b H0 x0 x1 H13 u) H14))))) H12)) (H2 v1 
x0 i H11 v2 H4))) w1 H10))))) (subst0_gen_lift_ge v1 t3 x (s (Bind b) i) (S 
O) O H7 (le_n_S O i (le_O_n i))))))) H5)) (\lambda (H5: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T w1 (THead (Bind b) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Bind b) i) v1 (lift (S O) O t3) t5))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t5: T).(eq T w1 (THead (Bind b) u2 t5)))) (\lambda 
(u2: T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Bind b) i) v1 (lift (S O) O t3) t5))) (or (pr0 w1 t4) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H6: (eq T w1 (THead (Bind b) x0 
x1))).(\lambda (_: (subst0 i v1 u x0)).(\lambda (H8: (subst0 (s (Bind b) i) 
v1 (lift (S O) O t3) x1)).(ex2_ind T (\lambda (t5: T).(eq T x1 (lift (S O) O 
t5))) (\lambda (t5: T).(subst0 (minus (s (Bind b) i) (S O)) v1 t3 t5)) (or 
(pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i 
v2 t4 w2)))) (\lambda (x: T).(\lambda (H9: (eq T x1 (lift (S O) O 
x))).(\lambda (H10: (subst0 (minus (s (Bind b) i) (S O)) v1 t3 x)).(let H11 
\def (eq_ind T x1 (\lambda (t: T).(eq T w1 (THead (Bind b) x0 t))) H6 (lift 
(S O) O x) H9) in (eq_ind_r T (THead (Bind b) x0 (lift (S O) O x)) (\lambda 
(t: T).(or (pr0 t t4) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2))))) (let H12 \def (eq_ind_r nat (minus i O) (\lambda 
(n: nat).(subst0 n v1 t3 x)) H10 i (minus_n_O i)) in (or_ind (pr0 x t4) (ex2 
T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (or 
(pr0 (THead (Bind b) x0 (lift (S O) O x)) t4) (ex2 T (\lambda (w2: T).(pr0 
(THead (Bind b) x0 (lift (S O) O x)) w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2)))) (\lambda (H13: (pr0 x t4)).(or_introl (pr0 (THead (Bind b) x0 (lift (S 
O) O x)) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind b) x0 (lift (S O) O 
x)) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (pr0_zeta b H0 x t4 H13 x0))) 
(\lambda (H13: (ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 i 
v2 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 
i v2 t4 w2)) (or (pr0 (THead (Bind b) x0 (lift (S O) O x)) t4) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Bind b) x0 (lift (S O) O x)) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)))) (\lambda (x2: T).(\lambda (H14: (pr0 x 
x2)).(\lambda (H15: (subst0 i v2 t4 x2)).(or_intror (pr0 (THead (Bind b) x0 
(lift (S O) O x)) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Bind b) x0 (lift 
(S O) O x)) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (ex_intro2 T (\lambda 
(w2: T).(pr0 (THead (Bind b) x0 (lift (S O) O x)) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)) x2 (pr0_zeta b H0 x x2 H14 x0) H15))))) H13)) (H2 v1 
x i H12 v2 H4))) w1 H11))))) (subst0_gen_lift_ge v1 t3 x1 (s (Bind b) i) (S 
O) O H8 (le_n_S O i (le_O_n i))))))))) H5)) (subst0_gen_head (Bind b) v1 u 
(lift (S O) O t3) w1 i H3))))))))))))))) (\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H0: (pr0 t3 t4)).(\lambda (H1: ((\forall (v1: T).(\forall (w1: 
T).(\forall (i: nat).((subst0 i v1 t3 w1) \to (\forall (v2: T).((pr0 v1 v2) 
\to (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)))))))))))).(\lambda (u: T).(\lambda (v1: T).(\lambda 
(w1: T).(\lambda (i: nat).(\lambda (H2: (subst0 i v1 (THead (Flat Cast) u t3) 
w1)).(\lambda (v2: T).(\lambda (H3: (pr0 v1 v2)).(or3_ind (ex2 T (\lambda 
(u2: T).(eq T w1 (THead (Flat Cast) u2 t3))) (\lambda (u2: T).(subst0 i v1 u 
u2))) (ex2 T (\lambda (t5: T).(eq T w1 (THead (Flat Cast) u t5))) (\lambda 
(t5: T).(subst0 (s (Flat Cast) i) v1 t3 t5))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T w1 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Flat Cast) i) v1 t3 t5)))) (or (pr0 w1 t4) (ex2 T (\lambda 
(w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (H4: 
(ex2 T (\lambda (u2: T).(eq T w1 (THead (Flat Cast) u2 t3))) (\lambda (u2: 
T).(subst0 i v1 u u2)))).(ex2_ind T (\lambda (u2: T).(eq T w1 (THead (Flat 
Cast) u2 t3))) (\lambda (u2: T).(subst0 i v1 u u2)) (or (pr0 w1 t4) (ex2 T 
(\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) 
(\lambda (x: T).(\lambda (H5: (eq T w1 (THead (Flat Cast) x t3))).(\lambda 
(_: (subst0 i v1 u x)).(eq_ind_r T (THead (Flat Cast) x t3) (\lambda (t: 
T).(or (pr0 t t4) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2))))) (or_introl (pr0 (THead (Flat Cast) x t3) t4) (ex2 
T (\lambda (w2: T).(pr0 (THead (Flat Cast) x t3) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2))) (pr0_tau t3 t4 H0 x)) w1 H5)))) H4)) (\lambda (H4: 
(ex2 T (\lambda (t5: T).(eq T w1 (THead (Flat Cast) u t5))) (\lambda (t5: 
T).(subst0 (s (Flat Cast) i) v1 t3 t5)))).(ex2_ind T (\lambda (t5: T).(eq T 
w1 (THead (Flat Cast) u t5))) (\lambda (t5: T).(subst0 (s (Flat Cast) i) v1 
t3 t5)) (or (pr0 w1 t4) (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)))) (\lambda (x: T).(\lambda (H5: (eq T w1 (THead (Flat 
Cast) u x))).(\lambda (H6: (subst0 (s (Flat Cast) i) v1 t3 x)).(eq_ind_r T 
(THead (Flat Cast) u x) (\lambda (t: T).(or (pr0 t t4) (ex2 T (\lambda (w2: 
T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))))) (or_ind (pr0 x t4) 
(ex2 T (\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Flat Cast) 
i) v2 t4 w2))) (or (pr0 (THead (Flat Cast) u x) t4) (ex2 T (\lambda (w2: 
T).(pr0 (THead (Flat Cast) u x) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) 
(\lambda (H7: (pr0 x t4)).(or_introl (pr0 (THead (Flat Cast) u x) t4) (ex2 T 
(\lambda (w2: T).(pr0 (THead (Flat Cast) u x) w2)) (\lambda (w2: T).(subst0 i 
v2 t4 w2))) (pr0_tau x t4 H7 u))) (\lambda (H7: (ex2 T (\lambda (w2: T).(pr0 
x w2)) (\lambda (w2: T).(subst0 (s (Flat Cast) i) v2 t4 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 x w2)) (\lambda (w2: T).(subst0 (s (Flat Cast) i) v2 t4 
w2)) (or (pr0 (THead (Flat Cast) u x) t4) (ex2 T (\lambda (w2: T).(pr0 (THead 
(Flat Cast) u x) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (x0: 
T).(\lambda (H8: (pr0 x x0)).(\lambda (H9: (subst0 (s (Flat Cast) i) v2 t4 
x0)).(or_intror (pr0 (THead (Flat Cast) u x) t4) (ex2 T (\lambda (w2: T).(pr0 
(THead (Flat Cast) u x) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) 
(ex_intro2 T (\lambda (w2: T).(pr0 (THead (Flat Cast) u x) w2)) (\lambda (w2: 
T).(subst0 i v2 t4 w2)) x0 (pr0_tau x x0 H8 u) H9))))) H7)) (H1 v1 x (s (Flat 
Cast) i) H6 v2 H3)) w1 H5)))) H4)) (\lambda (H4: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T w1 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Flat Cast) i) v1 t3 t5))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T w1 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v1 u u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s (Flat Cast) i) v1 t3 t5))) (or (pr0 w1 t4) (ex2 T (\lambda (w2: 
T).(pr0 w1 w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H5: (eq T w1 (THead (Flat Cast) x0 
x1))).(\lambda (_: (subst0 i v1 u x0)).(\lambda (H7: (subst0 (s (Flat Cast) 
i) v1 t3 x1)).(eq_ind_r T (THead (Flat Cast) x0 x1) (\lambda (t: T).(or (pr0 
t t4) (ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst0 i v2 t4 
w2))))) (or_ind (pr0 x1 t4) (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda 
(w2: T).(subst0 (s (Flat Cast) i) v2 t4 w2))) (or (pr0 (THead (Flat Cast) x0 
x1) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Cast) x0 x1) w2)) (\lambda 
(w2: T).(subst0 i v2 t4 w2)))) (\lambda (H8: (pr0 x1 t4)).(or_introl (pr0 
(THead (Flat Cast) x0 x1) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Cast) 
x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (pr0_tau x1 t4 H8 x0))) 
(\lambda (H8: (ex2 T (\lambda (w2: T).(pr0 x1 w2)) (\lambda (w2: T).(subst0 
(s (Flat Cast) i) v2 t4 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 x1 w2)) 
(\lambda (w2: T).(subst0 (s (Flat Cast) i) v2 t4 w2)) (or (pr0 (THead (Flat 
Cast) x0 x1) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Cast) x0 x1) w2)) 
(\lambda (w2: T).(subst0 i v2 t4 w2)))) (\lambda (x: T).(\lambda (H9: (pr0 x1 
x)).(\lambda (H10: (subst0 (s (Flat Cast) i) v2 t4 x)).(or_intror (pr0 (THead 
(Flat Cast) x0 x1) t4) (ex2 T (\lambda (w2: T).(pr0 (THead (Flat Cast) x0 x1) 
w2)) (\lambda (w2: T).(subst0 i v2 t4 w2))) (ex_intro2 T (\lambda (w2: 
T).(pr0 (THead (Flat Cast) x0 x1) w2)) (\lambda (w2: T).(subst0 i v2 t4 w2)) 
x (pr0_tau x1 x H9 x0) H10))))) H8)) (H1 v1 x1 (s (Flat Cast) i) H7 v2 H3)) 
w1 H5)))))) H4)) (subst0_gen_head (Flat Cast) v1 u t3 w1 i H2))))))))))))) t1 
t2 H))).
(* COMMENTS
Initial nodes: 38857
END *)

