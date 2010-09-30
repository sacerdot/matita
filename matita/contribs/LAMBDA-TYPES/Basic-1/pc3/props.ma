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

include "Basic-1/pc3/defs.ma".

include "Basic-1/pr3/pr3.ma".

theorem clear_pc3_trans:
 \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pc3 c2 t1 t2) \to 
(\forall (c1: C).((clear c1 c2) \to (pc3 c1 t1 t2))))))
\def
 \lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c2 t1 
t2)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(let H1 \def H in (ex2_ind 
T (\lambda (t: T).(pr3 c2 t1 t)) (\lambda (t: T).(pr3 c2 t2 t)) (pc3 c1 t1 
t2) (\lambda (x: T).(\lambda (H2: (pr3 c2 t1 x)).(\lambda (H3: (pr3 c2 t2 
x)).(ex_intro2 T (\lambda (t: T).(pr3 c1 t1 t)) (\lambda (t: T).(pr3 c1 t2 
t)) x (clear_pr3_trans c2 t1 x H2 c1 H0) (clear_pr3_trans c2 t2 x H3 c1 
H0))))) H1))))))).
(* COMMENTS
Initial nodes: 129
END *)

theorem pc3_pr2_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t2 (pr3_pr2 c t1 t2 H) (pr3_refl c t2))))).
(* COMMENTS
Initial nodes: 55
END *)

theorem pc3_pr2_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t2 
t1)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t1 (pr3_refl c t1) (pr3_pr2 c t2 t1 H))))).
(* COMMENTS
Initial nodes: 55
END *)

theorem pc3_pr3_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t2 H (pr3_refl c t2))))).
(* COMMENTS
Initial nodes: 47
END *)

theorem pc3_pr3_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t2 
t1)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t1 (pr3_refl c t1) H)))).
(* COMMENTS
Initial nodes: 47
END *)

theorem pc3_pr3_t:
 \forall (c: C).(\forall (t1: T).(\forall (t0: T).((pr3 c t1 t0) \to (\forall 
(t2: T).((pr3 c t2 t0) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t0: T).(\lambda (H: (pr3 c t1 
t0)).(\lambda (t2: T).(\lambda (H0: (pr3 c t2 t0)).(ex_intro2 T (\lambda (t: 
T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) t0 H H0)))))).
(* COMMENTS
Initial nodes: 53
END *)

theorem pc3_refl:
 \forall (c: C).(\forall (t: T).(pc3 c t t))
\def
 \lambda (c: C).(\lambda (t: T).(ex_intro2 T (\lambda (t0: T).(pr3 c t t0)) 
(\lambda (t0: T).(pr3 c t t0)) t (pr3_refl c t) (pr3_refl c t))).
(* COMMENTS
Initial nodes: 41
END *)

theorem pc3_s:
 \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pc3 c t1 t2) \to (pc3 c 
t2 t1))))
\def
 \lambda (c: C).(\lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc3 c t1 
t2)).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t)) (pc3 c t2 t1) (\lambda (x: T).(\lambda (H1: (pr3 c t1 
x)).(\lambda (H2: (pr3 c t2 x)).(ex_intro2 T (\lambda (t: T).(pr3 c t2 t)) 
(\lambda (t: T).(pr3 c t1 t)) x H2 H1)))) H0))))).
(* COMMENTS
Initial nodes: 97
END *)

theorem pc3_thin_dx:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (\forall 
(u: T).(\forall (f: F).(pc3 c (THead (Flat f) u t1) (THead (Flat f) u 
t2)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (u: T).(\lambda (f: F).(let H0 \def H in (ex2_ind T (\lambda 
(t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) (pc3 c (THead (Flat f) u 
t1) (THead (Flat f) u t2)) (\lambda (x: T).(\lambda (H1: (pr3 c t1 
x)).(\lambda (H2: (pr3 c t2 x)).(ex_intro2 T (\lambda (t: T).(pr3 c (THead 
(Flat f) u t1) t)) (\lambda (t: T).(pr3 c (THead (Flat f) u t2) t)) (THead 
(Flat f) u x) (pr3_thin_dx c t1 x H1 u f) (pr3_thin_dx c t2 x H2 u f))))) 
H0))))))).
(* COMMENTS
Initial nodes: 165
END *)

theorem pc3_head_1:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).(pc3 c (THead k u1 t) (THead k u2 t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t: T).(let H0 \def H in (ex2_ind T (\lambda 
(t0: T).(pr3 c u1 t0)) (\lambda (t0: T).(pr3 c u2 t0)) (pc3 c (THead k u1 t) 
(THead k u2 t)) (\lambda (x: T).(\lambda (H1: (pr3 c u1 x)).(\lambda (H2: 
(pr3 c u2 x)).(ex_intro2 T (\lambda (t0: T).(pr3 c (THead k u1 t) t0)) 
(\lambda (t0: T).(pr3 c (THead k u2 t) t0)) (THead k x t) (pr3_head_12 c u1 x 
H1 k t t (pr3_refl (CHead c k x) t)) (pr3_head_12 c u2 x H2 k t t (pr3_refl 
(CHead c k x) t)))))) H0))))))).
(* COMMENTS
Initial nodes: 183
END *)

theorem pc3_head_2:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pc3 (CHead c k u) t1 t2) \to (pc3 c (THead k u t1) (THead k u 
t2)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pc3 (CHead c k u) t1 t2)).(let H0 \def H in (ex2_ind T 
(\lambda (t: T).(pr3 (CHead c k u) t1 t)) (\lambda (t: T).(pr3 (CHead c k u) 
t2 t)) (pc3 c (THead k u t1) (THead k u t2)) (\lambda (x: T).(\lambda (H1: 
(pr3 (CHead c k u) t1 x)).(\lambda (H2: (pr3 (CHead c k u) t2 x)).(ex_intro2 
T (\lambda (t: T).(pr3 c (THead k u t1) t)) (\lambda (t: T).(pr3 c (THead k u 
t2) t)) (THead k u x) (pr3_head_12 c u u (pr3_refl c u) k t1 x H1) 
(pr3_head_12 c u u (pr3_refl c u) k t2 x H2))))) H0))))))).
(* COMMENTS
Initial nodes: 201
END *)

theorem pc3_pr2_u:
 \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall 
(t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3))))))
\def
 \lambda (c: C).(\lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr2 c t1 
t2)).(\lambda (t3: T).(\lambda (H0: (pc3 c t2 t3)).(let H1 \def H0 in 
(ex2_ind T (\lambda (t: T).(pr3 c t2 t)) (\lambda (t: T).(pr3 c t3 t)) (pc3 c 
t1 t3) (\lambda (x: T).(\lambda (H2: (pr3 c t2 x)).(\lambda (H3: (pr3 c t3 
x)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t3 t)) 
x (pr3_sing c t2 t1 H x H2) H3)))) H1))))))).
(* COMMENTS
Initial nodes: 119
END *)

theorem pc3_t:
 \forall (t2: T).(\forall (c: C).(\forall (t1: T).((pc3 c t1 t2) \to (\forall 
(t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3))))))
\def
 \lambda (t2: T).(\lambda (c: C).(\lambda (t1: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (t3: T).(\lambda (H0: (pc3 c t2 t3)).(let H1 \def H0 in 
(ex2_ind T (\lambda (t: T).(pr3 c t2 t)) (\lambda (t: T).(pr3 c t3 t)) (pc3 c 
t1 t3) (\lambda (x: T).(\lambda (H2: (pr3 c t2 x)).(\lambda (H3: (pr3 c t3 
x)).(let H4 \def H in (ex2_ind T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t)) (pc3 c t1 t3) (\lambda (x0: T).(\lambda (H5: (pr3 c t1 
x0)).(\lambda (H6: (pr3 c t2 x0)).(ex2_ind T (\lambda (t: T).(pr3 c x0 t)) 
(\lambda (t: T).(pr3 c x t)) (pc3 c t1 t3) (\lambda (x1: T).(\lambda (H7: 
(pr3 c x0 x1)).(\lambda (H8: (pr3 c x x1)).(pc3_pr3_t c t1 x1 (pr3_t x0 t1 c 
H5 x1 H7) t3 (pr3_t x t3 c H3 x1 H8))))) (pr3_confluence c t2 x0 H6 x H2))))) 
H4))))) H1))))))).
(* COMMENTS
Initial nodes: 233
END *)

theorem pc3_pr2_u2:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall 
(t2: T).((pc3 c t0 t2) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr2 c t0 
t1)).(\lambda (t2: T).(\lambda (H0: (pc3 c t0 t2)).(pc3_t t0 c t1 (pc3_pr2_x 
c t1 t0 H) t2 H0)))))).
(* COMMENTS
Initial nodes: 45
END *)

theorem pc3_pr3_conf:
 \forall (c: C).(\forall (t: T).(\forall (t1: T).((pc3 c t t1) \to (\forall 
(t2: T).((pr3 c t t2) \to (pc3 c t2 t1))))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (t1: T).(\lambda (H: (pc3 c t 
t1)).(\lambda (t2: T).(\lambda (H0: (pr3 c t t2)).(pc3_t t c t2 (pc3_pr3_x c 
t2 t H0) t1 H)))))).
(* COMMENTS
Initial nodes: 45
END *)

theorem pc3_head_12:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u2) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u2) t1 t2)).(pc3_t (THead k u2 t1) c (THead k u1 t1) (pc3_head_1 c 
u1 u2 H k t1) (THead k u2 t2) (pc3_head_2 c u2 t1 t2 k H0))))))))).
(* COMMENTS
Initial nodes: 89
END *)

theorem pc3_head_21:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u1) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u1) t1 t2)).(pc3_t (THead k u1 t2) c (THead k u1 t1) (pc3_head_2 c 
u1 t1 t2 k H0) (THead k u2 t2) (pc3_head_1 c u1 u2 H k t2))))))))).
(* COMMENTS
Initial nodes: 89
END *)

theorem pc3_pr0_pr2_t:
 \forall (u1: T).(\forall (u2: T).((pr0 u2 u1) \to (\forall (c: C).(\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u2 u1)).(\lambda (c: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H0: (pr2 
(CHead c k u2) t1 t2)).(insert_eq C (CHead c k u2) (\lambda (c0: C).(pr2 c0 
t1 t2)) (\lambda (_: C).(pc3 (CHead c k u1) t1 t2)) (\lambda (y: C).(\lambda 
(H1: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).((eq C c0 (CHead c k u2)) \to (pc3 (CHead c k u1) t t0))))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (H3: 
(eq C c0 (CHead c k u2))).(let H4 \def (f_equal C C (\lambda (e: C).e) c0 
(CHead c k u2) H3) in (pc3_pr2_r (CHead c k u1) t3 t4 (pr2_free (CHead c k 
u1) t3 t4 H2)))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H2: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H4: (subst0 i u t4 t)).(\lambda (H5: (eq C c0 (CHead c k 
u2))).(let H6 \def (f_equal C C (\lambda (e: C).e) c0 (CHead c k u2) H5) in 
(let H7 \def (eq_ind C c0 (\lambda (c1: C).(getl i c1 (CHead d (Bind Abbr) 
u))) H2 (CHead c k u2) H6) in (nat_ind (\lambda (n: nat).((getl n (CHead c k 
u2) (CHead d (Bind Abbr) u)) \to ((subst0 n u t4 t) \to (pc3 (CHead c k u1) 
t3 t)))) (\lambda (H8: (getl O (CHead c k u2) (CHead d (Bind Abbr) 
u))).(\lambda (H9: (subst0 O u t4 t)).(K_ind (\lambda (k0: K).((clear (CHead 
c k0 u2) (CHead d (Bind Abbr) u)) \to (pc3 (CHead c k0 u1) t3 t))) (\lambda 
(b: B).(\lambda (H10: (clear (CHead c (Bind b) u2) (CHead d (Bind Abbr) 
u))).(let H11 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) 
(CHead d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d 
(Bind Abbr) u) u2 H10)) in ((let H12 \def (f_equal C B (\lambda (e: C).(match 
e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ 
k0 _) \Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind Abbr) u) u2 H10)) in 
((let H13 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead 
d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind 
Abbr) u) u2 H10)) in (\lambda (H14: (eq B Abbr b)).(\lambda (_: (eq C d 
c)).(let H16 \def (eq_ind T u (\lambda (t0: T).(subst0 O t0 t4 t)) H9 u2 H13) 
in (eq_ind B Abbr (\lambda (b0: B).(pc3 (CHead c (Bind b0) u1) t3 t)) 
(ex2_ind T (\lambda (t0: T).(subst0 O u1 t4 t0)) (\lambda (t0: T).(pr0 t t0)) 
(pc3 (CHead c (Bind Abbr) u1) t3 t) (\lambda (x: T).(\lambda (H17: (subst0 O 
u1 t4 x)).(\lambda (H18: (pr0 t x)).(pc3_pr3_t (CHead c (Bind Abbr) u1) t3 x 
(pr3_pr2 (CHead c (Bind Abbr) u1) t3 x (pr2_delta (CHead c (Bind Abbr) u1) c 
u1 O (getl_refl Abbr c u1) t3 t4 H3 x H17)) t (pr3_pr2 (CHead c (Bind Abbr) 
u1) t x (pr2_free (CHead c (Bind Abbr) u1) t x H18)))))) (pr0_subst0_fwd u2 
t4 t O H16 u1 H)) b H14))))) H12)) H11)))) (\lambda (f: F).(\lambda (H10: 
(clear (CHead c (Flat f) u2) (CHead d (Bind Abbr) u))).(clear_pc3_trans 
(CHead d (Bind Abbr) u) t3 t (pc3_pr2_r (CHead d (Bind Abbr) u) t3 t 
(pr2_delta (CHead d (Bind Abbr) u) d u O (getl_refl Abbr d u) t3 t4 H3 t H9)) 
(CHead c (Flat f) u1) (clear_flat c (CHead d (Bind Abbr) u) (clear_gen_flat f 
c (CHead d (Bind Abbr) u) u2 H10) f u1)))) k (getl_gen_O (CHead c k u2) 
(CHead d (Bind Abbr) u) H8)))) (\lambda (i0: nat).(\lambda (IHi: (((getl i0 
(CHead c k u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 t) \to (pc3 
(CHead c k u1) t3 t))))).(\lambda (H8: (getl (S i0) (CHead c k u2) (CHead d 
(Bind Abbr) u))).(\lambda (H9: (subst0 (S i0) u t4 t)).(K_ind (\lambda (k0: 
K).((((getl i0 (CHead c k0 u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 
t) \to (pc3 (CHead c k0 u1) t3 t)))) \to ((getl (r k0 i0) c (CHead d (Bind 
Abbr) u)) \to (pc3 (CHead c k0 u1) t3 t)))) (\lambda (b: B).(\lambda (_: 
(((getl i0 (CHead c (Bind b) u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u 
t4 t) \to (pc3 (CHead c (Bind b) u1) t3 t))))).(\lambda (H10: (getl (r (Bind 
b) i0) c (CHead d (Bind Abbr) u))).(pc3_pr2_r (CHead c (Bind b) u1) t3 t 
(pr2_delta (CHead c (Bind b) u1) d u (S i0) (getl_head (Bind b) i0 c (CHead d 
(Bind Abbr) u) H10 u1) t3 t4 H3 t H9))))) (\lambda (f: F).(\lambda (_: 
(((getl i0 (CHead c (Flat f) u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u 
t4 t) \to (pc3 (CHead c (Flat f) u1) t3 t))))).(\lambda (H10: (getl (r (Flat 
f) i0) c (CHead d (Bind Abbr) u))).(pc3_pr2_r (CHead c (Flat f) u1) t3 t 
(pr2_cflat c t3 t (pr2_delta c d u (r (Flat f) i0) H10 t3 t4 H3 t H9) f 
u1))))) k IHi (getl_gen_S k c (CHead d (Bind Abbr) u) u2 i0 H8)))))) i H7 
H4)))))))))))))) y t1 t2 H1))) H0)))))))).
(* COMMENTS
Initial nodes: 1533
END *)

theorem pc3_pr2_pr2_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u2 u1) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u2 
u1)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (t1: 
T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c0 k t) t1 t2) \to (pc3 
(CHead c0 k t0) t1 t2)))))))) (\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t0: T).(\lambda (t3: T).(\lambda (k: 
K).(\lambda (H1: (pr2 (CHead c0 k t1) t0 t3)).(pc3_pr0_pr2_t t2 t1 H0 c0 t0 
t3 k H1))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H1: (pr0 t1 t2)).(\lambda (t: T).(\lambda (H2: 
(subst0 i u t2 t)).(\lambda (t0: T).(\lambda (t3: T).(\lambda (k: K).(\lambda 
(H3: (pr2 (CHead c0 k t1) t0 t3)).(insert_eq C (CHead c0 k t1) (\lambda (c1: 
C).(pr2 c1 t0 t3)) (\lambda (_: C).(pc3 (CHead c0 k t) t0 t3)) (\lambda (y: 
C).(\lambda (H4: (pr2 y t0 t3)).(pr2_ind (\lambda (c1: C).(\lambda (t4: 
T).(\lambda (t5: T).((eq C c1 (CHead c0 k t1)) \to (pc3 (CHead c0 k t) t4 
t5))))) (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: T).(\lambda (H5: (pr0 
t4 t5)).(\lambda (_: (eq C c1 (CHead c0 k t1))).(pc3_pr2_r (CHead c0 k t) t4 
t5 (pr2_free (CHead c0 k t) t4 t5 H5))))))) (\lambda (c1: C).(\lambda (d0: 
C).(\lambda (u0: T).(\lambda (i0: nat).(\lambda (H5: (getl i0 c1 (CHead d0 
(Bind Abbr) u0))).(\lambda (t4: T).(\lambda (t5: T).(\lambda (H6: (pr0 t4 
t5)).(\lambda (t6: T).(\lambda (H7: (subst0 i0 u0 t5 t6)).(\lambda (H8: (eq C 
c1 (CHead c0 k t1))).(let H9 \def (eq_ind C c1 (\lambda (c2: C).(getl i0 c2 
(CHead d0 (Bind Abbr) u0))) H5 (CHead c0 k t1) H8) in (nat_ind (\lambda (n: 
nat).((getl n (CHead c0 k t1) (CHead d0 (Bind Abbr) u0)) \to ((subst0 n u0 t5 
t6) \to (pc3 (CHead c0 k t) t4 t6)))) (\lambda (H10: (getl O (CHead c0 k t1) 
(CHead d0 (Bind Abbr) u0))).(\lambda (H11: (subst0 O u0 t5 t6)).(K_ind 
(\lambda (k0: K).((clear (CHead c0 k0 t1) (CHead d0 (Bind Abbr) u0)) \to (pc3 
(CHead c0 k0 t) t4 t6))) (\lambda (b: B).(\lambda (H12: (clear (CHead c0 
(Bind b) t1) (CHead d0 (Bind Abbr) u0))).(let H13 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d0 
| (CHead c2 _ _) \Rightarrow c2])) (CHead d0 (Bind Abbr) u0) (CHead c0 (Bind 
b) t1) (clear_gen_bind b c0 (CHead d0 (Bind Abbr) u0) t1 H12)) in ((let H14 
\def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) 
with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abbr])])) (CHead d0 (Bind Abbr) u0) (CHead c0 (Bind b) t1) 
(clear_gen_bind b c0 (CHead d0 (Bind Abbr) u0) t1 H12)) in ((let H15 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t7) \Rightarrow t7])) (CHead d0 (Bind 
Abbr) u0) (CHead c0 (Bind b) t1) (clear_gen_bind b c0 (CHead d0 (Bind Abbr) 
u0) t1 H12)) in (\lambda (H16: (eq B Abbr b)).(\lambda (_: (eq C d0 c0)).(let 
H18 \def (eq_ind T u0 (\lambda (t7: T).(subst0 O t7 t5 t6)) H11 t1 H15) in 
(eq_ind B Abbr (\lambda (b0: B).(pc3 (CHead c0 (Bind b0) t) t4 t6)) (ex2_ind 
T (\lambda (t7: T).(subst0 O t2 t5 t7)) (\lambda (t7: T).(pr0 t6 t7)) (pc3 
(CHead c0 (Bind Abbr) t) t4 t6) (\lambda (x: T).(\lambda (H19: (subst0 O t2 
t5 x)).(\lambda (H20: (pr0 t6 x)).(ex2_ind T (\lambda (t7: T).(subst0 O t t5 
t7)) (\lambda (t7: T).(subst0 (S (plus i O)) u x t7)) (pc3 (CHead c0 (Bind 
Abbr) t) t4 t6) (\lambda (x0: T).(\lambda (H21: (subst0 O t t5 x0)).(\lambda 
(H22: (subst0 (S (plus i O)) u x x0)).(let H23 \def (f_equal nat nat S (plus 
i O) i (sym_eq nat i (plus i O) (plus_n_O i))) in (let H24 \def (eq_ind nat 
(S (plus i O)) (\lambda (n: nat).(subst0 n u x x0)) H22 (S i) H23) in 
(pc3_pr2_u (CHead c0 (Bind Abbr) t) x0 t4 (pr2_delta (CHead c0 (Bind Abbr) t) 
c0 t O (getl_refl Abbr c0 t) t4 t5 H6 x0 H21) t6 (pc3_pr2_x (CHead c0 (Bind 
Abbr) t) x0 t6 (pr2_delta (CHead c0 (Bind Abbr) t) d u (S i) (getl_head (Bind 
Abbr) i c0 (CHead d (Bind Abbr) u) H0 t) t6 x H20 x0 H24)))))))) 
(subst0_subst0_back t5 x t2 O H19 t u i H2))))) (pr0_subst0_fwd t1 t5 t6 O 
H18 t2 H1)) b H16))))) H14)) H13)))) (\lambda (f: F).(\lambda (H12: (clear 
(CHead c0 (Flat f) t1) (CHead d0 (Bind Abbr) u0))).(clear_pc3_trans (CHead d0 
(Bind Abbr) u0) t4 t6 (pc3_pr2_r (CHead d0 (Bind Abbr) u0) t4 t6 (pr2_delta 
(CHead d0 (Bind Abbr) u0) d0 u0 O (getl_refl Abbr d0 u0) t4 t5 H6 t6 H11)) 
(CHead c0 (Flat f) t) (clear_flat c0 (CHead d0 (Bind Abbr) u0) 
(clear_gen_flat f c0 (CHead d0 (Bind Abbr) u0) t1 H12) f t)))) k (getl_gen_O 
(CHead c0 k t1) (CHead d0 (Bind Abbr) u0) H10)))) (\lambda (i1: nat).(\lambda 
(_: (((getl i1 (CHead c0 k t1) (CHead d0 (Bind Abbr) u0)) \to ((subst0 i1 u0 
t5 t6) \to (pc3 (CHead c0 k t) t4 t6))))).(\lambda (H10: (getl (S i1) (CHead 
c0 k t1) (CHead d0 (Bind Abbr) u0))).(\lambda (H11: (subst0 (S i1) u0 t5 
t6)).(K_ind (\lambda (k0: K).((getl (r k0 i1) c0 (CHead d0 (Bind Abbr) u0)) 
\to (pc3 (CHead c0 k0 t) t4 t6))) (\lambda (b: B).(\lambda (H12: (getl (r 
(Bind b) i1) c0 (CHead d0 (Bind Abbr) u0))).(pc3_pr2_r (CHead c0 (Bind b) t) 
t4 t6 (pr2_delta (CHead c0 (Bind b) t) d0 u0 (S i1) (getl_head (Bind b) i1 c0 
(CHead d0 (Bind Abbr) u0) H12 t) t4 t5 H6 t6 H11)))) (\lambda (f: F).(\lambda 
(H12: (getl (r (Flat f) i1) c0 (CHead d0 (Bind Abbr) u0))).(pc3_pr2_r (CHead 
c0 (Flat f) t) t4 t6 (pr2_cflat c0 t4 t6 (pr2_delta c0 d0 u0 (r (Flat f) i1) 
H12 t4 t5 H6 t6 H11) f t)))) k (getl_gen_S k c0 (CHead d0 (Bind Abbr) u0) t1 
i1 H10)))))) i0 H9 H7))))))))))))) y t0 t3 H4))) H3))))))))))))))) c u2 u1 
H)))).
(* COMMENTS
Initial nodes: 1671
END *)

theorem pc3_pr2_pr3_t:
 \forall (c: C).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr3 (CHead c k u2) t1 t2) \to (\forall (u1: T).((pr2 c u2 u1) \to 
(pc3 (CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pr3 (CHead c k u2) t1 t2)).(pr3_ind (CHead c k u2) 
(\lambda (t: T).(\lambda (t0: T).(\forall (u1: T).((pr2 c u2 u1) \to (pc3 
(CHead c k u1) t t0))))) (\lambda (t: T).(\lambda (u1: T).(\lambda (_: (pr2 c 
u2 u1)).(pc3_refl (CHead c k u1) t)))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 (CHead c k u2) t3 t0)).(\lambda (t4: T).(\lambda (_: 
(pr3 (CHead c k u2) t0 t4)).(\lambda (H2: ((\forall (u1: T).((pr2 c u2 u1) 
\to (pc3 (CHead c k u1) t0 t4))))).(\lambda (u1: T).(\lambda (H3: (pr2 c u2 
u1)).(pc3_t t0 (CHead c k u1) t3 (pc3_pr2_pr2_t c u1 u2 H3 t3 t0 k H0) t4 (H2 
u1 H3)))))))))) t1 t2 H)))))).
(* COMMENTS
Initial nodes: 199
END *)

theorem pc3_pr3_pc3_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u2 u1) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pc3 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u2 
u1)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (t1: T).(\forall 
(t2: T).(\forall (k: K).((pc3 (CHead c k t) t1 t2) \to (pc3 (CHead c k t0) t1 
t2))))))) (\lambda (t: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: 
K).(\lambda (H0: (pc3 (CHead c k t) t1 t2)).H0))))) (\lambda (t2: T).(\lambda 
(t1: T).(\lambda (H0: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda (_: (pr3 c t2 
t3)).(\lambda (H2: ((\forall (t4: T).(\forall (t5: T).(\forall (k: K).((pc3 
(CHead c k t2) t4 t5) \to (pc3 (CHead c k t3) t4 t5))))))).(\lambda (t0: 
T).(\lambda (t4: T).(\lambda (k: K).(\lambda (H3: (pc3 (CHead c k t1) t0 
t4)).(H2 t0 t4 k (let H4 \def H3 in (ex2_ind T (\lambda (t: T).(pr3 (CHead c 
k t1) t0 t)) (\lambda (t: T).(pr3 (CHead c k t1) t4 t)) (pc3 (CHead c k t2) 
t0 t4) (\lambda (x: T).(\lambda (H5: (pr3 (CHead c k t1) t0 x)).(\lambda (H6: 
(pr3 (CHead c k t1) t4 x)).(pc3_t x (CHead c k t2) t0 (pc3_pr2_pr3_t c t1 t0 
x k H5 t2 H0) t4 (pc3_s (CHead c k t2) x t4 (pc3_pr2_pr3_t c t1 t4 x k H6 t2 
H0)))))) H4))))))))))))) u2 u1 H)))).
(* COMMENTS
Initial nodes: 319
END *)

theorem pc3_lift:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c e) \to (\forall (t1: T).(\forall (t2: T).((pc3 e t1 t2) \to (pc3 c (lift 
h d t1) (lift h d t2)))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (drop h d c e)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 e t1 
t2)).(let H1 \def H0 in (ex2_ind T (\lambda (t: T).(pr3 e t1 t)) (\lambda (t: 
T).(pr3 e t2 t)) (pc3 c (lift h d t1) (lift h d t2)) (\lambda (x: T).(\lambda 
(H2: (pr3 e t1 x)).(\lambda (H3: (pr3 e t2 x)).(pc3_pr3_t c (lift h d t1) 
(lift h d x) (pr3_lift c e h d H t1 x H2) (lift h d t2) (pr3_lift c e h d H 
t2 x H3))))) H1))))))))).
(* COMMENTS
Initial nodes: 159
END *)

theorem pc3_eta:
 \forall (c: C).(\forall (t: T).(\forall (w: T).(\forall (u: T).((pc3 c t 
(THead (Bind Abst) w u)) \to (\forall (v: T).((pc3 c v w) \to (pc3 c (THead 
(Bind Abst) v (THead (Flat Appl) (TLRef O) (lift (S O) O t))) t)))))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (w: T).(\lambda (u: T).(\lambda (H: 
(pc3 c t (THead (Bind Abst) w u))).(\lambda (v: T).(\lambda (H0: (pc3 c v 
w)).(pc3_t (THead (Bind Abst) w (THead (Flat Appl) (TLRef O) (lift (S O) O 
(THead (Bind Abst) w u)))) c (THead (Bind Abst) v (THead (Flat Appl) (TLRef 
O) (lift (S O) O t))) (pc3_head_21 c v w H0 (Bind Abst) (THead (Flat Appl) 
(TLRef O) (lift (S O) O t)) (THead (Flat Appl) (TLRef O) (lift (S O) O (THead 
(Bind Abst) w u))) (pc3_thin_dx (CHead c (Bind Abst) v) (lift (S O) O t) 
(lift (S O) O (THead (Bind Abst) w u)) (pc3_lift (CHead c (Bind Abst) v) c (S 
O) O (drop_drop (Bind Abst) O c c (drop_refl c) v) t (THead (Bind Abst) w u) 
H) (TLRef O) Appl)) t (pc3_t (THead (Bind Abst) w u) c (THead (Bind Abst) w 
(THead (Flat Appl) (TLRef O) (lift (S O) O (THead (Bind Abst) w u)))) 
(pc3_pr3_r c (THead (Bind Abst) w (THead (Flat Appl) (TLRef O) (lift (S O) O 
(THead (Bind Abst) w u)))) (THead (Bind Abst) w u) (pr3_eta c w u w (pr3_refl 
c w))) t (pc3_s c (THead (Bind Abst) w u) t H))))))))).
(* COMMENTS
Initial nodes: 399
END *)

