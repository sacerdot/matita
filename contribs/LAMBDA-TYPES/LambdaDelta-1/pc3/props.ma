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



include "pc3/defs.ma".

include "pr3/pr3.ma".

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

theorem pc3_pr2_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t2 (pr3_pr2 c t1 t2 H) (pr3_refl c t2))))).

theorem pc3_pr2_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t2 
t1)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t1 (pr3_refl c t1) (pr3_pr2 c t2 t1 H))))).

theorem pc3_pr3_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t2 H (pr3_refl c t2))))).

theorem pc3_pr3_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t2 
t1)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) 
t1 (pr3_refl c t1) H)))).

theorem pc3_pr3_t:
 \forall (c: C).(\forall (t1: T).(\forall (t0: T).((pr3 c t1 t0) \to (\forall 
(t2: T).((pr3 c t2 t0) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t0: T).(\lambda (H: (pr3 c t1 
t0)).(\lambda (t2: T).(\lambda (H0: (pr3 c t2 t0)).(ex_intro2 T (\lambda (t: 
T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) t0 H H0)))))).

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

theorem pc3_refl:
 \forall (c: C).(\forall (t: T).(pc3 c t t))
\def
 \lambda (c: C).(\lambda (t: T).(ex_intro2 T (\lambda (t0: T).(pr3 c t t0)) 
(\lambda (t0: T).(pr3 c t t0)) t (pr3_refl c t) (pr3_refl c t))).

theorem pc3_s:
 \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pc3 c t1 t2) \to (pc3 c 
t2 t1))))
\def
 \lambda (c: C).(\lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc3 c t1 
t2)).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t)) (pc3 c t2 t1) (\lambda (x: T).(\lambda (H1: (pr3 c t1 
x)).(\lambda (H2: (pr3 c t2 x)).(ex_intro2 T (\lambda (t: T).(pr3 c t2 t)) 
(\lambda (t: T).(pr3 c t1 t)) x H2 H1)))) H0))))).

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

theorem pc3_pr2_u2:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall 
(t2: T).((pc3 c t0 t2) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr2 c t0 
t1)).(\lambda (t2: T).(\lambda (H0: (pc3 c t0 t2)).(pc3_t t0 c t1 (pc3_pr2_x 
c t1 t0 H) t2 H0)))))).

theorem pc3_head_12:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u2) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u2) t1 t2)).(pc3_t (THead k u2 t1) c (THead k u1 t1) (pc3_head_1 c 
u1 u2 H k t1) (THead k u2 t2) (pc3_head_2 c u2 t1 t2 k H0))))))))).

theorem pc3_head_21:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u1) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u1) t1 t2)).(pc3_t (THead k u1 t2) c (THead k u1 t1) (pc3_head_2 c 
u1 t1 t2 k H0) (THead k u2 t2) (pc3_head_1 c u1 u2 H k t2))))))))).

theorem pc3_pr0_pr2_t:
 \forall (u1: T).(\forall (u2: T).((pr0 u2 u1) \to (\forall (c: C).(\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u2 u1)).(\lambda (c: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H0: (pr2 
(CHead c k u2) t1 t2)).(let H1 \def (match H0 in pr2 return (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 
(CHead c k u2)) \to ((eq T t t1) \to ((eq T t0 t2) \to (pc3 (CHead c k u1) t1 
t2)))))))) with [(pr2_free c0 t0 t3 H1) \Rightarrow (\lambda (H2: (eq C c0 
(CHead c k u2))).(\lambda (H3: (eq T t0 t1)).(\lambda (H4: (eq T t3 
t2)).(eq_ind C (CHead c k u2) (\lambda (_: C).((eq T t0 t1) \to ((eq T t3 t2) 
\to ((pr0 t0 t3) \to (pc3 (CHead c k u1) t1 t2))))) (\lambda (H5: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to (pc3 
(CHead c k u1) t1 t2)))) (\lambda (H6: (eq T t3 t2)).(eq_ind T t2 (\lambda 
(t: T).((pr0 t1 t) \to (pc3 (CHead c k u1) t1 t2))) (\lambda (H7: (pr0 t1 
t2)).(pc3_pr2_r (CHead c k u1) t1 t2 (pr2_free (CHead c k u1) t1 t2 H7))) t3 
(sym_eq T t3 t2 H6))) t0 (sym_eq T t0 t1 H5))) c0 (sym_eq C c0 (CHead c k u2) 
H2) H3 H4 H1)))) | (pr2_delta c0 d u i H1 t0 t3 H2 t H3) \Rightarrow (\lambda 
(H4: (eq C c0 (CHead c k u2))).(\lambda (H5: (eq T t0 t1)).(\lambda (H6: (eq 
T t t2)).(eq_ind C (CHead c k u2) (\lambda (c1: C).((eq T t0 t1) \to ((eq T t 
t2) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i 
u t3 t) \to (pc3 (CHead c k u1) t1 t2))))))) (\lambda (H7: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t4: T).((eq T t t2) \to ((getl i (CHead c k u2) 
(CHead d (Bind Abbr) u)) \to ((pr0 t4 t3) \to ((subst0 i u t3 t) \to (pc3 
(CHead c k u1) t1 t2)))))) (\lambda (H8: (eq T t t2)).(eq_ind T t2 (\lambda 
(t4: T).((getl i (CHead c k u2) (CHead d (Bind Abbr) u)) \to ((pr0 t1 t3) \to 
((subst0 i u t3 t4) \to (pc3 (CHead c k u1) t1 t2))))) (\lambda (H9: (getl i 
(CHead c k u2) (CHead d (Bind Abbr) u))).(\lambda (H10: (pr0 t1 t3)).(\lambda 
(H11: (subst0 i u t3 t2)).(nat_ind (\lambda (n: nat).((getl n (CHead c k u2) 
(CHead d (Bind Abbr) u)) \to ((subst0 n u t3 t2) \to (pc3 (CHead c k u1) t1 
t2)))) (\lambda (H12: (getl O (CHead c k u2) (CHead d (Bind Abbr) 
u))).(\lambda (H13: (subst0 O u t3 t2)).(K_ind (\lambda (k0: K).((clear 
(CHead c k0 u2) (CHead d (Bind Abbr) u)) \to (pc3 (CHead c k0 u1) t1 t2))) 
(\lambda (b: B).(\lambda (H14: (clear (CHead c (Bind b) u2) (CHead d (Bind 
Abbr) u))).(let H15 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow 
c1])) (CHead d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c 
(CHead d (Bind Abbr) u) u2 H14)) in ((let H16 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | 
(CHead _ k0 _) \Rightarrow (match k0 in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind 
Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind Abbr) u) u2 
H14)) in ((let H17 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t4) \Rightarrow 
t4])) (CHead d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c 
(CHead d (Bind Abbr) u) u2 H14)) in (\lambda (H18: (eq B Abbr b)).(\lambda 
(_: (eq C d c)).(let H20 \def (eq_ind T u (\lambda (t4: T).(subst0 O t4 t3 
t2)) H13 u2 H17) in (eq_ind B Abbr (\lambda (b0: B).(pc3 (CHead c (Bind b0) 
u1) t1 t2)) (ex2_ind T (\lambda (t4: T).(subst0 O u1 t3 t4)) (\lambda (t4: 
T).(pr0 t2 t4)) (pc3 (CHead c (Bind Abbr) u1) t1 t2) (\lambda (x: T).(\lambda 
(H21: (subst0 O u1 t3 x)).(\lambda (H22: (pr0 t2 x)).(pc3_pr3_t (CHead c 
(Bind Abbr) u1) t1 x (pr3_pr2 (CHead c (Bind Abbr) u1) t1 x (pr2_delta (CHead 
c (Bind Abbr) u1) c u1 O (getl_refl Abbr c u1) t1 t3 H10 x H21)) t2 (pr3_pr2 
(CHead c (Bind Abbr) u1) t2 x (pr2_free (CHead c (Bind Abbr) u1) t2 x 
H22)))))) (pr0_subst0_fwd u2 t3 t2 O H20 u1 H)) b H18))))) H16)) H15)))) 
(\lambda (f: F).(\lambda (H14: (clear (CHead c (Flat f) u2) (CHead d (Bind 
Abbr) u))).(clear_pc3_trans (CHead d (Bind Abbr) u) t1 t2 (pc3_pr2_r (CHead d 
(Bind Abbr) u) t1 t2 (pr2_delta (CHead d (Bind Abbr) u) d u O (getl_refl Abbr 
d u) t1 t3 H10 t2 H13)) (CHead c (Flat f) u1) (clear_flat c (CHead d (Bind 
Abbr) u) (clear_gen_flat f c (CHead d (Bind Abbr) u) u2 H14) f u1)))) k 
(getl_gen_O (CHead c k u2) (CHead d (Bind Abbr) u) H12)))) (\lambda (i0: 
nat).(\lambda (IHi: (((getl i0 (CHead c k u2) (CHead d (Bind Abbr) u)) \to 
((subst0 i0 u t3 t2) \to (pc3 (CHead c k u1) t1 t2))))).(\lambda (H12: (getl 
(S i0) (CHead c k u2) (CHead d (Bind Abbr) u))).(\lambda (H13: (subst0 (S i0) 
u t3 t2)).(K_ind (\lambda (k0: K).((((getl i0 (CHead c k0 u2) (CHead d (Bind 
Abbr) u)) \to ((subst0 i0 u t3 t2) \to (pc3 (CHead c k0 u1) t1 t2)))) \to 
((getl (r k0 i0) c (CHead d (Bind Abbr) u)) \to (pc3 (CHead c k0 u1) t1 
t2)))) (\lambda (b: B).(\lambda (_: (((getl i0 (CHead c (Bind b) u2) (CHead d 
(Bind Abbr) u)) \to ((subst0 i0 u t3 t2) \to (pc3 (CHead c (Bind b) u1) t1 
t2))))).(\lambda (H14: (getl (r (Bind b) i0) c (CHead d (Bind Abbr) 
u))).(pc3_pr2_r (CHead c (Bind b) u1) t1 t2 (pr2_delta (CHead c (Bind b) u1) 
d u (S i0) (getl_head (Bind b) i0 c (CHead d (Bind Abbr) u) H14 u1) t1 t3 H10 
t2 H13))))) (\lambda (f: F).(\lambda (_: (((getl i0 (CHead c (Flat f) u2) 
(CHead d (Bind Abbr) u)) \to ((subst0 i0 u t3 t2) \to (pc3 (CHead c (Flat f) 
u1) t1 t2))))).(\lambda (H14: (getl (r (Flat f) i0) c (CHead d (Bind Abbr) 
u))).(pc3_pr2_r (CHead c (Flat f) u1) t1 t2 (pr2_cflat c t1 t2 (pr2_delta c d 
u (r (Flat f) i0) H14 t1 t3 H10 t2 H13) f u1))))) k IHi (getl_gen_S k c 
(CHead d (Bind Abbr) u) u2 i0 H12)))))) i H9 H11)))) t (sym_eq T t t2 H8))) 
t0 (sym_eq T t0 t1 H7))) c0 (sym_eq C c0 (CHead c k u2) H4) H5 H6 H1 H2 
H3))))]) in (H1 (refl_equal C (CHead c k u2)) (refl_equal T t1) (refl_equal T 
t2)))))))))).

theorem pc3_pr2_pr2_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u2 u1) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u2 
u1)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 c) \to ((eq T t u2) 
\to ((eq T t0 u1) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 
(CHead c k u2) t1 t2) \to (pc3 (CHead c k u1) t1 t2)))))))))))) with 
[(pr2_free c0 t1 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: 
(eq T t1 u2)).(\lambda (H3: (eq T t2 u1)).(eq_ind C c (\lambda (_: C).((eq T 
t1 u2) \to ((eq T t2 u1) \to ((pr0 t1 t2) \to (\forall (t3: T).(\forall (t4: 
T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pc3 (CHead c k u1) t3 
t4))))))))) (\lambda (H4: (eq T t1 u2)).(eq_ind T u2 (\lambda (t: T).((eq T 
t2 u1) \to ((pr0 t t2) \to (\forall (t3: T).(\forall (t4: T).(\forall (k: 
K).((pr2 (CHead c k u2) t3 t4) \to (pc3 (CHead c k u1) t3 t4)))))))) (\lambda 
(H5: (eq T t2 u1)).(eq_ind T u1 (\lambda (t: T).((pr0 u2 t) \to (\forall (t3: 
T).(\forall (t4: T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pc3 
(CHead c k u1) t3 t4))))))) (\lambda (H6: (pr0 u2 u1)).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (k: K).(\lambda (H7: (pr2 (CHead c k u2) t0 
t3)).(pc3_pr0_pr2_t u1 u2 H6 c t0 t3 k H7)))))) t2 (sym_eq T t2 u1 H5))) t1 
(sym_eq T t1 u2 H4))) c0 (sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u 
i H0 t1 t2 H1 t H2) \Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq 
T t1 u2)).(\lambda (H5: (eq T t u1)).(eq_ind C c (\lambda (c1: C).((eq T t1 
u2) \to ((eq T t u1) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t1 
t2) \to ((subst0 i u t2 t) \to (\forall (t3: T).(\forall (t4: T).(\forall (k: 
K).((pr2 (CHead c k u2) t3 t4) \to (pc3 (CHead c k u1) t3 t4))))))))))) 
(\lambda (H6: (eq T t1 u2)).(eq_ind T u2 (\lambda (t0: T).((eq T t u1) \to 
((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) 
\to (\forall (t3: T).(\forall (t4: T).(\forall (k: K).((pr2 (CHead c k u2) t3 
t4) \to (pc3 (CHead c k u1) t3 t4)))))))))) (\lambda (H7: (eq T t 
u1)).(eq_ind T u1 (\lambda (t0: T).((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 u2 t2) \to ((subst0 i u t2 t0) \to (\forall (t3: T).(\forall (t4: 
T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pc3 (CHead c k u1) t3 
t4))))))))) (\lambda (H8: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H9: 
(pr0 u2 t2)).(\lambda (H10: (subst0 i u t2 u1)).(\lambda (t0: T).(\lambda 
(t3: T).(\lambda (k: K).(\lambda (H11: (pr2 (CHead c k u2) t0 t3)).(let H12 
\def (match H11 in pr2 return (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: 
T).(\lambda (_: (pr2 c1 t4 t5)).((eq C c1 (CHead c k u2)) \to ((eq T t4 t0) 
\to ((eq T t5 t3) \to (pc3 (CHead c k u1) t0 t3)))))))) with [(pr2_free c1 t4 
t5 H12) \Rightarrow (\lambda (H13: (eq C c1 (CHead c k u2))).(\lambda (H14: 
(eq T t4 t0)).(\lambda (H15: (eq T t5 t3)).(eq_ind C (CHead c k u2) (\lambda 
(_: C).((eq T t4 t0) \to ((eq T t5 t3) \to ((pr0 t4 t5) \to (pc3 (CHead c k 
u1) t0 t3))))) (\lambda (H16: (eq T t4 t0)).(eq_ind T t0 (\lambda (t6: 
T).((eq T t5 t3) \to ((pr0 t6 t5) \to (pc3 (CHead c k u1) t0 t3)))) (\lambda 
(H17: (eq T t5 t3)).(eq_ind T t3 (\lambda (t6: T).((pr0 t0 t6) \to (pc3 
(CHead c k u1) t0 t3))) (\lambda (H18: (pr0 t0 t3)).(pc3_pr2_r (CHead c k u1) 
t0 t3 (pr2_free (CHead c k u1) t0 t3 H18))) t5 (sym_eq T t5 t3 H17))) t4 
(sym_eq T t4 t0 H16))) c1 (sym_eq C c1 (CHead c k u2) H13) H14 H15 H12)))) | 
(pr2_delta c1 d0 u0 i0 H12 t4 t5 H13 t6 H14) \Rightarrow (\lambda (H15: (eq C 
c1 (CHead c k u2))).(\lambda (H16: (eq T t4 t0)).(\lambda (H17: (eq T t6 
t3)).(eq_ind C (CHead c k u2) (\lambda (c2: C).((eq T t4 t0) \to ((eq T t6 
t3) \to ((getl i0 c2 (CHead d0 (Bind Abbr) u0)) \to ((pr0 t4 t5) \to ((subst0 
i0 u0 t5 t6) \to (pc3 (CHead c k u1) t0 t3))))))) (\lambda (H18: (eq T t4 
t0)).(eq_ind T t0 (\lambda (t7: T).((eq T t6 t3) \to ((getl i0 (CHead c k u2) 
(CHead d0 (Bind Abbr) u0)) \to ((pr0 t7 t5) \to ((subst0 i0 u0 t5 t6) \to 
(pc3 (CHead c k u1) t0 t3)))))) (\lambda (H19: (eq T t6 t3)).(eq_ind T t3 
(\lambda (t7: T).((getl i0 (CHead c k u2) (CHead d0 (Bind Abbr) u0)) \to 
((pr0 t0 t5) \to ((subst0 i0 u0 t5 t7) \to (pc3 (CHead c k u1) t0 t3))))) 
(\lambda (H20: (getl i0 (CHead c k u2) (CHead d0 (Bind Abbr) u0))).(\lambda 
(H21: (pr0 t0 t5)).(\lambda (H22: (subst0 i0 u0 t5 t3)).(nat_ind (\lambda (n: 
nat).((getl n (CHead c k u2) (CHead d0 (Bind Abbr) u0)) \to ((subst0 n u0 t5 
t3) \to (pc3 (CHead c k u1) t0 t3)))) (\lambda (H23: (getl O (CHead c k u2) 
(CHead d0 (Bind Abbr) u0))).(\lambda (H24: (subst0 O u0 t5 t3)).(K_ind 
(\lambda (k0: K).((clear (CHead c k0 u2) (CHead d0 (Bind Abbr) u0)) \to (pc3 
(CHead c k0 u1) t0 t3))) (\lambda (b: B).(\lambda (H25: (clear (CHead c (Bind 
b) u2) (CHead d0 (Bind Abbr) u0))).(let H26 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d0 | 
(CHead c2 _ _) \Rightarrow c2])) (CHead d0 (Bind Abbr) u0) (CHead c (Bind b) 
u2) (clear_gen_bind b c (CHead d0 (Bind Abbr) u0) u2 H25)) in ((let H27 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abbr])])) (CHead d0 (Bind Abbr) u0) (CHead c (Bind b) u2) 
(clear_gen_bind b c (CHead d0 (Bind Abbr) u0) u2 H25)) in ((let H28 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t7) \Rightarrow t7])) (CHead d0 (Bind 
Abbr) u0) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d0 (Bind Abbr) u0) 
u2 H25)) in (\lambda (H29: (eq B Abbr b)).(\lambda (_: (eq C d0 c)).(let H31 
\def (eq_ind T u0 (\lambda (t7: T).(subst0 O t7 t5 t3)) H24 u2 H28) in 
(eq_ind B Abbr (\lambda (b0: B).(pc3 (CHead c (Bind b0) u1) t0 t3)) (ex2_ind 
T (\lambda (t7: T).(subst0 O t2 t5 t7)) (\lambda (t7: T).(pr0 t3 t7)) (pc3 
(CHead c (Bind Abbr) u1) t0 t3) (\lambda (x: T).(\lambda (H32: (subst0 O t2 
t5 x)).(\lambda (H33: (pr0 t3 x)).(ex2_ind T (\lambda (t7: T).(subst0 O u1 t5 
t7)) (\lambda (t7: T).(subst0 (S (plus i O)) u x t7)) (pc3 (CHead c (Bind 
Abbr) u1) t0 t3) (\lambda (x0: T).(\lambda (H34: (subst0 O u1 t5 
x0)).(\lambda (H35: (subst0 (S (plus i O)) u x x0)).(let H36 \def (f_equal 
nat nat S (plus i O) i (sym_eq nat i (plus i O) (plus_n_O i))) in (let H37 
\def (eq_ind nat (S (plus i O)) (\lambda (n: nat).(subst0 n u x x0)) H35 (S 
i) H36) in (pc3_pr2_u (CHead c (Bind Abbr) u1) x0 t0 (pr2_delta (CHead c 
(Bind Abbr) u1) c u1 O (getl_refl Abbr c u1) t0 t5 H21 x0 H34) t3 (pc3_pr2_x 
(CHead c (Bind Abbr) u1) x0 t3 (pr2_delta (CHead c (Bind Abbr) u1) d u (S i) 
(getl_head (Bind Abbr) i c (CHead d (Bind Abbr) u) H8 u1) t3 x H33 x0 
H37)))))))) (subst0_subst0_back t5 x t2 O H32 u1 u i H10))))) (pr0_subst0_fwd 
u2 t5 t3 O H31 t2 H9)) b H29))))) H27)) H26)))) (\lambda (f: F).(\lambda 
(H25: (clear (CHead c (Flat f) u2) (CHead d0 (Bind Abbr) 
u0))).(clear_pc3_trans (CHead d0 (Bind Abbr) u0) t0 t3 (pc3_pr2_r (CHead d0 
(Bind Abbr) u0) t0 t3 (pr2_delta (CHead d0 (Bind Abbr) u0) d0 u0 O (getl_refl 
Abbr d0 u0) t0 t5 H21 t3 H24)) (CHead c (Flat f) u1) (clear_flat c (CHead d0 
(Bind Abbr) u0) (clear_gen_flat f c (CHead d0 (Bind Abbr) u0) u2 H25) f 
u1)))) k (getl_gen_O (CHead c k u2) (CHead d0 (Bind Abbr) u0) H23)))) 
(\lambda (i1: nat).(\lambda (_: (((getl i1 (CHead c k u2) (CHead d0 (Bind 
Abbr) u0)) \to ((subst0 i1 u0 t5 t3) \to (pc3 (CHead c k u1) t0 
t3))))).(\lambda (H23: (getl (S i1) (CHead c k u2) (CHead d0 (Bind Abbr) 
u0))).(\lambda (H24: (subst0 (S i1) u0 t5 t3)).(K_ind (\lambda (k0: K).((getl 
(r k0 i1) c (CHead d0 (Bind Abbr) u0)) \to (pc3 (CHead c k0 u1) t0 t3))) 
(\lambda (b: B).(\lambda (H25: (getl (r (Bind b) i1) c (CHead d0 (Bind Abbr) 
u0))).(pc3_pr2_r (CHead c (Bind b) u1) t0 t3 (pr2_delta (CHead c (Bind b) u1) 
d0 u0 (S i1) (getl_head (Bind b) i1 c (CHead d0 (Bind Abbr) u0) H25 u1) t0 t5 
H21 t3 H24)))) (\lambda (f: F).(\lambda (H25: (getl (r (Flat f) i1) c (CHead 
d0 (Bind Abbr) u0))).(pc3_pr2_r (CHead c (Flat f) u1) t0 t3 (pr2_cflat c t0 
t3 (pr2_delta c d0 u0 (r (Flat f) i1) H25 t0 t5 H21 t3 H24) f u1)))) k 
(getl_gen_S k c (CHead d0 (Bind Abbr) u0) u2 i1 H23)))))) i0 H20 H22)))) t6 
(sym_eq T t6 t3 H19))) t4 (sym_eq T t4 t0 H18))) c1 (sym_eq C c1 (CHead c k 
u2) H15) H16 H17 H12 H13 H14))))]) in (H12 (refl_equal C (CHead c k u2)) 
(refl_equal T t0) (refl_equal T t3)))))))))) t (sym_eq T t u1 H7))) t1 
(sym_eq T t1 u2 H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 
(refl_equal C c) (refl_equal T u2) (refl_equal T u1)))))).

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

