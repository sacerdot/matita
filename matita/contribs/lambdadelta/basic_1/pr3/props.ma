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

include "basic_1/pr3/fwd.ma".

include "basic_1/pr3/pr1.ma".

include "basic_1/pr2/props.ma".

include "basic_1/pr1/props.ma".

theorem clear_pr3_trans:
 \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pr3 c2 t1 t2) \to 
(\forall (c1: C).((clear c1 c2) \to (pr3 c1 t1 t2))))))
\def
 \lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c2 t1 
t2)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(pr3_ind c2 (\lambda (t: 
T).(\lambda (t0: T).(pr3 c1 t t0))) (\lambda (t: T).(pr3_refl c1 t)) (\lambda 
(t3: T).(\lambda (t4: T).(\lambda (H1: (pr2 c2 t4 t3)).(\lambda (t5: 
T).(\lambda (_: (pr3 c2 t3 t5)).(\lambda (H3: (pr3 c1 t3 t5)).(pr3_sing c1 t3 
t4 (clear_pr2_trans c2 t4 t3 H1 c1 H0) t5 H3))))))) t1 t2 H)))))).

theorem pr3_pr2:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pr3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(pr3_sing c t2 t1 H t2 (pr3_refl c t2))))).

theorem pr3_t:
 \forall (t2: T).(\forall (t1: T).(\forall (c: C).((pr3 c t1 t2) \to (\forall 
(t3: T).((pr3 c t2 t3) \to (pr3 c t1 t3))))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (c: C).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (t3: T).((pr3 c t0 
t3) \to (pr3 c t t3))))) (\lambda (t: T).(\lambda (t3: T).(\lambda (H0: (pr3 
c t t3)).H0))) (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t3 
t0)).(\lambda (t4: T).(\lambda (_: (pr3 c t0 t4)).(\lambda (H2: ((\forall 
(t5: T).((pr3 c t4 t5) \to (pr3 c t0 t5))))).(\lambda (t5: T).(\lambda (H3: 
(pr3 c t4 t5)).(pr3_sing c t0 t3 H0 t5 (H2 t5 H3)))))))))) t1 t2 H)))).

theorem pr3_thin_dx:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(u: T).(\forall (f: F).(pr3 c (THead (Flat f) u t1) (THead (Flat f) u 
t2)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(\lambda (u: T).(\lambda (f: F).(pr3_ind c (\lambda (t: T).(\lambda (t0: 
T).(pr3 c (THead (Flat f) u t) (THead (Flat f) u t0)))) (\lambda (t: 
T).(pr3_refl c (THead (Flat f) u t))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 c t3 t0)).(\lambda (t4: T).(\lambda (_: (pr3 c t0 
t4)).(\lambda (H2: (pr3 c (THead (Flat f) u t0) (THead (Flat f) u 
t4))).(pr3_sing c (THead (Flat f) u t0) (THead (Flat f) u t3) (pr2_thin_dx c 
t3 t0 H0 u f) (THead (Flat f) u t4) H2))))))) t1 t2 H)))))).

theorem pr3_head_1:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).(pr3 c (THead k u1 t) (THead k u2 t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (k: K).(\forall 
(t1: T).(pr3 c (THead k t t1) (THead k t0 t1)))))) (\lambda (t: T).(\lambda 
(k: K).(\lambda (t0: T).(pr3_refl c (THead k t t0))))) (\lambda (t2: 
T).(\lambda (t1: T).(\lambda (H0: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda 
(_: (pr3 c t2 t3)).(\lambda (H2: ((\forall (k: K).(\forall (t: T).(pr3 c 
(THead k t2 t) (THead k t3 t)))))).(\lambda (k: K).(\lambda (t: T).(pr3_sing 
c (THead k t2 t) (THead k t1 t) (pr2_head_1 c t1 t2 H0 k t) (THead k t3 t) 
(H2 k t)))))))))) u1 u2 H)))).

theorem pr3_head_2:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr3 (CHead c k u) t1 t2) \to (pr3 c (THead k u t1) (THead k u 
t2)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pr3 (CHead c k u) t1 t2)).(pr3_ind (CHead c k u) 
(\lambda (t: T).(\lambda (t0: T).(pr3 c (THead k u t) (THead k u t0)))) 
(\lambda (t: T).(pr3_refl c (THead k u t))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 (CHead c k u) t3 t0)).(\lambda (t4: T).(\lambda (_: 
(pr3 (CHead c k u) t0 t4)).(\lambda (H2: (pr3 c (THead k u t0) (THead k u 
t4))).(pr3_sing c (THead k u t0) (THead k u t3) (pr2_head_2 c u t3 t0 k H0) 
(THead k u t4) H2))))))) t1 t2 H)))))).

theorem pr3_head_21:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c k u1) t1 t2) \to (pr3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 
(CHead c k u1) t1 t2)).(pr3_t (THead k u1 t2) (THead k u1 t1) c (pr3_head_2 c 
u1 t1 t2 k H0) (THead k u2 t2) (pr3_head_1 c u1 u2 H k t2))))))))).

theorem pr3_head_12:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c k u2) t1 t2) \to (pr3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 
(CHead c k u2) t1 t2)).(pr3_t (THead k u2 t1) (THead k u1 t1) c (pr3_head_1 c 
u1 u2 H k t1) (THead k u2 t2) (pr3_head_2 c u2 t1 t2 k H0))))))))).

theorem pr3_cflat:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(f: F).(\forall (v: T).(pr3 (CHead c (Flat f) v) t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (f: F).(\forall (v: 
T).(pr3 (CHead c (Flat f) v) t t0))))) (\lambda (t: T).(\lambda (f: 
F).(\lambda (v: T).(pr3_refl (CHead c (Flat f) v) t)))) (\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H0: (pr2 c t4 t3)).(\lambda (t5: T).(\lambda 
(_: (pr3 c t3 t5)).(\lambda (H2: ((\forall (f: F).(\forall (v: T).(pr3 (CHead 
c (Flat f) v) t3 t5))))).(\lambda (f: F).(\lambda (v: T).(pr3_sing (CHead c 
(Flat f) v) t3 t4 (pr2_cflat c t4 t3 H0 f v) t5 (H2 f v)))))))))) t1 t2 H)))).

theorem pr3_flat:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall (f: F).(pr3 c (THead 
(Flat f) u1 t1) (THead (Flat f) u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).(\lambda 
(f: F).(pr3_head_12 c u1 u2 H (Flat f) t1 t2 (pr3_cflat c t1 t2 H0 f 
u2))))))))).

theorem pr3_pr0_pr2_t:
 \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (c: C).(\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pr3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u1 u2)).(\lambda (c: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H0: (pr2 
(CHead c k u2) t1 t2)).(insert_eq C (CHead c k u2) (\lambda (c0: C).(pr2 c0 
t1 t2)) (\lambda (_: C).(pr3 (CHead c k u1) t1 t2)) (\lambda (y: C).(\lambda 
(H1: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).((eq C c0 (CHead c k u2)) \to (pr3 (CHead c k u1) t t0))))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (_: 
(eq C c0 (CHead c k u2))).(pr3_pr2 (CHead c k u1) t3 t4 (pr2_free (CHead c k 
u1) t3 t4 H2))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H2: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H4: 
(subst0 i u t4 t)).(\lambda (H5: (eq C c0 (CHead c k u2))).(let H6 \def 
(eq_ind C c0 (\lambda (c1: C).(getl i c1 (CHead d (Bind Abbr) u))) H2 (CHead 
c k u2) H5) in (nat_ind (\lambda (n: nat).((getl n (CHead c k u2) (CHead d 
(Bind Abbr) u)) \to ((subst0 n u t4 t) \to (pr3 (CHead c k u1) t3 t)))) 
(\lambda (H7: (getl O (CHead c k u2) (CHead d (Bind Abbr) u))).(\lambda (H8: 
(subst0 O u t4 t)).(K_ind (\lambda (k0: K).((getl O (CHead c k0 u2) (CHead d 
(Bind Abbr) u)) \to (pr3 (CHead c k0 u1) t3 t))) (\lambda (b: B).(\lambda 
(H9: (getl O (CHead c (Bind b) u2) (CHead d (Bind Abbr) u))).(let H10 \def 
(f_equal C C (\lambda (e: C).(match e with [(CSort _) \Rightarrow d | (CHead 
c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u) (CHead c (Bind b) u2) 
(clear_gen_bind b c (CHead d (Bind Abbr) u) u2 (getl_gen_O (CHead c (Bind b) 
u2) (CHead d (Bind Abbr) u) H9))) in ((let H11 \def (f_equal C B (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow 
(match k0 with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) 
(CHead d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d 
(Bind Abbr) u) u2 (getl_gen_O (CHead c (Bind b) u2) (CHead d (Bind Abbr) u) 
H9))) in ((let H12 \def (f_equal C T (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind Abbr) u) u2 
(getl_gen_O (CHead c (Bind b) u2) (CHead d (Bind Abbr) u) H9))) in (\lambda 
(H13: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H15 \def (eq_ind T u 
(\lambda (t0: T).(subst0 O t0 t4 t)) H8 u2 H12) in (eq_ind B Abbr (\lambda 
(b0: B).(pr3 (CHead c (Bind b0) u1) t3 t)) (ex2_ind T (\lambda (t0: 
T).(subst0 O u1 t4 t0)) (\lambda (t0: T).(pr0 t0 t)) (pr3 (CHead c (Bind 
Abbr) u1) t3 t) (\lambda (x: T).(\lambda (H16: (subst0 O u1 t4 x)).(\lambda 
(H17: (pr0 x t)).(pr3_sing (CHead c (Bind Abbr) u1) x t3 (pr2_delta (CHead c 
(Bind Abbr) u1) c u1 O (getl_refl Abbr c u1) t3 t4 H3 x H16) t (pr3_pr2 
(CHead c (Bind Abbr) u1) x t (pr2_free (CHead c (Bind Abbr) u1) x t H17)))))) 
(pr0_subst0_back u2 t4 t O H15 u1 H)) b H13))))) H11)) H10)))) (\lambda (f: 
F).(\lambda (H9: (getl O (CHead c (Flat f) u2) (CHead d (Bind Abbr) 
u))).(pr3_pr2 (CHead c (Flat f) u1) t3 t (pr2_cflat c t3 t (pr2_delta c d u O 
(getl_intro O c (CHead d (Bind Abbr) u) c (drop_refl c) (clear_gen_flat f c 
(CHead d (Bind Abbr) u) u2 (getl_gen_O (CHead c (Flat f) u2) (CHead d (Bind 
Abbr) u) H9))) t3 t4 H3 t H8) f u1)))) k H7))) (\lambda (i0: nat).(\lambda 
(IHi: (((getl i0 (CHead c k u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 
t) \to (pr3 (CHead c k u1) t3 t))))).(\lambda (H7: (getl (S i0) (CHead c k 
u2) (CHead d (Bind Abbr) u))).(\lambda (H8: (subst0 (S i0) u t4 t)).(K_ind 
(\lambda (k0: K).((getl (S i0) (CHead c k0 u2) (CHead d (Bind Abbr) u)) \to 
((((getl i0 (CHead c k0 u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 t) 
\to (pr3 (CHead c k0 u1) t3 t)))) \to (pr3 (CHead c k0 u1) t3 t)))) (\lambda 
(b: B).(\lambda (H9: (getl (S i0) (CHead c (Bind b) u2) (CHead d (Bind Abbr) 
u))).(\lambda (_: (((getl i0 (CHead c (Bind b) u2) (CHead d (Bind Abbr) u)) 
\to ((subst0 i0 u t4 t) \to (pr3 (CHead c (Bind b) u1) t3 t))))).(pr3_pr2 
(CHead c (Bind b) u1) t3 t (pr2_delta (CHead c (Bind b) u1) d u (S i0) 
(getl_head (Bind b) i0 c (CHead d (Bind Abbr) u) (getl_gen_S (Bind b) c 
(CHead d (Bind Abbr) u) u2 i0 H9) u1) t3 t4 H3 t H8))))) (\lambda (f: 
F).(\lambda (H9: (getl (S i0) (CHead c (Flat f) u2) (CHead d (Bind Abbr) 
u))).(\lambda (_: (((getl i0 (CHead c (Flat f) u2) (CHead d (Bind Abbr) u)) 
\to ((subst0 i0 u t4 t) \to (pr3 (CHead c (Flat f) u1) t3 t))))).(pr3_pr2 
(CHead c (Flat f) u1) t3 t (pr2_cflat c t3 t (pr2_delta c d u (r (Flat f) i0) 
(getl_gen_S (Flat f) c (CHead d (Bind Abbr) u) u2 i0 H9) t3 t4 H3 t H8) f 
u1))))) k H7 IHi))))) i H6 H4))))))))))))) y t1 t2 H1))) H0)))))))).

theorem pr3_pr2_pr2_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u1 u2) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pr3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u1 
u2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (t1: 
T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c0 k t0) t1 t2) \to (pr3 
(CHead c0 k t) t1 t2)))))))) (\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t0: T).(\lambda (t3: T).(\lambda (k: 
K).(\lambda (H1: (pr2 (CHead c0 k t2) t0 t3)).(pr3_pr0_pr2_t t1 t2 H0 c0 t0 
t3 k H1))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H1: (pr0 t1 t2)).(\lambda (t: T).(\lambda (H2: 
(subst0 i u t2 t)).(\lambda (t0: T).(\lambda (t3: T).(\lambda (k: K).(\lambda 
(H3: (pr2 (CHead c0 k t) t0 t3)).(insert_eq C (CHead c0 k t) (\lambda (c1: 
C).(pr2 c1 t0 t3)) (\lambda (_: C).(pr3 (CHead c0 k t1) t0 t3)) (\lambda (y: 
C).(\lambda (H4: (pr2 y t0 t3)).(pr2_ind (\lambda (c1: C).(\lambda (t4: 
T).(\lambda (t5: T).((eq C c1 (CHead c0 k t)) \to (pr3 (CHead c0 k t1) t4 
t5))))) (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: T).(\lambda (H5: (pr0 
t4 t5)).(\lambda (_: (eq C c1 (CHead c0 k t))).(pr3_pr2 (CHead c0 k t1) t4 t5 
(pr2_free (CHead c0 k t1) t4 t5 H5))))))) (\lambda (c1: C).(\lambda (d0: 
C).(\lambda (u0: T).(\lambda (i0: nat).(\lambda (H5: (getl i0 c1 (CHead d0 
(Bind Abbr) u0))).(\lambda (t4: T).(\lambda (t5: T).(\lambda (H6: (pr0 t4 
t5)).(\lambda (t6: T).(\lambda (H7: (subst0 i0 u0 t5 t6)).(\lambda (H8: (eq C 
c1 (CHead c0 k t))).(let H9 \def (eq_ind C c1 (\lambda (c2: C).(getl i0 c2 
(CHead d0 (Bind Abbr) u0))) H5 (CHead c0 k t) H8) in (nat_ind (\lambda (n: 
nat).((getl n (CHead c0 k t) (CHead d0 (Bind Abbr) u0)) \to ((subst0 n u0 t5 
t6) \to (pr3 (CHead c0 k t1) t4 t6)))) (\lambda (H10: (getl O (CHead c0 k t) 
(CHead d0 (Bind Abbr) u0))).(\lambda (H11: (subst0 O u0 t5 t6)).(K_ind 
(\lambda (k0: K).((clear (CHead c0 k0 t) (CHead d0 (Bind Abbr) u0)) \to (pr3 
(CHead c0 k0 t1) t4 t6))) (\lambda (b: B).(\lambda (H12: (clear (CHead c0 
(Bind b) t) (CHead d0 (Bind Abbr) u0))).(let H13 \def (f_equal C C (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow d0 | (CHead c2 _ _) \Rightarrow 
c2])) (CHead d0 (Bind Abbr) u0) (CHead c0 (Bind b) t) (clear_gen_bind b c0 
(CHead d0 (Bind Abbr) u0) t H12)) in ((let H14 \def (f_equal C B (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow 
(match k0 with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) 
(CHead d0 (Bind Abbr) u0) (CHead c0 (Bind b) t) (clear_gen_bind b c0 (CHead 
d0 (Bind Abbr) u0) t H12)) in ((let H15 \def (f_equal C T (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t7) \Rightarrow t7])) 
(CHead d0 (Bind Abbr) u0) (CHead c0 (Bind b) t) (clear_gen_bind b c0 (CHead 
d0 (Bind Abbr) u0) t H12)) in (\lambda (H16: (eq B Abbr b)).(\lambda (_: (eq 
C d0 c0)).(let H18 \def (eq_ind T u0 (\lambda (t7: T).(subst0 O t7 t5 t6)) 
H11 t H15) in (eq_ind B Abbr (\lambda (b0: B).(pr3 (CHead c0 (Bind b0) t1) t4 
t6)) (ex2_ind T (\lambda (t7: T).(subst0 O t2 t5 t7)) (\lambda (t7: 
T).(subst0 (S (plus i O)) u t7 t6)) (pr3 (CHead c0 (Bind Abbr) t1) t4 t6) 
(\lambda (x: T).(\lambda (H19: (subst0 O t2 t5 x)).(\lambda (H20: (subst0 (S 
(plus i O)) u x t6)).(let H21 \def (f_equal nat nat S (plus i O) i (sym_eq 
nat i (plus i O) (plus_n_O i))) in (let H22 \def (eq_ind nat (S (plus i O)) 
(\lambda (n: nat).(subst0 n u x t6)) H20 (S i) H21) in (ex2_ind T (\lambda 
(t7: T).(subst0 O t1 t5 t7)) (\lambda (t7: T).(pr0 t7 x)) (pr3 (CHead c0 
(Bind Abbr) t1) t4 t6) (\lambda (x0: T).(\lambda (H23: (subst0 O t1 t5 
x0)).(\lambda (H24: (pr0 x0 x)).(pr3_sing (CHead c0 (Bind Abbr) t1) x0 t4 
(pr2_delta (CHead c0 (Bind Abbr) t1) c0 t1 O (getl_refl Abbr c0 t1) t4 t5 H6 
x0 H23) t6 (pr3_pr2 (CHead c0 (Bind Abbr) t1) x0 t6 (pr2_delta (CHead c0 
(Bind Abbr) t1) d u (S i) (getl_clear_bind Abbr (CHead c0 (Bind Abbr) t1) c0 
t1 (clear_bind Abbr c0 t1) (CHead d (Bind Abbr) u) i H0) x0 x H24 t6 
H22)))))) (pr0_subst0_back t2 t5 x O H19 t1 H1))))))) (subst0_subst0 t5 t6 t 
O H18 t2 u i H2)) b H16))))) H14)) H13)))) (\lambda (f: F).(\lambda (H12: 
(clear (CHead c0 (Flat f) t) (CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c0 
(Flat f) t1) t4 t6 (pr2_cflat c0 t4 t6 (pr2_delta c0 d0 u0 O (getl_intro O c0 
(CHead d0 (Bind Abbr) u0) c0 (drop_refl c0) (clear_gen_flat f c0 (CHead d0 
(Bind Abbr) u0) t H12)) t4 t5 H6 t6 H11) f t1)))) k (getl_gen_O (CHead c0 k 
t) (CHead d0 (Bind Abbr) u0) H10)))) (\lambda (i1: nat).(\lambda (_: (((getl 
i1 (CHead c0 k t) (CHead d0 (Bind Abbr) u0)) \to ((subst0 i1 u0 t5 t6) \to 
(pr3 (CHead c0 k t1) t4 t6))))).(\lambda (H10: (getl (S i1) (CHead c0 k t) 
(CHead d0 (Bind Abbr) u0))).(\lambda (H11: (subst0 (S i1) u0 t5 t6)).(K_ind 
(\lambda (k0: K).((getl (S i1) (CHead c0 k0 t) (CHead d0 (Bind Abbr) u0)) \to 
(pr3 (CHead c0 k0 t1) t4 t6))) (\lambda (b: B).(\lambda (H12: (getl (S i1) 
(CHead c0 (Bind b) t) (CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c0 (Bind b) 
t1) t4 t6 (pr2_delta (CHead c0 (Bind b) t1) d0 u0 (S i1) (getl_head (Bind b) 
i1 c0 (CHead d0 (Bind Abbr) u0) (getl_gen_S (Bind b) c0 (CHead d0 (Bind Abbr) 
u0) t i1 H12) t1) t4 t5 H6 t6 H11)))) (\lambda (f: F).(\lambda (H12: (getl (S 
i1) (CHead c0 (Flat f) t) (CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c0 
(Flat f) t1) t4 t6 (pr2_cflat c0 t4 t6 (pr2_delta c0 d0 u0 (r (Flat f) i1) 
(getl_gen_S (Flat f) c0 (CHead d0 (Bind Abbr) u0) t i1 H12) t4 t5 H6 t6 H11) 
f t1)))) k H10))))) i0 H9 H7))))))))))))) y t0 t3 H4))) H3))))))))))))))) c 
u1 u2 H)))).

theorem pr3_pr2_pr3_t:
 \forall (c: C).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr3 (CHead c k u2) t1 t2) \to (\forall (u1: T).((pr2 c u1 u2) \to 
(pr3 (CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pr3 (CHead c k u2) t1 t2)).(pr3_ind (CHead c k u2) 
(\lambda (t: T).(\lambda (t0: T).(\forall (u1: T).((pr2 c u1 u2) \to (pr3 
(CHead c k u1) t t0))))) (\lambda (t: T).(\lambda (u1: T).(\lambda (_: (pr2 c 
u1 u2)).(pr3_refl (CHead c k u1) t)))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 (CHead c k u2) t3 t0)).(\lambda (t4: T).(\lambda (_: 
(pr3 (CHead c k u2) t0 t4)).(\lambda (H2: ((\forall (u1: T).((pr2 c u1 u2) 
\to (pr3 (CHead c k u1) t0 t4))))).(\lambda (u1: T).(\lambda (H3: (pr2 c u1 
u2)).(pr3_t t0 t3 (CHead c k u1) (pr3_pr2_pr2_t c u1 u2 H3 t3 t0 k H0) t4 (H2 
u1 H3)))))))))) t1 t2 H)))))).

theorem pr3_pr3_pr3_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u1 u2) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr3 (CHead c k u2) t1 t2) \to (pr3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u1 
u2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (t1: T).(\forall 
(t2: T).(\forall (k: K).((pr3 (CHead c k t0) t1 t2) \to (pr3 (CHead c k t) t1 
t2))))))) (\lambda (t: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: 
K).(\lambda (H0: (pr3 (CHead c k t) t1 t2)).H0))))) (\lambda (t2: T).(\lambda 
(t1: T).(\lambda (H0: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda (_: (pr3 c t2 
t3)).(\lambda (H2: ((\forall (t4: T).(\forall (t5: T).(\forall (k: K).((pr3 
(CHead c k t3) t4 t5) \to (pr3 (CHead c k t2) t4 t5))))))).(\lambda (t0: 
T).(\lambda (t4: T).(\lambda (k: K).(\lambda (H3: (pr3 (CHead c k t3) t0 
t4)).(pr3_pr2_pr3_t c t2 t0 t4 k (H2 t0 t4 k H3) t1 H0))))))))))) u1 u2 H)))).

theorem pr3_lift:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c e) \to (\forall (t1: T).(\forall (t2: T).((pr3 e t1 t2) \to (pr3 c (lift 
h d t1) (lift h d t2)))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (drop h d c e)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 e t1 
t2)).(pr3_ind e (\lambda (t: T).(\lambda (t0: T).(pr3 c (lift h d t) (lift h 
d t0)))) (\lambda (t: T).(pr3_refl c (lift h d t))) (\lambda (t0: T).(\lambda 
(t3: T).(\lambda (H1: (pr2 e t3 t0)).(\lambda (t4: T).(\lambda (_: (pr3 e t0 
t4)).(\lambda (H3: (pr3 c (lift h d t0) (lift h d t4))).(pr3_sing c (lift h d 
t0) (lift h d t3) (pr2_lift c e h d H t3 t0 H1) (lift h d t4) H3))))))) t1 t2 
H0)))))))).

theorem pr3_eta:
 \forall (c: C).(\forall (w: T).(\forall (u: T).(let t \def (THead (Bind 
Abst) w u) in (\forall (v: T).((pr3 c v w) \to (pr3 c (THead (Bind Abst) v 
(THead (Flat Appl) (TLRef O) (lift (S O) O t))) t))))))
\def
 \lambda (c: C).(\lambda (w: T).(\lambda (u: T).(let t \def (THead (Bind 
Abst) w u) in (\lambda (v: T).(\lambda (H: (pr3 c v w)).(eq_ind_r T (THead 
(Bind Abst) (lift (S O) O w) (lift (S O) (S O) u)) (\lambda (t0: T).(pr3 c 
(THead (Bind Abst) v (THead (Flat Appl) (TLRef O) t0)) (THead (Bind Abst) w 
u))) (pr3_head_12 c v w H (Bind Abst) (THead (Flat Appl) (TLRef O) (THead 
(Bind Abst) (lift (S O) O w) (lift (S O) (S O) u))) u (pr3_pr1 (THead (Flat 
Appl) (TLRef O) (THead (Bind Abst) (lift (S O) O w) (lift (S O) (S O) u))) u 
(pr1_sing (THead (Bind Abbr) (TLRef O) (lift (S O) (S O) u)) (THead (Flat 
Appl) (TLRef O) (THead (Bind Abst) (lift (S O) O w) (lift (S O) (S O) u))) 
(pr0_beta (lift (S O) O w) (TLRef O) (TLRef O) (pr0_refl (TLRef O)) (lift (S 
O) (S O) u) (lift (S O) (S O) u) (pr0_refl (lift (S O) (S O) u))) u (pr1_sing 
(THead (Bind Abbr) (TLRef O) (lift (S O) O u)) (THead (Bind Abbr) (TLRef O) 
(lift (S O) (S O) u)) (pr0_delta1 (TLRef O) (TLRef O) (pr0_refl (TLRef O)) 
(lift (S O) (S O) u) (lift (S O) (S O) u) (pr0_refl (lift (S O) (S O) u)) 
(lift (S O) O u) (subst1_lift_S u O O (le_O_n O))) u (pr1_pr0 (THead (Bind 
Abbr) (TLRef O) (lift (S O) O u)) u (pr0_zeta Abbr not_abbr_abst u u 
(pr0_refl u) (TLRef O))))) (CHead c (Bind Abst) w))) (lift (S O) O (THead 
(Bind Abst) w u)) (lift_bind Abst w u (S O) O))))))).

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
\def (match (H (refl_equal B Abst)) in False with []) in H1))))))) (\lambda 
(_: (not (eq B Void Abst))).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: 
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

