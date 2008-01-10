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



include "pr3/pr1.ma".

include "pr2/props.ma".

include "pr1/props.ma".

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
(CHead c k u2) t1 t2)).(let H1 \def (match H0 in pr2 return (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 
(CHead c k u2)) \to ((eq T t t1) \to ((eq T t0 t2) \to (pr3 (CHead c k u1) t1 
t2)))))))) with [(pr2_free c0 t0 t3 H1) \Rightarrow (\lambda (H2: (eq C c0 
(CHead c k u2))).(\lambda (H3: (eq T t0 t1)).(\lambda (H4: (eq T t3 
t2)).(eq_ind C (CHead c k u2) (\lambda (_: C).((eq T t0 t1) \to ((eq T t3 t2) 
\to ((pr0 t0 t3) \to (pr3 (CHead c k u1) t1 t2))))) (\lambda (H5: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to (pr3 
(CHead c k u1) t1 t2)))) (\lambda (H6: (eq T t3 t2)).(eq_ind T t2 (\lambda 
(t: T).((pr0 t1 t) \to (pr3 (CHead c k u1) t1 t2))) (\lambda (H7: (pr0 t1 
t2)).(pr3_pr2 (CHead c k u1) t1 t2 (pr2_free (CHead c k u1) t1 t2 H7))) t3 
(sym_eq T t3 t2 H6))) t0 (sym_eq T t0 t1 H5))) c0 (sym_eq C c0 (CHead c k u2) 
H2) H3 H4 H1)))) | (pr2_delta c0 d u i H1 t0 t3 H2 t H3) \Rightarrow (\lambda 
(H4: (eq C c0 (CHead c k u2))).(\lambda (H5: (eq T t0 t1)).(\lambda (H6: (eq 
T t t2)).(eq_ind C (CHead c k u2) (\lambda (c1: C).((eq T t0 t1) \to ((eq T t 
t2) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i 
u t3 t) \to (pr3 (CHead c k u1) t1 t2))))))) (\lambda (H7: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t4: T).((eq T t t2) \to ((getl i (CHead c k u2) 
(CHead d (Bind Abbr) u)) \to ((pr0 t4 t3) \to ((subst0 i u t3 t) \to (pr3 
(CHead c k u1) t1 t2)))))) (\lambda (H8: (eq T t t2)).(eq_ind T t2 (\lambda 
(t4: T).((getl i (CHead c k u2) (CHead d (Bind Abbr) u)) \to ((pr0 t1 t3) \to 
((subst0 i u t3 t4) \to (pr3 (CHead c k u1) t1 t2))))) (\lambda (H9: (getl i 
(CHead c k u2) (CHead d (Bind Abbr) u))).(\lambda (H10: (pr0 t1 t3)).(\lambda 
(H11: (subst0 i u t3 t2)).(nat_ind (\lambda (n: nat).((getl n (CHead c k u2) 
(CHead d (Bind Abbr) u)) \to ((subst0 n u t3 t2) \to (pr3 (CHead c k u1) t1 
t2)))) (\lambda (H12: (getl O (CHead c k u2) (CHead d (Bind Abbr) 
u))).(\lambda (H13: (subst0 O u t3 t2)).(K_ind (\lambda (k0: K).((getl O 
(CHead c k0 u2) (CHead d (Bind Abbr) u)) \to (pr3 (CHead c k0 u1) t1 t2))) 
(\lambda (b: B).(\lambda (H14: (getl O (CHead c (Bind b) u2) (CHead d (Bind 
Abbr) u))).(let H15 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow 
c1])) (CHead d (Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c 
(CHead d (Bind Abbr) u) u2 (getl_gen_O (CHead c (Bind b) u2) (CHead d (Bind 
Abbr) u) H14))) in ((let H16 \def (f_equal C B (\lambda (e: C).(match e in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) 
\Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind Abbr) u) u2 
(getl_gen_O (CHead c (Bind b) u2) (CHead d (Bind Abbr) u) H14))) in ((let H17 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t4) \Rightarrow t4])) (CHead d 
(Bind Abbr) u) (CHead c (Bind b) u2) (clear_gen_bind b c (CHead d (Bind Abbr) 
u) u2 (getl_gen_O (CHead c (Bind b) u2) (CHead d (Bind Abbr) u) H14))) in 
(\lambda (H18: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H20 \def (eq_ind 
T u (\lambda (t4: T).(subst0 O t4 t3 t2)) H13 u2 H17) in (eq_ind B Abbr 
(\lambda (b0: B).(pr3 (CHead c (Bind b0) u1) t1 t2)) (ex2_ind T (\lambda (t4: 
T).(subst0 O u1 t3 t4)) (\lambda (t4: T).(pr0 t4 t2)) (pr3 (CHead c (Bind 
Abbr) u1) t1 t2) (\lambda (x: T).(\lambda (H21: (subst0 O u1 t3 x)).(\lambda 
(H22: (pr0 x t2)).(pr3_sing (CHead c (Bind Abbr) u1) x t1 (pr2_delta (CHead c 
(Bind Abbr) u1) c u1 O (getl_refl Abbr c u1) t1 t3 H10 x H21) t2 (pr3_pr2 
(CHead c (Bind Abbr) u1) x t2 (pr2_free (CHead c (Bind Abbr) u1) x t2 
H22)))))) (pr0_subst0_back u2 t3 t2 O H20 u1 H)) b H18))))) H16)) H15)))) 
(\lambda (f: F).(\lambda (H14: (getl O (CHead c (Flat f) u2) (CHead d (Bind 
Abbr) u))).(pr3_pr2 (CHead c (Flat f) u1) t1 t2 (pr2_cflat c t1 t2 (pr2_delta 
c d u O (getl_intro O c (CHead d (Bind Abbr) u) c (drop_refl c) 
(clear_gen_flat f c (CHead d (Bind Abbr) u) u2 (getl_gen_O (CHead c (Flat f) 
u2) (CHead d (Bind Abbr) u) H14))) t1 t3 H10 t2 H13) f u1)))) k H12))) 
(\lambda (i0: nat).(\lambda (IHi: (((getl i0 (CHead c k u2) (CHead d (Bind 
Abbr) u)) \to ((subst0 i0 u t3 t2) \to (pr3 (CHead c k u1) t1 
t2))))).(\lambda (H12: (getl (S i0) (CHead c k u2) (CHead d (Bind Abbr) 
u))).(\lambda (H13: (subst0 (S i0) u t3 t2)).(K_ind (\lambda (k0: K).((getl 
(S i0) (CHead c k0 u2) (CHead d (Bind Abbr) u)) \to ((((getl i0 (CHead c k0 
u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t3 t2) \to (pr3 (CHead c k0 
u1) t1 t2)))) \to (pr3 (CHead c k0 u1) t1 t2)))) (\lambda (b: B).(\lambda 
(H14: (getl (S i0) (CHead c (Bind b) u2) (CHead d (Bind Abbr) u))).(\lambda 
(_: (((getl i0 (CHead c (Bind b) u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 
u t3 t2) \to (pr3 (CHead c (Bind b) u1) t1 t2))))).(pr3_pr2 (CHead c (Bind b) 
u1) t1 t2 (pr2_delta (CHead c (Bind b) u1) d u (S i0) (getl_head (Bind b) i0 
c (CHead d (Bind Abbr) u) (getl_gen_S (Bind b) c (CHead d (Bind Abbr) u) u2 
i0 H14) u1) t1 t3 H10 t2 H13))))) (\lambda (f: F).(\lambda (H14: (getl (S i0) 
(CHead c (Flat f) u2) (CHead d (Bind Abbr) u))).(\lambda (_: (((getl i0 
(CHead c (Flat f) u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t3 t2) \to 
(pr3 (CHead c (Flat f) u1) t1 t2))))).(pr3_pr2 (CHead c (Flat f) u1) t1 t2 
(pr2_cflat c t1 t2 (pr2_delta c d u (r (Flat f) i0) (getl_gen_S (Flat f) c 
(CHead d (Bind Abbr) u) u2 i0 H14) t1 t3 H10 t2 H13) f u1))))) k H12 IHi))))) 
i H9 H11)))) t (sym_eq T t t2 H8))) t0 (sym_eq T t0 t1 H7))) c0 (sym_eq C c0 
(CHead c k u2) H4) H5 H6 H1 H2 H3))))]) in (H1 (refl_equal C (CHead c k u2)) 
(refl_equal T t1) (refl_equal T t2)))))))))).

theorem pr3_pr2_pr2_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u1 u2) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pr3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u1 
u2)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 c) \to ((eq T t u1) 
\to ((eq T t0 u2) \to (\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 
(CHead c k u2) t1 t2) \to (pr3 (CHead c k u1) t1 t2)))))))))))) with 
[(pr2_free c0 t1 t2 H0) \Rightarrow (\lambda (H1: (eq C c0 c)).(\lambda (H2: 
(eq T t1 u1)).(\lambda (H3: (eq T t2 u2)).(eq_ind C c (\lambda (_: C).((eq T 
t1 u1) \to ((eq T t2 u2) \to ((pr0 t1 t2) \to (\forall (t3: T).(\forall (t4: 
T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pr3 (CHead c k u1) t3 
t4))))))))) (\lambda (H4: (eq T t1 u1)).(eq_ind T u1 (\lambda (t: T).((eq T 
t2 u2) \to ((pr0 t t2) \to (\forall (t3: T).(\forall (t4: T).(\forall (k: 
K).((pr2 (CHead c k u2) t3 t4) \to (pr3 (CHead c k u1) t3 t4)))))))) (\lambda 
(H5: (eq T t2 u2)).(eq_ind T u2 (\lambda (t: T).((pr0 u1 t) \to (\forall (t3: 
T).(\forall (t4: T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pr3 
(CHead c k u1) t3 t4))))))) (\lambda (H6: (pr0 u1 u2)).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (k: K).(\lambda (H7: (pr2 (CHead c k u2) t3 
t4)).(pr3_pr0_pr2_t u1 u2 H6 c t3 t4 k H7)))))) t2 (sym_eq T t2 u2 H5))) t1 
(sym_eq T t1 u1 H4))) c0 (sym_eq C c0 c H1) H2 H3 H0)))) | (pr2_delta c0 d u 
i H0 t1 t2 H1 t H2) \Rightarrow (\lambda (H3: (eq C c0 c)).(\lambda (H4: (eq 
T t1 u1)).(\lambda (H5: (eq T t u2)).(eq_ind C c (\lambda (c1: C).((eq T t1 
u1) \to ((eq T t u2) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t1 
t2) \to ((subst0 i u t2 t) \to (\forall (t3: T).(\forall (t4: T).(\forall (k: 
K).((pr2 (CHead c k u2) t3 t4) \to (pr3 (CHead c k u1) t3 t4))))))))))) 
(\lambda (H6: (eq T t1 u1)).(eq_ind T u1 (\lambda (t0: T).((eq T t u2) \to 
((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t2) \to ((subst0 i u t2 t) 
\to (\forall (t3: T).(\forall (t4: T).(\forall (k: K).((pr2 (CHead c k u2) t3 
t4) \to (pr3 (CHead c k u1) t3 t4)))))))))) (\lambda (H7: (eq T t 
u2)).(eq_ind T u2 (\lambda (t0: T).((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 u1 t2) \to ((subst0 i u t2 t0) \to (\forall (t3: T).(\forall (t4: 
T).(\forall (k: K).((pr2 (CHead c k u2) t3 t4) \to (pr3 (CHead c k u1) t3 
t4))))))))) (\lambda (H8: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H9: 
(pr0 u1 t2)).(\lambda (H10: (subst0 i u t2 u2)).(\lambda (t3: T).(\lambda 
(t0: T).(\lambda (k: K).(\lambda (H11: (pr2 (CHead c k u2) t3 t0)).(let H12 
\def (match H11 in pr2 return (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: 
T).(\lambda (_: (pr2 c1 t4 t5)).((eq C c1 (CHead c k u2)) \to ((eq T t4 t3) 
\to ((eq T t5 t0) \to (pr3 (CHead c k u1) t3 t0)))))))) with [(pr2_free c1 t4 
t5 H12) \Rightarrow (\lambda (H13: (eq C c1 (CHead c k u2))).(\lambda (H14: 
(eq T t4 t3)).(\lambda (H15: (eq T t5 t0)).(eq_ind C (CHead c k u2) (\lambda 
(_: C).((eq T t4 t3) \to ((eq T t5 t0) \to ((pr0 t4 t5) \to (pr3 (CHead c k 
u1) t3 t0))))) (\lambda (H16: (eq T t4 t3)).(eq_ind T t3 (\lambda (t6: 
T).((eq T t5 t0) \to ((pr0 t6 t5) \to (pr3 (CHead c k u1) t3 t0)))) (\lambda 
(H17: (eq T t5 t0)).(eq_ind T t0 (\lambda (t6: T).((pr0 t3 t6) \to (pr3 
(CHead c k u1) t3 t0))) (\lambda (H18: (pr0 t3 t0)).(pr3_pr2 (CHead c k u1) 
t3 t0 (pr2_free (CHead c k u1) t3 t0 H18))) t5 (sym_eq T t5 t0 H17))) t4 
(sym_eq T t4 t3 H16))) c1 (sym_eq C c1 (CHead c k u2) H13) H14 H15 H12)))) | 
(pr2_delta c1 d0 u0 i0 H12 t4 t5 H13 t6 H14) \Rightarrow (\lambda (H15: (eq C 
c1 (CHead c k u2))).(\lambda (H16: (eq T t4 t3)).(\lambda (H17: (eq T t6 
t0)).(eq_ind C (CHead c k u2) (\lambda (c2: C).((eq T t4 t3) \to ((eq T t6 
t0) \to ((getl i0 c2 (CHead d0 (Bind Abbr) u0)) \to ((pr0 t4 t5) \to ((subst0 
i0 u0 t5 t6) \to (pr3 (CHead c k u1) t3 t0))))))) (\lambda (H18: (eq T t4 
t3)).(eq_ind T t3 (\lambda (t7: T).((eq T t6 t0) \to ((getl i0 (CHead c k u2) 
(CHead d0 (Bind Abbr) u0)) \to ((pr0 t7 t5) \to ((subst0 i0 u0 t5 t6) \to 
(pr3 (CHead c k u1) t3 t0)))))) (\lambda (H19: (eq T t6 t0)).(eq_ind T t0 
(\lambda (t7: T).((getl i0 (CHead c k u2) (CHead d0 (Bind Abbr) u0)) \to 
((pr0 t3 t5) \to ((subst0 i0 u0 t5 t7) \to (pr3 (CHead c k u1) t3 t0))))) 
(\lambda (H20: (getl i0 (CHead c k u2) (CHead d0 (Bind Abbr) u0))).(\lambda 
(H21: (pr0 t3 t5)).(\lambda (H22: (subst0 i0 u0 t5 t0)).(nat_ind (\lambda (n: 
nat).((getl n (CHead c k u2) (CHead d0 (Bind Abbr) u0)) \to ((subst0 n u0 t5 
t0) \to (pr3 (CHead c k u1) t3 t0)))) (\lambda (H23: (getl O (CHead c k u2) 
(CHead d0 (Bind Abbr) u0))).(\lambda (H24: (subst0 O u0 t5 t0)).(K_ind 
(\lambda (k0: K).((clear (CHead c k0 u2) (CHead d0 (Bind Abbr) u0)) \to (pr3 
(CHead c k0 u1) t3 t0))) (\lambda (b: B).(\lambda (H25: (clear (CHead c (Bind 
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
\def (eq_ind T u0 (\lambda (t7: T).(subst0 O t7 t5 t0)) H24 u2 H28) in 
(eq_ind B Abbr (\lambda (b0: B).(pr3 (CHead c (Bind b0) u1) t3 t0)) (ex2_ind 
T (\lambda (t7: T).(subst0 O t2 t5 t7)) (\lambda (t7: T).(subst0 (S (plus i 
O)) u t7 t0)) (pr3 (CHead c (Bind Abbr) u1) t3 t0) (\lambda (x: T).(\lambda 
(H32: (subst0 O t2 t5 x)).(\lambda (H33: (subst0 (S (plus i O)) u x t0)).(let 
H34 \def (f_equal nat nat S (plus i O) i (sym_eq nat i (plus i O) (plus_n_O 
i))) in (let H35 \def (eq_ind nat (S (plus i O)) (\lambda (n: nat).(subst0 n 
u x t0)) H33 (S i) H34) in (ex2_ind T (\lambda (t7: T).(subst0 O u1 t5 t7)) 
(\lambda (t7: T).(pr0 t7 x)) (pr3 (CHead c (Bind Abbr) u1) t3 t0) (\lambda 
(x0: T).(\lambda (H36: (subst0 O u1 t5 x0)).(\lambda (H37: (pr0 x0 
x)).(pr3_sing (CHead c (Bind Abbr) u1) x0 t3 (pr2_delta (CHead c (Bind Abbr) 
u1) c u1 O (getl_refl Abbr c u1) t3 t5 H21 x0 H36) t0 (pr3_pr2 (CHead c (Bind 
Abbr) u1) x0 t0 (pr2_delta (CHead c (Bind Abbr) u1) d u (S i) 
(getl_clear_bind Abbr (CHead c (Bind Abbr) u1) c u1 (clear_bind Abbr c u1) 
(CHead d (Bind Abbr) u) i H8) x0 x H37 t0 H35)))))) (pr0_subst0_back t2 t5 x 
O H32 u1 H9))))))) (subst0_subst0 t5 t0 u2 O H31 t2 u i H10)) b H29))))) 
H27)) H26)))) (\lambda (f: F).(\lambda (H25: (clear (CHead c (Flat f) u2) 
(CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c (Flat f) u1) t3 t0 (pr2_cflat c 
t3 t0 (pr2_delta c d0 u0 O (getl_intro O c (CHead d0 (Bind Abbr) u0) c 
(drop_refl c) (clear_gen_flat f c (CHead d0 (Bind Abbr) u0) u2 H25)) t3 t5 
H21 t0 H24) f u1)))) k (getl_gen_O (CHead c k u2) (CHead d0 (Bind Abbr) u0) 
H23)))) (\lambda (i1: nat).(\lambda (_: (((getl i1 (CHead c k u2) (CHead d0 
(Bind Abbr) u0)) \to ((subst0 i1 u0 t5 t0) \to (pr3 (CHead c k u1) t3 
t0))))).(\lambda (H23: (getl (S i1) (CHead c k u2) (CHead d0 (Bind Abbr) 
u0))).(\lambda (H24: (subst0 (S i1) u0 t5 t0)).(K_ind (\lambda (k0: K).((getl 
(S i1) (CHead c k0 u2) (CHead d0 (Bind Abbr) u0)) \to (pr3 (CHead c k0 u1) t3 
t0))) (\lambda (b: B).(\lambda (H25: (getl (S i1) (CHead c (Bind b) u2) 
(CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c (Bind b) u1) t3 t0 (pr2_delta 
(CHead c (Bind b) u1) d0 u0 (S i1) (getl_head (Bind b) i1 c (CHead d0 (Bind 
Abbr) u0) (getl_gen_S (Bind b) c (CHead d0 (Bind Abbr) u0) u2 i1 H25) u1) t3 
t5 H21 t0 H24)))) (\lambda (f: F).(\lambda (H25: (getl (S i1) (CHead c (Flat 
f) u2) (CHead d0 (Bind Abbr) u0))).(pr3_pr2 (CHead c (Flat f) u1) t3 t0 
(pr2_cflat c t3 t0 (pr2_delta c d0 u0 (r (Flat f) i1) (getl_gen_S (Flat f) c 
(CHead d0 (Bind Abbr) u0) u2 i1 H25) t3 t5 H21 t0 H24) f u1)))) k H23))))) i0 
H20 H22)))) t6 (sym_eq T t6 t0 H19))) t4 (sym_eq T t4 t3 H18))) c1 (sym_eq C 
c1 (CHead c k u2) H15) H16 H17 H12 H13 H14))))]) in (H12 (refl_equal C (CHead 
c k u2)) (refl_equal T t3) (refl_equal T t0)))))))))) t (sym_eq T t u2 H7))) 
t1 (sym_eq T t1 u1 H6))) c0 (sym_eq C c0 c H3) H4 H5 H0 H1 H2))))]) in (H0 
(refl_equal C c) (refl_equal T u1) (refl_equal T u2)))))).

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
(lift (S O) O u) (subst1_lift_S u O O (le_n O))) u (pr1_pr0 (THead (Bind 
Abbr) (TLRef O) (lift (S O) O u)) u (pr0_zeta Abbr not_abbr_abst u u 
(pr0_refl u) (TLRef O))))) (CHead c (Bind Abst) w))) (lift (S O) O (THead 
(Bind Abst) w u)) (lift_bind Abst w u (S O) O))))))).

