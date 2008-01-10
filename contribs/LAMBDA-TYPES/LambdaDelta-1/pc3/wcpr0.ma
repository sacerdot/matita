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



include "pc3/props.ma".

include "wcpr0/getl.ma".

theorem pc3_wcpr0__pc3_wcpr0_t_aux:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (k: K).(\forall 
(u: T).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c1 k u) t1 t2) \to (pc3 
(CHead c2 k u) t1 t2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(\lambda (k: 
K).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 
(CHead c1 k u) t1 t2)).(pr3_ind (CHead c1 k u) (\lambda (t: T).(\lambda (t0: 
T).(pc3 (CHead c2 k u) t t0))) (\lambda (t: T).(pc3_refl (CHead c2 k u) t)) 
(\lambda (t0: T).(\lambda (t3: T).(\lambda (H1: (pr2 (CHead c1 k u) t3 
t0)).(\lambda (t4: T).(\lambda (_: (pr3 (CHead c1 k u) t0 t4)).(\lambda (H3: 
(pc3 (CHead c2 k u) t0 t4)).(pc3_t t0 (CHead c2 k u) t3 (let H4 \def (match 
H1 in pr2 return (\lambda (c: C).(\lambda (t: T).(\lambda (t5: T).(\lambda 
(_: (pr2 c t t5)).((eq C c (CHead c1 k u)) \to ((eq T t t3) \to ((eq T t5 t0) 
\to (pc3 (CHead c2 k u) t3 t0)))))))) with [(pr2_free c t5 t6 H4) \Rightarrow 
(\lambda (H5: (eq C c (CHead c1 k u))).(\lambda (H6: (eq T t5 t3)).(\lambda 
(H7: (eq T t6 t0)).(eq_ind C (CHead c1 k u) (\lambda (_: C).((eq T t5 t3) \to 
((eq T t6 t0) \to ((pr0 t5 t6) \to (pc3 (CHead c2 k u) t3 t0))))) (\lambda 
(H8: (eq T t5 t3)).(eq_ind T t3 (\lambda (t: T).((eq T t6 t0) \to ((pr0 t t6) 
\to (pc3 (CHead c2 k u) t3 t0)))) (\lambda (H9: (eq T t6 t0)).(eq_ind T t0 
(\lambda (t: T).((pr0 t3 t) \to (pc3 (CHead c2 k u) t3 t0))) (\lambda (H10: 
(pr0 t3 t0)).(pc3_pr2_r (CHead c2 k u) t3 t0 (pr2_free (CHead c2 k u) t3 t0 
H10))) t6 (sym_eq T t6 t0 H9))) t5 (sym_eq T t5 t3 H8))) c (sym_eq C c (CHead 
c1 k u) H5) H6 H7 H4)))) | (pr2_delta c d u0 i H4 t5 t6 H5 t H6) \Rightarrow 
(\lambda (H7: (eq C c (CHead c1 k u))).(\lambda (H8: (eq T t5 t3)).(\lambda 
(H9: (eq T t t0)).(eq_ind C (CHead c1 k u) (\lambda (c0: C).((eq T t5 t3) \to 
((eq T t t0) \to ((getl i c0 (CHead d (Bind Abbr) u0)) \to ((pr0 t5 t6) \to 
((subst0 i u0 t6 t) \to (pc3 (CHead c2 k u) t3 t0))))))) (\lambda (H10: (eq T 
t5 t3)).(eq_ind T t3 (\lambda (t7: T).((eq T t t0) \to ((getl i (CHead c1 k 
u) (CHead d (Bind Abbr) u0)) \to ((pr0 t7 t6) \to ((subst0 i u0 t6 t) \to 
(pc3 (CHead c2 k u) t3 t0)))))) (\lambda (H11: (eq T t t0)).(eq_ind T t0 
(\lambda (t7: T).((getl i (CHead c1 k u) (CHead d (Bind Abbr) u0)) \to ((pr0 
t3 t6) \to ((subst0 i u0 t6 t7) \to (pc3 (CHead c2 k u) t3 t0))))) (\lambda 
(H12: (getl i (CHead c1 k u) (CHead d (Bind Abbr) u0))).(\lambda (H13: (pr0 
t3 t6)).(\lambda (H14: (subst0 i u0 t6 t0)).(ex3_2_ind C T (\lambda (e2: 
C).(\lambda (u2: T).(getl i (CHead c2 k u) (CHead e2 (Bind Abbr) u2)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 d e2))) (\lambda (_: C).(\lambda (u2: 
T).(pr0 u0 u2))) (pc3 (CHead c2 k u) t3 t0) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H15: (getl i (CHead c2 k u) (CHead x0 (Bind Abbr) x1))).(\lambda 
(_: (wcpr0 d x0)).(\lambda (H17: (pr0 u0 x1)).(ex2_ind T (\lambda (t7: 
T).(subst0 i x1 t6 t7)) (\lambda (t7: T).(pr0 t0 t7)) (pc3 (CHead c2 k u) t3 
t0) (\lambda (x: T).(\lambda (H18: (subst0 i x1 t6 x)).(\lambda (H19: (pr0 t0 
x)).(pc3_pr2_u (CHead c2 k u) x t3 (pr2_delta (CHead c2 k u) x0 x1 i H15 t3 
t6 H13 x H18) t0 (pc3_pr2_x (CHead c2 k u) x t0 (pr2_free (CHead c2 k u) t0 x 
H19)))))) (pr0_subst0_fwd u0 t6 t0 i H14 x1 H17))))))) (wcpr0_getl (CHead c1 
k u) (CHead c2 k u) (wcpr0_comp c1 c2 H u u (pr0_refl u) k) i d u0 (Bind 
Abbr) H12))))) t (sym_eq T t t0 H11))) t5 (sym_eq T t5 t3 H10))) c (sym_eq C 
c (CHead c1 k u) H7) H8 H9 H4 H5 H6))))]) in (H4 (refl_equal C (CHead c1 k 
u)) (refl_equal T t3) (refl_equal T t0))) t4 H3))))))) t1 t2 H0)))))))).

theorem pc3_wcpr0_t:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: 
T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pc3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 
t2) \to (pc3 c0 t1 t2)))))) (\lambda (c: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr3 c t1 t2)).(pc3_pr3_r c t1 t2 H0))))) (\lambda (c0: 
C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 c3)).(\lambda (_: ((\forall (t1: 
T).(\forall (t2: T).((pr3 c0 t1 t2) \to (pc3 c3 t1 t2)))))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H3: (pr3 (CHead c0 k u1) t1 t2)).(let H4 \def 
(pc3_pr2_pr3_t c0 u1 t1 t2 k H3 u2 (pr2_free c0 u1 u2 H2)) in (ex2_ind T 
(\lambda (t: T).(pr3 (CHead c0 k u2) t1 t)) (\lambda (t: T).(pr3 (CHead c0 k 
u2) t2 t)) (pc3 (CHead c3 k u2) t1 t2) (\lambda (x: T).(\lambda (H5: (pr3 
(CHead c0 k u2) t1 x)).(\lambda (H6: (pr3 (CHead c0 k u2) t2 x)).(pc3_t x 
(CHead c3 k u2) t1 (pc3_wcpr0__pc3_wcpr0_t_aux c0 c3 H0 k u2 t1 x H5) t2 
(pc3_s (CHead c3 k u2) x t2 (pc3_wcpr0__pc3_wcpr0_t_aux c0 c3 H0 k u2 t2 x 
H6)))))) H4))))))))))))) c1 c2 H))).

theorem pc3_wcpr0:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: 
T).(\forall (t2: T).((pc3 c1 t1 t2) \to (pc3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pc3 c1 t1 t2)).(let H1 \def H0 in (ex2_ind 
T (\lambda (t: T).(pr3 c1 t1 t)) (\lambda (t: T).(pr3 c1 t2 t)) (pc3 c2 t1 
t2) (\lambda (x: T).(\lambda (H2: (pr3 c1 t1 x)).(\lambda (H3: (pr3 c1 t2 
x)).(pc3_t x c2 t1 (pc3_wcpr0_t c1 c2 H t1 x H2) t2 (pc3_s c2 x t2 
(pc3_wcpr0_t c1 c2 H t2 x H3)))))) H1))))))).

