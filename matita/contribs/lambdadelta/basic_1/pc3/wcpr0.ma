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

include "Basic-1/pc3/props.ma".

include "Basic-1/wcpr0/getl.ma".

theorem pc3_wcpr0__pc3_wcpr0_t_aux:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (k: K).(\forall 
(u: T).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c1 k u) t1 t2) \to (pc3 
(CHead c2 k u) t1 t2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(\lambda (k: 
K).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 
(CHead c1 k u) t1 t2)).(pr3_ind (CHead c1 k u) (\lambda (t: T).(\lambda (t0: 
T).(pc3 (CHead c2 k u) t t0))) (\lambda (t: T).(pc3_refl (CHead c2 k u) t)) 
(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr2 (CHead c1 k u) t4 
t3)).(\lambda (t5: T).(\lambda (_: (pr3 (CHead c1 k u) t3 t5)).(\lambda (H3: 
(pc3 (CHead c2 k u) t3 t5)).(pc3_t t3 (CHead c2 k u) t4 (insert_eq C (CHead 
c1 k u) (\lambda (c: C).(pr2 c t4 t3)) (\lambda (_: C).(pc3 (CHead c2 k u) t4 
t3)) (\lambda (y: C).(\lambda (H4: (pr2 y t4 t3)).(pr2_ind (\lambda (c: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c (CHead c1 k u)) \to (pc3 (CHead 
c2 k u) t t0))))) (\lambda (c: C).(\lambda (t6: T).(\lambda (t0: T).(\lambda 
(H5: (pr0 t6 t0)).(\lambda (_: (eq C c (CHead c1 k u))).(pc3_pr2_r (CHead c2 
k u) t6 t0 (pr2_free (CHead c2 k u) t6 t0 H5))))))) (\lambda (c: C).(\lambda 
(d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H5: (getl i c (CHead d 
(Bind Abbr) u0))).(\lambda (t6: T).(\lambda (t0: T).(\lambda (H6: (pr0 t6 
t0)).(\lambda (t: T).(\lambda (H7: (subst0 i u0 t0 t)).(\lambda (H8: (eq C c 
(CHead c1 k u))).(let H9 \def (eq_ind C c (\lambda (c0: C).(getl i c0 (CHead 
d (Bind Abbr) u0))) H5 (CHead c1 k u) H8) in (ex3_2_ind C T (\lambda (e2: 
C).(\lambda (u2: T).(getl i (CHead c2 k u) (CHead e2 (Bind Abbr) u2)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 d e2))) (\lambda (_: C).(\lambda (u2: 
T).(pr0 u0 u2))) (pc3 (CHead c2 k u) t6 t) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H10: (getl i (CHead c2 k u) (CHead x0 (Bind Abbr) x1))).(\lambda 
(_: (wcpr0 d x0)).(\lambda (H12: (pr0 u0 x1)).(ex2_ind T (\lambda (t7: 
T).(subst0 i x1 t0 t7)) (\lambda (t7: T).(pr0 t t7)) (pc3 (CHead c2 k u) t6 
t) (\lambda (x: T).(\lambda (H13: (subst0 i x1 t0 x)).(\lambda (H14: (pr0 t 
x)).(pc3_pr2_u (CHead c2 k u) x t6 (pr2_delta (CHead c2 k u) x0 x1 i H10 t6 
t0 H6 x H13) t (pc3_pr2_x (CHead c2 k u) x t (pr2_free (CHead c2 k u) t x 
H14)))))) (pr0_subst0_fwd u0 t0 t i H7 x1 H12))))))) (wcpr0_getl (CHead c1 k 
u) (CHead c2 k u) (wcpr0_comp c1 c2 H u u (pr0_refl u) k) i d u0 (Bind Abbr) 
H9)))))))))))))) y t4 t3 H4))) H1) t5 H3))))))) t1 t2 H0)))))))).
(* COMMENTS
Initial nodes: 689
END *)

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
(* COMMENTS
Initial nodes: 299
END *)

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
(* COMMENTS
Initial nodes: 121
END *)

