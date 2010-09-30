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

include "Basic-1/pr3/props.ma".

include "Basic-1/wcpr0/getl.ma".

theorem pr3_wcpr0_t:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (t1: 
T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pr3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(wcpr0_ind 
(\lambda (c: C).(\lambda (c0: C).(\forall (t1: T).(\forall (t2: T).((pr3 c0 
t1 t2) \to (pr3 c t1 t2)))))) (\lambda (c: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr3 c t1 t2)).H0)))) (\lambda (c0: C).(\lambda (c3: 
C).(\lambda (H0: (wcpr0 c0 c3)).(\lambda (_: ((\forall (t1: T).(\forall (t2: 
T).((pr3 c3 t1 t2) \to (pr3 c0 t1 t2)))))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H3: (pr3 (CHead c3 k u2) t1 t2)).(pr3_ind (CHead c3 k u1) 
(\lambda (t: T).(\lambda (t0: T).(pr3 (CHead c0 k u1) t t0))) (\lambda (t: 
T).(pr3_refl (CHead c0 k u1) t)) (\lambda (t0: T).(\lambda (t3: T).(\lambda 
(H4: (pr2 (CHead c3 k u1) t3 t0)).(\lambda (t4: T).(\lambda (_: (pr3 (CHead 
c3 k u1) t0 t4)).(\lambda (H6: (pr3 (CHead c0 k u1) t0 t4)).(pr3_t t0 t3 
(CHead c0 k u1) (insert_eq C (CHead c3 k u1) (\lambda (c: C).(pr2 c t3 t0)) 
(\lambda (_: C).(pr3 (CHead c0 k u1) t3 t0)) (\lambda (y: C).(\lambda (H7: 
(pr2 y t3 t0)).(pr2_ind (\lambda (c: C).(\lambda (t: T).(\lambda (t5: T).((eq 
C c (CHead c3 k u1)) \to (pr3 (CHead c0 k u1) t t5))))) (\lambda (c: 
C).(\lambda (t5: T).(\lambda (t6: T).(\lambda (H8: (pr0 t5 t6)).(\lambda (_: 
(eq C c (CHead c3 k u1))).(pr3_pr2 (CHead c0 k u1) t5 t6 (pr2_free (CHead c0 
k u1) t5 t6 H8))))))) (\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H8: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (t5: T).(\lambda (t6: T).(\lambda (H9: (pr0 t5 t6)).(\lambda 
(t: T).(\lambda (H10: (subst0 i u t6 t)).(\lambda (H11: (eq C c (CHead c3 k 
u1))).(let H12 \def (eq_ind C c (\lambda (c4: C).(getl i c4 (CHead d (Bind 
Abbr) u))) H8 (CHead c3 k u1) H11) in (ex3_2_ind C T (\lambda (e2: 
C).(\lambda (u3: T).(getl i (CHead c0 k u1) (CHead e2 (Bind Abbr) u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 d))) (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u))) (pr3 (CHead c0 k u1) t5 t) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H13: (getl i (CHead c0 k u1) (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (wcpr0 x0 d)).(\lambda (H15: (pr0 x1 u)).(ex2_ind T 
(\lambda (t7: T).(subst0 i x1 t6 t7)) (\lambda (t7: T).(pr0 t7 t)) (pr3 
(CHead c0 k u1) t5 t) (\lambda (x: T).(\lambda (H16: (subst0 i x1 t6 
x)).(\lambda (H17: (pr0 x t)).(pr3_sing (CHead c0 k u1) x t5 (pr2_delta 
(CHead c0 k u1) x0 x1 i H13 t5 t6 H9 x H16) t (pr3_pr2 (CHead c0 k u1) x t 
(pr2_free (CHead c0 k u1) x t H17)))))) (pr0_subst0_back u t6 t i H10 x1 
H15))))))) (wcpr0_getl_back (CHead c3 k u1) (CHead c0 k u1) (wcpr0_comp c0 c3 
H0 u1 u1 (pr0_refl u1) k) i d u (Bind Abbr) H12)))))))))))))) y t3 t0 H7))) 
H4) t4 H6))))))) t1 t2 (pr3_pr2_pr3_t c3 u2 t1 t2 k H3 u1 (pr2_free c3 u1 u2 
H2)))))))))))))) c2 c1 H))).
(* COMMENTS
Initial nodes: 799
END *)

