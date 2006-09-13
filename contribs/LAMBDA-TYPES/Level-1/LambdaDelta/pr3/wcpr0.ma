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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr3/wcpr0".

include "pr3/props.ma".

include "wcpr0/getl.ma".

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
(CHead c0 k u1) (let H7 \def (match H4 in pr2 return (\lambda (c: C).(\lambda 
(t: T).(\lambda (t5: T).(\lambda (_: (pr2 c t t5)).((eq C c (CHead c3 k u1)) 
\to ((eq T t t3) \to ((eq T t5 t0) \to (pr3 (CHead c0 k u1) t3 t0)))))))) 
with [(pr2_free c t5 t6 H7) \Rightarrow (\lambda (H8: (eq C c (CHead c3 k 
u1))).(\lambda (H9: (eq T t5 t3)).(\lambda (H10: (eq T t6 t0)).(eq_ind C 
(CHead c3 k u1) (\lambda (_: C).((eq T t5 t3) \to ((eq T t6 t0) \to ((pr0 t5 
t6) \to (pr3 (CHead c0 k u1) t3 t0))))) (\lambda (H11: (eq T t5 t3)).(eq_ind 
T t3 (\lambda (t: T).((eq T t6 t0) \to ((pr0 t t6) \to (pr3 (CHead c0 k u1) 
t3 t0)))) (\lambda (H12: (eq T t6 t0)).(eq_ind T t0 (\lambda (t: T).((pr0 t3 
t) \to (pr3 (CHead c0 k u1) t3 t0))) (\lambda (H13: (pr0 t3 t0)).(pr3_pr2 
(CHead c0 k u1) t3 t0 (pr2_free (CHead c0 k u1) t3 t0 H13))) t6 (sym_eq T t6 
t0 H12))) t5 (sym_eq T t5 t3 H11))) c (sym_eq C c (CHead c3 k u1) H8) H9 H10 
H7)))) | (pr2_delta c d u i H7 t5 t6 H8 t H9) \Rightarrow (\lambda (H10: (eq 
C c (CHead c3 k u1))).(\lambda (H11: (eq T t5 t3)).(\lambda (H12: (eq T t 
t0)).(eq_ind C (CHead c3 k u1) (\lambda (c4: C).((eq T t5 t3) \to ((eq T t 
t0) \to ((getl i c4 (CHead d (Bind Abbr) u)) \to ((pr0 t5 t6) \to ((subst0 i 
u t6 t) \to (pr3 (CHead c0 k u1) t3 t0))))))) (\lambda (H13: (eq T t5 
t3)).(eq_ind T t3 (\lambda (t7: T).((eq T t t0) \to ((getl i (CHead c3 k u1) 
(CHead d (Bind Abbr) u)) \to ((pr0 t7 t6) \to ((subst0 i u t6 t) \to (pr3 
(CHead c0 k u1) t3 t0)))))) (\lambda (H14: (eq T t t0)).(eq_ind T t0 (\lambda 
(t7: T).((getl i (CHead c3 k u1) (CHead d (Bind Abbr) u)) \to ((pr0 t3 t6) 
\to ((subst0 i u t6 t7) \to (pr3 (CHead c0 k u1) t3 t0))))) (\lambda (H15: 
(getl i (CHead c3 k u1) (CHead d (Bind Abbr) u))).(\lambda (H16: (pr0 t3 
t6)).(\lambda (H17: (subst0 i u t6 t0)).(ex3_2_ind C T (\lambda (e2: 
C).(\lambda (u3: T).(getl i (CHead c0 k u1) (CHead e2 (Bind Abbr) u3)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 d))) (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u))) (pr3 (CHead c0 k u1) t3 t0) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H18: (getl i (CHead c0 k u1) (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (wcpr0 x0 d)).(\lambda (H20: (pr0 x1 u)).(ex2_ind T 
(\lambda (t7: T).(subst0 i x1 t6 t7)) (\lambda (t7: T).(pr0 t7 t0)) (pr3 
(CHead c0 k u1) t3 t0) (\lambda (x: T).(\lambda (H21: (subst0 i x1 t6 
x)).(\lambda (H22: (pr0 x t0)).(pr3_sing (CHead c0 k u1) x t3 (pr2_delta 
(CHead c0 k u1) x0 x1 i H18 t3 t6 H16 x H21) t0 (pr3_pr2 (CHead c0 k u1) x t0 
(pr2_free (CHead c0 k u1) x t0 H22)))))) (pr0_subst0_back u t6 t0 i H17 x1 
H20))))))) (wcpr0_getl_back (CHead c3 k u1) (CHead c0 k u1) (wcpr0_comp c0 c3 
H0 u1 u1 (pr0_refl u1) k) i d u (Bind Abbr) H15))))) t (sym_eq T t t0 H14))) 
t5 (sym_eq T t5 t3 H13))) c (sym_eq C c (CHead c3 k u1) H10) H11 H12 H7 H8 
H9))))]) in (H7 (refl_equal C (CHead c3 k u1)) (refl_equal T t3) (refl_equal 
T t0))) t4 H6))))))) t1 t2 (pr3_pr2_pr3_t c3 u2 t1 t2 k H3 u1 (pr2_free c3 u1 
u2 H2)))))))))))))) c2 c1 H))).

