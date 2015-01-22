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

include "Basic-1/pr3/subst1.ma".

theorem pc3_gen_cabbr:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (\forall 
(e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) 
\to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (\forall 
(x2: T).((subst1 d u t2 (lift (S O) d x2)) \to (pc3 a x1 x2))))))))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (e: C).(\lambda (u: T).(\lambda (d: nat).(\lambda (H0: (getl d 
c (CHead e (Bind Abbr) u))).(\lambda (a0: C).(\lambda (H1: (csubst1 d u c 
a0)).(\lambda (a: C).(\lambda (H2: (drop (S O) d a0 a)).(\lambda (x1: 
T).(\lambda (H3: (subst1 d u t1 (lift (S O) d x1))).(\lambda (x2: T).(\lambda 
(H4: (subst1 d u t2 (lift (S O) d x2))).(let H5 \def H in (ex2_ind T (\lambda 
(t: T).(pr3 c t1 t)) (\lambda (t: T).(pr3 c t2 t)) (pc3 a x1 x2) (\lambda (x: 
T).(\lambda (H6: (pr3 c t1 x)).(\lambda (H7: (pr3 c t2 x)).(ex2_ind T 
(\lambda (x3: T).(subst1 d u x (lift (S O) d x3))) (\lambda (x3: T).(pr3 a x2 
x3)) (pc3 a x1 x2) (\lambda (x0: T).(\lambda (H8: (subst1 d u x (lift (S O) d 
x0))).(\lambda (H9: (pr3 a x2 x0)).(ex2_ind T (\lambda (x3: T).(subst1 d u x 
(lift (S O) d x3))) (\lambda (x3: T).(pr3 a x1 x3)) (pc3 a x1 x2) (\lambda 
(x3: T).(\lambda (H10: (subst1 d u x (lift (S O) d x3))).(\lambda (H11: (pr3 
a x1 x3)).(let H12 \def (eq_ind T x3 (\lambda (t: T).(pr3 a x1 t)) H11 x0 
(subst1_confluence_lift x x3 u d H10 x0 H8)) in (pc3_pr3_t a x1 x0 H12 x2 
H9))))) (pr3_gen_cabbr c t1 x H6 e u d H0 a0 H1 a H2 x1 H3))))) 
(pr3_gen_cabbr c t2 x H7 e u d H0 a0 H1 a H2 x2 H4))))) H5))))))))))))))))).
(* COMMENTS
Initial nodes: 405
END *)

