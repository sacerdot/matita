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

include "Basic-1/pr2/pr2.ma".

theorem pr3_strip:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr3 c t0 t1) \to (\forall 
(t2: T).((pr2 c t0 t2) \to (ex2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr3 c t0 
t1)).(pr3_ind c (\lambda (t: T).(\lambda (t2: T).(\forall (t3: T).((pr2 c t 
t3) \to (ex2 T (\lambda (t4: T).(pr3 c t2 t4)) (\lambda (t4: T).(pr3 c t3 
t4))))))) (\lambda (t: T).(\lambda (t2: T).(\lambda (H0: (pr2 c t 
t2)).(ex_intro2 T (\lambda (t3: T).(pr3 c t t3)) (\lambda (t3: T).(pr3 c t2 
t3)) t2 (pr3_pr2 c t t2 H0) (pr3_refl c t2))))) (\lambda (t2: T).(\lambda 
(t3: T).(\lambda (H0: (pr2 c t3 t2)).(\lambda (t4: T).(\lambda (_: (pr3 c t2 
t4)).(\lambda (H2: ((\forall (t5: T).((pr2 c t2 t5) \to (ex2 T (\lambda (t: 
T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t))))))).(\lambda (t5: T).(\lambda 
(H3: (pr2 c t3 t5)).(ex2_ind T (\lambda (t: T).(pr2 c t5 t)) (\lambda (t: 
T).(pr2 c t2 t)) (ex2 T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c 
t5 t))) (\lambda (x: T).(\lambda (H4: (pr2 c t5 x)).(\lambda (H5: (pr2 c t2 
x)).(ex2_ind T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c x t)) 
(ex2 T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t))) (\lambda 
(x0: T).(\lambda (H6: (pr3 c t4 x0)).(\lambda (H7: (pr3 c x x0)).(ex_intro2 T 
(\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t)) x0 H6 (pr3_sing c 
x t5 H4 x0 H7))))) (H2 x H5))))) (pr2_confluence c t3 t5 H3 t2 H0)))))))))) 
t0 t1 H)))).
(* COMMENTS
Initial nodes: 375
END *)

theorem pr3_confluence:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr3 c t0 t1) \to (\forall 
(t2: T).((pr3 c t0 t2) \to (ex2 T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr3 c t0 
t1)).(pr3_ind c (\lambda (t: T).(\lambda (t2: T).(\forall (t3: T).((pr3 c t 
t3) \to (ex2 T (\lambda (t4: T).(pr3 c t2 t4)) (\lambda (t4: T).(pr3 c t3 
t4))))))) (\lambda (t: T).(\lambda (t2: T).(\lambda (H0: (pr3 c t 
t2)).(ex_intro2 T (\lambda (t3: T).(pr3 c t t3)) (\lambda (t3: T).(pr3 c t2 
t3)) t2 H0 (pr3_refl c t2))))) (\lambda (t2: T).(\lambda (t3: T).(\lambda 
(H0: (pr2 c t3 t2)).(\lambda (t4: T).(\lambda (_: (pr3 c t2 t4)).(\lambda 
(H2: ((\forall (t5: T).((pr3 c t2 t5) \to (ex2 T (\lambda (t: T).(pr3 c t4 
t)) (\lambda (t: T).(pr3 c t5 t))))))).(\lambda (t5: T).(\lambda (H3: (pr3 c 
t3 t5)).(ex2_ind T (\lambda (t: T).(pr3 c t5 t)) (\lambda (t: T).(pr3 c t2 
t)) (ex2 T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t))) 
(\lambda (x: T).(\lambda (H4: (pr3 c t5 x)).(\lambda (H5: (pr3 c t2 
x)).(ex2_ind T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c x t)) 
(ex2 T (\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t))) (\lambda 
(x0: T).(\lambda (H6: (pr3 c t4 x0)).(\lambda (H7: (pr3 c x x0)).(ex_intro2 T 
(\lambda (t: T).(pr3 c t4 t)) (\lambda (t: T).(pr3 c t5 t)) x0 H6 (pr3_t x t5 
c H4 x0 H7))))) (H2 x H5))))) (pr3_strip c t3 t5 H3 t2 H0)))))))))) t0 t1 
H)))).
(* COMMENTS
Initial nodes: 367
END *)

