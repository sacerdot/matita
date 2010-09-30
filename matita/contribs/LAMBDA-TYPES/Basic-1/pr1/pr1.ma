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

include "Basic-1/pr1/props.ma".

include "Basic-1/pr0/pr0.ma".

theorem pr1_strip:
 \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr0 t0 
t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr1 t0 t1)).(pr1_ind (\lambda 
(t: T).(\lambda (t2: T).(\forall (t3: T).((pr0 t t3) \to (ex2 T (\lambda (t4: 
T).(pr1 t2 t4)) (\lambda (t4: T).(pr1 t3 t4))))))) (\lambda (t: T).(\lambda 
(t2: T).(\lambda (H0: (pr0 t t2)).(ex_intro2 T (\lambda (t3: T).(pr1 t t3)) 
(\lambda (t3: T).(pr1 t2 t3)) t2 (pr1_pr0 t t2 H0) (pr1_refl t2))))) (\lambda 
(t2: T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t2)).(\lambda (t4: T).(\lambda 
(_: (pr1 t2 t4)).(\lambda (H2: ((\forall (t5: T).((pr0 t2 t5) \to (ex2 T 
(\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t))))))).(\lambda (t5: 
T).(\lambda (H3: (pr0 t3 t5)).(ex2_ind T (\lambda (t: T).(pr0 t5 t)) (\lambda 
(t: T).(pr0 t2 t)) (ex2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 
t))) (\lambda (x: T).(\lambda (H4: (pr0 t5 x)).(\lambda (H5: (pr0 t2 x)).(let 
H6 \def (H2 x H5) in (ex2_ind T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: 
T).(pr1 x t)) (ex2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t))) 
(\lambda (x0: T).(\lambda (H7: (pr1 t4 x0)).(\lambda (H8: (pr1 x 
x0)).(ex_intro2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t)) x0 
H7 (pr1_t x t5 (pr1_pr0 t5 x H4) x0 H8))))) H6))))) (pr0_confluence t3 t5 H3 
t2 H0)))))))))) t0 t1 H))).
(* COMMENTS
Initial nodes: 317
END *)

theorem pr1_confluence:
 \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr1 t0 
t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr1 t0 t1)).(pr1_ind (\lambda 
(t: T).(\lambda (t2: T).(\forall (t3: T).((pr1 t t3) \to (ex2 T (\lambda (t4: 
T).(pr1 t2 t4)) (\lambda (t4: T).(pr1 t3 t4))))))) (\lambda (t: T).(\lambda 
(t2: T).(\lambda (H0: (pr1 t t2)).(ex_intro2 T (\lambda (t3: T).(pr1 t t3)) 
(\lambda (t3: T).(pr1 t2 t3)) t2 H0 (pr1_refl t2))))) (\lambda (t2: 
T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t2)).(\lambda (t4: T).(\lambda (_: 
(pr1 t2 t4)).(\lambda (H2: ((\forall (t5: T).((pr1 t2 t5) \to (ex2 T (\lambda 
(t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t))))))).(\lambda (t5: T).(\lambda 
(H3: (pr1 t3 t5)).(let H_x \def (pr1_strip t3 t5 H3 t2 H0) in (let H4 \def 
H_x in (ex2_ind T (\lambda (t: T).(pr1 t5 t)) (\lambda (t: T).(pr1 t2 t)) 
(ex2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t))) (\lambda (x: 
T).(\lambda (H5: (pr1 t5 x)).(\lambda (H6: (pr1 t2 x)).(let H_x0 \def (H2 x 
H6) in (let H7 \def H_x0 in (ex2_ind T (\lambda (t: T).(pr1 t4 t)) (\lambda 
(t: T).(pr1 x t)) (ex2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 
t))) (\lambda (x0: T).(\lambda (H8: (pr1 t4 x0)).(\lambda (H9: (pr1 x 
x0)).(ex_intro2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t)) x0 
H8 (pr1_t x t5 H5 x0 H9))))) H7)))))) H4))))))))))) t0 t1 H))).
(* COMMENTS
Initial nodes: 311
END *)

