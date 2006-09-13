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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr1/props".

include "pr1/defs.ma".

theorem pr1_pr0:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(pr1_u t2 t1 H t2 
(pr1_r t2)))).

theorem pr1_t:
 \forall (t2: T).(\forall (t1: T).((pr1 t1 t2) \to (\forall (t3: T).((pr1 t2 
t3) \to (pr1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr1 t1 t2)).(pr1_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (t3: T).((pr1 t0 t3) \to (pr1 t t3))))) 
(\lambda (t: T).(\lambda (t3: T).(\lambda (H0: (pr1 t t3)).H0))) (\lambda 
(t0: T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda 
(_: (pr1 t0 t4)).(\lambda (H2: ((\forall (t5: T).((pr1 t4 t5) \to (pr1 t0 
t5))))).(\lambda (t5: T).(\lambda (H3: (pr1 t4 t5)).(pr1_u t0 t3 H0 t5 (H2 t5 
H3)))))))))) t1 t2 H))).

theorem pr1_head_1:
 \forall (u1: T).(\forall (u2: T).((pr1 u1 u2) \to (\forall (t: T).(\forall 
(k: K).(pr1 (THead k u1 t) (THead k u2 t))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr1 u1 u2)).(\lambda (t: 
T).(\lambda (k: K).(pr1_ind (\lambda (t0: T).(\lambda (t1: T).(pr1 (THead k 
t0 t) (THead k t1 t)))) (\lambda (t0: T).(pr1_r (THead k t0 t))) (\lambda 
(t2: T).(\lambda (t1: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t3: T).(\lambda 
(_: (pr1 t2 t3)).(\lambda (H2: (pr1 (THead k t2 t) (THead k t3 t))).(pr1_u 
(THead k t2 t) (THead k t1 t) (pr0_comp t1 t2 H0 t t (pr0_refl t) k) (THead k 
t3 t) H2))))))) u1 u2 H))))).

theorem pr1_head_2:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (u: T).(\forall 
(k: K).(pr1 (THead k u t1) (THead k u t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(\lambda (u: 
T).(\lambda (k: K).(pr1_ind (\lambda (t: T).(\lambda (t0: T).(pr1 (THead k u 
t) (THead k u t0)))) (\lambda (t: T).(pr1_r (THead k u t))) (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda (_: 
(pr1 t0 t4)).(\lambda (H2: (pr1 (THead k u t0) (THead k u t4))).(pr1_u (THead 
k u t0) (THead k u t3) (pr0_comp u u (pr0_refl u) t3 t0 H0 k) (THead k u t4) 
H2))))))) t1 t2 H))))).

