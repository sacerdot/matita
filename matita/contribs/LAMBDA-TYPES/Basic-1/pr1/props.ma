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

include "Basic-1/pr1/defs.ma".

include "Basic-1/pr0/subst1.ma".

include "Basic-1/subst1/props.ma".

include "Basic-1/T/props.ma".

theorem pr1_pr0:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(pr1_sing t2 t1 H 
t2 (pr1_refl t2)))).
(* COMMENTS
Initial nodes: 23
END *)

theorem pr1_t:
 \forall (t2: T).(\forall (t1: T).((pr1 t1 t2) \to (\forall (t3: T).((pr1 t2 
t3) \to (pr1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr1 t1 t2)).(pr1_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (t3: T).((pr1 t0 t3) \to (pr1 t t3))))) 
(\lambda (t: T).(\lambda (t3: T).(\lambda (H0: (pr1 t t3)).H0))) (\lambda 
(t0: T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda 
(_: (pr1 t0 t4)).(\lambda (H2: ((\forall (t5: T).((pr1 t4 t5) \to (pr1 t0 
t5))))).(\lambda (t5: T).(\lambda (H3: (pr1 t4 t5)).(pr1_sing t0 t3 H0 t5 (H2 
t5 H3)))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 103
END *)

theorem pr1_head_1:
 \forall (u1: T).(\forall (u2: T).((pr1 u1 u2) \to (\forall (t: T).(\forall 
(k: K).(pr1 (THead k u1 t) (THead k u2 t))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr1 u1 u2)).(\lambda (t: 
T).(\lambda (k: K).(pr1_ind (\lambda (t0: T).(\lambda (t1: T).(pr1 (THead k 
t0 t) (THead k t1 t)))) (\lambda (t0: T).(pr1_refl (THead k t0 t))) (\lambda 
(t2: T).(\lambda (t1: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t3: T).(\lambda 
(_: (pr1 t2 t3)).(\lambda (H2: (pr1 (THead k t2 t) (THead k t3 t))).(pr1_sing 
(THead k t2 t) (THead k t1 t) (pr0_comp t1 t2 H0 t t (pr0_refl t) k) (THead k 
t3 t) H2))))))) u1 u2 H))))).
(* COMMENTS
Initial nodes: 137
END *)

theorem pr1_head_2:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (u: T).(\forall 
(k: K).(pr1 (THead k u t1) (THead k u t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(\lambda (u: 
T).(\lambda (k: K).(pr1_ind (\lambda (t: T).(\lambda (t0: T).(pr1 (THead k u 
t) (THead k u t0)))) (\lambda (t: T).(pr1_refl (THead k u t))) (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda (_: 
(pr1 t0 t4)).(\lambda (H2: (pr1 (THead k u t0) (THead k u t4))).(pr1_sing 
(THead k u t0) (THead k u t3) (pr0_comp u u (pr0_refl u) t3 t0 H0 k) (THead k 
u t4) H2))))))) t1 t2 H))))).
(* COMMENTS
Initial nodes: 137
END *)

theorem pr1_comp:
 \forall (v: T).(\forall (w: T).((pr1 v w) \to (\forall (t: T).(\forall (u: 
T).((pr1 t u) \to (\forall (k: K).(pr1 (THead k v t) (THead k w u))))))))
\def
 \lambda (v: T).(\lambda (w: T).(\lambda (H: (pr1 v w)).(pr1_ind (\lambda (t: 
T).(\lambda (t0: T).(\forall (t1: T).(\forall (u: T).((pr1 t1 u) \to (\forall 
(k: K).(pr1 (THead k t t1) (THead k t0 u)))))))) (\lambda (t: T).(\lambda 
(t0: T).(\lambda (u: T).(\lambda (H0: (pr1 t0 u)).(\lambda (k: K).(pr1_head_2 
t0 u H0 t k)))))) (\lambda (t2: T).(\lambda (t1: T).(\lambda (H0: (pr0 t1 
t2)).(\lambda (t3: T).(\lambda (H1: (pr1 t2 t3)).(\lambda (_: ((\forall (t: 
T).(\forall (u: T).((pr1 t u) \to (\forall (k: K).(pr1 (THead k t2 t) (THead 
k t3 u)))))))).(\lambda (t: T).(\lambda (u: T).(\lambda (H3: (pr1 t 
u)).(\lambda (k: K).(pr1_ind (\lambda (t0: T).(\lambda (t4: T).(pr1 (THead k 
t1 t0) (THead k t3 t4)))) (\lambda (t0: T).(pr1_head_1 t1 t3 (pr1_sing t2 t1 
H0 t3 H1) t0 k)) (\lambda (t0: T).(\lambda (t4: T).(\lambda (H4: (pr0 t4 
t0)).(\lambda (t5: T).(\lambda (_: (pr1 t0 t5)).(\lambda (H6: (pr1 (THead k 
t1 t0) (THead k t3 t5))).(pr1_sing (THead k t1 t0) (THead k t1 t4) (pr0_comp 
t1 t1 (pr0_refl t1) t4 t0 H4 k) (THead k t3 t5) H6))))))) t u H3))))))))))) v 
w H))).
(* COMMENTS
Initial nodes: 273
END *)

theorem pr1_eta:
 \forall (w: T).(\forall (u: T).(let t \def (THead (Bind Abst) w u) in 
(\forall (v: T).((pr1 v w) \to (pr1 (THead (Bind Abst) v (THead (Flat Appl) 
(TLRef O) (lift (S O) O t))) t)))))
\def
 \lambda (w: T).(\lambda (u: T).(let t \def (THead (Bind Abst) w u) in 
(\lambda (v: T).(\lambda (H: (pr1 v w)).(eq_ind_r T (THead (Bind Abst) (lift 
(S O) O w) (lift (S O) (S O) u)) (\lambda (t0: T).(pr1 (THead (Bind Abst) v 
(THead (Flat Appl) (TLRef O) t0)) (THead (Bind Abst) w u))) (pr1_comp v w H 
(THead (Flat Appl) (TLRef O) (THead (Bind Abst) (lift (S O) O w) (lift (S O) 
(S O) u))) u (pr1_sing (THead (Bind Abbr) (TLRef O) (lift (S O) (S O) u)) 
(THead (Flat Appl) (TLRef O) (THead (Bind Abst) (lift (S O) O w) (lift (S O) 
(S O) u))) (pr0_beta (lift (S O) O w) (TLRef O) (TLRef O) (pr0_refl (TLRef 
O)) (lift (S O) (S O) u) (lift (S O) (S O) u) (pr0_refl (lift (S O) (S O) 
u))) u (pr1_sing (THead (Bind Abbr) (TLRef O) (lift (S O) O u)) (THead (Bind 
Abbr) (TLRef O) (lift (S O) (S O) u)) (pr0_delta1 (TLRef O) (TLRef O) 
(pr0_refl (TLRef O)) (lift (S O) (S O) u) (lift (S O) (S O) u) (pr0_refl 
(lift (S O) (S O) u)) (lift (S O) O u) (subst1_lift_S u O O (le_n O))) u 
(pr1_pr0 (THead (Bind Abbr) (TLRef O) (lift (S O) O u)) u (pr0_zeta Abbr 
not_abbr_abst u u (pr0_refl u) (TLRef O))))) (Bind Abst)) (lift (S O) O 
(THead (Bind Abst) w u)) (lift_bind Abst w u (S O) O)))))).
(* COMMENTS
Initial nodes: 463
END *)

