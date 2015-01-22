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

include "Basic-1/pc1/defs.ma".

include "Basic-1/pr1/pr1.ma".

theorem pc1_pr0_r:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pc1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(ex_intro2 T 
(\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)) t2 (pr1_pr0 t1 t2 H) 
(pr1_refl t2)))).
(* COMMENTS
Initial nodes: 43
END *)

theorem pc1_pr0_x:
 \forall (t1: T).(\forall (t2: T).((pr0 t2 t1) \to (pc1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t2 t1)).(ex_intro2 T 
(\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)) t1 (pr1_refl t1) 
(pr1_pr0 t2 t1 H)))).
(* COMMENTS
Initial nodes: 43
END *)

theorem pc1_refl:
 \forall (t: T).(pc1 t t)
\def
 \lambda (t: T).(ex_intro2 T (\lambda (t0: T).(pr1 t t0)) (\lambda (t0: 
T).(pr1 t t0)) t (pr1_refl t) (pr1_refl t)).
(* COMMENTS
Initial nodes: 31
END *)

theorem pc1_pr0_u:
 \forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: T).((pc1 t2 
t3) \to (pc1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr0 t1 t2)).(\lambda (t3: 
T).(\lambda (H0: (pc1 t2 t3)).(let H1 \def H0 in (ex2_ind T (\lambda (t: 
T).(pr1 t2 t)) (\lambda (t: T).(pr1 t3 t)) (pc1 t1 t3) (\lambda (x: 
T).(\lambda (H2: (pr1 t2 x)).(\lambda (H3: (pr1 t3 x)).(ex_intro2 T (\lambda 
(t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t3 t)) x (pr1_sing t2 t1 H x H2) 
H3)))) H1)))))).
(* COMMENTS
Initial nodes: 97
END *)

theorem pc1_s:
 \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (pc1 t2 t1)))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc1 t1 t2)).(let H0 \def H in 
(ex2_ind T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)) (pc1 t2 
t1) (\lambda (x: T).(\lambda (H1: (pr1 t1 x)).(\lambda (H2: (pr1 t2 
x)).(ex_intro2 T (\lambda (t: T).(pr1 t2 t)) (\lambda (t: T).(pr1 t1 t)) x H2 
H1)))) H0)))).
(* COMMENTS
Initial nodes: 79
END *)

theorem pc1_head_1:
 \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t: T).(\forall 
(k: K).(pc1 (THead k u1 t) (THead k u2 t))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc1 u1 u2)).(\lambda (t: 
T).(\lambda (k: K).(let H0 \def H in (ex2_ind T (\lambda (t0: T).(pr1 u1 t0)) 
(\lambda (t0: T).(pr1 u2 t0)) (pc1 (THead k u1 t) (THead k u2 t)) (\lambda 
(x: T).(\lambda (H1: (pr1 u1 x)).(\lambda (H2: (pr1 u2 x)).(ex_intro2 T 
(\lambda (t0: T).(pr1 (THead k u1 t) t0)) (\lambda (t0: T).(pr1 (THead k u2 
t) t0)) (THead k x t) (pr1_head_1 u1 x H1 t k) (pr1_head_1 u2 x H2 t k))))) 
H0)))))).
(* COMMENTS
Initial nodes: 133
END *)

theorem pc1_head_2:
 \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (u: T).(\forall 
(k: K).(pc1 (THead k u t1) (THead k u t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc1 t1 t2)).(\lambda (u: 
T).(\lambda (k: K).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr1 t1 t)) 
(\lambda (t: T).(pr1 t2 t)) (pc1 (THead k u t1) (THead k u t2)) (\lambda (x: 
T).(\lambda (H1: (pr1 t1 x)).(\lambda (H2: (pr1 t2 x)).(ex_intro2 T (\lambda 
(t: T).(pr1 (THead k u t1) t)) (\lambda (t: T).(pr1 (THead k u t2) t)) (THead 
k u x) (pr1_head_2 t1 x H1 u k) (pr1_head_2 t2 x H2 u k))))) H0)))))).
(* COMMENTS
Initial nodes: 133
END *)

theorem pc1_t:
 \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (\forall (t3: T).((pc1 t2 
t3) \to (pc1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc1 t1 t2)).(\lambda (t3: 
T).(\lambda (H0: (pc1 t2 t3)).(let H1 \def H0 in (ex2_ind T (\lambda (t: 
T).(pr1 t2 t)) (\lambda (t: T).(pr1 t3 t)) (pc1 t1 t3) (\lambda (x: 
T).(\lambda (H2: (pr1 t2 x)).(\lambda (H3: (pr1 t3 x)).(let H4 \def H in 
(ex2_ind T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)) (pc1 t1 
t3) (\lambda (x0: T).(\lambda (H5: (pr1 t1 x0)).(\lambda (H6: (pr1 t2 
x0)).(ex2_ind T (\lambda (t: T).(pr1 x0 t)) (\lambda (t: T).(pr1 x t)) (pc1 
t1 t3) (\lambda (x1: T).(\lambda (H7: (pr1 x0 x1)).(\lambda (H8: (pr1 x 
x1)).(ex_intro2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t3 t)) x1 
(pr1_t x0 t1 H5 x1 H7) (pr1_t x t3 H3 x1 H8))))) (pr1_confluence t2 x0 H6 x 
H2))))) H4))))) H1)))))).
(* COMMENTS
Initial nodes: 203
END *)

theorem pc1_pr0_u2:
 \forall (t0: T).(\forall (t1: T).((pr0 t0 t1) \to (\forall (t2: T).((pc1 t0 
t2) \to (pc1 t1 t2)))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr0 t0 t1)).(\lambda (t2: 
T).(\lambda (H0: (pc1 t0 t2)).(pc1_t t0 t1 (pc1_pr0_x t1 t0 H) t2 H0))))).
(* COMMENTS
Initial nodes: 35
END *)

theorem pc1_head:
 \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t1: T).(\forall 
(t2: T).((pc1 t1 t2) \to (\forall (k: K).(pc1 (THead k u1 t1) (THead k u2 
t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc1 u1 u2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pc1 t1 t2)).(\lambda (k: K).(pc1_t (THead 
k u2 t1) (THead k u1 t1) (pc1_head_1 u1 u2 H t1 k) (THead k u2 t2) 
(pc1_head_2 t1 t2 H0 u2 k)))))))).
(* COMMENTS
Initial nodes: 71
END *)

