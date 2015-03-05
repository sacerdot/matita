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

include "basic_1/pc1/defs.ma".

include "basic_1/pr1/pr1.ma".

theorem pc1_pr0_r:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pc1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(let TMP_1 \def 
(\lambda (t: T).(pr1 t1 t)) in (let TMP_2 \def (\lambda (t: T).(pr1 t2 t)) in 
(let TMP_3 \def (pr1_pr0 t1 t2 H) in (let TMP_4 \def (pr1_refl t2) in 
(ex_intro2 T TMP_1 TMP_2 t2 TMP_3 TMP_4))))))).

theorem pc1_pr0_x:
 \forall (t1: T).(\forall (t2: T).((pr0 t2 t1) \to (pc1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t2 t1)).(let TMP_1 \def 
(\lambda (t: T).(pr1 t1 t)) in (let TMP_2 \def (\lambda (t: T).(pr1 t2 t)) in 
(let TMP_3 \def (pr1_refl t1) in (let TMP_4 \def (pr1_pr0 t2 t1 H) in 
(ex_intro2 T TMP_1 TMP_2 t1 TMP_3 TMP_4))))))).

theorem pc1_refl:
 \forall (t: T).(pc1 t t)
\def
 \lambda (t: T).(let TMP_1 \def (\lambda (t0: T).(pr1 t t0)) in (let TMP_2 
\def (\lambda (t0: T).(pr1 t t0)) in (let TMP_3 \def (pr1_refl t) in (let 
TMP_4 \def (pr1_refl t) in (ex_intro2 T TMP_1 TMP_2 t TMP_3 TMP_4))))).

theorem pc1_pr0_u:
 \forall (t2: T).(\forall (t1: T).((pr0 t1 t2) \to (\forall (t3: T).((pc1 t2 
t3) \to (pc1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr0 t1 t2)).(\lambda (t3: 
T).(\lambda (H0: (pc1 t2 t3)).(let H1 \def H0 in (let TMP_1 \def (\lambda (t: 
T).(pr1 t2 t)) in (let TMP_2 \def (\lambda (t: T).(pr1 t3 t)) in (let TMP_3 
\def (pc1 t1 t3) in (let TMP_7 \def (\lambda (x: T).(\lambda (H2: (pr1 t2 
x)).(\lambda (H3: (pr1 t3 x)).(let TMP_4 \def (\lambda (t: T).(pr1 t1 t)) in 
(let TMP_5 \def (\lambda (t: T).(pr1 t3 t)) in (let TMP_6 \def (pr1_sing t2 
t1 H x H2) in (ex_intro2 T TMP_4 TMP_5 x TMP_6 H3))))))) in (ex2_ind T TMP_1 
TMP_2 TMP_3 TMP_7 H1)))))))))).

theorem pc1_s:
 \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (pc1 t2 t1)))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc1 t1 t2)).(let H0 \def H in 
(let TMP_1 \def (\lambda (t: T).(pr1 t1 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr1 t2 t)) in (let TMP_3 \def (pc1 t2 t1) in (let TMP_6 \def (\lambda (x: 
T).(\lambda (H1: (pr1 t1 x)).(\lambda (H2: (pr1 t2 x)).(let TMP_4 \def 
(\lambda (t: T).(pr1 t2 t)) in (let TMP_5 \def (\lambda (t: T).(pr1 t1 t)) in 
(ex_intro2 T TMP_4 TMP_5 x H2 H1)))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_6 
H0)))))))).

theorem pc1_head_1:
 \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t: T).(\forall 
(k: K).(pc1 (THead k u1 t) (THead k u2 t))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc1 u1 u2)).(\lambda (t: 
T).(\lambda (k: K).(let H0 \def H in (let TMP_1 \def (\lambda (t0: T).(pr1 u1 
t0)) in (let TMP_2 \def (\lambda (t0: T).(pr1 u2 t0)) in (let TMP_3 \def 
(THead k u1 t) in (let TMP_4 \def (THead k u2 t) in (let TMP_5 \def (pc1 
TMP_3 TMP_4) in (let TMP_13 \def (\lambda (x: T).(\lambda (H1: (pr1 u1 
x)).(\lambda (H2: (pr1 u2 x)).(let TMP_7 \def (\lambda (t0: T).(let TMP_6 
\def (THead k u1 t) in (pr1 TMP_6 t0))) in (let TMP_9 \def (\lambda (t0: 
T).(let TMP_8 \def (THead k u2 t) in (pr1 TMP_8 t0))) in (let TMP_10 \def 
(THead k x t) in (let TMP_11 \def (pr1_head_1 u1 x H1 t k) in (let TMP_12 
\def (pr1_head_1 u2 x H2 t k) in (ex_intro2 T TMP_7 TMP_9 TMP_10 TMP_11 
TMP_12))))))))) in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_13 H0)))))))))))).

theorem pc1_head_2:
 \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (u: T).(\forall 
(k: K).(pc1 (THead k u t1) (THead k u t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc1 t1 t2)).(\lambda (u: 
T).(\lambda (k: K).(let H0 \def H in (let TMP_1 \def (\lambda (t: T).(pr1 t1 
t)) in (let TMP_2 \def (\lambda (t: T).(pr1 t2 t)) in (let TMP_3 \def (THead 
k u t1) in (let TMP_4 \def (THead k u t2) in (let TMP_5 \def (pc1 TMP_3 
TMP_4) in (let TMP_13 \def (\lambda (x: T).(\lambda (H1: (pr1 t1 x)).(\lambda 
(H2: (pr1 t2 x)).(let TMP_7 \def (\lambda (t: T).(let TMP_6 \def (THead k u 
t1) in (pr1 TMP_6 t))) in (let TMP_9 \def (\lambda (t: T).(let TMP_8 \def 
(THead k u t2) in (pr1 TMP_8 t))) in (let TMP_10 \def (THead k u x) in (let 
TMP_11 \def (pr1_head_2 t1 x H1 u k) in (let TMP_12 \def (pr1_head_2 t2 x H2 
u k) in (ex_intro2 T TMP_7 TMP_9 TMP_10 TMP_11 TMP_12))))))))) in (ex2_ind T 
TMP_1 TMP_2 TMP_5 TMP_13 H0)))))))))))).

theorem pc1_t:
 \forall (t2: T).(\forall (t1: T).((pc1 t1 t2) \to (\forall (t3: T).((pc1 t2 
t3) \to (pc1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc1 t1 t2)).(\lambda (t3: 
T).(\lambda (H0: (pc1 t2 t3)).(let H1 \def H0 in (let TMP_1 \def (\lambda (t: 
T).(pr1 t2 t)) in (let TMP_2 \def (\lambda (t: T).(pr1 t3 t)) in (let TMP_3 
\def (pc1 t1 t3) in (let TMP_17 \def (\lambda (x: T).(\lambda (H2: (pr1 t2 
x)).(\lambda (H3: (pr1 t3 x)).(let H4 \def H in (let TMP_4 \def (\lambda (t: 
T).(pr1 t1 t)) in (let TMP_5 \def (\lambda (t: T).(pr1 t2 t)) in (let TMP_6 
\def (pc1 t1 t3) in (let TMP_16 \def (\lambda (x0: T).(\lambda (H5: (pr1 t1 
x0)).(\lambda (H6: (pr1 t2 x0)).(let TMP_7 \def (\lambda (t: T).(pr1 x0 t)) 
in (let TMP_8 \def (\lambda (t: T).(pr1 x t)) in (let TMP_9 \def (pc1 t1 t3) 
in (let TMP_14 \def (\lambda (x1: T).(\lambda (H7: (pr1 x0 x1)).(\lambda (H8: 
(pr1 x x1)).(let TMP_10 \def (\lambda (t: T).(pr1 t1 t)) in (let TMP_11 \def 
(\lambda (t: T).(pr1 t3 t)) in (let TMP_12 \def (pr1_t x0 t1 H5 x1 H7) in 
(let TMP_13 \def (pr1_t x t3 H3 x1 H8) in (ex_intro2 T TMP_10 TMP_11 x1 
TMP_12 TMP_13)))))))) in (let TMP_15 \def (pr1_confluence t2 x0 H6 x H2) in 
(ex2_ind T TMP_7 TMP_8 TMP_9 TMP_14 TMP_15))))))))) in (ex2_ind T TMP_4 TMP_5 
TMP_6 TMP_16 H4))))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_17 H1)))))))))).

theorem pc1_pr0_u2:
 \forall (t0: T).(\forall (t1: T).((pr0 t0 t1) \to (\forall (t2: T).((pc1 t0 
t2) \to (pc1 t1 t2)))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr0 t0 t1)).(\lambda (t2: 
T).(\lambda (H0: (pc1 t0 t2)).(let TMP_1 \def (pc1_pr0_x t1 t0 H) in (pc1_t 
t0 t1 TMP_1 t2 H0)))))).

theorem pc1_head:
 \forall (u1: T).(\forall (u2: T).((pc1 u1 u2) \to (\forall (t1: T).(\forall 
(t2: T).((pc1 t1 t2) \to (\forall (k: K).(pc1 (THead k u1 t1) (THead k u2 
t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc1 u1 u2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pc1 t1 t2)).(\lambda (k: K).(let TMP_1 
\def (THead k u2 t1) in (let TMP_2 \def (THead k u1 t1) in (let TMP_3 \def 
(pc1_head_1 u1 u2 H t1 k) in (let TMP_4 \def (THead k u2 t2) in (let TMP_5 
\def (pc1_head_2 t1 t2 H0 u2 k) in (pc1_t TMP_1 TMP_2 TMP_3 TMP_4 
TMP_5)))))))))))).

