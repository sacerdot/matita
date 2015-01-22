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

theorem pc3_ind_left__pc3_left_pr3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to 
(pc3_left c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(pc3_left c t t0))) (\lambda 
(t: T).(pc3_left_r c t)) (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 
c t3 t0)).(\lambda (t4: T).(\lambda (_: (pr3 c t0 t4)).(\lambda (H2: 
(pc3_left c t0 t4)).(pc3_left_ur c t3 t0 H0 t4 H2))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 87
END *)

theorem pc3_ind_left__pc3_left_trans:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(\forall (t3: T).((pc3_left c t2 t3) \to (pc3_left c t1 t3))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(pc3_left_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (t3: 
T).((pc3_left c t0 t3) \to (pc3_left c t t3))))) (\lambda (t: T).(\lambda 
(t3: T).(\lambda (H0: (pc3_left c t t3)).H0))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t3 
t4)).(\lambda (H2: ((\forall (t5: T).((pc3_left c t4 t5) \to (pc3_left c t3 
t5))))).(\lambda (t5: T).(\lambda (H3: (pc3_left c t4 t5)).(pc3_left_ur c t0 
t3 H0 t5 (H2 t5 H3)))))))))) (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: 
(pr2 c t0 t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t0 t4)).(\lambda 
(H2: ((\forall (t5: T).((pc3_left c t4 t5) \to (pc3_left c t0 
t5))))).(\lambda (t5: T).(\lambda (H3: (pc3_left c t4 t5)).(pc3_left_ux c t0 
t3 H0 t5 (H2 t5 H3)))))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 195
END *)

theorem pc3_ind_left__pc3_left_sym:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(pc3_left c t2 t1))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(pc3_left_ind c (\lambda (t: T).(\lambda (t0: T).(pc3_left c t0 t))) 
(\lambda (t: T).(pc3_left_r c t)) (\lambda (t0: T).(\lambda (t3: T).(\lambda 
(H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t3 
t4)).(\lambda (H2: (pc3_left c t4 t3)).(pc3_ind_left__pc3_left_trans c t4 t3 
H2 t0 (pc3_left_ux c t0 t3 H0 t0 (pc3_left_r c t0))))))))) (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda 
(_: (pc3_left c t0 t4)).(\lambda (H2: (pc3_left c t4 
t0)).(pc3_ind_left__pc3_left_trans c t4 t0 H2 t3 (pc3_left_ur c t0 t3 H0 t3 
(pc3_left_r c t3))))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 163
END *)

theorem pc3_ind_left__pc3_left_pc3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to 
(pc3_left c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr3 c t1 t)) (\lambda (t: 
T).(pr3 c t2 t)) (pc3_left c t1 t2) (\lambda (x: T).(\lambda (H1: (pr3 c t1 
x)).(\lambda (H2: (pr3 c t2 x)).(pc3_ind_left__pc3_left_trans c t1 x 
(pc3_ind_left__pc3_left_pr3 c t1 x H1) t2 (pc3_ind_left__pc3_left_sym c t2 x 
(pc3_ind_left__pc3_left_pr3 c t2 x H2)))))) H0))))).
(* COMMENTS
Initial nodes: 105
END *)

theorem pc3_ind_left__pc3_pc3_left:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(pc3 c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(pc3_left_ind c (\lambda (t: T).(\lambda (t0: T).(pc3 c t t0))) (\lambda 
(t: T).(pc3_refl c t)) (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c 
t0 t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t3 t4)).(\lambda (H2: (pc3 
c t3 t4)).(pc3_t t3 c t0 (pc3_pr2_r c t0 t3 H0) t4 H2))))))) (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda 
(_: (pc3_left c t0 t4)).(\lambda (H2: (pc3 c t0 t4)).(pc3_t t0 c t3 
(pc3_pr2_x c t3 t0 H0) t4 H2))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 147
END *)

theorem pc3_ind_left:
 \forall (c: C).(\forall (P: ((T \to (T \to Prop)))).(((\forall (t: T).(P t 
t))) \to (((\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: 
T).((pc3 c t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) \to (((\forall (t1: 
T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3 c t1 t3) \to 
((P t1 t3) \to (P t2 t3)))))))) \to (\forall (t: T).(\forall (t0: T).((pc3 c 
t t0) \to (P t t0))))))))
\def
 \lambda (c: C).(\lambda (P: ((T \to (T \to Prop)))).(\lambda (H: ((\forall 
(t: T).(P t t)))).(\lambda (H0: ((\forall (t1: T).(\forall (t2: T).((pr2 c t1 
t2) \to (\forall (t3: T).((pc3 c t2 t3) \to ((P t2 t3) \to (P t1 
t3))))))))).(\lambda (H1: ((\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) 
\to (\forall (t3: T).((pc3 c t1 t3) \to ((P t1 t3) \to (P t2 
t3))))))))).(\lambda (t: T).(\lambda (t0: T).(\lambda (H2: (pc3 c t 
t0)).(pc3_left_ind c (\lambda (t1: T).(\lambda (t2: T).(P t1 t2))) H (\lambda 
(t1: T).(\lambda (t2: T).(\lambda (H3: (pr2 c t1 t2)).(\lambda (t3: 
T).(\lambda (H4: (pc3_left c t2 t3)).(\lambda (H5: (P t2 t3)).(H0 t1 t2 H3 t3 
(pc3_ind_left__pc3_pc3_left c t2 t3 H4) H5))))))) (\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H3: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda (H4: (pc3_left 
c t1 t3)).(\lambda (H5: (P t1 t3)).(H1 t1 t2 H3 t3 
(pc3_ind_left__pc3_pc3_left c t1 t3 H4) H5))))))) t t0 
(pc3_ind_left__pc3_left_pc3 c t t0 H2))))))))).
(* COMMENTS
Initial nodes: 225
END *)

