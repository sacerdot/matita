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

include "basic_1/pc3/props.ma".

let rec pc3_left_ind (c: C) (P: (T \to (T \to Prop))) (f: (\forall (t: T).(P 
t t))) (f0: (\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(t3: T).((pc3_left c t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) (f1: (\forall 
(t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall (t3: T).((pc3_left c t1 
t3) \to ((P t1 t3) \to (P t2 t3)))))))) (t: T) (t0: T) (p: pc3_left c t t0) 
on p: P t t0 \def match p with [(pc3_left_r t1) \Rightarrow (f t1) | 
(pc3_left_ur t1 t2 p0 t3 p1) \Rightarrow (let TMP_2 \def ((pc3_left_ind c P f 
f0 f1) t2 t3 p1) in (f0 t1 t2 p0 t3 p1 TMP_2)) | (pc3_left_ux t1 t2 p0 t3 p1) 
\Rightarrow (let TMP_1 \def ((pc3_left_ind c P f f0 f1) t1 t3 p1) in (f1 t1 
t2 p0 t3 p1 TMP_1))].

theorem pc3_ind_left__pc3_left_pr3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to 
(pc3_left c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(\lambda (t0: T).(pc3_left c t t0))) in 
(let TMP_2 \def (\lambda (t: T).(pc3_left_r c t)) in (let TMP_3 \def (\lambda 
(t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t3 t0)).(\lambda (t4: 
T).(\lambda (_: (pr3 c t0 t4)).(\lambda (H2: (pc3_left c t0 t4)).(pc3_left_ur 
c t3 t0 H0 t4 H2))))))) in (pr3_ind c TMP_1 TMP_2 TMP_3 t1 t2 H))))))).

theorem pc3_ind_left__pc3_left_trans:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(\forall (t3: T).((pc3_left c t2 t3) \to (pc3_left c t1 t3))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(\lambda (t0: T).(\forall (t3: 
T).((pc3_left c t0 t3) \to (pc3_left c t t3))))) in (let TMP_2 \def (\lambda 
(t: T).(\lambda (t3: T).(\lambda (H0: (pc3_left c t t3)).H0))) in (let TMP_4 
\def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda 
(t4: T).(\lambda (_: (pc3_left c t3 t4)).(\lambda (H2: ((\forall (t5: 
T).((pc3_left c t4 t5) \to (pc3_left c t3 t5))))).(\lambda (t5: T).(\lambda 
(H3: (pc3_left c t4 t5)).(let TMP_3 \def (H2 t5 H3) in (pc3_left_ur c t0 t3 
H0 t5 TMP_3)))))))))) in (let TMP_6 \def (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t0 
t4)).(\lambda (H2: ((\forall (t5: T).((pc3_left c t4 t5) \to (pc3_left c t0 
t5))))).(\lambda (t5: T).(\lambda (H3: (pc3_left c t4 t5)).(let TMP_5 \def 
(H2 t5 H3) in (pc3_left_ux c t0 t3 H0 t5 TMP_5)))))))))) in (pc3_left_ind c 
TMP_1 TMP_2 TMP_4 TMP_6 t1 t2 H)))))))).

theorem pc3_ind_left__pc3_left_sym:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(pc3_left c t2 t1))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(\lambda (t0: T).(pc3_left c t0 t))) in 
(let TMP_2 \def (\lambda (t: T).(pc3_left_r c t)) in (let TMP_5 \def (\lambda 
(t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: 
T).(\lambda (_: (pc3_left c t3 t4)).(\lambda (H2: (pc3_left c t4 t3)).(let 
TMP_3 \def (pc3_left_r c t0) in (let TMP_4 \def (pc3_left_ux c t0 t3 H0 t0 
TMP_3) in (pc3_ind_left__pc3_left_trans c t4 t3 H2 t0 TMP_4))))))))) in (let 
TMP_8 \def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 
t3)).(\lambda (t4: T).(\lambda (_: (pc3_left c t0 t4)).(\lambda (H2: 
(pc3_left c t4 t0)).(let TMP_6 \def (pc3_left_r c t3) in (let TMP_7 \def 
(pc3_left_ur c t0 t3 H0 t3 TMP_6) in (pc3_ind_left__pc3_left_trans c t4 t0 H2 
t3 TMP_7))))))))) in (pc3_left_ind c TMP_1 TMP_2 TMP_5 TMP_8 t1 t2 H)))))))).

theorem pc3_ind_left__pc3_left_pc3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to 
(pc3_left c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(let H0 \def H in (let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let 
TMP_2 \def (\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pc3_left c t1 
t2) in (let TMP_7 \def (\lambda (x: T).(\lambda (H1: (pr3 c t1 x)).(\lambda 
(H2: (pr3 c t2 x)).(let TMP_4 \def (pc3_ind_left__pc3_left_pr3 c t1 x H1) in 
(let TMP_5 \def (pc3_ind_left__pc3_left_pr3 c t2 x H2) in (let TMP_6 \def 
(pc3_ind_left__pc3_left_sym c t2 x TMP_5) in (pc3_ind_left__pc3_left_trans c 
t1 x TMP_4 t2 TMP_6))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_7 H0))))))))).

theorem pc3_ind_left__pc3_pc3_left:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3_left c t1 t2) \to 
(pc3 c t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3_left c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(\lambda (t0: T).(pc3 c t t0))) in (let 
TMP_2 \def (\lambda (t: T).(pc3_refl c t)) in (let TMP_4 \def (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda (t4: T).(\lambda 
(_: (pc3_left c t3 t4)).(\lambda (H2: (pc3 c t3 t4)).(let TMP_3 \def 
(pc3_pr2_r c t0 t3 H0) in (pc3_t t3 c t0 TMP_3 t4 H2)))))))) in (let TMP_6 
\def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t0 t3)).(\lambda 
(t4: T).(\lambda (_: (pc3_left c t0 t4)).(\lambda (H2: (pc3 c t0 t4)).(let 
TMP_5 \def (pc3_pr2_x c t3 t0 H0) in (pc3_t t0 c t3 TMP_5 t4 H2)))))))) in 
(pc3_left_ind c TMP_1 TMP_2 TMP_4 TMP_6 t1 t2 H)))))))).

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
t3))))))))).(\lambda (t: T).(\lambda (t0: T).(\lambda (H2: (pc3 c t t0)).(let 
TMP_1 \def (\lambda (t1: T).(\lambda (t2: T).(P t1 t2))) in (let TMP_3 \def 
(\lambda (t1: T).(\lambda (t2: T).(\lambda (H3: (pr2 c t1 t2)).(\lambda (t3: 
T).(\lambda (H4: (pc3_left c t2 t3)).(\lambda (H5: (P t2 t3)).(let TMP_2 \def 
(pc3_ind_left__pc3_pc3_left c t2 t3 H4) in (H0 t1 t2 H3 t3 TMP_2 H5)))))))) 
in (let TMP_5 \def (\lambda (t1: T).(\lambda (t2: T).(\lambda (H3: (pr2 c t1 
t2)).(\lambda (t3: T).(\lambda (H4: (pc3_left c t1 t3)).(\lambda (H5: (P t1 
t3)).(let TMP_4 \def (pc3_ind_left__pc3_pc3_left c t1 t3 H4) in (H1 t1 t2 H3 
t3 TMP_4 H5)))))))) in (let TMP_6 \def (pc3_ind_left__pc3_left_pc3 c t t0 H2) 
in (pc3_left_ind c TMP_1 H TMP_3 TMP_5 t t0 TMP_6)))))))))))).

