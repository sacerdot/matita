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

include "basic_1/wcpr0/getl.ma".

theorem pc3_wcpr0__pc3_wcpr0_t_aux:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (k: K).(\forall 
(u: T).(\forall (t1: T).(\forall (t2: T).((pr3 (CHead c1 k u) t1 t2) \to (pc3 
(CHead c2 k u) t1 t2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(\lambda (k: 
K).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 
(CHead c1 k u) t1 t2)).(let TMP_1 \def (CHead c1 k u) in (let TMP_3 \def 
(\lambda (t: T).(\lambda (t0: T).(let TMP_2 \def (CHead c2 k u) in (pc3 TMP_2 
t t0)))) in (let TMP_5 \def (\lambda (t: T).(let TMP_4 \def (CHead c2 k u) in 
(pc3_refl TMP_4 t))) in (let TMP_52 \def (\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H1: (pr2 (CHead c1 k u) t4 t3)).(\lambda (t5: T).(\lambda (_: 
(pr3 (CHead c1 k u) t3 t5)).(\lambda (H3: (pc3 (CHead c2 k u) t3 t5)).(let 
TMP_6 \def (CHead c2 k u) in (let TMP_7 \def (CHead c1 k u) in (let TMP_8 
\def (\lambda (c: C).(pr2 c t4 t3)) in (let TMP_10 \def (\lambda (_: C).(let 
TMP_9 \def (CHead c2 k u) in (pc3 TMP_9 t4 t3))) in (let TMP_50 \def (\lambda 
(y: C).(\lambda (H4: (pr2 y t4 t3)).(let TMP_12 \def (\lambda (c: C).(\lambda 
(t: T).(\lambda (t0: T).((eq C c (CHead c1 k u)) \to (let TMP_11 \def (CHead 
c2 k u) in (pc3 TMP_11 t t0)))))) in (let TMP_16 \def (\lambda (c: 
C).(\lambda (t6: T).(\lambda (t0: T).(\lambda (H5: (pr0 t6 t0)).(\lambda (_: 
(eq C c (CHead c1 k u))).(let TMP_13 \def (CHead c2 k u) in (let TMP_14 \def 
(CHead c2 k u) in (let TMP_15 \def (pr2_free TMP_14 t6 t0 H5) in (pc3_pr2_r 
TMP_13 t6 t0 TMP_15))))))))) in (let TMP_49 \def (\lambda (c: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H5: (getl i c (CHead d (Bind 
Abbr) u0))).(\lambda (t6: T).(\lambda (t0: T).(\lambda (H6: (pr0 t6 
t0)).(\lambda (t: T).(\lambda (H7: (subst0 i u0 t0 t)).(\lambda (H8: (eq C c 
(CHead c1 k u))).(let TMP_19 \def (\lambda (c0: C).(let TMP_17 \def (Bind 
Abbr) in (let TMP_18 \def (CHead d TMP_17 u0) in (getl i c0 TMP_18)))) in 
(let TMP_20 \def (CHead c1 k u) in (let H9 \def (eq_ind C c TMP_19 H5 TMP_20 
H8) in (let TMP_24 \def (\lambda (e2: C).(\lambda (u2: T).(let TMP_21 \def 
(CHead c2 k u) in (let TMP_22 \def (Bind Abbr) in (let TMP_23 \def (CHead e2 
TMP_22 u2) in (getl i TMP_21 TMP_23)))))) in (let TMP_25 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 d e2))) in (let TMP_26 \def (\lambda (_: 
C).(\lambda (u2: T).(pr0 u0 u2))) in (let TMP_27 \def (CHead c2 k u) in (let 
TMP_28 \def (pc3 TMP_27 t6 t) in (let TMP_42 \def (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H10: (getl i (CHead c2 k u) (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (wcpr0 d x0)).(\lambda (H12: (pr0 u0 x1)).(let TMP_29 \def 
(\lambda (t7: T).(subst0 i x1 t0 t7)) in (let TMP_30 \def (\lambda (t7: 
T).(pr0 t t7)) in (let TMP_31 \def (CHead c2 k u) in (let TMP_32 \def (pc3 
TMP_31 t6 t) in (let TMP_40 \def (\lambda (x: T).(\lambda (H13: (subst0 i x1 
t0 x)).(\lambda (H14: (pr0 t x)).(let TMP_33 \def (CHead c2 k u) in (let 
TMP_34 \def (CHead c2 k u) in (let TMP_35 \def (pr2_delta TMP_34 x0 x1 i H10 
t6 t0 H6 x H13) in (let TMP_36 \def (CHead c2 k u) in (let TMP_37 \def (CHead 
c2 k u) in (let TMP_38 \def (pr2_free TMP_37 t x H14) in (let TMP_39 \def 
(pc3_pr2_x TMP_36 x t TMP_38) in (pc3_pr2_u TMP_33 x t6 TMP_35 t 
TMP_39))))))))))) in (let TMP_41 \def (pr0_subst0_fwd u0 t0 t i H7 x1 H12) in 
(ex2_ind T TMP_29 TMP_30 TMP_32 TMP_40 TMP_41)))))))))))) in (let TMP_43 \def 
(CHead c1 k u) in (let TMP_44 \def (CHead c2 k u) in (let TMP_45 \def 
(pr0_refl u) in (let TMP_46 \def (wcpr0_comp c1 c2 H u u TMP_45 k) in (let 
TMP_47 \def (Bind Abbr) in (let TMP_48 \def (wcpr0_getl TMP_43 TMP_44 TMP_46 
i d u0 TMP_47 H9) in (ex3_2_ind C T TMP_24 TMP_25 TMP_26 TMP_28 TMP_42 
TMP_48))))))))))))))))))))))))))) in (pr2_ind TMP_12 TMP_16 TMP_49 y t4 t3 
H4)))))) in (let TMP_51 \def (insert_eq C TMP_7 TMP_8 TMP_10 TMP_50 H1) in 
(pc3_t t3 TMP_6 t4 TMP_51 t5 H3))))))))))))) in (pr3_ind TMP_1 TMP_3 TMP_5 
TMP_52 t1 t2 H0)))))))))))).

theorem pc3_wcpr0_t:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: 
T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pc3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(let TMP_1 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 
t2) \to (pc3 c0 t1 t2)))))) in (let TMP_2 \def (\lambda (c: C).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).(pc3_pr3_r c t1 t2 H0))))) 
in (let TMP_16 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 
c3)).(\lambda (_: ((\forall (t1: T).(\forall (t2: T).((pr3 c0 t1 t2) \to (pc3 
c3 t1 t2)))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H3: (pr3 
(CHead c0 k u1) t1 t2)).(let TMP_3 \def (pr2_free c0 u1 u2 H2) in (let H4 
\def (pc3_pr2_pr3_t c0 u1 t1 t2 k H3 u2 TMP_3) in (let TMP_5 \def (\lambda 
(t: T).(let TMP_4 \def (CHead c0 k u2) in (pr3 TMP_4 t1 t))) in (let TMP_7 
\def (\lambda (t: T).(let TMP_6 \def (CHead c0 k u2) in (pr3 TMP_6 t2 t))) in 
(let TMP_8 \def (CHead c3 k u2) in (let TMP_9 \def (pc3 TMP_8 t1 t2) in (let 
TMP_15 \def (\lambda (x: T).(\lambda (H5: (pr3 (CHead c0 k u2) t1 
x)).(\lambda (H6: (pr3 (CHead c0 k u2) t2 x)).(let TMP_10 \def (CHead c3 k 
u2) in (let TMP_11 \def (pc3_wcpr0__pc3_wcpr0_t_aux c0 c3 H0 k u2 t1 x H5) in 
(let TMP_12 \def (CHead c3 k u2) in (let TMP_13 \def 
(pc3_wcpr0__pc3_wcpr0_t_aux c0 c3 H0 k u2 t2 x H6) in (let TMP_14 \def (pc3_s 
TMP_12 x t2 TMP_13) in (pc3_t x TMP_10 t1 TMP_11 t2 TMP_14))))))))) in 
(ex2_ind T TMP_5 TMP_7 TMP_9 TMP_15 H4))))))))))))))))))) in (wcpr0_ind TMP_1 
TMP_2 TMP_16 c1 c2 H)))))).

theorem pc3_wcpr0:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t1: 
T).(\forall (t2: T).((pc3 c1 t1 t2) \to (pc3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pc3 c1 t1 t2)).(let H1 \def H0 in (let 
TMP_1 \def (\lambda (t: T).(pr3 c1 t1 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr3 c1 t2 t)) in (let TMP_3 \def (pc3 c2 t1 t2) in (let TMP_7 \def 
(\lambda (x: T).(\lambda (H2: (pr3 c1 t1 x)).(\lambda (H3: (pr3 c1 t2 
x)).(let TMP_4 \def (pc3_wcpr0_t c1 c2 H t1 x H2) in (let TMP_5 \def 
(pc3_wcpr0_t c1 c2 H t2 x H3) in (let TMP_6 \def (pc3_s c2 x t2 TMP_5) in 
(pc3_t x c2 t1 TMP_4 t2 TMP_6))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_7 
H1))))))))))).

