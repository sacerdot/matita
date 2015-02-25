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

include "basic_1/pr3/props.ma".

include "basic_1/wcpr0/getl.ma".

theorem pr3_wcpr0_t:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (t1: 
T).(\forall (t2: T).((pr3 c1 t1 t2) \to (pr3 c2 t1 t2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(let TMP_1 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (t1: T).(\forall (t2: T).((pr3 c0 
t1 t2) \to (pr3 c t1 t2)))))) in (let TMP_2 \def (\lambda (c: C).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (H0: (pr3 c t1 t2)).H0)))) in (let TMP_57 
\def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H0: (wcpr0 c0 c3)).(\lambda 
(_: ((\forall (t1: T).(\forall (t2: T).((pr3 c3 t1 t2) \to (pr3 c0 t1 
t2)))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H3: (pr3 
(CHead c3 k u2) t1 t2)).(let TMP_3 \def (CHead c3 k u1) in (let TMP_5 \def 
(\lambda (t: T).(\lambda (t0: T).(let TMP_4 \def (CHead c0 k u1) in (pr3 
TMP_4 t t0)))) in (let TMP_7 \def (\lambda (t: T).(let TMP_6 \def (CHead c0 k 
u1) in (pr3_refl TMP_6 t))) in (let TMP_54 \def (\lambda (t0: T).(\lambda 
(t3: T).(\lambda (H4: (pr2 (CHead c3 k u1) t3 t0)).(\lambda (t4: T).(\lambda 
(_: (pr3 (CHead c3 k u1) t0 t4)).(\lambda (H6: (pr3 (CHead c0 k u1) t0 
t4)).(let TMP_8 \def (CHead c0 k u1) in (let TMP_9 \def (CHead c3 k u1) in 
(let TMP_10 \def (\lambda (c: C).(pr2 c t3 t0)) in (let TMP_12 \def (\lambda 
(_: C).(let TMP_11 \def (CHead c0 k u1) in (pr3 TMP_11 t3 t0))) in (let 
TMP_52 \def (\lambda (y: C).(\lambda (H7: (pr2 y t3 t0)).(let TMP_14 \def 
(\lambda (c: C).(\lambda (t: T).(\lambda (t5: T).((eq C c (CHead c3 k u1)) 
\to (let TMP_13 \def (CHead c0 k u1) in (pr3 TMP_13 t t5)))))) in (let TMP_18 
\def (\lambda (c: C).(\lambda (t5: T).(\lambda (t6: T).(\lambda (H8: (pr0 t5 
t6)).(\lambda (_: (eq C c (CHead c3 k u1))).(let TMP_15 \def (CHead c0 k u1) 
in (let TMP_16 \def (CHead c0 k u1) in (let TMP_17 \def (pr2_free TMP_16 t5 
t6 H8) in (pr3_pr2 TMP_15 t5 t6 TMP_17))))))))) in (let TMP_51 \def (\lambda 
(c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H8: (getl 
i c (CHead d (Bind Abbr) u))).(\lambda (t5: T).(\lambda (t6: T).(\lambda (H9: 
(pr0 t5 t6)).(\lambda (t: T).(\lambda (H10: (subst0 i u t6 t)).(\lambda (H11: 
(eq C c (CHead c3 k u1))).(let TMP_21 \def (\lambda (c4: C).(let TMP_19 \def 
(Bind Abbr) in (let TMP_20 \def (CHead d TMP_19 u) in (getl i c4 TMP_20)))) 
in (let TMP_22 \def (CHead c3 k u1) in (let H12 \def (eq_ind C c TMP_21 H8 
TMP_22 H11) in (let TMP_26 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_23 
\def (CHead c0 k u1) in (let TMP_24 \def (Bind Abbr) in (let TMP_25 \def 
(CHead e2 TMP_24 u3) in (getl i TMP_23 TMP_25)))))) in (let TMP_27 \def 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 d))) in (let TMP_28 \def (\lambda 
(_: C).(\lambda (u3: T).(pr0 u3 u))) in (let TMP_29 \def (CHead c0 k u1) in 
(let TMP_30 \def (pr3 TMP_29 t5 t) in (let TMP_44 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H13: (getl i (CHead c0 k u1) (CHead x0 (Bind 
Abbr) x1))).(\lambda (_: (wcpr0 x0 d)).(\lambda (H15: (pr0 x1 u)).(let TMP_31 
\def (\lambda (t7: T).(subst0 i x1 t6 t7)) in (let TMP_32 \def (\lambda (t7: 
T).(pr0 t7 t)) in (let TMP_33 \def (CHead c0 k u1) in (let TMP_34 \def (pr3 
TMP_33 t5 t) in (let TMP_42 \def (\lambda (x: T).(\lambda (H16: (subst0 i x1 
t6 x)).(\lambda (H17: (pr0 x t)).(let TMP_35 \def (CHead c0 k u1) in (let 
TMP_36 \def (CHead c0 k u1) in (let TMP_37 \def (pr2_delta TMP_36 x0 x1 i H13 
t5 t6 H9 x H16) in (let TMP_38 \def (CHead c0 k u1) in (let TMP_39 \def 
(CHead c0 k u1) in (let TMP_40 \def (pr2_free TMP_39 x t H17) in (let TMP_41 
\def (pr3_pr2 TMP_38 x t TMP_40) in (pr3_sing TMP_35 x t5 TMP_37 t 
TMP_41))))))))))) in (let TMP_43 \def (pr0_subst0_back u t6 t i H10 x1 H15) 
in (ex2_ind T TMP_31 TMP_32 TMP_34 TMP_42 TMP_43)))))))))))) in (let TMP_45 
\def (CHead c3 k u1) in (let TMP_46 \def (CHead c0 k u1) in (let TMP_47 \def 
(pr0_refl u1) in (let TMP_48 \def (wcpr0_comp c0 c3 H0 u1 u1 TMP_47 k) in 
(let TMP_49 \def (Bind Abbr) in (let TMP_50 \def (wcpr0_getl_back TMP_45 
TMP_46 TMP_48 i d u TMP_49 H12) in (ex3_2_ind C T TMP_26 TMP_27 TMP_28 TMP_30 
TMP_44 TMP_50))))))))))))))))))))))))))) in (pr2_ind TMP_14 TMP_18 TMP_51 y 
t3 t0 H7)))))) in (let TMP_53 \def (insert_eq C TMP_9 TMP_10 TMP_12 TMP_52 
H4) in (pr3_t t0 t3 TMP_8 TMP_53 t4 H6))))))))))))) in (let TMP_55 \def 
(pr2_free c3 u1 u2 H2) in (let TMP_56 \def (pr3_pr2_pr3_t c3 u2 t1 t2 k H3 u1 
TMP_55) in (pr3_ind TMP_3 TMP_5 TMP_7 TMP_54 t1 t2 TMP_56)))))))))))))))))) 
in (wcpr0_ind TMP_1 TMP_2 TMP_57 c2 c1 H)))))).

