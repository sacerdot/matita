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

include "basic_1/subst1/fwd.ma".

include "basic_1/subst0/subst0.ma".

theorem subst1_subst1:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i 
u u1 u2) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: 
T).(subst1 (S (plus i j)) u t t2)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst1 j u2 t1 t2)).(let TMP_5 \def (\lambda (t: T).(\forall (u1: 
T).(\forall (u: T).(\forall (i: nat).((subst1 i u u1 u2) \to (let TMP_1 \def 
(\lambda (t0: T).(subst1 j u1 t1 t0)) in (let TMP_4 \def (\lambda (t0: 
T).(let TMP_2 \def (plus i j) in (let TMP_3 \def (S TMP_2) in (subst1 TMP_3 u 
t0 t)))) in (ex2 T TMP_1 TMP_4)))))))) in (let TMP_14 \def (\lambda (u1: 
T).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: (subst1 i u u1 u2)).(let 
TMP_6 \def (\lambda (t: T).(subst1 j u1 t1 t)) in (let TMP_9 \def (\lambda 
(t: T).(let TMP_7 \def (plus i j) in (let TMP_8 \def (S TMP_7) in (subst1 
TMP_8 u t t1)))) in (let TMP_10 \def (subst1_refl j u1 t1) in (let TMP_11 
\def (plus i j) in (let TMP_12 \def (S TMP_11) in (let TMP_13 \def 
(subst1_refl TMP_12 u t1) in (ex_intro2 T TMP_6 TMP_9 t1 TMP_10 
TMP_13))))))))))) in (let TMP_63 \def (\lambda (t3: T).(\lambda (H0: (subst0 
j u2 t1 t3)).(\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: 
(subst1 i u u1 u2)).(let TMP_15 \def (\lambda (t: T).(subst1 i u u1 t)) in 
(let TMP_20 \def (\lambda (_: T).(let TMP_16 \def (\lambda (t0: T).(subst1 j 
u1 t1 t0)) in (let TMP_19 \def (\lambda (t0: T).(let TMP_17 \def (plus i j) 
in (let TMP_18 \def (S TMP_17) in (subst1 TMP_18 u t0 t3)))) in (ex2 T TMP_16 
TMP_19)))) in (let TMP_62 \def (\lambda (y: T).(\lambda (H2: (subst1 i u u1 
y)).(let TMP_25 \def (\lambda (t: T).((eq T t u2) \to (let TMP_21 \def 
(\lambda (t0: T).(subst1 j u1 t1 t0)) in (let TMP_24 \def (\lambda (t0: 
T).(let TMP_22 \def (plus i j) in (let TMP_23 \def (S TMP_22) in (subst1 
TMP_23 u t0 t3)))) in (ex2 T TMP_21 TMP_24))))) in (let TMP_40 \def (\lambda 
(H3: (eq T u1 u2)).(let TMP_30 \def (\lambda (t: T).(let TMP_26 \def (\lambda 
(t0: T).(subst1 j t t1 t0)) in (let TMP_29 \def (\lambda (t0: T).(let TMP_27 
\def (plus i j) in (let TMP_28 \def (S TMP_27) in (subst1 TMP_28 u t0 t3)))) 
in (ex2 T TMP_26 TMP_29)))) in (let TMP_31 \def (\lambda (t: T).(subst1 j u2 
t1 t)) in (let TMP_34 \def (\lambda (t: T).(let TMP_32 \def (plus i j) in 
(let TMP_33 \def (S TMP_32) in (subst1 TMP_33 u t t3)))) in (let TMP_35 \def 
(subst1_single j u2 t1 t3 H0) in (let TMP_36 \def (plus i j) in (let TMP_37 
\def (S TMP_36) in (let TMP_38 \def (subst1_refl TMP_37 u t3) in (let TMP_39 
\def (ex_intro2 T TMP_31 TMP_34 t3 TMP_35 TMP_38) in (eq_ind_r T u2 TMP_30 
TMP_39 u1 H3)))))))))) in (let TMP_61 \def (\lambda (t0: T).(\lambda (H3: 
(subst0 i u u1 t0)).(\lambda (H4: (eq T t0 u2)).(let TMP_41 \def (\lambda (t: 
T).(subst0 i u u1 t)) in (let H5 \def (eq_ind T t0 TMP_41 H3 u2 H4) in (let 
TMP_42 \def (\lambda (t: T).(subst0 j u1 t1 t)) in (let TMP_45 \def (\lambda 
(t: T).(let TMP_43 \def (plus i j) in (let TMP_44 \def (S TMP_43) in (subst0 
TMP_44 u t t3)))) in (let TMP_46 \def (\lambda (t: T).(subst1 j u1 t1 t)) in 
(let TMP_49 \def (\lambda (t: T).(let TMP_47 \def (plus i j) in (let TMP_48 
\def (S TMP_47) in (subst1 TMP_48 u t t3)))) in (let TMP_50 \def (ex2 T 
TMP_46 TMP_49) in (let TMP_59 \def (\lambda (x: T).(\lambda (H6: (subst0 j u1 
t1 x)).(\lambda (H7: (subst0 (S (plus i j)) u x t3)).(let TMP_51 \def 
(\lambda (t: T).(subst1 j u1 t1 t)) in (let TMP_54 \def (\lambda (t: T).(let 
TMP_52 \def (plus i j) in (let TMP_53 \def (S TMP_52) in (subst1 TMP_53 u t 
t3)))) in (let TMP_55 \def (subst1_single j u1 t1 x H6) in (let TMP_56 \def 
(plus i j) in (let TMP_57 \def (S TMP_56) in (let TMP_58 \def (subst1_single 
TMP_57 u x t3 H7) in (ex_intro2 T TMP_51 TMP_54 x TMP_55 TMP_58)))))))))) in 
(let TMP_60 \def (subst0_subst0 t1 t3 u2 j H0 u1 u i H5) in (ex2_ind T TMP_42 
TMP_45 TMP_50 TMP_59 TMP_60))))))))))))) in (subst1_ind i u u1 TMP_25 TMP_40 
TMP_61 y H2)))))) in (insert_eq T u2 TMP_15 TMP_20 TMP_62 H1)))))))))) in 
(subst1_ind j u2 t1 TMP_5 TMP_14 TMP_63 t2 H)))))))).

theorem subst1_subst1_back:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i 
u u2 u1) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: 
T).(subst1 (S (plus i j)) u t2 t)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst1 j u2 t1 t2)).(let TMP_5 \def (\lambda (t: T).(\forall (u1: 
T).(\forall (u: T).(\forall (i: nat).((subst1 i u u2 u1) \to (let TMP_1 \def 
(\lambda (t0: T).(subst1 j u1 t1 t0)) in (let TMP_4 \def (\lambda (t0: 
T).(let TMP_2 \def (plus i j) in (let TMP_3 \def (S TMP_2) in (subst1 TMP_3 u 
t t0)))) in (ex2 T TMP_1 TMP_4)))))))) in (let TMP_14 \def (\lambda (u1: 
T).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: (subst1 i u u2 u1)).(let 
TMP_6 \def (\lambda (t: T).(subst1 j u1 t1 t)) in (let TMP_9 \def (\lambda 
(t: T).(let TMP_7 \def (plus i j) in (let TMP_8 \def (S TMP_7) in (subst1 
TMP_8 u t1 t)))) in (let TMP_10 \def (subst1_refl j u1 t1) in (let TMP_11 
\def (plus i j) in (let TMP_12 \def (S TMP_11) in (let TMP_13 \def 
(subst1_refl TMP_12 u t1) in (ex_intro2 T TMP_6 TMP_9 t1 TMP_10 
TMP_13))))))))))) in (let TMP_49 \def (\lambda (t3: T).(\lambda (H0: (subst0 
j u2 t1 t3)).(\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: 
(subst1 i u u2 u1)).(let TMP_19 \def (\lambda (t: T).(let TMP_15 \def 
(\lambda (t0: T).(subst1 j t t1 t0)) in (let TMP_18 \def (\lambda (t0: 
T).(let TMP_16 \def (plus i j) in (let TMP_17 \def (S TMP_16) in (subst1 
TMP_17 u t3 t0)))) in (ex2 T TMP_15 TMP_18)))) in (let TMP_20 \def (\lambda 
(t: T).(subst1 j u2 t1 t)) in (let TMP_23 \def (\lambda (t: T).(let TMP_21 
\def (plus i j) in (let TMP_22 \def (S TMP_21) in (subst1 TMP_22 u t3 t)))) 
in (let TMP_24 \def (subst1_single j u2 t1 t3 H0) in (let TMP_25 \def (plus i 
j) in (let TMP_26 \def (S TMP_25) in (let TMP_27 \def (subst1_refl TMP_26 u 
t3) in (let TMP_28 \def (ex_intro2 T TMP_20 TMP_23 t3 TMP_24 TMP_27) in (let 
TMP_48 \def (\lambda (t0: T).(\lambda (H2: (subst0 i u u2 t0)).(let TMP_29 
\def (\lambda (t: T).(subst0 j t0 t1 t)) in (let TMP_32 \def (\lambda (t: 
T).(let TMP_30 \def (plus i j) in (let TMP_31 \def (S TMP_30) in (subst0 
TMP_31 u t3 t)))) in (let TMP_33 \def (\lambda (t: T).(subst1 j t0 t1 t)) in 
(let TMP_36 \def (\lambda (t: T).(let TMP_34 \def (plus i j) in (let TMP_35 
\def (S TMP_34) in (subst1 TMP_35 u t3 t)))) in (let TMP_37 \def (ex2 T 
TMP_33 TMP_36) in (let TMP_46 \def (\lambda (x: T).(\lambda (H3: (subst0 j t0 
t1 x)).(\lambda (H4: (subst0 (S (plus i j)) u t3 x)).(let TMP_38 \def 
(\lambda (t: T).(subst1 j t0 t1 t)) in (let TMP_41 \def (\lambda (t: T).(let 
TMP_39 \def (plus i j) in (let TMP_40 \def (S TMP_39) in (subst1 TMP_40 u t3 
t)))) in (let TMP_42 \def (subst1_single j t0 t1 x H3) in (let TMP_43 \def 
(plus i j) in (let TMP_44 \def (S TMP_43) in (let TMP_45 \def (subst1_single 
TMP_44 u t3 x H4) in (ex_intro2 T TMP_38 TMP_41 x TMP_42 TMP_45)))))))))) in 
(let TMP_47 \def (subst0_subst0_back t1 t3 u2 j H0 t0 u i H2) in (ex2_ind T 
TMP_29 TMP_32 TMP_37 TMP_46 TMP_47)))))))))) in (subst1_ind i u u2 TMP_19 
TMP_28 TMP_48 u1 H1)))))))))))))))) in (subst1_ind j u2 t1 TMP_5 TMP_14 
TMP_49 t2 H)))))))).

theorem subst1_trans:
 \forall (t2: T).(\forall (t1: T).(\forall (v: T).(\forall (i: nat).((subst1 
i v t1 t2) \to (\forall (t3: T).((subst1 i v t2 t3) \to (subst1 i v t1 
t3)))))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i v t1 t2)).(let TMP_1 \def (\lambda (t: T).(\forall (t3: 
T).((subst1 i v t t3) \to (subst1 i v t1 t3)))) in (let TMP_2 \def (\lambda 
(t3: T).(\lambda (H0: (subst1 i v t1 t3)).H0)) in (let TMP_7 \def (\lambda 
(t3: T).(\lambda (H0: (subst0 i v t1 t3)).(\lambda (t4: T).(\lambda (H1: 
(subst1 i v t3 t4)).(let TMP_3 \def (\lambda (t: T).(subst1 i v t1 t)) in 
(let TMP_4 \def (subst1_single i v t1 t3 H0) in (let TMP_6 \def (\lambda (t0: 
T).(\lambda (H2: (subst0 i v t3 t0)).(let TMP_5 \def (subst0_trans t3 t1 v i 
H0 t0 H2) in (subst1_single i v t1 t0 TMP_5)))) in (subst1_ind i v t3 TMP_3 
TMP_4 TMP_6 t4 H1)))))))) in (subst1_ind i v t1 TMP_1 TMP_2 TMP_7 t2 
H)))))))).

theorem subst1_confluence_neq:
 \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: 
nat).((subst1 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall 
(i2: nat).((subst1 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda 
(t: T).(subst1 i2 u2 t1 t)) (\lambda (t: T).(subst1 i1 u1 t2 t))))))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u1: T).(\lambda (i1: 
nat).(\lambda (H: (subst1 i1 u1 t0 t1)).(let TMP_3 \def (\lambda (t: 
T).(\forall (t2: T).(\forall (u2: T).(\forall (i2: nat).((subst1 i2 u2 t0 t2) 
\to ((not (eq nat i1 i2)) \to (let TMP_1 \def (\lambda (t3: T).(subst1 i2 u2 
t t3)) in (let TMP_2 \def (\lambda (t3: T).(subst1 i1 u1 t2 t3)) in (ex2 T 
TMP_1 TMP_2))))))))) in (let TMP_7 \def (\lambda (t2: T).(\lambda (u2: 
T).(\lambda (i2: nat).(\lambda (H0: (subst1 i2 u2 t0 t2)).(\lambda (_: (not 
(eq nat i1 i2))).(let TMP_4 \def (\lambda (t: T).(subst1 i2 u2 t0 t)) in (let 
TMP_5 \def (\lambda (t: T).(subst1 i1 u1 t2 t)) in (let TMP_6 \def 
(subst1_refl i1 u1 t2) in (ex_intro2 T TMP_4 TMP_5 t2 H0 TMP_6))))))))) in 
(let TMP_29 \def (\lambda (t2: T).(\lambda (H0: (subst0 i1 u1 t0 
t2)).(\lambda (t3: T).(\lambda (u2: T).(\lambda (i2: nat).(\lambda (H1: 
(subst1 i2 u2 t0 t3)).(\lambda (H2: (not (eq nat i1 i2))).(let TMP_10 \def 
(\lambda (t: T).(let TMP_8 \def (\lambda (t4: T).(subst1 i2 u2 t2 t4)) in 
(let TMP_9 \def (\lambda (t4: T).(subst1 i1 u1 t t4)) in (ex2 T TMP_8 
TMP_9)))) in (let TMP_11 \def (\lambda (t: T).(subst1 i2 u2 t2 t)) in (let 
TMP_12 \def (\lambda (t: T).(subst1 i1 u1 t0 t)) in (let TMP_13 \def 
(subst1_refl i2 u2 t2) in (let TMP_14 \def (subst1_single i1 u1 t0 t2 H0) in 
(let TMP_15 \def (ex_intro2 T TMP_11 TMP_12 t2 TMP_13 TMP_14) in (let TMP_28 
\def (\lambda (t4: T).(\lambda (H3: (subst0 i2 u2 t0 t4)).(let TMP_16 \def 
(\lambda (t: T).(subst0 i1 u1 t4 t)) in (let TMP_17 \def (\lambda (t: 
T).(subst0 i2 u2 t2 t)) in (let TMP_18 \def (\lambda (t: T).(subst1 i2 u2 t2 
t)) in (let TMP_19 \def (\lambda (t: T).(subst1 i1 u1 t4 t)) in (let TMP_20 
\def (ex2 T TMP_18 TMP_19) in (let TMP_25 \def (\lambda (x: T).(\lambda (H4: 
(subst0 i1 u1 t4 x)).(\lambda (H5: (subst0 i2 u2 t2 x)).(let TMP_21 \def 
(\lambda (t: T).(subst1 i2 u2 t2 t)) in (let TMP_22 \def (\lambda (t: 
T).(subst1 i1 u1 t4 t)) in (let TMP_23 \def (subst1_single i2 u2 t2 x H5) in 
(let TMP_24 \def (subst1_single i1 u1 t4 x H4) in (ex_intro2 T TMP_21 TMP_22 
x TMP_23 TMP_24)))))))) in (let TMP_26 \def (sym_not_eq nat i1 i2 H2) in (let 
TMP_27 \def (subst0_confluence_neq t0 t4 u2 i2 H3 t2 u1 i1 H0 TMP_26) in 
(ex2_ind T TMP_16 TMP_17 TMP_20 TMP_25 TMP_27))))))))))) in (subst1_ind i2 u2 
t0 TMP_10 TMP_15 TMP_28 t3 H1))))))))))))))) in (subst1_ind i1 u1 t0 TMP_3 
TMP_7 TMP_29 t1 H)))))))).

theorem subst1_confluence_eq:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t0 t1) \to (\forall (t2: T).((subst1 i u t0 t2) \to (ex2 T (\lambda (t: 
T).(subst1 i u t1 t)) (\lambda (t: T).(subst1 i u t2 t)))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t0 t1)).(let TMP_3 \def (\lambda (t: T).(\forall (t2: 
T).((subst1 i u t0 t2) \to (let TMP_1 \def (\lambda (t3: T).(subst1 i u t 
t3)) in (let TMP_2 \def (\lambda (t3: T).(subst1 i u t2 t3)) in (ex2 T TMP_1 
TMP_2)))))) in (let TMP_7 \def (\lambda (t2: T).(\lambda (H0: (subst1 i u t0 
t2)).(let TMP_4 \def (\lambda (t: T).(subst1 i u t0 t)) in (let TMP_5 \def 
(\lambda (t: T).(subst1 i u t2 t)) in (let TMP_6 \def (subst1_refl i u t2) in 
(ex_intro2 T TMP_4 TMP_5 t2 H0 TMP_6)))))) in (let TMP_57 \def (\lambda (t2: 
T).(\lambda (H0: (subst0 i u t0 t2)).(\lambda (t3: T).(\lambda (H1: (subst1 i 
u t0 t3)).(let TMP_10 \def (\lambda (t: T).(let TMP_8 \def (\lambda (t4: 
T).(subst1 i u t2 t4)) in (let TMP_9 \def (\lambda (t4: T).(subst1 i u t t4)) 
in (ex2 T TMP_8 TMP_9)))) in (let TMP_11 \def (\lambda (t: T).(subst1 i u t2 
t)) in (let TMP_12 \def (\lambda (t: T).(subst1 i u t0 t)) in (let TMP_13 
\def (subst1_refl i u t2) in (let TMP_14 \def (subst1_single i u t0 t2 H0) in 
(let TMP_15 \def (ex_intro2 T TMP_11 TMP_12 t2 TMP_13 TMP_14) in (let TMP_56 
\def (\lambda (t4: T).(\lambda (H2: (subst0 i u t0 t4)).(let TMP_16 \def (eq 
T t4 t2) in (let TMP_17 \def (\lambda (t: T).(subst0 i u t4 t)) in (let 
TMP_18 \def (\lambda (t: T).(subst0 i u t2 t)) in (let TMP_19 \def (ex2 T 
TMP_17 TMP_18) in (let TMP_20 \def (subst0 i u t4 t2) in (let TMP_21 \def 
(subst0 i u t2 t4) in (let TMP_22 \def (\lambda (t: T).(subst1 i u t2 t)) in 
(let TMP_23 \def (\lambda (t: T).(subst1 i u t4 t)) in (let TMP_24 \def (ex2 
T TMP_22 TMP_23) in (let TMP_33 \def (\lambda (H3: (eq T t4 t2)).(let TMP_27 
\def (\lambda (t: T).(let TMP_25 \def (\lambda (t5: T).(subst1 i u t2 t5)) in 
(let TMP_26 \def (\lambda (t5: T).(subst1 i u t t5)) in (ex2 T TMP_25 
TMP_26)))) in (let TMP_28 \def (\lambda (t: T).(subst1 i u t2 t)) in (let 
TMP_29 \def (\lambda (t: T).(subst1 i u t2 t)) in (let TMP_30 \def 
(subst1_refl i u t2) in (let TMP_31 \def (subst1_refl i u t2) in (let TMP_32 
\def (ex_intro2 T TMP_28 TMP_29 t2 TMP_30 TMP_31) in (eq_ind_r T t2 TMP_27 
TMP_32 t4 H3)))))))) in (let TMP_44 \def (\lambda (H3: (ex2 T (\lambda (t: 
T).(subst0 i u t4 t)) (\lambda (t: T).(subst0 i u t2 t)))).(let TMP_34 \def 
(\lambda (t: T).(subst0 i u t4 t)) in (let TMP_35 \def (\lambda (t: 
T).(subst0 i u t2 t)) in (let TMP_36 \def (\lambda (t: T).(subst1 i u t2 t)) 
in (let TMP_37 \def (\lambda (t: T).(subst1 i u t4 t)) in (let TMP_38 \def 
(ex2 T TMP_36 TMP_37) in (let TMP_43 \def (\lambda (x: T).(\lambda (H4: 
(subst0 i u t4 x)).(\lambda (H5: (subst0 i u t2 x)).(let TMP_39 \def (\lambda 
(t: T).(subst1 i u t2 t)) in (let TMP_40 \def (\lambda (t: T).(subst1 i u t4 
t)) in (let TMP_41 \def (subst1_single i u t2 x H5) in (let TMP_42 \def 
(subst1_single i u t4 x H4) in (ex_intro2 T TMP_39 TMP_40 x TMP_41 
TMP_42)))))))) in (ex2_ind T TMP_34 TMP_35 TMP_38 TMP_43 H3)))))))) in (let 
TMP_49 \def (\lambda (H3: (subst0 i u t4 t2)).(let TMP_45 \def (\lambda (t: 
T).(subst1 i u t2 t)) in (let TMP_46 \def (\lambda (t: T).(subst1 i u t4 t)) 
in (let TMP_47 \def (subst1_refl i u t2) in (let TMP_48 \def (subst1_single i 
u t4 t2 H3) in (ex_intro2 T TMP_45 TMP_46 t2 TMP_47 TMP_48)))))) in (let 
TMP_54 \def (\lambda (H3: (subst0 i u t2 t4)).(let TMP_50 \def (\lambda (t: 
T).(subst1 i u t2 t)) in (let TMP_51 \def (\lambda (t: T).(subst1 i u t4 t)) 
in (let TMP_52 \def (subst1_single i u t2 t4 H3) in (let TMP_53 \def 
(subst1_refl i u t4) in (ex_intro2 T TMP_50 TMP_51 t4 TMP_52 TMP_53)))))) in 
(let TMP_55 \def (subst0_confluence_eq t0 t4 u i H2 t2 H0) in (or4_ind TMP_16 
TMP_19 TMP_20 TMP_21 TMP_24 TMP_33 TMP_44 TMP_49 TMP_54 
TMP_55))))))))))))))))) in (subst1_ind i u t0 TMP_10 TMP_15 TMP_56 t3 
H1)))))))))))) in (subst1_ind i u t0 TMP_3 TMP_7 TMP_57 t1 H)))))))).

theorem subst1_confluence_lift:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t0 (lift (S O) i t1)) \to (\forall (t2: T).((subst1 i u t0 (lift (S O) i 
t2)) \to (eq T t1 t2)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t0 (lift (S O) i t1))).(let TMP_1 \def (S O) in (let TMP_2 
\def (lift TMP_1 i t1) in (let TMP_3 \def (\lambda (t: T).(subst1 i u t0 t)) 
in (let TMP_4 \def (\lambda (_: T).(\forall (t2: T).((subst1 i u t0 (lift (S 
O) i t2)) \to (eq T t1 t2)))) in (let TMP_70 \def (\lambda (y: T).(\lambda 
(H0: (subst1 i u t0 y)).(let TMP_5 \def (\lambda (t: T).((eq T t (lift (S O) 
i t1)) \to (\forall (t2: T).((subst1 i u t0 (lift (S O) i t2)) \to (eq T t1 
t2))))) in (let TMP_32 \def (\lambda (H1: (eq T t0 (lift (S O) i 
t1))).(\lambda (t2: T).(\lambda (H2: (subst1 i u t0 (lift (S O) i t2))).(let 
TMP_8 \def (\lambda (t: T).(let TMP_6 \def (S O) in (let TMP_7 \def (lift 
TMP_6 i t2) in (subst1 i u t TMP_7)))) in (let TMP_9 \def (S O) in (let 
TMP_10 \def (lift TMP_9 i t1) in (let H3 \def (eq_ind T t0 TMP_8 H2 TMP_10 
H1) in (let TMP_11 \def (S O) in (let TMP_12 \def (lift TMP_11 i t2) in (let 
TMP_13 \def (S O) in (let TMP_14 \def (lift TMP_13 i t1) in (let TMP_15 \def 
(S O) in (let TMP_16 \def (lift TMP_15 i t2) in (let TMP_17 \def (S O) in 
(let TMP_18 \def (le_n i) in (let TMP_19 \def (S O) in (let TMP_20 \def (plus 
TMP_19 i) in (let TMP_21 \def (\lambda (n: nat).(lt i n)) in (let TMP_22 \def 
(S O) in (let TMP_23 \def (plus TMP_22 i) in (let TMP_24 \def (le_n TMP_23) 
in (let TMP_25 \def (S O) in (let TMP_26 \def (plus i TMP_25) in (let TMP_27 
\def (S O) in (let TMP_28 \def (plus_sym i TMP_27) in (let TMP_29 \def 
(eq_ind_r nat TMP_20 TMP_21 TMP_24 TMP_26 TMP_28) in (let TMP_30 \def 
(subst1_gen_lift_eq t1 u TMP_16 TMP_17 i i TMP_18 TMP_29 H3) in (let H4 \def 
(sym_eq T TMP_12 TMP_14 TMP_30) in (let TMP_31 \def (S O) in (lift_inj t1 t2 
TMP_31 i H4)))))))))))))))))))))))))))))) in (let TMP_69 \def (\lambda (t2: 
T).(\lambda (H1: (subst0 i u t0 t2)).(\lambda (H2: (eq T t2 (lift (S O) i 
t1))).(\lambda (t3: T).(\lambda (H3: (subst1 i u t0 (lift (S O) i t3))).(let 
TMP_33 \def (\lambda (t: T).(subst0 i u t0 t)) in (let TMP_34 \def (S O) in 
(let TMP_35 \def (lift TMP_34 i t1) in (let H4 \def (eq_ind T t2 TMP_33 H1 
TMP_35 H2) in (let TMP_36 \def (S O) in (let TMP_37 \def (lift TMP_36 i t3) 
in (let TMP_38 \def (\lambda (t: T).(subst1 i u t0 t)) in (let TMP_39 \def 
(\lambda (_: T).(eq T t1 t3)) in (let TMP_68 \def (\lambda (y0: T).(\lambda 
(H5: (subst1 i u t0 y0)).(let TMP_40 \def (\lambda (t: T).((eq T t (lift (S 
O) i t3)) \to (eq T t1 t3))) in (let TMP_62 \def (\lambda (H6: (eq T t0 (lift 
(S O) i t3))).(let TMP_43 \def (\lambda (t: T).(let TMP_41 \def (S O) in (let 
TMP_42 \def (lift TMP_41 i t1) in (subst0 i u t TMP_42)))) in (let TMP_44 
\def (S O) in (let TMP_45 \def (lift TMP_44 i t3) in (let H7 \def (eq_ind T 
t0 TMP_43 H4 TMP_45 H6) in (let TMP_46 \def (S O) in (let TMP_47 \def (lift 
TMP_46 i t1) in (let TMP_48 \def (S O) in (let TMP_49 \def (le_n i) in (let 
TMP_50 \def (S O) in (let TMP_51 \def (plus TMP_50 i) in (let TMP_52 \def 
(\lambda (n: nat).(lt i n)) in (let TMP_53 \def (S O) in (let TMP_54 \def 
(plus TMP_53 i) in (let TMP_55 \def (le_n TMP_54) in (let TMP_56 \def (S O) 
in (let TMP_57 \def (plus i TMP_56) in (let TMP_58 \def (S O) in (let TMP_59 
\def (plus_sym i TMP_58) in (let TMP_60 \def (eq_ind_r nat TMP_51 TMP_52 
TMP_55 TMP_57 TMP_59) in (let TMP_61 \def (eq T t1 t3) in 
(subst0_gen_lift_false t3 u TMP_47 TMP_48 i i TMP_49 TMP_60 H7 
TMP_61)))))))))))))))))))))) in (let TMP_67 \def (\lambda (t4: T).(\lambda 
(H6: (subst0 i u t0 t4)).(\lambda (H7: (eq T t4 (lift (S O) i t3))).(let 
TMP_63 \def (\lambda (t: T).(subst0 i u t0 t)) in (let TMP_64 \def (S O) in 
(let TMP_65 \def (lift TMP_64 i t3) in (let H8 \def (eq_ind T t4 TMP_63 H6 
TMP_65 H7) in (let TMP_66 \def (subst0_confluence_lift t0 t3 u i H8 t1 H4) in 
(sym_eq T t3 t1 TMP_66))))))))) in (subst1_ind i u t0 TMP_40 TMP_62 TMP_67 y0 
H5)))))) in (insert_eq T TMP_37 TMP_38 TMP_39 TMP_68 H3))))))))))))))) in 
(subst1_ind i u t0 TMP_5 TMP_32 TMP_69 y H0)))))) in (insert_eq T TMP_2 TMP_3 
TMP_4 TMP_70 H)))))))))).

