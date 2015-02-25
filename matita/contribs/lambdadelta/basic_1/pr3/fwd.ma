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

include "basic_1/pr3/defs.ma".

include "basic_1/pr2/fwd.ma".

let rec pr3_ind (c: C) (P: (T \to (T \to Prop))) (f: (\forall (t: T).(P t 
t))) (f0: (\forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall (t3: 
T).((pr3 c t2 t3) \to ((P t2 t3) \to (P t1 t3)))))))) (t: T) (t0: T) (p: pr3 
c t t0) on p: P t t0 \def match p with [(pr3_refl t1) \Rightarrow (f t1) | 
(pr3_sing t2 t1 p0 t3 p1) \Rightarrow (let TMP_1 \def ((pr3_ind c P f f0) t2 
t3 p1) in (f0 t2 t1 p0 t3 p1 TMP_1))].

theorem pr3_gen_sort:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TSort n) x) \to 
(eq T x (TSort n)))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr3 c (TSort 
n) x)).(let TMP_1 \def (TSort n) in (let TMP_2 \def (\lambda (t: T).(pr3 c t 
x)) in (let TMP_3 \def (\lambda (t: T).(eq T x t)) in (let TMP_17 \def 
(\lambda (y: T).(\lambda (H0: (pr3 c y x)).(let TMP_4 \def (\lambda (t: 
T).(\lambda (t0: T).((eq T t (TSort n)) \to (eq T t0 t)))) in (let TMP_5 \def 
(\lambda (t: T).(\lambda (_: (eq T t (TSort n))).(refl_equal T t))) in (let 
TMP_16 \def (\lambda (t2: T).(\lambda (t1: T).(\lambda (H1: (pr2 c t1 
t2)).(\lambda (t3: T).(\lambda (_: (pr3 c t2 t3)).(\lambda (H3: (((eq T t2 
(TSort n)) \to (eq T t3 t2)))).(\lambda (H4: (eq T t1 (TSort n))).(let TMP_6 
\def (\lambda (t: T).(pr2 c t t2)) in (let TMP_7 \def (TSort n) in (let H5 
\def (eq_ind T t1 TMP_6 H1 TMP_7 H4) in (let TMP_8 \def (TSort n) in (let 
TMP_9 \def (\lambda (t: T).(eq T t3 t)) in (let TMP_10 \def (\lambda (t: 
T).((eq T t (TSort n)) \to (eq T t3 t))) in (let TMP_11 \def (TSort n) in 
(let TMP_12 \def (pr2_gen_sort c t2 n H5) in (let H6 \def (eq_ind T t2 TMP_10 
H3 TMP_11 TMP_12) in (let TMP_13 \def (TSort n) in (let TMP_14 \def 
(refl_equal T TMP_13) in (let TMP_15 \def (H6 TMP_14) in (eq_ind_r T TMP_8 
TMP_9 TMP_15 t1 H4)))))))))))))))))))) in (pr3_ind c TMP_4 TMP_5 TMP_16 y x 
H0)))))) in (insert_eq T TMP_1 TMP_2 TMP_3 TMP_17 H)))))))).

theorem pr3_gen_abst:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Bind Abst) u1 t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: 
T).(pr3 (CHead c (Bind b) u) t1 t2))))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Bind Abst) u1 t1) x)).(let TMP_1 \def (Bind Abst) in (let 
TMP_2 \def (THead TMP_1 u1 t1) in (let TMP_3 \def (\lambda (t: T).(pr3 c t 
x)) in (let TMP_11 \def (\lambda (_: T).(let TMP_6 \def (\lambda (u2: 
T).(\lambda (t2: T).(let TMP_4 \def (Bind Abst) in (let TMP_5 \def (THead 
TMP_4 u2 t2) in (eq T x TMP_5))))) in (let TMP_7 \def (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) in (let TMP_10 \def (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(let TMP_8 \def (Bind b) 
in (let TMP_9 \def (CHead c TMP_8 u) in (pr3 TMP_9 t1 t2))))))) in (ex3_2 T T 
TMP_6 TMP_7 TMP_10))))) in (let TMP_112 \def (\lambda (y: T).(\lambda (H0: 
(pr3 c y x)).(let TMP_19 \def (\lambda (t: T).((eq T y (THead (Bind Abst) u1 
t)) \to (let TMP_14 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_12 \def 
(Bind Abst) in (let TMP_13 \def (THead TMP_12 u2 t2) in (eq T x TMP_13))))) 
in (let TMP_15 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c u1 u2))) in (let 
TMP_18 \def (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: 
T).(let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead c TMP_16 u) in (pr3 
TMP_17 t t2))))))) in (ex3_2 T T TMP_14 TMP_15 TMP_18)))))) in (let TMP_27 
\def (\lambda (t: T).(\forall (x0: T).((eq T y (THead (Bind Abst) t x0)) \to 
(let TMP_22 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_20 \def (Bind 
Abst) in (let TMP_21 \def (THead TMP_20 u2 t2) in (eq T x TMP_21))))) in (let 
TMP_23 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) in (let TMP_26 
\def (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(let 
TMP_24 \def (Bind b) in (let TMP_25 \def (CHead c TMP_24 u) in (pr3 TMP_25 x0 
t2))))))) in (ex3_2 T T TMP_22 TMP_23 TMP_26))))))) in (let TMP_35 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: T).((eq T t 
(THead (Bind Abst) x0 x1)) \to (let TMP_30 \def (\lambda (u2: T).(\lambda 
(t2: T).(let TMP_28 \def (Bind Abst) in (let TMP_29 \def (THead TMP_28 u2 t2) 
in (eq T t0 TMP_29))))) in (let TMP_31 \def (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) in (let TMP_34 \def (\lambda (_: T).(\lambda (t2: 
T).(\forall (b: B).(\forall (u: T).(let TMP_32 \def (Bind b) in (let TMP_33 
\def (CHead c TMP_32 u) in (pr3 TMP_33 x1 t2))))))) in (ex3_2 T T TMP_30 
TMP_31 TMP_34))))))))) in (let TMP_47 \def (\lambda (t: T).(\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H1: (eq T t (THead (Bind Abst) x0 x1))).(let 
TMP_38 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_36 \def (Bind Abst) in 
(let TMP_37 \def (THead TMP_36 u2 t2) in (eq T t TMP_37))))) in (let TMP_39 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_42 \def 
(\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(let TMP_40 
\def (Bind b) in (let TMP_41 \def (CHead c TMP_40 u) in (pr3 TMP_41 x1 
t2))))))) in (let TMP_43 \def (pr3_refl c x0) in (let TMP_46 \def (\lambda 
(b: B).(\lambda (u: T).(let TMP_44 \def (Bind b) in (let TMP_45 \def (CHead c 
TMP_44 u) in (pr3_refl TMP_45 x1))))) in (ex3_2_intro T T TMP_38 TMP_39 
TMP_42 x0 x1 H1 TMP_43 TMP_46)))))))))) in (let TMP_109 \def (\lambda (t2: 
T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: T).(\lambda 
(_: (pr3 c t2 t4)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: T).((eq T t2 
(THead (Bind Abst) x0 x1)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t5: 
T).(eq T t4 (THead (Bind Abst) u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) x1 t5))))))))))).(\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H4: (eq T t3 (THead (Bind Abst) x0 x1))).(let TMP_48 \def 
(\lambda (t: T).(pr2 c t t2)) in (let TMP_49 \def (Bind Abst) in (let TMP_50 
\def (THead TMP_49 x0 x1) in (let H5 \def (eq_ind T t3 TMP_48 H1 TMP_50 H4) 
in (let H6 \def (pr2_gen_abst c x0 x1 t2 H5) in (let TMP_53 \def (\lambda 
(u2: T).(\lambda (t5: T).(let TMP_51 \def (Bind Abst) in (let TMP_52 \def 
(THead TMP_51 u2 t5) in (eq T t2 TMP_52))))) in (let TMP_54 \def (\lambda 
(u2: T).(\lambda (_: T).(pr2 c x0 u2))) in (let TMP_57 \def (\lambda (_: 
T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(let TMP_55 \def (Bind b) 
in (let TMP_56 \def (CHead c TMP_55 u) in (pr2 TMP_56 x1 t5))))))) in (let 
TMP_60 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_58 \def (Bind Abst) in 
(let TMP_59 \def (THead TMP_58 u2 t5) in (eq T t4 TMP_59))))) in (let TMP_61 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_64 \def 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(let TMP_62 
\def (Bind b) in (let TMP_63 \def (CHead c TMP_62 u) in (pr3 TMP_63 x1 
t5))))))) in (let TMP_65 \def (ex3_2 T T TMP_60 TMP_61 TMP_64) in (let 
TMP_108 \def (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T t2 (THead 
(Bind Abst) x2 x3))).(\lambda (H8: (pr2 c x0 x2)).(\lambda (H9: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 x3))))).(let TMP_73 \def 
(\lambda (t: T).(\forall (x4: T).(\forall (x5: T).((eq T t (THead (Bind Abst) 
x4 x5)) \to (let TMP_68 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_66 
\def (Bind Abst) in (let TMP_67 \def (THead TMP_66 u2 t5) in (eq T t4 
TMP_67))))) in (let TMP_69 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x4 
u2))) in (let TMP_72 \def (\lambda (_: T).(\lambda (t5: T).(\forall (b: 
B).(\forall (u: T).(let TMP_70 \def (Bind b) in (let TMP_71 \def (CHead c 
TMP_70 u) in (pr3 TMP_71 x5 t5))))))) in (ex3_2 T T TMP_68 TMP_69 
TMP_72)))))))) in (let TMP_74 \def (Bind Abst) in (let TMP_75 \def (THead 
TMP_74 x2 x3) in (let H10 \def (eq_ind T t2 TMP_73 H3 TMP_75 H7) in (let 
TMP_76 \def (Bind Abst) in (let TMP_77 \def (THead TMP_76 x2 x3) in (let 
TMP_78 \def (refl_equal T TMP_77) in (let H11 \def (H10 x2 x3 TMP_78) in (let 
TMP_81 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_79 \def (Bind Abst) in 
(let TMP_80 \def (THead TMP_79 u2 t5) in (eq T t4 TMP_80))))) in (let TMP_82 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) in (let TMP_85 \def 
(\lambda (_: T).(\lambda (t5: T).(\forall (b: B).(\forall (u: T).(let TMP_83 
\def (Bind b) in (let TMP_84 \def (CHead c TMP_83 u) in (pr3 TMP_84 x3 
t5))))))) in (let TMP_88 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_86 
\def (Bind Abst) in (let TMP_87 \def (THead TMP_86 u2 t5) in (eq T t4 
TMP_87))))) in (let TMP_89 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) in (let TMP_92 \def (\lambda (_: T).(\lambda (t5: T).(\forall (b: 
B).(\forall (u: T).(let TMP_90 \def (Bind b) in (let TMP_91 \def (CHead c 
TMP_90 u) in (pr3 TMP_91 x1 t5))))))) in (let TMP_93 \def (ex3_2 T T TMP_88 
TMP_89 TMP_92) in (let TMP_107 \def (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H12: (eq T t4 (THead (Bind Abst) x4 x5))).(\lambda (H13: (pr3 c 
x2 x4)).(\lambda (H14: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind 
b) u) x3 x5))))).(let TMP_96 \def (\lambda (u2: T).(\lambda (t5: T).(let 
TMP_94 \def (Bind Abst) in (let TMP_95 \def (THead TMP_94 u2 t5) in (eq T t4 
TMP_95))))) in (let TMP_97 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) in (let TMP_100 \def (\lambda (_: T).(\lambda (t5: T).(\forall (b: 
B).(\forall (u: T).(let TMP_98 \def (Bind b) in (let TMP_99 \def (CHead c 
TMP_98 u) in (pr3 TMP_99 x1 t5))))))) in (let TMP_101 \def (pr3_sing c x2 x0 
H8 x4 H13) in (let TMP_106 \def (\lambda (b: B).(\lambda (u: T).(let TMP_102 
\def (Bind b) in (let TMP_103 \def (CHead c TMP_102 u) in (let TMP_104 \def 
(H9 b u) in (let TMP_105 \def (H14 b u) in (pr3_sing TMP_103 x3 x1 TMP_104 x5 
TMP_105))))))) in (ex3_2_intro T T TMP_96 TMP_97 TMP_100 x4 x5 H12 TMP_101 
TMP_106))))))))))) in (ex3_2_ind T T TMP_81 TMP_82 TMP_85 TMP_93 TMP_107 
H11)))))))))))))))))))))) in (ex3_2_ind T T TMP_53 TMP_54 TMP_57 TMP_65 
TMP_108 H6))))))))))))))))))))))) in (let TMP_110 \def (pr3_ind c TMP_35 
TMP_47 TMP_109 y x H0) in (let TMP_111 \def (unintro T u1 TMP_27 TMP_110) in 
(unintro T t1 TMP_19 TMP_111)))))))))) in (insert_eq T TMP_2 TMP_3 TMP_11 
TMP_112 H)))))))))).

theorem pr3_gen_cast:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr3 c 
(THead (Flat Cast) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr3 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr3 c t1 t2)))) (pr3 c 
t1 x))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr3 c (THead (Flat Cast) u1 t1) x)).(let TMP_1 \def (Flat Cast) in (let 
TMP_2 \def (THead TMP_1 u1 t1) in (let TMP_3 \def (\lambda (t: T).(pr3 c t 
x)) in (let TMP_11 \def (\lambda (_: T).(let TMP_6 \def (\lambda (u2: 
T).(\lambda (t2: T).(let TMP_4 \def (Flat Cast) in (let TMP_5 \def (THead 
TMP_4 u2 t2) in (eq T x TMP_5))))) in (let TMP_7 \def (\lambda (u2: 
T).(\lambda (_: T).(pr3 c u1 u2))) in (let TMP_8 \def (\lambda (_: 
T).(\lambda (t2: T).(pr3 c t1 t2))) in (let TMP_9 \def (ex3_2 T T TMP_6 TMP_7 
TMP_8) in (let TMP_10 \def (pr3 c t1 x) in (or TMP_9 TMP_10))))))) in (let 
TMP_204 \def (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(let TMP_19 \def 
(\lambda (t: T).((eq T y (THead (Flat Cast) u1 t)) \to (let TMP_14 \def 
(\lambda (u2: T).(\lambda (t2: T).(let TMP_12 \def (Flat Cast) in (let TMP_13 
\def (THead TMP_12 u2 t2) in (eq T x TMP_13))))) in (let TMP_15 \def (\lambda 
(u2: T).(\lambda (_: T).(pr3 c u1 u2))) in (let TMP_16 \def (\lambda (_: 
T).(\lambda (t2: T).(pr3 c t t2))) in (let TMP_17 \def (ex3_2 T T TMP_14 
TMP_15 TMP_16) in (let TMP_18 \def (pr3 c t x) in (or TMP_17 TMP_18)))))))) 
in (let TMP_27 \def (\lambda (t: T).(\forall (x0: T).((eq T y (THead (Flat 
Cast) t x0)) \to (let TMP_22 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_20 \def (Flat Cast) in (let TMP_21 \def (THead TMP_20 u2 t2) in (eq T x 
TMP_21))))) in (let TMP_23 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c t 
u2))) in (let TMP_24 \def (\lambda (_: T).(\lambda (t2: T).(pr3 c x0 t2))) in 
(let TMP_25 \def (ex3_2 T T TMP_22 TMP_23 TMP_24) in (let TMP_26 \def (pr3 c 
x0 x) in (or TMP_25 TMP_26))))))))) in (let TMP_35 \def (\lambda (t: 
T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: T).((eq T t (THead (Flat 
Cast) x0 x1)) \to (let TMP_30 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_28 \def (Flat Cast) in (let TMP_29 \def (THead TMP_28 u2 t2) in (eq T t0 
TMP_29))))) in (let TMP_31 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) in (let TMP_32 \def (\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2))) in 
(let TMP_33 \def (ex3_2 T T TMP_30 TMP_31 TMP_32) in (let TMP_34 \def (pr3 c 
x1 t0) in (or TMP_33 TMP_34))))))))))) in (let TMP_71 \def (\lambda (t: 
T).(\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T t (THead (Flat Cast) 
x0 x1))).(let TMP_36 \def (Flat Cast) in (let TMP_37 \def (THead TMP_36 x0 
x1) in (let TMP_45 \def (\lambda (t0: T).(let TMP_40 \def (\lambda (u2: 
T).(\lambda (t2: T).(let TMP_38 \def (Flat Cast) in (let TMP_39 \def (THead 
TMP_38 u2 t2) in (eq T t0 TMP_39))))) in (let TMP_41 \def (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_42 \def (\lambda (_: 
T).(\lambda (t2: T).(pr3 c x1 t2))) in (let TMP_43 \def (ex3_2 T T TMP_40 
TMP_41 TMP_42) in (let TMP_44 \def (pr3 c x1 t0) in (or TMP_43 TMP_44))))))) 
in (let TMP_50 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_46 \def (Flat 
Cast) in (let TMP_47 \def (THead TMP_46 x0 x1) in (let TMP_48 \def (Flat 
Cast) in (let TMP_49 \def (THead TMP_48 u2 t2) in (eq T TMP_47 TMP_49))))))) 
in (let TMP_51 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let 
TMP_52 \def (\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2))) in (let TMP_53 
\def (ex3_2 T T TMP_50 TMP_51 TMP_52) in (let TMP_54 \def (Flat Cast) in (let 
TMP_55 \def (THead TMP_54 x0 x1) in (let TMP_56 \def (pr3 c x1 TMP_55) in 
(let TMP_61 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_57 \def (Flat 
Cast) in (let TMP_58 \def (THead TMP_57 x0 x1) in (let TMP_59 \def (Flat 
Cast) in (let TMP_60 \def (THead TMP_59 u2 t2) in (eq T TMP_58 TMP_60))))))) 
in (let TMP_62 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let 
TMP_63 \def (\lambda (_: T).(\lambda (t2: T).(pr3 c x1 t2))) in (let TMP_64 
\def (Flat Cast) in (let TMP_65 \def (THead TMP_64 x0 x1) in (let TMP_66 \def 
(refl_equal T TMP_65) in (let TMP_67 \def (pr3_refl c x0) in (let TMP_68 \def 
(pr3_refl c x1) in (let TMP_69 \def (ex3_2_intro T T TMP_61 TMP_62 TMP_63 x0 
x1 TMP_66 TMP_67 TMP_68) in (let TMP_70 \def (or_introl TMP_53 TMP_56 TMP_69) 
in (eq_ind_r T TMP_37 TMP_45 TMP_70 t H1))))))))))))))))))))))))) in (let 
TMP_201 \def (\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 
t2)).(\lambda (t4: T).(\lambda (H2: (pr3 c t2 t4)).(\lambda (H3: ((\forall 
(x0: T).(\forall (x1: T).((eq T t2 (THead (Flat Cast) x0 x1)) \to (or (ex3_2 
T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead (Flat Cast) u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) (\lambda (_: T).(\lambda 
(t5: T).(pr3 c x1 t5)))) (pr3 c x1 t4))))))).(\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H4: (eq T t3 (THead (Flat Cast) x0 x1))).(let TMP_72 \def 
(\lambda (t: T).(pr2 c t t2)) in (let TMP_73 \def (Flat Cast) in (let TMP_74 
\def (THead TMP_73 x0 x1) in (let H5 \def (eq_ind T t3 TMP_72 H1 TMP_74 H4) 
in (let H6 \def (pr2_gen_cast c x0 x1 t2 H5) in (let TMP_77 \def (\lambda 
(u2: T).(\lambda (t5: T).(let TMP_75 \def (Flat Cast) in (let TMP_76 \def 
(THead TMP_75 u2 t5) in (eq T t2 TMP_76))))) in (let TMP_78 \def (\lambda 
(u2: T).(\lambda (_: T).(pr2 c x0 u2))) in (let TMP_79 \def (\lambda (_: 
T).(\lambda (t5: T).(pr2 c x1 t5))) in (let TMP_80 \def (ex3_2 T T TMP_77 
TMP_78 TMP_79) in (let TMP_81 \def (pr2 c x1 t2) in (let TMP_84 \def (\lambda 
(u2: T).(\lambda (t5: T).(let TMP_82 \def (Flat Cast) in (let TMP_83 \def 
(THead TMP_82 u2 t5) in (eq T t4 TMP_83))))) in (let TMP_85 \def (\lambda 
(u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_86 \def (\lambda (_: 
T).(\lambda (t5: T).(pr3 c x1 t5))) in (let TMP_87 \def (ex3_2 T T TMP_84 
TMP_85 TMP_86) in (let TMP_88 \def (pr3 c x1 t4) in (let TMP_89 \def (or 
TMP_87 TMP_88) in (let TMP_191 \def (\lambda (H7: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t2 (THead (Flat Cast) u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c x0 u2))) (\lambda (_: T).(\lambda (t5: T).(pr2 c x1 
t5))))).(let TMP_92 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_90 \def 
(Flat Cast) in (let TMP_91 \def (THead TMP_90 u2 t5) in (eq T t2 TMP_91))))) 
in (let TMP_93 \def (\lambda (u2: T).(\lambda (_: T).(pr2 c x0 u2))) in (let 
TMP_94 \def (\lambda (_: T).(\lambda (t5: T).(pr2 c x1 t5))) in (let TMP_97 
\def (\lambda (u2: T).(\lambda (t5: T).(let TMP_95 \def (Flat Cast) in (let 
TMP_96 \def (THead TMP_95 u2 t5) in (eq T t4 TMP_96))))) in (let TMP_98 \def 
(\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_99 \def (\lambda 
(_: T).(\lambda (t5: T).(pr3 c x1 t5))) in (let TMP_100 \def (ex3_2 T T 
TMP_97 TMP_98 TMP_99) in (let TMP_101 \def (pr3 c x1 t4) in (let TMP_102 \def 
(or TMP_100 TMP_101) in (let TMP_190 \def (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H8: (eq T t2 (THead (Flat Cast) x2 x3))).(\lambda (H9: (pr2 c x0 
x2)).(\lambda (H10: (pr2 c x1 x3)).(let TMP_110 \def (\lambda (t: T).(\forall 
(x4: T).(\forall (x5: T).((eq T t (THead (Flat Cast) x4 x5)) \to (let TMP_105 
\def (\lambda (u2: T).(\lambda (t5: T).(let TMP_103 \def (Flat Cast) in (let 
TMP_104 \def (THead TMP_103 u2 t5) in (eq T t4 TMP_104))))) in (let TMP_106 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x4 u2))) in (let TMP_107 \def 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x5 t5))) in (let TMP_108 \def (ex3_2 
T T TMP_105 TMP_106 TMP_107) in (let TMP_109 \def (pr3 c x5 t4) in (or 
TMP_108 TMP_109)))))))))) in (let TMP_111 \def (Flat Cast) in (let TMP_112 
\def (THead TMP_111 x2 x3) in (let H11 \def (eq_ind T t2 TMP_110 H3 TMP_112 
H8) in (let TMP_113 \def (Flat Cast) in (let TMP_114 \def (THead TMP_113 x2 
x3) in (let TMP_115 \def (refl_equal T TMP_114) in (let H12 \def (H11 x2 x3 
TMP_115) in (let TMP_118 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_116 
\def (Flat Cast) in (let TMP_117 \def (THead TMP_116 u2 t5) in (eq T t4 
TMP_117))))) in (let TMP_119 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 
u2))) in (let TMP_120 \def (\lambda (_: T).(\lambda (t5: T).(pr3 c x3 t5))) 
in (let TMP_121 \def (ex3_2 T T TMP_118 TMP_119 TMP_120) in (let TMP_122 \def 
(pr3 c x3 t4) in (let TMP_125 \def (\lambda (u2: T).(\lambda (t5: T).(let 
TMP_123 \def (Flat Cast) in (let TMP_124 \def (THead TMP_123 u2 t5) in (eq T 
t4 TMP_124))))) in (let TMP_126 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c 
x0 u2))) in (let TMP_127 \def (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5))) in (let TMP_128 \def (ex3_2 T T TMP_125 TMP_126 TMP_127) in (let 
TMP_129 \def (pr3 c x1 t4) in (let TMP_130 \def (or TMP_128 TMP_129) in (let 
TMP_180 \def (\lambda (H13: (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq 
T t4 (THead (Flat Cast) u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 
u2))) (\lambda (_: T).(\lambda (t5: T).(pr3 c x3 t5))))).(let TMP_133 \def 
(\lambda (u2: T).(\lambda (t5: T).(let TMP_131 \def (Flat Cast) in (let 
TMP_132 \def (THead TMP_131 u2 t5) in (eq T t4 TMP_132))))) in (let TMP_134 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x2 u2))) in (let TMP_135 \def 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x3 t5))) in (let TMP_138 \def 
(\lambda (u2: T).(\lambda (t5: T).(let TMP_136 \def (Flat Cast) in (let 
TMP_137 \def (THead TMP_136 u2 t5) in (eq T t4 TMP_137))))) in (let TMP_139 
\def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_140 \def 
(\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5))) in (let TMP_141 \def (ex3_2 
T T TMP_138 TMP_139 TMP_140) in (let TMP_142 \def (pr3 c x1 t4) in (let 
TMP_143 \def (or TMP_141 TMP_142) in (let TMP_179 \def (\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H14: (eq T t4 (THead (Flat Cast) x4 
x5))).(\lambda (H15: (pr3 c x2 x4)).(\lambda (H16: (pr3 c x3 x5)).(let 
TMP_144 \def (Flat Cast) in (let TMP_145 \def (THead TMP_144 x4 x5) in (let 
TMP_153 \def (\lambda (t: T).(let TMP_148 \def (\lambda (u2: T).(\lambda (t5: 
T).(let TMP_146 \def (Flat Cast) in (let TMP_147 \def (THead TMP_146 u2 t5) 
in (eq T t TMP_147))))) in (let TMP_149 \def (\lambda (u2: T).(\lambda (_: 
T).(pr3 c x0 u2))) in (let TMP_150 \def (\lambda (_: T).(\lambda (t5: T).(pr3 
c x1 t5))) in (let TMP_151 \def (ex3_2 T T TMP_148 TMP_149 TMP_150) in (let 
TMP_152 \def (pr3 c x1 t) in (or TMP_151 TMP_152))))))) in (let TMP_158 \def 
(\lambda (u2: T).(\lambda (t5: T).(let TMP_154 \def (Flat Cast) in (let 
TMP_155 \def (THead TMP_154 x4 x5) in (let TMP_156 \def (Flat Cast) in (let 
TMP_157 \def (THead TMP_156 u2 t5) in (eq T TMP_155 TMP_157))))))) in (let 
TMP_159 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_160 
\def (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5))) in (let TMP_161 \def 
(ex3_2 T T TMP_158 TMP_159 TMP_160) in (let TMP_162 \def (Flat Cast) in (let 
TMP_163 \def (THead TMP_162 x4 x5) in (let TMP_164 \def (pr3 c x1 TMP_163) in 
(let TMP_169 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_165 \def (Flat 
Cast) in (let TMP_166 \def (THead TMP_165 x4 x5) in (let TMP_167 \def (Flat 
Cast) in (let TMP_168 \def (THead TMP_167 u2 t5) in (eq T TMP_166 
TMP_168))))))) in (let TMP_170 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c 
x0 u2))) in (let TMP_171 \def (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5))) in (let TMP_172 \def (Flat Cast) in (let TMP_173 \def (THead TMP_172 x4 
x5) in (let TMP_174 \def (refl_equal T TMP_173) in (let TMP_175 \def 
(pr3_sing c x2 x0 H9 x4 H15) in (let TMP_176 \def (pr3_sing c x3 x1 H10 x5 
H16) in (let TMP_177 \def (ex3_2_intro T T TMP_169 TMP_170 TMP_171 x4 x5 
TMP_174 TMP_175 TMP_176) in (let TMP_178 \def (or_introl TMP_161 TMP_164 
TMP_177) in (eq_ind_r T TMP_145 TMP_153 TMP_178 t4 
H14)))))))))))))))))))))))))) in (ex3_2_ind T T TMP_133 TMP_134 TMP_135 
TMP_143 TMP_179 H13)))))))))))) in (let TMP_189 \def (\lambda (H13: (pr3 c x3 
t4)).(let TMP_183 \def (\lambda (u2: T).(\lambda (t5: T).(let TMP_181 \def 
(Flat Cast) in (let TMP_182 \def (THead TMP_181 u2 t5) in (eq T t4 
TMP_182))))) in (let TMP_184 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c x0 
u2))) in (let TMP_185 \def (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 t5))) 
in (let TMP_186 \def (ex3_2 T T TMP_183 TMP_184 TMP_185) in (let TMP_187 \def 
(pr3 c x1 t4) in (let TMP_188 \def (pr3_sing c x3 x1 H10 t4 H13) in 
(or_intror TMP_186 TMP_187 TMP_188)))))))) in (or_ind TMP_121 TMP_122 TMP_130 
TMP_180 TMP_189 H12))))))))))))))))))))))))))) in (ex3_2_ind T T TMP_92 
TMP_93 TMP_94 TMP_102 TMP_190 H7)))))))))))) in (let TMP_200 \def (\lambda 
(H7: (pr2 c x1 t2)).(let TMP_194 \def (\lambda (u2: T).(\lambda (t5: T).(let 
TMP_192 \def (Flat Cast) in (let TMP_193 \def (THead TMP_192 u2 t5) in (eq T 
t4 TMP_193))))) in (let TMP_195 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c 
x0 u2))) in (let TMP_196 \def (\lambda (_: T).(\lambda (t5: T).(pr3 c x1 
t5))) in (let TMP_197 \def (ex3_2 T T TMP_194 TMP_195 TMP_196) in (let 
TMP_198 \def (pr3 c x1 t4) in (let TMP_199 \def (pr3_sing c t2 x1 H7 t4 H2) 
in (or_intror TMP_197 TMP_198 TMP_199)))))))) in (or_ind TMP_80 TMP_81 TMP_89 
TMP_191 TMP_200 H6)))))))))))))))))))))))))))) in (let TMP_202 \def (pr3_ind 
c TMP_35 TMP_71 TMP_201 y x H0) in (let TMP_203 \def (unintro T u1 TMP_27 
TMP_202) in (unintro T t1 TMP_19 TMP_203)))))))))) in (insert_eq T TMP_2 
TMP_3 TMP_11 TMP_204 H)))))))))).

theorem pr3_gen_lift:
 \forall (c: C).(\forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).((pr3 c (lift h d t1) x) \to (\forall (e: C).((drop h d c e) \to 
(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr3 e t1 
t2))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H: (pr3 c (lift h d t1) x)).(let TMP_1 \def (lift h d t1) 
in (let TMP_2 \def (\lambda (t: T).(pr3 c t x)) in (let TMP_6 \def (\lambda 
(_: T).(\forall (e: C).((drop h d c e) \to (let TMP_4 \def (\lambda (t2: 
T).(let TMP_3 \def (lift h d t2) in (eq T x TMP_3))) in (let TMP_5 \def 
(\lambda (t2: T).(pr3 e t1 t2)) in (ex2 T TMP_4 TMP_5)))))) in (let TMP_45 
\def (\lambda (y: T).(\lambda (H0: (pr3 c y x)).(let TMP_10 \def (\lambda (t: 
T).((eq T y (lift h d t)) \to (\forall (e: C).((drop h d c e) \to (let TMP_8 
\def (\lambda (t2: T).(let TMP_7 \def (lift h d t2) in (eq T x TMP_7))) in 
(let TMP_9 \def (\lambda (t2: T).(pr3 e t t2)) in (ex2 T TMP_8 TMP_9))))))) 
in (let TMP_14 \def (\lambda (t: T).(\lambda (t0: T).(\forall (x0: T).((eq T 
t (lift h d x0)) \to (\forall (e: C).((drop h d c e) \to (let TMP_12 \def 
(\lambda (t2: T).(let TMP_11 \def (lift h d t2) in (eq T t0 TMP_11))) in (let 
TMP_13 \def (\lambda (t2: T).(pr3 e x0 t2)) in (ex2 T TMP_12 TMP_13))))))))) 
in (let TMP_19 \def (\lambda (t: T).(\lambda (x0: T).(\lambda (H1: (eq T t 
(lift h d x0))).(\lambda (e: C).(\lambda (_: (drop h d c e)).(let TMP_16 \def 
(\lambda (t2: T).(let TMP_15 \def (lift h d t2) in (eq T t TMP_15))) in (let 
TMP_17 \def (\lambda (t2: T).(pr3 e x0 t2)) in (let TMP_18 \def (pr3_refl e 
x0) in (ex_intro2 T TMP_16 TMP_17 x0 H1 TMP_18))))))))) in (let TMP_43 \def 
(\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: (pr2 c t3 t2)).(\lambda (t4: 
T).(\lambda (_: (pr3 c t2 t4)).(\lambda (H3: ((\forall (x0: T).((eq T t2 
(lift h d x0)) \to (\forall (e: C).((drop h d c e) \to (ex2 T (\lambda (t5: 
T).(eq T t4 (lift h d t5))) (\lambda (t5: T).(pr3 e x0 t5))))))))).(\lambda 
(x0: T).(\lambda (H4: (eq T t3 (lift h d x0))).(\lambda (e: C).(\lambda (H5: 
(drop h d c e)).(let TMP_20 \def (\lambda (t: T).(pr2 c t t2)) in (let TMP_21 
\def (lift h d x0) in (let H6 \def (eq_ind T t3 TMP_20 H1 TMP_21 H4) in (let 
H7 \def (pr2_gen_lift c x0 t2 h d H6 e H5) in (let TMP_23 \def (\lambda (t5: 
T).(let TMP_22 \def (lift h d t5) in (eq T t2 TMP_22))) in (let TMP_24 \def 
(\lambda (t5: T).(pr2 e x0 t5)) in (let TMP_26 \def (\lambda (t5: T).(let 
TMP_25 \def (lift h d t5) in (eq T t4 TMP_25))) in (let TMP_27 \def (\lambda 
(t5: T).(pr3 e x0 t5)) in (let TMP_28 \def (ex2 T TMP_26 TMP_27) in (let 
TMP_42 \def (\lambda (x1: T).(\lambda (H8: (eq T t2 (lift h d x1))).(\lambda 
(H9: (pr2 e x0 x1)).(let TMP_30 \def (\lambda (t5: T).(let TMP_29 \def (lift 
h d t5) in (eq T t4 TMP_29))) in (let TMP_31 \def (\lambda (t5: T).(pr3 e x1 
t5)) in (let TMP_33 \def (\lambda (t5: T).(let TMP_32 \def (lift h d t5) in 
(eq T t4 TMP_32))) in (let TMP_34 \def (\lambda (t5: T).(pr3 e x0 t5)) in 
(let TMP_35 \def (ex2 T TMP_33 TMP_34) in (let TMP_40 \def (\lambda (x2: 
T).(\lambda (H10: (eq T t4 (lift h d x2))).(\lambda (H11: (pr3 e x1 x2)).(let 
TMP_37 \def (\lambda (t5: T).(let TMP_36 \def (lift h d t5) in (eq T t4 
TMP_36))) in (let TMP_38 \def (\lambda (t5: T).(pr3 e x0 t5)) in (let TMP_39 
\def (pr3_sing e x1 x0 H9 x2 H11) in (ex_intro2 T TMP_37 TMP_38 x2 H10 
TMP_39))))))) in (let TMP_41 \def (H3 x1 H8 e H5) in (ex2_ind T TMP_30 TMP_31 
TMP_35 TMP_40 TMP_41))))))))))) in (ex2_ind T TMP_23 TMP_24 TMP_28 TMP_42 
H7))))))))))))))))))))) in (let TMP_44 \def (pr3_ind c TMP_14 TMP_19 TMP_43 y 
x H0) in (unintro T t1 TMP_10 TMP_44)))))))) in (insert_eq T TMP_1 TMP_2 
TMP_6 TMP_45 H)))))))))).

theorem pr3_gen_lref:
 \forall (c: C).(\forall (x: T).(\forall (n: nat).((pr3 c (TLRef n) x) \to 
(or (eq T x (TLRef n)) (ex3_3 C T T (\lambda (d: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c (CHead d (Bind Abbr) u))))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(v: T).(eq T x (lift (S n) O v))))))))))
\def
 \lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr3 c (TLRef 
n) x)).(let TMP_1 \def (TLRef n) in (let TMP_2 \def (\lambda (t: T).(pr3 c t 
x)) in (let TMP_12 \def (\lambda (t: T).(let TMP_3 \def (eq T x t) in (let 
TMP_6 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(let TMP_4 \def 
(Bind Abbr) in (let TMP_5 \def (CHead d TMP_4 u) in (getl n c TMP_5)))))) in 
(let TMP_7 \def (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u 
v)))) in (let TMP_10 \def (\lambda (_: C).(\lambda (_: T).(\lambda (v: 
T).(let TMP_8 \def (S n) in (let TMP_9 \def (lift TMP_8 O v) in (eq T x 
TMP_9)))))) in (let TMP_11 \def (ex3_3 C T T TMP_6 TMP_7 TMP_10) in (or TMP_3 
TMP_11))))))) in (let TMP_155 \def (\lambda (y: T).(\lambda (H0: (pr3 c y 
x)).(let TMP_22 \def (\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n)) \to 
(let TMP_13 \def (eq T t0 t) in (let TMP_16 \def (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: T).(let TMP_14 \def (Bind Abbr) in (let TMP_15 \def (CHead d 
TMP_14 u) in (getl n c TMP_15)))))) in (let TMP_17 \def (\lambda (d: 
C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_20 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_18 \def (S n) in 
(let TMP_19 \def (lift TMP_18 O v) in (eq T t0 TMP_19)))))) in (let TMP_21 
\def (ex3_3 C T T TMP_16 TMP_17 TMP_20) in (or TMP_13 TMP_21))))))))) in (let 
TMP_33 \def (\lambda (t: T).(\lambda (_: (eq T t (TLRef n))).(let TMP_23 \def 
(eq T t t) in (let TMP_26 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
T).(let TMP_24 \def (Bind Abbr) in (let TMP_25 \def (CHead d TMP_24 u) in 
(getl n c TMP_25)))))) in (let TMP_27 \def (\lambda (d: C).(\lambda (u: 
T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_30 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (v: T).(let TMP_28 \def (S n) in (let TMP_29 \def 
(lift TMP_28 O v) in (eq T t TMP_29)))))) in (let TMP_31 \def (ex3_3 C T T 
TMP_26 TMP_27 TMP_30) in (let TMP_32 \def (refl_equal T t) in (or_introl 
TMP_23 TMP_31 TMP_32))))))))) in (let TMP_154 \def (\lambda (t2: T).(\lambda 
(t1: T).(\lambda (H1: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda (H2: (pr3 c t2 
t3)).(\lambda (H3: (((eq T t2 (TLRef n)) \to (or (eq T t3 t2) (ex3_3 C T T 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead d (Bind 
Abbr) u))))) (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(eq T t3 (lift (S n) O 
v)))))))))).(\lambda (H4: (eq T t1 (TLRef n))).(let TMP_34 \def (\lambda (t: 
T).(pr2 c t t2)) in (let TMP_35 \def (TLRef n) in (let H5 \def (eq_ind T t1 
TMP_34 H1 TMP_35 H4) in (let TMP_36 \def (TLRef n) in (let TMP_46 \def 
(\lambda (t: T).(let TMP_37 \def (eq T t3 t) in (let TMP_40 \def (\lambda (d: 
C).(\lambda (u: T).(\lambda (_: T).(let TMP_38 \def (Bind Abbr) in (let 
TMP_39 \def (CHead d TMP_38 u) in (getl n c TMP_39)))))) in (let TMP_41 \def 
(\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_44 
\def (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_42 \def (S n) 
in (let TMP_43 \def (lift TMP_42 O v) in (eq T t3 TMP_43)))))) in (let TMP_45 
\def (ex3_3 C T T TMP_40 TMP_41 TMP_44) in (or TMP_37 TMP_45))))))) in (let 
H6 \def (pr2_gen_lref c t2 n H5) in (let TMP_47 \def (TLRef n) in (let TMP_48 
\def (eq T t2 TMP_47) in (let TMP_51 \def (\lambda (d: C).(\lambda (u: 
T).(let TMP_49 \def (Bind Abbr) in (let TMP_50 \def (CHead d TMP_49 u) in 
(getl n c TMP_50))))) in (let TMP_54 \def (\lambda (_: C).(\lambda (u: 
T).(let TMP_52 \def (S n) in (let TMP_53 \def (lift TMP_52 O u) in (eq T t2 
TMP_53))))) in (let TMP_55 \def (ex2_2 C T TMP_51 TMP_54) in (let TMP_56 \def 
(TLRef n) in (let TMP_57 \def (eq T t3 TMP_56) in (let TMP_60 \def (\lambda 
(d: C).(\lambda (u: T).(\lambda (_: T).(let TMP_58 \def (Bind Abbr) in (let 
TMP_59 \def (CHead d TMP_58 u) in (getl n c TMP_59)))))) in (let TMP_61 \def 
(\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_64 
\def (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_62 \def (S n) 
in (let TMP_63 \def (lift TMP_62 O v) in (eq T t3 TMP_63)))))) in (let TMP_65 
\def (ex3_3 C T T TMP_60 TMP_61 TMP_64) in (let TMP_66 \def (or TMP_57 
TMP_65) in (let TMP_82 \def (\lambda (H7: (eq T t2 (TLRef n))).(let TMP_76 
\def (\lambda (t: T).((eq T t (TLRef n)) \to (let TMP_67 \def (eq T t3 t) in 
(let TMP_70 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(let TMP_68 
\def (Bind Abbr) in (let TMP_69 \def (CHead d TMP_68 u) in (getl n c 
TMP_69)))))) in (let TMP_71 \def (\lambda (d: C).(\lambda (u: T).(\lambda (v: 
T).(pr3 d u v)))) in (let TMP_74 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (v: T).(let TMP_72 \def (S n) in (let TMP_73 \def (lift TMP_72 O 
v) in (eq T t3 TMP_73)))))) in (let TMP_75 \def (ex3_3 C T T TMP_70 TMP_71 
TMP_74) in (or TMP_67 TMP_75)))))))) in (let TMP_77 \def (TLRef n) in (let H8 
\def (eq_ind T t2 TMP_76 H3 TMP_77 H7) in (let TMP_78 \def (\lambda (t: 
T).(pr3 c t t3)) in (let TMP_79 \def (TLRef n) in (let H9 \def (eq_ind T t2 
TMP_78 H2 TMP_79 H7) in (let TMP_80 \def (TLRef n) in (let TMP_81 \def 
(refl_equal T TMP_80) in (H8 TMP_81)))))))))) in (let TMP_152 \def (\lambda 
(H7: (ex2_2 C T (\lambda (d: C).(\lambda (u: T).(getl n c (CHead d (Bind 
Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(eq T t2 (lift (S n) O 
u)))))).(let TMP_85 \def (\lambda (d: C).(\lambda (u: T).(let TMP_83 \def 
(Bind Abbr) in (let TMP_84 \def (CHead d TMP_83 u) in (getl n c TMP_84))))) 
in (let TMP_88 \def (\lambda (_: C).(\lambda (u: T).(let TMP_86 \def (S n) in 
(let TMP_87 \def (lift TMP_86 O u) in (eq T t2 TMP_87))))) in (let TMP_89 
\def (TLRef n) in (let TMP_90 \def (eq T t3 TMP_89) in (let TMP_93 \def 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(let TMP_91 \def (Bind Abbr) 
in (let TMP_92 \def (CHead d TMP_91 u) in (getl n c TMP_92)))))) in (let 
TMP_94 \def (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in 
(let TMP_97 \def (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_95 
\def (S n) in (let TMP_96 \def (lift TMP_95 O v) in (eq T t3 TMP_96)))))) in 
(let TMP_98 \def (ex3_3 C T T TMP_93 TMP_94 TMP_97) in (let TMP_99 \def (or 
TMP_90 TMP_98) in (let TMP_151 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H8: (getl n c (CHead x0 (Bind Abbr) x1))).(\lambda (H9: (eq T t2 
(lift (S n) O x1))).(let TMP_109 \def (\lambda (t: T).((eq T t (TLRef n)) \to 
(let TMP_100 \def (eq T t3 t) in (let TMP_103 \def (\lambda (d: C).(\lambda 
(u: T).(\lambda (_: T).(let TMP_101 \def (Bind Abbr) in (let TMP_102 \def 
(CHead d TMP_101 u) in (getl n c TMP_102)))))) in (let TMP_104 \def (\lambda 
(d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_107 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_105 \def (S n) in 
(let TMP_106 \def (lift TMP_105 O v) in (eq T t3 TMP_106)))))) in (let 
TMP_108 \def (ex3_3 C T T TMP_103 TMP_104 TMP_107) in (or TMP_100 
TMP_108)))))))) in (let TMP_110 \def (S n) in (let TMP_111 \def (lift TMP_110 
O x1) in (let H10 \def (eq_ind T t2 TMP_109 H3 TMP_111 H9) in (let TMP_112 
\def (\lambda (t: T).(pr3 c t t3)) in (let TMP_113 \def (S n) in (let TMP_114 
\def (lift TMP_113 O x1) in (let H11 \def (eq_ind T t2 TMP_112 H2 TMP_114 H9) 
in (let TMP_115 \def (S n) in (let TMP_116 \def (getl_drop Abbr c x0 x1 n H8) 
in (let H12 \def (pr3_gen_lift c x1 t3 TMP_115 O H11 x0 TMP_116) in (let 
TMP_119 \def (\lambda (t4: T).(let TMP_117 \def (S n) in (let TMP_118 \def 
(lift TMP_117 O t4) in (eq T t3 TMP_118)))) in (let TMP_120 \def (\lambda 
(t4: T).(pr3 x0 x1 t4)) in (let TMP_121 \def (TLRef n) in (let TMP_122 \def 
(eq T t3 TMP_121) in (let TMP_125 \def (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: T).(let TMP_123 \def (Bind Abbr) in (let TMP_124 \def (CHead 
d TMP_123 u) in (getl n c TMP_124)))))) in (let TMP_126 \def (\lambda (d: 
C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) in (let TMP_129 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let TMP_127 \def (S n) in 
(let TMP_128 \def (lift TMP_127 O v) in (eq T t3 TMP_128)))))) in (let 
TMP_130 \def (ex3_3 C T T TMP_125 TMP_126 TMP_129) in (let TMP_131 \def (or 
TMP_122 TMP_130) in (let TMP_150 \def (\lambda (x2: T).(\lambda (H13: (eq T 
t3 (lift (S n) O x2))).(\lambda (H14: (pr3 x0 x1 x2)).(let TMP_132 \def 
(TLRef n) in (let TMP_133 \def (eq T t3 TMP_132) in (let TMP_136 \def 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(let TMP_134 \def (Bind Abbr) 
in (let TMP_135 \def (CHead d TMP_134 u) in (getl n c TMP_135)))))) in (let 
TMP_137 \def (\lambda (d: C).(\lambda (u: T).(\lambda (v: T).(pr3 d u v)))) 
in (let TMP_140 \def (\lambda (_: C).(\lambda (_: T).(\lambda (v: T).(let 
TMP_138 \def (S n) in (let TMP_139 \def (lift TMP_138 O v) in (eq T t3 
TMP_139)))))) in (let TMP_141 \def (ex3_3 C T T TMP_136 TMP_137 TMP_140) in 
(let TMP_144 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: T).(let 
TMP_142 \def (Bind Abbr) in (let TMP_143 \def (CHead d TMP_142 u) in (getl n 
c TMP_143)))))) in (let TMP_145 \def (\lambda (d: C).(\lambda (u: T).(\lambda 
(v: T).(pr3 d u v)))) in (let TMP_148 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (v: T).(let TMP_146 \def (S n) in (let TMP_147 \def (lift TMP_146 
O v) in (eq T t3 TMP_147)))))) in (let TMP_149 \def (ex3_3_intro C T T 
TMP_144 TMP_145 TMP_148 x0 x1 x2 H8 H14 H13) in (or_intror TMP_133 TMP_141 
TMP_149)))))))))))))) in (ex2_ind T TMP_119 TMP_120 TMP_131 TMP_150 
H12)))))))))))))))))))))))))) in (ex2_2_ind C T TMP_85 TMP_88 TMP_99 TMP_151 
H7)))))))))))) in (let TMP_153 \def (or_ind TMP_48 TMP_55 TMP_66 TMP_82 
TMP_152 H6) in (eq_ind_r T TMP_36 TMP_46 TMP_153 t1 
H4))))))))))))))))))))))))))))) in (pr3_ind c TMP_22 TMP_33 TMP_154 y x 
H0)))))) in (insert_eq T TMP_1 TMP_2 TMP_12 TMP_155 H)))))))).

