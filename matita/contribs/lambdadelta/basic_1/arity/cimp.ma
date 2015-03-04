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

include "basic_1/arity/fwd.ma".

include "basic_1/cimp/props.ma".

theorem arity_cimp_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((cimp c1 c2) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(let TMP_1 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a0: A).(\forall (c2: C).((cimp c c2) \to (arity g c2 t0 a0)))))) in (let 
TMP_2 \def (\lambda (c: C).(\lambda (n: nat).(\lambda (c2: C).(\lambda (_: 
(cimp c c2)).(arity_sort g c2 n))))) in (let TMP_41 \def (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u 
a0)).(\lambda (H2: ((\forall (c2: C).((cimp d c2) \to (arity g c2 u 
a0))))).(\lambda (c2: C).(\lambda (H3: (cimp c c2)).(let H_x \def (H3 Abbr d 
u i H0) in (let H4 \def H_x in (let TMP_5 \def (\lambda (d2: C).(let TMP_3 
\def (Bind Abbr) in (let TMP_4 \def (CHead d2 TMP_3 u) in (getl i c2 
TMP_4)))) in (let TMP_6 \def (TLRef i) in (let TMP_7 \def (arity g c2 TMP_6 
a0) in (let TMP_40 \def (\lambda (x: C).(\lambda (H5: (getl i c2 (CHead x 
(Bind Abbr) u))).(let H_x0 \def (cimp_getl_conf c c2 H3 Abbr d u i H0) in 
(let H6 \def H_x0 in (let TMP_8 \def (\lambda (d2: C).(cimp d d2)) in (let 
TMP_11 \def (\lambda (d2: C).(let TMP_9 \def (Bind Abbr) in (let TMP_10 \def 
(CHead d2 TMP_9 u) in (getl i c2 TMP_10)))) in (let TMP_12 \def (TLRef i) in 
(let TMP_13 \def (arity g c2 TMP_12 a0) in (let TMP_39 \def (\lambda (x0: 
C).(\lambda (H7: (cimp d x0)).(\lambda (H8: (getl i c2 (CHead x0 (Bind Abbr) 
u))).(let TMP_14 \def (Bind Abbr) in (let TMP_15 \def (CHead x TMP_14 u) in 
(let TMP_16 \def (\lambda (c0: C).(getl i c2 c0)) in (let TMP_17 \def (Bind 
Abbr) in (let TMP_18 \def (CHead x0 TMP_17 u) in (let TMP_19 \def (Bind Abbr) 
in (let TMP_20 \def (CHead x TMP_19 u) in (let TMP_21 \def (Bind Abbr) in 
(let TMP_22 \def (CHead x0 TMP_21 u) in (let TMP_23 \def (getl_mono c2 TMP_20 
i H5 TMP_22 H8) in (let H9 \def (eq_ind C TMP_15 TMP_16 H5 TMP_18 TMP_23) in 
(let TMP_24 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow x | 
(CHead c0 _ _) \Rightarrow c0])) in (let TMP_25 \def (Bind Abbr) in (let 
TMP_26 \def (CHead x TMP_25 u) in (let TMP_27 \def (Bind Abbr) in (let TMP_28 
\def (CHead x0 TMP_27 u) in (let TMP_29 \def (Bind Abbr) in (let TMP_30 \def 
(CHead x TMP_29 u) in (let TMP_31 \def (Bind Abbr) in (let TMP_32 \def (CHead 
x0 TMP_31 u) in (let TMP_33 \def (getl_mono c2 TMP_30 i H5 TMP_32 H8) in (let 
H10 \def (f_equal C C TMP_24 TMP_26 TMP_28 TMP_33) in (let TMP_36 \def 
(\lambda (c0: C).(let TMP_34 \def (Bind Abbr) in (let TMP_35 \def (CHead c0 
TMP_34 u) in (getl i c2 TMP_35)))) in (let H11 \def (eq_ind_r C x0 TMP_36 H9 
x H10) in (let TMP_37 \def (\lambda (c0: C).(cimp d c0)) in (let H12 \def 
(eq_ind_r C x0 TMP_37 H7 x H10) in (let TMP_38 \def (H2 x H12) in (arity_abbr 
g c2 x u i H11 a0 TMP_38))))))))))))))))))))))))))))))) in (ex2_ind C TMP_8 
TMP_11 TMP_13 TMP_39 H6)))))))))) in (ex_ind C TMP_5 TMP_7 TMP_40 
H4))))))))))))))))) in (let TMP_80 \def (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abst) u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g a0))).(\lambda 
(H2: ((\forall (c2: C).((cimp d c2) \to (arity g c2 u (asucc g 
a0)))))).(\lambda (c2: C).(\lambda (H3: (cimp c c2)).(let H_x \def (H3 Abst d 
u i H0) in (let H4 \def H_x in (let TMP_44 \def (\lambda (d2: C).(let TMP_42 
\def (Bind Abst) in (let TMP_43 \def (CHead d2 TMP_42 u) in (getl i c2 
TMP_43)))) in (let TMP_45 \def (TLRef i) in (let TMP_46 \def (arity g c2 
TMP_45 a0) in (let TMP_79 \def (\lambda (x: C).(\lambda (H5: (getl i c2 
(CHead x (Bind Abst) u))).(let H_x0 \def (cimp_getl_conf c c2 H3 Abst d u i 
H0) in (let H6 \def H_x0 in (let TMP_47 \def (\lambda (d2: C).(cimp d d2)) in 
(let TMP_50 \def (\lambda (d2: C).(let TMP_48 \def (Bind Abst) in (let TMP_49 
\def (CHead d2 TMP_48 u) in (getl i c2 TMP_49)))) in (let TMP_51 \def (TLRef 
i) in (let TMP_52 \def (arity g c2 TMP_51 a0) in (let TMP_78 \def (\lambda 
(x0: C).(\lambda (H7: (cimp d x0)).(\lambda (H8: (getl i c2 (CHead x0 (Bind 
Abst) u))).(let TMP_53 \def (Bind Abst) in (let TMP_54 \def (CHead x TMP_53 
u) in (let TMP_55 \def (\lambda (c0: C).(getl i c2 c0)) in (let TMP_56 \def 
(Bind Abst) in (let TMP_57 \def (CHead x0 TMP_56 u) in (let TMP_58 \def (Bind 
Abst) in (let TMP_59 \def (CHead x TMP_58 u) in (let TMP_60 \def (Bind Abst) 
in (let TMP_61 \def (CHead x0 TMP_60 u) in (let TMP_62 \def (getl_mono c2 
TMP_59 i H5 TMP_61 H8) in (let H9 \def (eq_ind C TMP_54 TMP_55 H5 TMP_57 
TMP_62) in (let TMP_63 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow x | (CHead c0 _ _) \Rightarrow c0])) in (let TMP_64 \def (Bind 
Abst) in (let TMP_65 \def (CHead x TMP_64 u) in (let TMP_66 \def (Bind Abst) 
in (let TMP_67 \def (CHead x0 TMP_66 u) in (let TMP_68 \def (Bind Abst) in 
(let TMP_69 \def (CHead x TMP_68 u) in (let TMP_70 \def (Bind Abst) in (let 
TMP_71 \def (CHead x0 TMP_70 u) in (let TMP_72 \def (getl_mono c2 TMP_69 i H5 
TMP_71 H8) in (let H10 \def (f_equal C C TMP_63 TMP_65 TMP_67 TMP_72) in (let 
TMP_75 \def (\lambda (c0: C).(let TMP_73 \def (Bind Abst) in (let TMP_74 \def 
(CHead c0 TMP_73 u) in (getl i c2 TMP_74)))) in (let H11 \def (eq_ind_r C x0 
TMP_75 H9 x H10) in (let TMP_76 \def (\lambda (c0: C).(cimp d c0)) in (let 
H12 \def (eq_ind_r C x0 TMP_76 H7 x H10) in (let TMP_77 \def (H2 x H12) in 
(arity_abst g c2 x u i H11 a0 TMP_77))))))))))))))))))))))))))))))) in 
(ex2_ind C TMP_47 TMP_50 TMP_52 TMP_78 H6)))))))))) in (ex_ind C TMP_44 
TMP_46 TMP_79 H4))))))))))))))))) in (let TMP_86 \def (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: ((\forall 
(c2: C).((cimp c c2) \to (arity g c2 u a1))))).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 a2)).(\lambda (H4: ((\forall 
(c2: C).((cimp (CHead c (Bind b) u) c2) \to (arity g c2 t0 a2))))).(\lambda 
(c2: C).(\lambda (H5: (cimp c c2)).(let TMP_81 \def (H2 c2 H5) in (let TMP_82 
\def (Bind b) in (let TMP_83 \def (CHead c2 TMP_82 u) in (let TMP_84 \def 
(cimp_bind c c2 H5 b u) in (let TMP_85 \def (H4 TMP_83 TMP_84) in (arity_bind 
g b H0 c2 u a1 TMP_81 t0 a2 TMP_85))))))))))))))))))) in (let TMP_92 \def 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u 
(asucc g a1))).(\lambda (H1: ((\forall (c2: C).((cimp c c2) \to (arity g c2 u 
(asucc g a1)))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g 
(CHead c (Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (c2: C).((cimp (CHead 
c (Bind Abst) u) c2) \to (arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda 
(H4: (cimp c c2)).(let TMP_87 \def (H1 c2 H4) in (let TMP_88 \def (Bind Abst) 
in (let TMP_89 \def (CHead c2 TMP_88 u) in (let TMP_90 \def (cimp_bind c c2 
H4 Abst u) in (let TMP_91 \def (H3 TMP_89 TMP_90) in (arity_head g c2 u a1 
TMP_87 t0 a2 TMP_91))))))))))))))))) in (let TMP_95 \def (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda 
(H1: ((\forall (c2: C).((cimp c c2) \to (arity g c2 u a1))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda (H3: 
((\forall (c2: C).((cimp c c2) \to (arity g c2 t0 (AHead a1 a2)))))).(\lambda 
(c2: C).(\lambda (H4: (cimp c c2)).(let TMP_93 \def (H1 c2 H4) in (let TMP_94 
\def (H3 c2 H4) in (arity_appl g c2 u a1 TMP_93 t0 a2 TMP_94)))))))))))))) in 
(let TMP_98 \def (\lambda (c: C).(\lambda (u: T).(\lambda (a0: A).(\lambda 
(_: (arity g c u (asucc g a0))).(\lambda (H1: ((\forall (c2: C).((cimp c c2) 
\to (arity g c2 u (asucc g a0)))))).(\lambda (t0: T).(\lambda (_: (arity g c 
t0 a0)).(\lambda (H3: ((\forall (c2: C).((cimp c c2) \to (arity g c2 t0 
a0))))).(\lambda (c2: C).(\lambda (H4: (cimp c c2)).(let TMP_96 \def (H1 c2 
H4) in (let TMP_97 \def (H3 c2 H4) in (arity_cast g c2 u a0 TMP_96 t0 
TMP_97))))))))))))) in (let TMP_100 \def (\lambda (c: C).(\lambda (t0: 
T).(\lambda (a1: A).(\lambda (_: (arity g c t0 a1)).(\lambda (H1: ((\forall 
(c2: C).((cimp c c2) \to (arity g c2 t0 a1))))).(\lambda (a2: A).(\lambda 
(H2: (leq g a1 a2)).(\lambda (c2: C).(\lambda (H3: (cimp c c2)).(let TMP_99 
\def (H1 c2 H3) in (arity_repl g c2 t0 a1 TMP_99 a2 H2))))))))))) in 
(arity_ind g TMP_1 TMP_2 TMP_41 TMP_80 TMP_86 TMP_92 TMP_95 TMP_98 TMP_100 c1 
t a H)))))))))))))).

