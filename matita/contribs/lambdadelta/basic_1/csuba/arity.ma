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

include "basic_1/csuba/getl.ma".

include "basic_1/csuba/props.ma".

include "basic_1/arity/fwd.ma".

include "basic_1/csubv/getl.ma".

theorem csuba_arity:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((csuba g c1 c2) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(let TMP_1 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a0: A).(\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 a0)))))) in (let 
TMP_2 \def (\lambda (c: C).(\lambda (n: nat).(\lambda (c2: C).(\lambda (_: 
(csuba g c c2)).(arity_sort g c2 n))))) in (let TMP_11 \def (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u 
a0)).(\lambda (H2: ((\forall (c2: C).((csuba g d c2) \to (arity g c2 u 
a0))))).(\lambda (c2: C).(\lambda (H3: (csuba g c c2)).(let H4 \def 
(csuba_getl_abbr g c d u i H0 c2 H3) in (let TMP_5 \def (\lambda (d2: C).(let 
TMP_3 \def (Bind Abbr) in (let TMP_4 \def (CHead d2 TMP_3 u) in (getl i c2 
TMP_4)))) in (let TMP_6 \def (\lambda (d2: C).(csuba g d d2)) in (let TMP_7 
\def (TLRef i) in (let TMP_8 \def (arity g c2 TMP_7 a0) in (let TMP_10 \def 
(\lambda (x: C).(\lambda (H5: (getl i c2 (CHead x (Bind Abbr) u))).(\lambda 
(H6: (csuba g d x)).(let TMP_9 \def (H2 x H6) in (arity_abbr g c2 x u i H5 a0 
TMP_9))))) in (ex2_ind C TMP_5 TMP_6 TMP_8 TMP_10 H4))))))))))))))))) in (let 
TMP_53 \def (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c (CHead d (Bind Abst) u))).(\lambda (a0: 
A).(\lambda (H1: (arity g d u (asucc g a0))).(\lambda (H2: ((\forall (c2: 
C).((csuba g d c2) \to (arity g c2 u (asucc g a0)))))).(\lambda (c2: 
C).(\lambda (H3: (csuba g c c2)).(let H4 \def (csuba_getl_abst g c d u i H0 
c2 H3) in (let TMP_14 \def (\lambda (d2: C).(let TMP_12 \def (Bind Abst) in 
(let TMP_13 \def (CHead d2 TMP_12 u) in (getl i c2 TMP_13)))) in (let TMP_15 
\def (\lambda (d2: C).(csuba g d d2)) in (let TMP_16 \def (ex2 C TMP_14 
TMP_15) in (let TMP_19 \def (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(let TMP_17 \def (Bind Abbr) in (let TMP_18 \def (CHead d2 TMP_17 u2) in 
(getl i c2 TMP_18)))))) in (let TMP_20 \def (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d d2)))) in (let TMP_22 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a1: A).(let TMP_21 \def (asucc g a1) in (arity g 
d u TMP_21))))) in (let TMP_23 \def (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a1: A).(arity g d2 u2 a1)))) in (let TMP_24 \def (ex4_3 C T A 
TMP_19 TMP_20 TMP_22 TMP_23) in (let TMP_25 \def (TLRef i) in (let TMP_26 
\def (arity g c2 TMP_25 a0) in (let TMP_35 \def (\lambda (H5: (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d 
d2)))).(let TMP_29 \def (\lambda (d2: C).(let TMP_27 \def (Bind Abst) in (let 
TMP_28 \def (CHead d2 TMP_27 u) in (getl i c2 TMP_28)))) in (let TMP_30 \def 
(\lambda (d2: C).(csuba g d d2)) in (let TMP_31 \def (TLRef i) in (let TMP_32 
\def (arity g c2 TMP_31 a0) in (let TMP_34 \def (\lambda (x: C).(\lambda (H6: 
(getl i c2 (CHead x (Bind Abst) u))).(\lambda (H7: (csuba g d x)).(let TMP_33 
\def (H2 x H7) in (arity_abst g c2 x u i H6 a0 TMP_33))))) in (ex2_ind C 
TMP_29 TMP_30 TMP_32 TMP_34 H5))))))) in (let TMP_52 \def (\lambda (H5: 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(arity 
g d u (asucc g a1))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: 
A).(arity g d2 u2 a1)))))).(let TMP_38 \def (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(let TMP_36 \def (Bind Abbr) in (let TMP_37 \def (CHead d2 
TMP_36 u2) in (getl i c2 TMP_37)))))) in (let TMP_39 \def (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d d2)))) in (let TMP_41 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(let TMP_40 \def (asucc g 
a1) in (arity g d u TMP_40))))) in (let TMP_42 \def (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a1: A).(arity g d2 u2 a1)))) in (let TMP_43 \def (TLRef i) 
in (let TMP_44 \def (arity g c2 TMP_43 a0) in (let TMP_51 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H6: (getl i c2 (CHead x0 (Bind 
Abbr) x1))).(\lambda (_: (csuba g d x0)).(\lambda (H8: (arity g d u (asucc g 
x2))).(\lambda (H9: (arity g x0 x1 x2)).(let TMP_45 \def (TLRef i) in (let 
TMP_46 \def (arity_abbr g c2 x0 x1 i H6 x2 H9) in (let TMP_47 \def (asucc g 
x2) in (let TMP_48 \def (asucc g a0) in (let TMP_49 \def (arity_mono g d u 
TMP_47 H8 TMP_48 H1) in (let TMP_50 \def (asucc_inj g x2 a0 TMP_49) in 
(arity_repl g c2 TMP_45 x2 TMP_46 a0 TMP_50)))))))))))))) in (ex4_3_ind C T A 
TMP_38 TMP_39 TMP_41 TMP_42 TMP_44 TMP_51 H5))))))))) in (or_ind TMP_16 
TMP_24 TMP_26 TMP_35 TMP_52 H4)))))))))))))))))))))))) in (let TMP_60 \def 
(\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 u a1))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 
a2)).(\lambda (H4: ((\forall (c2: C).((csuba g (CHead c (Bind b) u) c2) \to 
(arity g c2 t0 a2))))).(\lambda (c2: C).(\lambda (H5: (csuba g c c2)).(let 
TMP_54 \def (H2 c2 H5) in (let TMP_55 \def (Bind b) in (let TMP_56 \def 
(CHead c2 TMP_55 u) in (let TMP_57 \def (Bind b) in (let TMP_58 \def 
(csuba_head g c c2 H5 TMP_57 u) in (let TMP_59 \def (H4 TMP_56 TMP_58) in 
(arity_bind g b H0 c2 u a1 TMP_54 t0 a2 TMP_59)))))))))))))))))))) in (let 
TMP_67 \def (\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: 
(arity g c u (asucc g a1))).(\lambda (H1: ((\forall (c2: C).((csuba g c c2) 
\to (arity g c2 u (asucc g a1)))))).(\lambda (t0: T).(\lambda (a2: 
A).(\lambda (_: (arity g (CHead c (Bind Abst) u) t0 a2)).(\lambda (H3: 
((\forall (c2: C).((csuba g (CHead c (Bind Abst) u) c2) \to (arity g c2 t0 
a2))))).(\lambda (c2: C).(\lambda (H4: (csuba g c c2)).(let TMP_61 \def (H1 
c2 H4) in (let TMP_62 \def (Bind Abst) in (let TMP_63 \def (CHead c2 TMP_62 
u) in (let TMP_64 \def (Bind Abst) in (let TMP_65 \def (csuba_head g c c2 H4 
TMP_64 u) in (let TMP_66 \def (H3 TMP_63 TMP_65) in (arity_head g c2 u a1 
TMP_61 t0 a2 TMP_66)))))))))))))))))) in (let TMP_70 \def (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda 
(H1: ((\forall (c2: C).((csuba g c c2) \to (arity g c2 u a1))))).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda 
(H3: ((\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 (AHead a1 
a2)))))).(\lambda (c2: C).(\lambda (H4: (csuba g c c2)).(let TMP_68 \def (H1 
c2 H4) in (let TMP_69 \def (H3 c2 H4) in (arity_appl g c2 u a1 TMP_68 t0 a2 
TMP_69)))))))))))))) in (let TMP_73 \def (\lambda (c: C).(\lambda (u: 
T).(\lambda (a0: A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda (H1: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 u (asucc g 
a0)))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: 
((\forall (c2: C).((csuba g c c2) \to (arity g c2 t0 a0))))).(\lambda (c2: 
C).(\lambda (H4: (csuba g c c2)).(let TMP_71 \def (H1 c2 H4) in (let TMP_72 
\def (H3 c2 H4) in (arity_cast g c2 u a0 TMP_71 t0 TMP_72))))))))))))) in 
(let TMP_75 \def (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda 
(_: (arity g c t0 a1)).(\lambda (H1: ((\forall (c2: C).((csuba g c c2) \to 
(arity g c2 t0 a1))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda 
(c2: C).(\lambda (H3: (csuba g c c2)).(let TMP_74 \def (H1 c2 H3) in 
(arity_repl g c2 t0 a1 TMP_74 a2 H2))))))))))) in (arity_ind g TMP_1 TMP_2 
TMP_11 TMP_53 TMP_60 TMP_67 TMP_70 TMP_73 TMP_75 c1 t a H)))))))))))))).

theorem csuba_arity_rev:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (c2: C).((csuba g c2 c1) \to ((csubv c2 c1) \to (arity g c2 
t a))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(let TMP_1 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a0: A).(\forall (c2: C).((csuba g c2 c) \to ((csubv c2 c) \to (arity g c2 t0 
a0))))))) in (let TMP_2 \def (\lambda (c: C).(\lambda (n: nat).(\lambda (c2: 
C).(\lambda (_: (csuba g c2 c)).(\lambda (_: (csubv c2 c)).(arity_sort g c2 
n)))))) in (let TMP_142 \def (\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (a0: A).(\lambda (H1: (arity g d u a0)).(\lambda (H2: ((\forall 
(c2: C).((csuba g c2 d) \to ((csubv c2 d) \to (arity g c2 u a0)))))).(\lambda 
(c2: C).(\lambda (H3: (csuba g c2 c)).(\lambda (H4: (csubv c2 c)).(let H_x 
\def (csuba_getl_abbr_rev g c d u i H0 c2 H3) in (let H5 \def H_x in (let 
TMP_5 \def (\lambda (d2: C).(let TMP_3 \def (Bind Abbr) in (let TMP_4 \def 
(CHead d2 TMP_3 u) in (getl i c2 TMP_4)))) in (let TMP_6 \def (\lambda (d2: 
C).(csuba g d2 d)) in (let TMP_7 \def (ex2 C TMP_5 TMP_6) in (let TMP_10 \def 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(let TMP_8 \def (Bind Abst) 
in (let TMP_9 \def (CHead d2 TMP_8 u2) in (getl i c2 TMP_9)))))) in (let 
TMP_11 \def (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d)))) in (let TMP_13 \def (\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: 
A).(let TMP_12 \def (asucc g a1) in (arity g d2 u2 TMP_12))))) in (let TMP_14 
\def (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(arity g d u a1)))) in 
(let TMP_15 \def (ex4_3 C T A TMP_10 TMP_11 TMP_13 TMP_14) in (let TMP_18 
\def (\lambda (d2: C).(\lambda (u2: T).(let TMP_16 \def (Bind Void) in (let 
TMP_17 \def (CHead d2 TMP_16 u2) in (getl i c2 TMP_17))))) in (let TMP_19 
\def (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))) in (let TMP_20 \def 
(ex2_2 C T TMP_18 TMP_19) in (let TMP_21 \def (TLRef i) in (let TMP_22 \def 
(arity g c2 TMP_21 a0) in (let TMP_90 \def (\lambda (H6: (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d2 
d)))).(let TMP_25 \def (\lambda (d2: C).(let TMP_23 \def (Bind Abbr) in (let 
TMP_24 \def (CHead d2 TMP_23 u) in (getl i c2 TMP_24)))) in (let TMP_26 \def 
(\lambda (d2: C).(csuba g d2 d)) in (let TMP_27 \def (TLRef i) in (let TMP_28 
\def (arity g c2 TMP_27 a0) in (let TMP_89 \def (\lambda (x: C).(\lambda (H7: 
(getl i c2 (CHead x (Bind Abbr) u))).(\lambda (H8: (csuba g x d)).(let H_x0 
\def (csubv_getl_conf c2 c H4 Abbr x u i H7) in (let H9 \def H_x0 in (let 
TMP_29 \def (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv x d2)))) 
in (let TMP_32 \def (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(let 
TMP_30 \def (Bind b2) in (let TMP_31 \def (CHead d2 TMP_30 v2) in (getl i c 
TMP_31)))))) in (let TMP_33 \def (TLRef i) in (let TMP_34 \def (arity g c2 
TMP_33 a0) in (let TMP_88 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: T).(\lambda (H10: (csubv x x1)).(\lambda (H11: (getl i c (CHead x1 (Bind 
x0) x2))).(let TMP_35 \def (Bind Abbr) in (let TMP_36 \def (CHead d TMP_35 u) 
in (let TMP_37 \def (\lambda (c0: C).(getl i c c0)) in (let TMP_38 \def (Bind 
x0) in (let TMP_39 \def (CHead x1 TMP_38 x2) in (let TMP_40 \def (Bind Abbr) 
in (let TMP_41 \def (CHead d TMP_40 u) in (let TMP_42 \def (Bind x0) in (let 
TMP_43 \def (CHead x1 TMP_42 x2) in (let TMP_44 \def (getl_mono c TMP_41 i H0 
TMP_43 H11) in (let H12 \def (eq_ind C TMP_36 TMP_37 H0 TMP_39 TMP_44) in 
(let TMP_45 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow d | 
(CHead c0 _ _) \Rightarrow c0])) in (let TMP_46 \def (Bind Abbr) in (let 
TMP_47 \def (CHead d TMP_46 u) in (let TMP_48 \def (Bind x0) in (let TMP_49 
\def (CHead x1 TMP_48 x2) in (let TMP_50 \def (Bind Abbr) in (let TMP_51 \def 
(CHead d TMP_50 u) in (let TMP_52 \def (Bind x0) in (let TMP_53 \def (CHead 
x1 TMP_52 x2) in (let TMP_54 \def (getl_mono c TMP_51 i H0 TMP_53 H11) in 
(let H13 \def (f_equal C C TMP_45 TMP_47 TMP_49 TMP_54) in (let TMP_55 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) in (let TMP_56 \def (Bind Abbr) in (let TMP_57 \def (CHead d TMP_56 
u) in (let TMP_58 \def (Bind x0) in (let TMP_59 \def (CHead x1 TMP_58 x2) in 
(let TMP_60 \def (Bind Abbr) in (let TMP_61 \def (CHead d TMP_60 u) in (let 
TMP_62 \def (Bind x0) in (let TMP_63 \def (CHead x1 TMP_62 x2) in (let TMP_64 
\def (getl_mono c TMP_61 i H0 TMP_63 H11) in (let H14 \def (f_equal C B 
TMP_55 TMP_57 TMP_59 TMP_64) in (let TMP_65 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let 
TMP_66 \def (Bind Abbr) in (let TMP_67 \def (CHead d TMP_66 u) in (let TMP_68 
\def (Bind x0) in (let TMP_69 \def (CHead x1 TMP_68 x2) in (let TMP_70 \def 
(Bind Abbr) in (let TMP_71 \def (CHead d TMP_70 u) in (let TMP_72 \def (Bind 
x0) in (let TMP_73 \def (CHead x1 TMP_72 x2) in (let TMP_74 \def (getl_mono c 
TMP_71 i H0 TMP_73 H11) in (let H15 \def (f_equal C T TMP_65 TMP_67 TMP_69 
TMP_74) in (let TMP_86 \def (\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq 
C d x1)).(let TMP_77 \def (\lambda (t0: T).(let TMP_75 \def (Bind x0) in (let 
TMP_76 \def (CHead x1 TMP_75 t0) in (getl i c TMP_76)))) in (let H18 \def 
(eq_ind_r T x2 TMP_77 H12 u H15) in (let TMP_80 \def (\lambda (c0: C).(let 
TMP_78 \def (Bind x0) in (let TMP_79 \def (CHead c0 TMP_78 u) in (getl i c 
TMP_79)))) in (let H19 \def (eq_ind_r C x1 TMP_80 H18 d H17) in (let TMP_81 
\def (\lambda (c0: C).(csubv x c0)) in (let H20 \def (eq_ind_r C x1 TMP_81 
H10 d H17) in (let TMP_84 \def (\lambda (b: B).(let TMP_82 \def (Bind b) in 
(let TMP_83 \def (CHead d TMP_82 u) in (getl i c TMP_83)))) in (let H21 \def 
(eq_ind_r B x0 TMP_84 H19 Abbr H16) in (let TMP_85 \def (H2 x H8 H20) in 
(arity_abbr g c2 x u i H7 a0 TMP_85)))))))))))) in (let TMP_87 \def (TMP_86 
H14) in (TMP_87 H13)))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex2_3_ind B C T TMP_29 TMP_32 TMP_34 TMP_88 H9))))))))))) in (ex2_ind C 
TMP_25 TMP_26 TMP_28 TMP_89 H6))))))) in (let TMP_104 \def (\lambda (H6: 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: 
A).(arity g d2 u2 (asucc g a1))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a1: A).(arity g d u a1)))))).(let TMP_93 \def (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(let TMP_91 \def (Bind Abst) in (let TMP_92 \def (CHead d2 
TMP_91 u2) in (getl i c2 TMP_92)))))) in (let TMP_94 \def (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d)))) in (let TMP_96 \def 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a1: A).(let TMP_95 \def (asucc g 
a1) in (arity g d2 u2 TMP_95))))) in (let TMP_97 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a1: A).(arity g d u a1)))) in (let TMP_98 \def 
(TLRef i) in (let TMP_99 \def (arity g c2 TMP_98 a0) in (let TMP_103 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H7: (getl i c2 
(CHead x0 (Bind Abst) x1))).(\lambda (_: (csuba g x0 d)).(\lambda (H9: (arity 
g x0 x1 (asucc g x2))).(\lambda (H10: (arity g d u x2)).(let TMP_100 \def 
(TLRef i) in (let TMP_101 \def (arity_abst g c2 x0 x1 i H7 x2 H9) in (let 
TMP_102 \def (arity_mono g d u x2 H10 a0 H1) in (arity_repl g c2 TMP_100 x2 
TMP_101 a0 TMP_102))))))))))) in (ex4_3_ind C T A TMP_93 TMP_94 TMP_96 TMP_97 
TMP_99 TMP_103 H6))))))))) in (let TMP_141 \def (\lambda (H6: (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))))).(let TMP_107 \def 
(\lambda (d2: C).(\lambda (u2: T).(let TMP_105 \def (Bind Void) in (let 
TMP_106 \def (CHead d2 TMP_105 u2) in (getl i c2 TMP_106))))) in (let TMP_108 
\def (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))) in (let TMP_109 \def 
(TLRef i) in (let TMP_110 \def (arity g c2 TMP_109 a0) in (let TMP_140 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H7: (getl i c2 (CHead x0 (Bind 
Void) x1))).(\lambda (_: (csuba g x0 d)).(let H_x0 \def (csubv_getl_conf_void 
c2 c H4 x0 x1 i H7) in (let H9 \def H_x0 in (let TMP_111 \def (\lambda (d2: 
C).(\lambda (_: T).(csubv x0 d2))) in (let TMP_114 \def (\lambda (d2: 
C).(\lambda (v2: T).(let TMP_112 \def (Bind Void) in (let TMP_113 \def (CHead 
d2 TMP_112 v2) in (getl i c TMP_113))))) in (let TMP_115 \def (TLRef i) in 
(let TMP_116 \def (arity g c2 TMP_115 a0) in (let TMP_139 \def (\lambda (x2: 
C).(\lambda (x3: T).(\lambda (_: (csubv x0 x2)).(\lambda (H11: (getl i c 
(CHead x2 (Bind Void) x3))).(let TMP_117 \def (Bind Abbr) in (let TMP_118 
\def (CHead d TMP_117 u) in (let TMP_119 \def (\lambda (c0: C).(getl i c c0)) 
in (let TMP_120 \def (Bind Void) in (let TMP_121 \def (CHead x2 TMP_120 x3) 
in (let TMP_122 \def (Bind Abbr) in (let TMP_123 \def (CHead d TMP_122 u) in 
(let TMP_124 \def (Bind Void) in (let TMP_125 \def (CHead x2 TMP_124 x3) in 
(let TMP_126 \def (getl_mono c TMP_123 i H0 TMP_125 H11) in (let H12 \def 
(eq_ind C TMP_118 TMP_119 H0 TMP_121 TMP_126) in (let TMP_127 \def (Bind 
Abbr) in (let TMP_128 \def (CHead d TMP_127 u) in (let TMP_129 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_130 \def (Bind Void) in (let TMP_131 
\def (CHead x2 TMP_130 x3) in (let TMP_132 \def (Bind Abbr) in (let TMP_133 
\def (CHead d TMP_132 u) in (let TMP_134 \def (Bind Void) in (let TMP_135 
\def (CHead x2 TMP_134 x3) in (let TMP_136 \def (getl_mono c TMP_133 i H0 
TMP_135 H11) in (let H13 \def (eq_ind C TMP_128 TMP_129 I TMP_131 TMP_136) in 
(let TMP_137 \def (TLRef i) in (let TMP_138 \def (arity g c2 TMP_137 a0) in 
(False_ind TMP_138 H13))))))))))))))))))))))))))))) in (ex2_2_ind C T TMP_111 
TMP_114 TMP_116 TMP_139 H9)))))))))))) in (ex2_2_ind C T TMP_107 TMP_108 
TMP_110 TMP_140 H6))))))) in (or3_ind TMP_7 TMP_15 TMP_20 TMP_22 TMP_90 
TMP_104 TMP_141 H5)))))))))))))))))))))))))))))) in (let TMP_260 \def 
(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (_: (arity 
g d u (asucc g a0))).(\lambda (H2: ((\forall (c2: C).((csuba g c2 d) \to 
((csubv c2 d) \to (arity g c2 u (asucc g a0))))))).(\lambda (c2: C).(\lambda 
(H3: (csuba g c2 c)).(\lambda (H4: (csubv c2 c)).(let H_x \def 
(csuba_getl_abst_rev g c d u i H0 c2 H3) in (let H5 \def H_x in (let TMP_145 
\def (\lambda (d2: C).(let TMP_143 \def (Bind Abst) in (let TMP_144 \def 
(CHead d2 TMP_143 u) in (getl i c2 TMP_144)))) in (let TMP_146 \def (\lambda 
(d2: C).(csuba g d2 d)) in (let TMP_147 \def (ex2 C TMP_145 TMP_146) in (let 
TMP_150 \def (\lambda (d2: C).(\lambda (u2: T).(let TMP_148 \def (Bind Void) 
in (let TMP_149 \def (CHead d2 TMP_148 u2) in (getl i c2 TMP_149))))) in (let 
TMP_151 \def (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))) in (let 
TMP_152 \def (ex2_2 C T TMP_150 TMP_151) in (let TMP_153 \def (TLRef i) in 
(let TMP_154 \def (arity g c2 TMP_153 a0) in (let TMP_222 \def (\lambda (H6: 
(ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d)))).(let TMP_157 \def (\lambda (d2: C).(let TMP_155 \def 
(Bind Abst) in (let TMP_156 \def (CHead d2 TMP_155 u) in (getl i c2 
TMP_156)))) in (let TMP_158 \def (\lambda (d2: C).(csuba g d2 d)) in (let 
TMP_159 \def (TLRef i) in (let TMP_160 \def (arity g c2 TMP_159 a0) in (let 
TMP_221 \def (\lambda (x: C).(\lambda (H7: (getl i c2 (CHead x (Bind Abst) 
u))).(\lambda (H8: (csuba g x d)).(let H_x0 \def (csubv_getl_conf c2 c H4 
Abst x u i H7) in (let H9 \def H_x0 in (let TMP_161 \def (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv x d2)))) in (let TMP_164 \def 
(\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(let TMP_162 \def (Bind 
b2) in (let TMP_163 \def (CHead d2 TMP_162 v2) in (getl i c TMP_163)))))) in 
(let TMP_165 \def (TLRef i) in (let TMP_166 \def (arity g c2 TMP_165 a0) in 
(let TMP_220 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda 
(H10: (csubv x x1)).(\lambda (H11: (getl i c (CHead x1 (Bind x0) x2))).(let 
TMP_167 \def (Bind Abst) in (let TMP_168 \def (CHead d TMP_167 u) in (let 
TMP_169 \def (\lambda (c0: C).(getl i c c0)) in (let TMP_170 \def (Bind x0) 
in (let TMP_171 \def (CHead x1 TMP_170 x2) in (let TMP_172 \def (Bind Abst) 
in (let TMP_173 \def (CHead d TMP_172 u) in (let TMP_174 \def (Bind x0) in 
(let TMP_175 \def (CHead x1 TMP_174 x2) in (let TMP_176 \def (getl_mono c 
TMP_173 i H0 TMP_175 H11) in (let H12 \def (eq_ind C TMP_168 TMP_169 H0 
TMP_171 TMP_176) in (let TMP_177 \def (\lambda (e: C).(match e with [(CSort 
_) \Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) in (let TMP_178 \def 
(Bind Abst) in (let TMP_179 \def (CHead d TMP_178 u) in (let TMP_180 \def 
(Bind x0) in (let TMP_181 \def (CHead x1 TMP_180 x2) in (let TMP_182 \def 
(Bind Abst) in (let TMP_183 \def (CHead d TMP_182 u) in (let TMP_184 \def 
(Bind x0) in (let TMP_185 \def (CHead x1 TMP_184 x2) in (let TMP_186 \def 
(getl_mono c TMP_183 i H0 TMP_185 H11) in (let H13 \def (f_equal C C TMP_177 
TMP_179 TMP_181 TMP_186) in (let TMP_187 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow (match k with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) in (let TMP_188 \def (Bind 
Abst) in (let TMP_189 \def (CHead d TMP_188 u) in (let TMP_190 \def (Bind x0) 
in (let TMP_191 \def (CHead x1 TMP_190 x2) in (let TMP_192 \def (Bind Abst) 
in (let TMP_193 \def (CHead d TMP_192 u) in (let TMP_194 \def (Bind x0) in 
(let TMP_195 \def (CHead x1 TMP_194 x2) in (let TMP_196 \def (getl_mono c 
TMP_193 i H0 TMP_195 H11) in (let H14 \def (f_equal C B TMP_187 TMP_189 
TMP_191 TMP_196) in (let TMP_197 \def (\lambda (e: C).(match e with [(CSort 
_) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_198 \def 
(Bind Abst) in (let TMP_199 \def (CHead d TMP_198 u) in (let TMP_200 \def 
(Bind x0) in (let TMP_201 \def (CHead x1 TMP_200 x2) in (let TMP_202 \def 
(Bind Abst) in (let TMP_203 \def (CHead d TMP_202 u) in (let TMP_204 \def 
(Bind x0) in (let TMP_205 \def (CHead x1 TMP_204 x2) in (let TMP_206 \def 
(getl_mono c TMP_203 i H0 TMP_205 H11) in (let H15 \def (f_equal C T TMP_197 
TMP_199 TMP_201 TMP_206) in (let TMP_218 \def (\lambda (H16: (eq B Abst 
x0)).(\lambda (H17: (eq C d x1)).(let TMP_209 \def (\lambda (t0: T).(let 
TMP_207 \def (Bind x0) in (let TMP_208 \def (CHead x1 TMP_207 t0) in (getl i 
c TMP_208)))) in (let H18 \def (eq_ind_r T x2 TMP_209 H12 u H15) in (let 
TMP_212 \def (\lambda (c0: C).(let TMP_210 \def (Bind x0) in (let TMP_211 
\def (CHead c0 TMP_210 u) in (getl i c TMP_211)))) in (let H19 \def (eq_ind_r 
C x1 TMP_212 H18 d H17) in (let TMP_213 \def (\lambda (c0: C).(csubv x c0)) 
in (let H20 \def (eq_ind_r C x1 TMP_213 H10 d H17) in (let TMP_216 \def 
(\lambda (b: B).(let TMP_214 \def (Bind b) in (let TMP_215 \def (CHead d 
TMP_214 u) in (getl i c TMP_215)))) in (let H21 \def (eq_ind_r B x0 TMP_216 
H19 Abst H16) in (let TMP_217 \def (H2 x H8 H20) in (arity_abst g c2 x u i H7 
a0 TMP_217)))))))))))) in (let TMP_219 \def (TMP_218 H14) in (TMP_219 
H13)))))))))))))))))))))))))))))))))))))))))))))))))))) in (ex2_3_ind B C T 
TMP_161 TMP_164 TMP_166 TMP_220 H9))))))))))) in (ex2_ind C TMP_157 TMP_158 
TMP_160 TMP_221 H6))))))) in (let TMP_259 \def (\lambda (H6: (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))))).(let TMP_225 \def 
(\lambda (d2: C).(\lambda (u2: T).(let TMP_223 \def (Bind Void) in (let 
TMP_224 \def (CHead d2 TMP_223 u2) in (getl i c2 TMP_224))))) in (let TMP_226 
\def (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d))) in (let TMP_227 \def 
(TLRef i) in (let TMP_228 \def (arity g c2 TMP_227 a0) in (let TMP_258 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H7: (getl i c2 (CHead x0 (Bind 
Void) x1))).(\lambda (_: (csuba g x0 d)).(let H_x0 \def (csubv_getl_conf_void 
c2 c H4 x0 x1 i H7) in (let H9 \def H_x0 in (let TMP_229 \def (\lambda (d2: 
C).(\lambda (_: T).(csubv x0 d2))) in (let TMP_232 \def (\lambda (d2: 
C).(\lambda (v2: T).(let TMP_230 \def (Bind Void) in (let TMP_231 \def (CHead 
d2 TMP_230 v2) in (getl i c TMP_231))))) in (let TMP_233 \def (TLRef i) in 
(let TMP_234 \def (arity g c2 TMP_233 a0) in (let TMP_257 \def (\lambda (x2: 
C).(\lambda (x3: T).(\lambda (_: (csubv x0 x2)).(\lambda (H11: (getl i c 
(CHead x2 (Bind Void) x3))).(let TMP_235 \def (Bind Abst) in (let TMP_236 
\def (CHead d TMP_235 u) in (let TMP_237 \def (\lambda (c0: C).(getl i c c0)) 
in (let TMP_238 \def (Bind Void) in (let TMP_239 \def (CHead x2 TMP_238 x3) 
in (let TMP_240 \def (Bind Abst) in (let TMP_241 \def (CHead d TMP_240 u) in 
(let TMP_242 \def (Bind Void) in (let TMP_243 \def (CHead x2 TMP_242 x3) in 
(let TMP_244 \def (getl_mono c TMP_241 i H0 TMP_243 H11) in (let H12 \def 
(eq_ind C TMP_236 TMP_237 H0 TMP_239 TMP_244) in (let TMP_245 \def (Bind 
Abst) in (let TMP_246 \def (CHead d TMP_245 u) in (let TMP_247 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_248 \def (Bind Void) in (let TMP_249 
\def (CHead x2 TMP_248 x3) in (let TMP_250 \def (Bind Abst) in (let TMP_251 
\def (CHead d TMP_250 u) in (let TMP_252 \def (Bind Void) in (let TMP_253 
\def (CHead x2 TMP_252 x3) in (let TMP_254 \def (getl_mono c TMP_251 i H0 
TMP_253 H11) in (let H13 \def (eq_ind C TMP_246 TMP_247 I TMP_249 TMP_254) in 
(let TMP_255 \def (TLRef i) in (let TMP_256 \def (arity g c2 TMP_255 a0) in 
(False_ind TMP_256 H13))))))))))))))))))))))))))))) in (ex2_2_ind C T TMP_229 
TMP_232 TMP_234 TMP_257 H9)))))))))))) in (ex2_2_ind C T TMP_225 TMP_226 
TMP_228 TMP_258 H6))))))) in (or_ind TMP_147 TMP_152 TMP_154 TMP_222 TMP_259 
H5)))))))))))))))))))))))) in (let TMP_268 \def (\lambda (b: B).(\lambda (H0: 
(not (eq B b Abst))).(\lambda (c: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c u a1)).(\lambda (H2: ((\forall (c2: C).((csuba g 
c2 c) \to ((csubv c2 c) \to (arity g c2 u a1)))))).(\lambda (t0: T).(\lambda 
(a2: A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 a2)).(\lambda (H4: 
((\forall (c2: C).((csuba g c2 (CHead c (Bind b) u)) \to ((csubv c2 (CHead c 
(Bind b) u)) \to (arity g c2 t0 a2)))))).(\lambda (c2: C).(\lambda (H5: 
(csuba g c2 c)).(\lambda (H6: (csubv c2 c)).(let TMP_261 \def (H2 c2 H5 H6) 
in (let TMP_262 \def (Bind b) in (let TMP_263 \def (CHead c2 TMP_262 u) in 
(let TMP_264 \def (Bind b) in (let TMP_265 \def (csuba_head g c2 c H5 TMP_264 
u) in (let TMP_266 \def (csubv_bind_same c2 c H6 b u u) in (let TMP_267 \def 
(H4 TMP_263 TMP_265 TMP_266) in (arity_bind g b H0 c2 u a1 TMP_261 t0 a2 
TMP_267)))))))))))))))))))))) in (let TMP_276 \def (\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u (asucc g a1))).(\lambda 
(H1: ((\forall (c2: C).((csuba g c2 c) \to ((csubv c2 c) \to (arity g c2 u 
(asucc g a1))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g 
(CHead c (Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (c2: C).((csuba g c2 
(CHead c (Bind Abst) u)) \to ((csubv c2 (CHead c (Bind Abst) u)) \to (arity g 
c2 t0 a2)))))).(\lambda (c2: C).(\lambda (H4: (csuba g c2 c)).(\lambda (H5: 
(csubv c2 c)).(let TMP_269 \def (H1 c2 H4 H5) in (let TMP_270 \def (Bind 
Abst) in (let TMP_271 \def (CHead c2 TMP_270 u) in (let TMP_272 \def (Bind 
Abst) in (let TMP_273 \def (csuba_head g c2 c H4 TMP_272 u) in (let TMP_274 
\def (csubv_bind_same c2 c H5 Abst u u) in (let TMP_275 \def (H3 TMP_271 
TMP_273 TMP_274) in (arity_head g c2 u a1 TMP_269 t0 a2 
TMP_275)))))))))))))))))))) in (let TMP_279 \def (\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H1: ((\forall 
(c2: C).((csuba g c2 c) \to ((csubv c2 c) \to (arity g c2 u a1)))))).(\lambda 
(t0: T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda 
(H3: ((\forall (c2: C).((csuba g c2 c) \to ((csubv c2 c) \to (arity g c2 t0 
(AHead a1 a2))))))).(\lambda (c2: C).(\lambda (H4: (csuba g c2 c)).(\lambda 
(H5: (csubv c2 c)).(let TMP_277 \def (H1 c2 H4 H5) in (let TMP_278 \def (H3 
c2 H4 H5) in (arity_appl g c2 u a1 TMP_277 t0 a2 TMP_278))))))))))))))) in 
(let TMP_282 \def (\lambda (c: C).(\lambda (u: T).(\lambda (a0: A).(\lambda 
(_: (arity g c u (asucc g a0))).(\lambda (H1: ((\forall (c2: C).((csuba g c2 
c) \to ((csubv c2 c) \to (arity g c2 u (asucc g a0))))))).(\lambda (t0: 
T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: ((\forall (c2: C).((csuba g 
c2 c) \to ((csubv c2 c) \to (arity g c2 t0 a0)))))).(\lambda (c2: C).(\lambda 
(H4: (csuba g c2 c)).(\lambda (H5: (csubv c2 c)).(let TMP_280 \def (H1 c2 H4 
H5) in (let TMP_281 \def (H3 c2 H4 H5) in (arity_cast g c2 u a0 TMP_280 t0 
TMP_281)))))))))))))) in (let TMP_284 \def (\lambda (c: C).(\lambda (t0: 
T).(\lambda (a1: A).(\lambda (_: (arity g c t0 a1)).(\lambda (H1: ((\forall 
(c2: C).((csuba g c2 c) \to ((csubv c2 c) \to (arity g c2 t0 
a1)))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda (c2: 
C).(\lambda (H3: (csuba g c2 c)).(\lambda (H4: (csubv c2 c)).(let TMP_283 
\def (H1 c2 H3 H4) in (arity_repl g c2 t0 a1 TMP_283 a2 H2)))))))))))) in 
(arity_ind g TMP_1 TMP_2 TMP_142 TMP_260 TMP_268 TMP_276 TMP_279 TMP_282 
TMP_284 c1 t a H)))))))))))))).

theorem arity_appls_appl:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (a1: A).((arity g c 
v a1) \to (\forall (u: T).((arity g c u (asucc g a1)) \to (\forall (t: 
T).(\forall (vs: TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) vs 
(THead (Bind Abbr) v t)) a2) \to (arity g c (THeads (Flat Appl) vs (THead 
(Flat Appl) v (THead (Bind Abst) u t))) a2)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (a1: A).(\lambda (H: 
(arity g c v a1)).(\lambda (u: T).(\lambda (H0: (arity g c u (asucc g 
a1))).(\lambda (t: T).(\lambda (vs: TList).(let TMP_7 \def (\lambda (t0: 
TList).(\forall (a2: A).((arity g c (THeads (Flat Appl) t0 (THead (Bind Abbr) 
v t)) a2) \to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Flat Appl) in 
(let TMP_3 \def (Bind Abst) in (let TMP_4 \def (THead TMP_3 u t) in (let 
TMP_5 \def (THead TMP_2 v TMP_4) in (let TMP_6 \def (THeads TMP_1 t0 TMP_5) 
in (arity g c TMP_6 a2)))))))))) in (let TMP_30 \def (\lambda (a2: 
A).(\lambda (H1: (arity g c (THead (Bind Abbr) v t) a2)).(let H_x \def 
(arity_gen_bind Abbr not_abbr_abst g c v t a2 H1) in (let H2 \def H_x in (let 
TMP_8 \def (\lambda (a3: A).(arity g c v a3)) in (let TMP_11 \def (\lambda 
(_: A).(let TMP_9 \def (Bind Abbr) in (let TMP_10 \def (CHead c TMP_9 v) in 
(arity g TMP_10 t a2)))) in (let TMP_12 \def (Flat Appl) in (let TMP_13 \def 
(Bind Abst) in (let TMP_14 \def (THead TMP_13 u t) in (let TMP_15 \def (THead 
TMP_12 v TMP_14) in (let TMP_16 \def (arity g c TMP_15 a2) in (let TMP_29 
\def (\lambda (x: A).(\lambda (_: (arity g c v x)).(\lambda (H4: (arity g 
(CHead c (Bind Abbr) v) t a2)).(let TMP_17 \def (Bind Abst) in (let TMP_18 
\def (THead TMP_17 u t) in (let TMP_19 \def (Bind Abbr) in (let TMP_20 \def 
(CHead c TMP_19 v) in (let TMP_21 \def (Bind Abst) in (let TMP_22 \def (CHead 
c TMP_21 u) in (let TMP_23 \def (csuba_refl g c) in (let TMP_24 \def 
(csuba_abst g c c TMP_23 u a1 H0 v H) in (let TMP_25 \def (csubv_refl c) in 
(let TMP_26 \def (csubv_bind c c TMP_25 Abst not_abst_void Abbr u v) in (let 
TMP_27 \def (csuba_arity_rev g TMP_20 t a2 H4 TMP_22 TMP_24 TMP_26) in (let 
TMP_28 \def (arity_head g c u a1 H0 t a2 TMP_27) in (arity_appl g c v a1 H 
TMP_18 a2 TMP_28)))))))))))))))) in (ex2_ind A TMP_8 TMP_11 TMP_16 TMP_29 
H2))))))))))))) in (let TMP_60 \def (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (H1: ((\forall (a2: A).((arity g c (THeads (Flat Appl) t1 
(THead (Bind Abbr) v t)) a2) \to (arity g c (THeads (Flat Appl) t1 (THead 
(Flat Appl) v (THead (Bind Abst) u t))) a2))))).(\lambda (a2: A).(\lambda 
(H2: (arity g c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Bind 
Abbr) v t))) a2)).(let TMP_31 \def (Flat Appl) in (let TMP_32 \def (Bind 
Abbr) in (let TMP_33 \def (THead TMP_32 v t) in (let TMP_34 \def (THeads 
TMP_31 t1 TMP_33) in (let H3 \def (arity_gen_appl g c t0 TMP_34 a2 H2) in 
(let TMP_35 \def (\lambda (a3: A).(arity g c t0 a3)) in (let TMP_41 \def 
(\lambda (a3: A).(let TMP_36 \def (Flat Appl) in (let TMP_37 \def (Bind Abbr) 
in (let TMP_38 \def (THead TMP_37 v t) in (let TMP_39 \def (THeads TMP_36 t1 
TMP_38) in (let TMP_40 \def (AHead a3 a2) in (arity g c TMP_39 TMP_40))))))) 
in (let TMP_42 \def (Flat Appl) in (let TMP_43 \def (Flat Appl) in (let 
TMP_44 \def (Flat Appl) in (let TMP_45 \def (Bind Abst) in (let TMP_46 \def 
(THead TMP_45 u t) in (let TMP_47 \def (THead TMP_44 v TMP_46) in (let TMP_48 
\def (THeads TMP_43 t1 TMP_47) in (let TMP_49 \def (THead TMP_42 t0 TMP_48) 
in (let TMP_50 \def (arity g c TMP_49 a2) in (let TMP_59 \def (\lambda (x: 
A).(\lambda (H4: (arity g c t0 x)).(\lambda (H5: (arity g c (THeads (Flat 
Appl) t1 (THead (Bind Abbr) v t)) (AHead x a2))).(let TMP_51 \def (Flat Appl) 
in (let TMP_52 \def (Flat Appl) in (let TMP_53 \def (Bind Abst) in (let 
TMP_54 \def (THead TMP_53 u t) in (let TMP_55 \def (THead TMP_52 v TMP_54) in 
(let TMP_56 \def (THeads TMP_51 t1 TMP_55) in (let TMP_57 \def (AHead x a2) 
in (let TMP_58 \def (H1 TMP_57 H5) in (arity_appl g c t0 x H4 TMP_56 a2 
TMP_58)))))))))))) in (ex2_ind A TMP_35 TMP_41 TMP_50 TMP_59 
H3))))))))))))))))))))))) in (TList_ind TMP_7 TMP_30 TMP_60 vs)))))))))))).

