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

include "basic_1/pr2/defs.ma".

include "basic_1/pr0/pr0.ma".

include "basic_1/getl/fwd.ma".

theorem pr2_confluence__pr2_free_free:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).(\forall (t2: T).((pr0 t0 
t1) \to ((pr0 t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pr0 t0 t1)).(\lambda (H0: (pr0 t0 t2)).(let TMP_1 \def (\lambda (t: 
T).(pr0 t2 t)) in (let TMP_2 \def (\lambda (t: T).(pr0 t1 t)) in (let TMP_3 
\def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_4 \def (\lambda (t: T).(pr2 c 
t2 t)) in (let TMP_5 \def (ex2 T TMP_3 TMP_4) in (let TMP_10 \def (\lambda 
(x: T).(\lambda (H1: (pr0 t2 x)).(\lambda (H2: (pr0 t1 x)).(let TMP_6 \def 
(\lambda (t: T).(pr2 c t1 t)) in (let TMP_7 \def (\lambda (t: T).(pr2 c t2 
t)) in (let TMP_8 \def (pr2_free c t1 x H2) in (let TMP_9 \def (pr2_free c t2 
x H1) in (ex_intro2 T TMP_6 TMP_7 x TMP_8 TMP_9)))))))) in (let TMP_11 \def 
(pr0_confluence t0 t2 H0 t1 H) in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_10 
TMP_11))))))))))))).

theorem pr2_confluence__pr2_free_delta:
 \forall (c: C).(\forall (d: C).(\forall (t0: T).(\forall (t1: T).(\forall 
(t2: T).(\forall (t4: T).(\forall (u: T).(\forall (i: nat).((pr0 t0 t1) \to 
((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t4) \to ((subst0 i u t4 t2) 
\to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))))))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (t4: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H: (pr0 
t0 t1)).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H1: (pr0 
t0 t4)).(\lambda (H2: (subst0 i u t4 t2)).(let TMP_1 \def (\lambda (t: 
T).(pr0 t4 t)) in (let TMP_2 \def (\lambda (t: T).(pr0 t1 t)) in (let TMP_3 
\def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_4 \def (\lambda (t: T).(pr2 c 
t2 t)) in (let TMP_5 \def (ex2 T TMP_3 TMP_4) in (let TMP_31 \def (\lambda 
(x: T).(\lambda (H3: (pr0 t4 x)).(\lambda (H4: (pr0 t1 x)).(let TMP_6 \def 
(pr0 t2 x) in (let TMP_7 \def (\lambda (w2: T).(pr0 t2 w2)) in (let TMP_8 
\def (\lambda (w2: T).(subst0 i u x w2)) in (let TMP_9 \def (ex2 T TMP_7 
TMP_8) in (let TMP_10 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_11 \def 
(\lambda (t: T).(pr2 c t2 t)) in (let TMP_12 \def (ex2 T TMP_10 TMP_11) in 
(let TMP_17 \def (\lambda (H5: (pr0 t2 x)).(let TMP_13 \def (\lambda (t: 
T).(pr2 c t1 t)) in (let TMP_14 \def (\lambda (t: T).(pr2 c t2 t)) in (let 
TMP_15 \def (pr2_free c t1 x H4) in (let TMP_16 \def (pr2_free c t2 x H5) in 
(ex_intro2 T TMP_13 TMP_14 x TMP_15 TMP_16)))))) in (let TMP_28 \def (\lambda 
(H5: (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i u x 
w2)))).(let TMP_18 \def (\lambda (w2: T).(pr0 t2 w2)) in (let TMP_19 \def 
(\lambda (w2: T).(subst0 i u x w2)) in (let TMP_20 \def (\lambda (t: T).(pr2 
c t1 t)) in (let TMP_21 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_22 
\def (ex2 T TMP_20 TMP_21) in (let TMP_27 \def (\lambda (x0: T).(\lambda (H6: 
(pr0 t2 x0)).(\lambda (H7: (subst0 i u x x0)).(let TMP_23 \def (\lambda (t: 
T).(pr2 c t1 t)) in (let TMP_24 \def (\lambda (t: T).(pr2 c t2 t)) in (let 
TMP_25 \def (pr2_delta c d u i H0 t1 x H4 x0 H7) in (let TMP_26 \def 
(pr2_free c t2 x0 H6) in (ex_intro2 T TMP_23 TMP_24 x0 TMP_25 TMP_26)))))))) 
in (ex2_ind T TMP_18 TMP_19 TMP_22 TMP_27 H5)))))))) in (let TMP_29 \def 
(pr0_refl u) in (let TMP_30 \def (pr0_subst0 t4 x H3 u t2 i H2 u TMP_29) in 
(or_ind TMP_6 TMP_9 TMP_12 TMP_17 TMP_28 TMP_30))))))))))))))) in (let TMP_32 
\def (pr0_confluence t0 t4 H1 t1 H) in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_31 
TMP_32))))))))))))))))))).

theorem pr2_confluence__pr2_delta_delta:
 \forall (c: C).(\forall (d: C).(\forall (d0: C).(\forall (t0: T).(\forall 
(t1: T).(\forall (t2: T).(\forall (t3: T).(\forall (t4: T).(\forall (u: 
T).(\forall (u0: T).(\forall (i: nat).(\forall (i0: nat).((getl i c (CHead d 
(Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i u t3 t1) \to ((getl i0 c 
(CHead d0 (Bind Abbr) u0)) \to ((pr0 t0 t4) \to ((subst0 i0 u0 t4 t2) \to 
(ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))))))))))))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (d0: C).(\lambda (t0: T).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (u: 
T).(\lambda (u0: T).(\lambda (i: nat).(\lambda (i0: nat).(\lambda (H: (getl i 
c (CHead d (Bind Abbr) u))).(\lambda (H0: (pr0 t0 t3)).(\lambda (H1: (subst0 
i u t3 t1)).(\lambda (H2: (getl i0 c (CHead d0 (Bind Abbr) u0))).(\lambda 
(H3: (pr0 t0 t4)).(\lambda (H4: (subst0 i0 u0 t4 t2)).(let TMP_1 \def 
(\lambda (t: T).(pr0 t4 t)) in (let TMP_2 \def (\lambda (t: T).(pr0 t3 t)) in 
(let TMP_3 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_4 \def (\lambda (t: 
T).(pr2 c t2 t)) in (let TMP_5 \def (ex2 T TMP_3 TMP_4) in (let TMP_165 \def 
(\lambda (x: T).(\lambda (H5: (pr0 t4 x)).(\lambda (H6: (pr0 t3 x)).(let 
TMP_6 \def (pr0 t1 x) in (let TMP_7 \def (\lambda (w2: T).(pr0 t1 w2)) in 
(let TMP_8 \def (\lambda (w2: T).(subst0 i u x w2)) in (let TMP_9 \def (ex2 T 
TMP_7 TMP_8) in (let TMP_10 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_11 
\def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_12 \def (ex2 T TMP_10 TMP_11) 
in (let TMP_38 \def (\lambda (H7: (pr0 t1 x)).(let TMP_13 \def (pr0 t2 x) in 
(let TMP_14 \def (\lambda (w2: T).(pr0 t2 w2)) in (let TMP_15 \def (\lambda 
(w2: T).(subst0 i0 u0 x w2)) in (let TMP_16 \def (ex2 T TMP_14 TMP_15) in 
(let TMP_17 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_18 \def (\lambda 
(t: T).(pr2 c t2 t)) in (let TMP_19 \def (ex2 T TMP_17 TMP_18) in (let TMP_24 
\def (\lambda (H8: (pr0 t2 x)).(let TMP_20 \def (\lambda (t: T).(pr2 c t1 t)) 
in (let TMP_21 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_22 \def 
(pr2_free c t1 x H7) in (let TMP_23 \def (pr2_free c t2 x H8) in (ex_intro2 T 
TMP_20 TMP_21 x TMP_22 TMP_23)))))) in (let TMP_35 \def (\lambda (H8: (ex2 T 
(\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i0 u0 x w2)))).(let 
TMP_25 \def (\lambda (w2: T).(pr0 t2 w2)) in (let TMP_26 \def (\lambda (w2: 
T).(subst0 i0 u0 x w2)) in (let TMP_27 \def (\lambda (t: T).(pr2 c t1 t)) in 
(let TMP_28 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_29 \def (ex2 T 
TMP_27 TMP_28) in (let TMP_34 \def (\lambda (x0: T).(\lambda (H9: (pr0 t2 
x0)).(\lambda (H10: (subst0 i0 u0 x x0)).(let TMP_30 \def (\lambda (t: 
T).(pr2 c t1 t)) in (let TMP_31 \def (\lambda (t: T).(pr2 c t2 t)) in (let 
TMP_32 \def (pr2_delta c d0 u0 i0 H2 t1 x H7 x0 H10) in (let TMP_33 \def 
(pr2_free c t2 x0 H9) in (ex_intro2 T TMP_30 TMP_31 x0 TMP_32 TMP_33)))))))) 
in (ex2_ind T TMP_25 TMP_26 TMP_29 TMP_34 H8)))))))) in (let TMP_36 \def 
(pr0_refl u0) in (let TMP_37 \def (pr0_subst0 t4 x H5 u0 t2 i0 H4 u0 TMP_36) 
in (or_ind TMP_13 TMP_16 TMP_19 TMP_24 TMP_35 TMP_37))))))))))))) in (let 
TMP_162 \def (\lambda (H7: (ex2 T (\lambda (w2: T).(pr0 t1 w2)) (\lambda (w2: 
T).(subst0 i u x w2)))).(let TMP_39 \def (\lambda (w2: T).(pr0 t1 w2)) in 
(let TMP_40 \def (\lambda (w2: T).(subst0 i u x w2)) in (let TMP_41 \def 
(\lambda (t: T).(pr2 c t1 t)) in (let TMP_42 \def (\lambda (t: T).(pr2 c t2 
t)) in (let TMP_43 \def (ex2 T TMP_41 TMP_42) in (let TMP_161 \def (\lambda 
(x0: T).(\lambda (H8: (pr0 t1 x0)).(\lambda (H9: (subst0 i u x x0)).(let 
TMP_44 \def (pr0 t2 x) in (let TMP_45 \def (\lambda (w2: T).(pr0 t2 w2)) in 
(let TMP_46 \def (\lambda (w2: T).(subst0 i0 u0 x w2)) in (let TMP_47 \def 
(ex2 T TMP_45 TMP_46) in (let TMP_48 \def (\lambda (t: T).(pr2 c t1 t)) in 
(let TMP_49 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_50 \def (ex2 T 
TMP_48 TMP_49) in (let TMP_55 \def (\lambda (H10: (pr0 t2 x)).(let TMP_51 
\def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_52 \def (\lambda (t: T).(pr2 c 
t2 t)) in (let TMP_53 \def (pr2_free c t1 x0 H8) in (let TMP_54 \def 
(pr2_delta c d u i H t2 x H10 x0 H9) in (ex_intro2 T TMP_51 TMP_52 x0 TMP_53 
TMP_54)))))) in (let TMP_158 \def (\lambda (H10: (ex2 T (\lambda (w2: T).(pr0 
t2 w2)) (\lambda (w2: T).(subst0 i0 u0 x w2)))).(let TMP_56 \def (\lambda 
(w2: T).(pr0 t2 w2)) in (let TMP_57 \def (\lambda (w2: T).(subst0 i0 u0 x 
w2)) in (let TMP_58 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_59 \def 
(\lambda (t: T).(pr2 c t2 t)) in (let TMP_60 \def (ex2 T TMP_58 TMP_59) in 
(let TMP_157 \def (\lambda (x1: T).(\lambda (H11: (pr0 t2 x1)).(\lambda (H12: 
(subst0 i0 u0 x x1)).(let TMP_61 \def (\lambda (t: T).(pr2 c t1 t)) in (let 
TMP_62 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_63 \def (ex2 T TMP_61 
TMP_62) in (let TMP_76 \def (\lambda (H13: (not (eq nat i i0))).(let TMP_64 
\def (\lambda (t: T).(subst0 i u x1 t)) in (let TMP_65 \def (\lambda (t: 
T).(subst0 i0 u0 x0 t)) in (let TMP_66 \def (\lambda (t: T).(pr2 c t1 t)) in 
(let TMP_67 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_68 \def (ex2 T 
TMP_66 TMP_67) in (let TMP_73 \def (\lambda (x2: T).(\lambda (H14: (subst0 i 
u x1 x2)).(\lambda (H15: (subst0 i0 u0 x0 x2)).(let TMP_69 \def (\lambda (t: 
T).(pr2 c t1 t)) in (let TMP_70 \def (\lambda (t: T).(pr2 c t2 t)) in (let 
TMP_71 \def (pr2_delta c d0 u0 i0 H2 t1 x0 H8 x2 H15) in (let TMP_72 \def 
(pr2_delta c d u i H t2 x1 H11 x2 H14) in (ex_intro2 T TMP_69 TMP_70 x2 
TMP_71 TMP_72)))))))) in (let TMP_74 \def (sym_not_eq nat i i0 H13) in (let 
TMP_75 \def (subst0_confluence_neq x x1 u0 i0 H12 x0 u i H9 TMP_74) in 
(ex2_ind T TMP_64 TMP_65 TMP_68 TMP_73 TMP_75)))))))))) in (let TMP_156 \def 
(\lambda (H13: (eq nat i i0)).(let TMP_77 \def (\lambda (n: nat).(subst0 n u0 
x x1)) in (let H14 \def (eq_ind_r nat i0 TMP_77 H12 i H13) in (let TMP_80 
\def (\lambda (n: nat).(let TMP_78 \def (Bind Abbr) in (let TMP_79 \def 
(CHead d0 TMP_78 u0) in (getl n c TMP_79)))) in (let H15 \def (eq_ind_r nat 
i0 TMP_80 H2 i H13) in (let TMP_81 \def (Bind Abbr) in (let TMP_82 \def 
(CHead d TMP_81 u) in (let TMP_83 \def (\lambda (c0: C).(getl i c c0)) in 
(let TMP_84 \def (Bind Abbr) in (let TMP_85 \def (CHead d0 TMP_84 u0) in (let 
TMP_86 \def (Bind Abbr) in (let TMP_87 \def (CHead d TMP_86 u) in (let TMP_88 
\def (Bind Abbr) in (let TMP_89 \def (CHead d0 TMP_88 u0) in (let TMP_90 \def 
(getl_mono c TMP_87 i H TMP_89 H15) in (let H16 \def (eq_ind C TMP_82 TMP_83 
H TMP_85 TMP_90) in (let TMP_91 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) in (let TMP_92 \def (Bind 
Abbr) in (let TMP_93 \def (CHead d TMP_92 u) in (let TMP_94 \def (Bind Abbr) 
in (let TMP_95 \def (CHead d0 TMP_94 u0) in (let TMP_96 \def (Bind Abbr) in 
(let TMP_97 \def (CHead d TMP_96 u) in (let TMP_98 \def (Bind Abbr) in (let 
TMP_99 \def (CHead d0 TMP_98 u0) in (let TMP_100 \def (getl_mono c TMP_97 i H 
TMP_99 H15) in (let H17 \def (f_equal C C TMP_91 TMP_93 TMP_95 TMP_100) in 
(let TMP_101 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) in (let TMP_102 \def (Bind Abbr) in (let 
TMP_103 \def (CHead d TMP_102 u) in (let TMP_104 \def (Bind Abbr) in (let 
TMP_105 \def (CHead d0 TMP_104 u0) in (let TMP_106 \def (Bind Abbr) in (let 
TMP_107 \def (CHead d TMP_106 u) in (let TMP_108 \def (Bind Abbr) in (let 
TMP_109 \def (CHead d0 TMP_108 u0) in (let TMP_110 \def (getl_mono c TMP_107 
i H TMP_109 H15) in (let H18 \def (f_equal C T TMP_101 TMP_103 TMP_105 
TMP_110) in (let TMP_155 \def (\lambda (H19: (eq C d d0)).(let TMP_111 \def 
(\lambda (t: T).(subst0 i t x x1)) in (let H20 \def (eq_ind_r T u0 TMP_111 
H14 u H18) in (let TMP_114 \def (\lambda (t: T).(let TMP_112 \def (Bind Abbr) 
in (let TMP_113 \def (CHead d0 TMP_112 t) in (getl i c TMP_113)))) in (let 
H21 \def (eq_ind_r T u0 TMP_114 H16 u H18) in (let TMP_117 \def (\lambda (c0: 
C).(let TMP_115 \def (Bind Abbr) in (let TMP_116 \def (CHead c0 TMP_115 u) in 
(getl i c TMP_116)))) in (let H22 \def (eq_ind_r C d0 TMP_117 H21 d H19) in 
(let TMP_118 \def (eq T x1 x0) in (let TMP_119 \def (\lambda (t: T).(subst0 i 
u x1 t)) in (let TMP_120 \def (\lambda (t: T).(subst0 i u x0 t)) in (let 
TMP_121 \def (ex2 T TMP_119 TMP_120) in (let TMP_122 \def (subst0 i u x1 x0) 
in (let TMP_123 \def (subst0 i u x0 x1) in (let TMP_124 \def (\lambda (t: 
T).(pr2 c t1 t)) in (let TMP_125 \def (\lambda (t: T).(pr2 c t2 t)) in (let 
TMP_126 \def (ex2 T TMP_124 TMP_125) in (let TMP_132 \def (\lambda (H23: (eq 
T x1 x0)).(let TMP_127 \def (\lambda (t: T).(pr0 t2 t)) in (let H24 \def 
(eq_ind T x1 TMP_127 H11 x0 H23) in (let TMP_128 \def (\lambda (t: T).(pr2 c 
t1 t)) in (let TMP_129 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_130 
\def (pr2_free c t1 x0 H8) in (let TMP_131 \def (pr2_free c t2 x0 H24) in 
(ex_intro2 T TMP_128 TMP_129 x0 TMP_130 TMP_131)))))))) in (let TMP_143 \def 
(\lambda (H23: (ex2 T (\lambda (t: T).(subst0 i u x1 t)) (\lambda (t: 
T).(subst0 i u x0 t)))).(let TMP_133 \def (\lambda (t: T).(subst0 i u x1 t)) 
in (let TMP_134 \def (\lambda (t: T).(subst0 i u x0 t)) in (let TMP_135 \def 
(\lambda (t: T).(pr2 c t1 t)) in (let TMP_136 \def (\lambda (t: T).(pr2 c t2 
t)) in (let TMP_137 \def (ex2 T TMP_135 TMP_136) in (let TMP_142 \def 
(\lambda (x2: T).(\lambda (H24: (subst0 i u x1 x2)).(\lambda (H25: (subst0 i 
u x0 x2)).(let TMP_138 \def (\lambda (t: T).(pr2 c t1 t)) in (let TMP_139 
\def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_140 \def (pr2_delta c d u i 
H22 t1 x0 H8 x2 H25) in (let TMP_141 \def (pr2_delta c d u i H22 t2 x1 H11 x2 
H24) in (ex_intro2 T TMP_138 TMP_139 x2 TMP_140 TMP_141)))))))) in (ex2_ind T 
TMP_133 TMP_134 TMP_137 TMP_142 H23)))))))) in (let TMP_148 \def (\lambda 
(H23: (subst0 i u x1 x0)).(let TMP_144 \def (\lambda (t: T).(pr2 c t1 t)) in 
(let TMP_145 \def (\lambda (t: T).(pr2 c t2 t)) in (let TMP_146 \def 
(pr2_free c t1 x0 H8) in (let TMP_147 \def (pr2_delta c d u i H22 t2 x1 H11 
x0 H23) in (ex_intro2 T TMP_144 TMP_145 x0 TMP_146 TMP_147)))))) in (let 
TMP_153 \def (\lambda (H23: (subst0 i u x0 x1)).(let TMP_149 \def (\lambda 
(t: T).(pr2 c t1 t)) in (let TMP_150 \def (\lambda (t: T).(pr2 c t2 t)) in 
(let TMP_151 \def (pr2_delta c d u i H22 t1 x0 H8 x1 H23) in (let TMP_152 
\def (pr2_free c t2 x1 H11) in (ex_intro2 T TMP_149 TMP_150 x1 TMP_151 
TMP_152)))))) in (let TMP_154 \def (subst0_confluence_eq x x1 u i H20 x0 H9) 
in (or4_ind TMP_118 TMP_121 TMP_122 TMP_123 TMP_126 TMP_132 TMP_143 TMP_148 
TMP_153 TMP_154)))))))))))))))))))))) in (TMP_155 
H17)))))))))))))))))))))))))))))))))))))))) in (neq_eq_e i i0 TMP_63 TMP_76 
TMP_156))))))))) in (ex2_ind T TMP_56 TMP_57 TMP_60 TMP_157 H10)))))))) in 
(let TMP_159 \def (pr0_refl u0) in (let TMP_160 \def (pr0_subst0 t4 x H5 u0 
t2 i0 H4 u0 TMP_159) in (or_ind TMP_44 TMP_47 TMP_50 TMP_55 TMP_158 
TMP_160))))))))))))))) in (ex2_ind T TMP_39 TMP_40 TMP_43 TMP_161 H7)))))))) 
in (let TMP_163 \def (pr0_refl u) in (let TMP_164 \def (pr0_subst0 t3 x H6 u 
t1 i H1 u TMP_163) in (or_ind TMP_6 TMP_9 TMP_12 TMP_38 TMP_162 
TMP_164))))))))))))))) in (let TMP_166 \def (pr0_confluence t0 t4 H3 t3 H0) 
in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_165 TMP_166))))))))))))))))))))))))).

theorem pr2_confluence:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall 
(t2: T).((pr2 c t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr2 c t0 
t1)).(\lambda (t2: T).(\lambda (H0: (pr2 c t0 t2)).(let H1 \def (match H with 
[(pr2_free c0 t3 t4 H1) \Rightarrow (\lambda (H2: (eq C c0 c)).(\lambda (H3: 
(eq T t3 t0)).(\lambda (H4: (eq T t4 t1)).(let TMP_54 \def (\lambda (_: 
C).((eq T t3 t0) \to ((eq T t4 t1) \to ((pr0 t3 t4) \to (let TMP_52 \def 
(\lambda (t: T).(pr2 c t1 t)) in (let TMP_53 \def (\lambda (t: T).(pr2 c t2 
t)) in (ex2 T TMP_52 TMP_53))))))) in (let TMP_98 \def (\lambda (H5: (eq T t3 
t0)).(let TMP_57 \def (\lambda (t: T).((eq T t4 t1) \to ((pr0 t t4) \to (let 
TMP_55 \def (\lambda (t5: T).(pr2 c t1 t5)) in (let TMP_56 \def (\lambda (t5: 
T).(pr2 c t2 t5)) in (ex2 T TMP_55 TMP_56)))))) in (let TMP_96 \def (\lambda 
(H6: (eq T t4 t1)).(let TMP_60 \def (\lambda (t: T).((pr0 t0 t) \to (let 
TMP_58 \def (\lambda (t5: T).(pr2 c t1 t5)) in (let TMP_59 \def (\lambda (t5: 
T).(pr2 c t2 t5)) in (ex2 T TMP_58 TMP_59))))) in (let TMP_94 \def (\lambda 
(H7: (pr0 t0 t1)).(let H8 \def (match H0 with [(pr2_free c1 t5 t6 H8) 
\Rightarrow (\lambda (H9: (eq C c1 c)).(\lambda (H10: (eq T t5 t0)).(\lambda 
(H11: (eq T t6 t2)).(let TMP_78 \def (\lambda (_: C).((eq T t5 t0) \to ((eq T 
t6 t2) \to ((pr0 t5 t6) \to (let TMP_76 \def (\lambda (t: T).(pr2 c t1 t)) in 
(let TMP_77 \def (\lambda (t: T).(pr2 c t2 t)) in (ex2 T TMP_76 TMP_77))))))) 
in (let TMP_89 \def (\lambda (H12: (eq T t5 t0)).(let TMP_81 \def (\lambda 
(t: T).((eq T t6 t2) \to ((pr0 t t6) \to (let TMP_79 \def (\lambda (t7: 
T).(pr2 c t1 t7)) in (let TMP_80 \def (\lambda (t7: T).(pr2 c t2 t7)) in (ex2 
T TMP_79 TMP_80)))))) in (let TMP_87 \def (\lambda (H13: (eq T t6 t2)).(let 
TMP_84 \def (\lambda (t: T).((pr0 t0 t) \to (let TMP_82 \def (\lambda (t7: 
T).(pr2 c t1 t7)) in (let TMP_83 \def (\lambda (t7: T).(pr2 c t2 t7)) in (ex2 
T TMP_82 TMP_83))))) in (let TMP_85 \def (\lambda (H14: (pr0 t0 
t2)).(pr2_confluence__pr2_free_free c t0 t1 t2 H7 H14)) in (let TMP_86 \def 
(sym_eq T t6 t2 H13) in (eq_ind T t2 TMP_84 TMP_85 t6 TMP_86))))) in (let 
TMP_88 \def (sym_eq T t5 t0 H12) in (eq_ind T t0 TMP_81 TMP_87 t5 TMP_88))))) 
in (let TMP_90 \def (sym_eq C c1 c H9) in (eq_ind C c TMP_78 TMP_89 c1 TMP_90 
H10 H11 H8))))))) | (pr2_delta c1 d u i H8 t5 t6 H9 t H10) \Rightarrow 
(\lambda (H11: (eq C c1 c)).(\lambda (H12: (eq T t5 t0)).(\lambda (H13: (eq T 
t t2)).(let TMP_63 \def (\lambda (c2: C).((eq T t5 t0) \to ((eq T t t2) \to 
((getl i c2 (CHead d (Bind Abbr) u)) \to ((pr0 t5 t6) \to ((subst0 i u t6 t) 
\to (let TMP_61 \def (\lambda (t7: T).(pr2 c t1 t7)) in (let TMP_62 \def 
(\lambda (t7: T).(pr2 c t2 t7)) in (ex2 T TMP_61 TMP_62))))))))) in (let 
TMP_74 \def (\lambda (H14: (eq T t5 t0)).(let TMP_66 \def (\lambda (t7: 
T).((eq T t t2) \to ((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t7 t6) \to 
((subst0 i u t6 t) \to (let TMP_64 \def (\lambda (t8: T).(pr2 c t1 t8)) in 
(let TMP_65 \def (\lambda (t8: T).(pr2 c t2 t8)) in (ex2 T TMP_64 
TMP_65)))))))) in (let TMP_72 \def (\lambda (H15: (eq T t t2)).(let TMP_69 
\def (\lambda (t7: T).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t6) 
\to ((subst0 i u t6 t7) \to (let TMP_67 \def (\lambda (t8: T).(pr2 c t1 t8)) 
in (let TMP_68 \def (\lambda (t8: T).(pr2 c t2 t8)) in (ex2 T TMP_67 
TMP_68))))))) in (let TMP_70 \def (\lambda (H16: (getl i c (CHead d (Bind 
Abbr) u))).(\lambda (H17: (pr0 t0 t6)).(\lambda (H18: (subst0 i u t6 
t2)).(pr2_confluence__pr2_free_delta c d t0 t1 t2 t6 u i H7 H16 H17 H18)))) 
in (let TMP_71 \def (sym_eq T t t2 H15) in (eq_ind T t2 TMP_69 TMP_70 t 
TMP_71))))) in (let TMP_73 \def (sym_eq T t5 t0 H14) in (eq_ind T t0 TMP_66 
TMP_72 t5 TMP_73))))) in (let TMP_75 \def (sym_eq C c1 c H11) in (eq_ind C c 
TMP_63 TMP_74 c1 TMP_75 H12 H13 H8 H9 H10)))))))]) in (let TMP_91 \def 
(refl_equal C c) in (let TMP_92 \def (refl_equal T t0) in (let TMP_93 \def 
(refl_equal T t2) in (H8 TMP_91 TMP_92 TMP_93)))))) in (let TMP_95 \def 
(sym_eq T t4 t1 H6) in (eq_ind T t1 TMP_60 TMP_94 t4 TMP_95))))) in (let 
TMP_97 \def (sym_eq T t3 t0 H5) in (eq_ind T t0 TMP_57 TMP_96 t3 TMP_97))))) 
in (let TMP_99 \def (sym_eq C c0 c H2) in (eq_ind C c TMP_54 TMP_98 c0 TMP_99 
H3 H4 H1))))))) | (pr2_delta c0 d u i H1 t3 t4 H2 t H3) \Rightarrow (\lambda 
(H4: (eq C c0 c)).(\lambda (H5: (eq T t3 t0)).(\lambda (H6: (eq T t t1)).(let 
TMP_3 \def (\lambda (c1: C).((eq T t3 t0) \to ((eq T t t1) \to ((getl i c1 
(CHead d (Bind Abbr) u)) \to ((pr0 t3 t4) \to ((subst0 i u t4 t) \to (let 
TMP_1 \def (\lambda (t5: T).(pr2 c t1 t5)) in (let TMP_2 \def (\lambda (t5: 
T).(pr2 c t2 t5)) in (ex2 T TMP_1 TMP_2))))))))) in (let TMP_50 \def (\lambda 
(H7: (eq T t3 t0)).(let TMP_6 \def (\lambda (t5: T).((eq T t t1) \to ((getl i 
c (CHead d (Bind Abbr) u)) \to ((pr0 t5 t4) \to ((subst0 i u t4 t) \to (let 
TMP_4 \def (\lambda (t6: T).(pr2 c t1 t6)) in (let TMP_5 \def (\lambda (t6: 
T).(pr2 c t2 t6)) in (ex2 T TMP_4 TMP_5)))))))) in (let TMP_48 \def (\lambda 
(H8: (eq T t t1)).(let TMP_9 \def (\lambda (t5: T).((getl i c (CHead d (Bind 
Abbr) u)) \to ((pr0 t0 t4) \to ((subst0 i u t4 t5) \to (let TMP_7 \def 
(\lambda (t6: T).(pr2 c t1 t6)) in (let TMP_8 \def (\lambda (t6: T).(pr2 c t2 
t6)) in (ex2 T TMP_7 TMP_8))))))) in (let TMP_46 \def (\lambda (H9: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (H10: (pr0 t0 t4)).(\lambda (H11: (subst0 
i u t4 t1)).(let H12 \def (match H0 with [(pr2_free c1 t5 t6 H12) \Rightarrow 
(\lambda (H13: (eq C c1 c)).(\lambda (H14: (eq T t5 t0)).(\lambda (H15: (eq T 
t6 t2)).(let TMP_27 \def (\lambda (_: C).((eq T t5 t0) \to ((eq T t6 t2) \to 
((pr0 t5 t6) \to (let TMP_25 \def (\lambda (t7: T).(pr2 c t1 t7)) in (let 
TMP_26 \def (\lambda (t7: T).(pr2 c t2 t7)) in (ex2 T TMP_25 TMP_26))))))) in 
(let TMP_41 \def (\lambda (H16: (eq T t5 t0)).(let TMP_30 \def (\lambda (t7: 
T).((eq T t6 t2) \to ((pr0 t7 t6) \to (let TMP_28 \def (\lambda (t8: T).(pr2 
c t1 t8)) in (let TMP_29 \def (\lambda (t8: T).(pr2 c t2 t8)) in (ex2 T 
TMP_28 TMP_29)))))) in (let TMP_39 \def (\lambda (H17: (eq T t6 t2)).(let 
TMP_33 \def (\lambda (t7: T).((pr0 t0 t7) \to (let TMP_31 \def (\lambda (t8: 
T).(pr2 c t1 t8)) in (let TMP_32 \def (\lambda (t8: T).(pr2 c t2 t8)) in (ex2 
T TMP_31 TMP_32))))) in (let TMP_37 \def (\lambda (H18: (pr0 t0 t2)).(let 
TMP_34 \def (pr2 c t2) in (let TMP_35 \def (pr2 c t1) in (let TMP_36 \def 
(pr2_confluence__pr2_free_delta c d t0 t2 t1 t4 u i H18 H9 H10 H11) in 
(ex2_sym T TMP_34 TMP_35 TMP_36))))) in (let TMP_38 \def (sym_eq T t6 t2 H17) 
in (eq_ind T t2 TMP_33 TMP_37 t6 TMP_38))))) in (let TMP_40 \def (sym_eq T t5 
t0 H16) in (eq_ind T t0 TMP_30 TMP_39 t5 TMP_40))))) in (let TMP_42 \def 
(sym_eq C c1 c H13) in (eq_ind C c TMP_27 TMP_41 c1 TMP_42 H14 H15 H12))))))) 
| (pr2_delta c1 d0 u0 i0 H12 t5 t6 H13 t7 H14) \Rightarrow (\lambda (H15: (eq 
C c1 c)).(\lambda (H16: (eq T t5 t0)).(\lambda (H17: (eq T t7 t2)).(let 
TMP_12 \def (\lambda (c2: C).((eq T t5 t0) \to ((eq T t7 t2) \to ((getl i0 c2 
(CHead d0 (Bind Abbr) u0)) \to ((pr0 t5 t6) \to ((subst0 i0 u0 t6 t7) \to 
(let TMP_10 \def (\lambda (t8: T).(pr2 c t1 t8)) in (let TMP_11 \def (\lambda 
(t8: T).(pr2 c t2 t8)) in (ex2 T TMP_10 TMP_11))))))))) in (let TMP_23 \def 
(\lambda (H18: (eq T t5 t0)).(let TMP_15 \def (\lambda (t8: T).((eq T t7 t2) 
\to ((getl i0 c (CHead d0 (Bind Abbr) u0)) \to ((pr0 t8 t6) \to ((subst0 i0 
u0 t6 t7) \to (let TMP_13 \def (\lambda (t9: T).(pr2 c t1 t9)) in (let TMP_14 
\def (\lambda (t9: T).(pr2 c t2 t9)) in (ex2 T TMP_13 TMP_14)))))))) in (let 
TMP_21 \def (\lambda (H19: (eq T t7 t2)).(let TMP_18 \def (\lambda (t8: 
T).((getl i0 c (CHead d0 (Bind Abbr) u0)) \to ((pr0 t0 t6) \to ((subst0 i0 u0 
t6 t8) \to (let TMP_16 \def (\lambda (t9: T).(pr2 c t1 t9)) in (let TMP_17 
\def (\lambda (t9: T).(pr2 c t2 t9)) in (ex2 T TMP_16 TMP_17))))))) in (let 
TMP_19 \def (\lambda (H20: (getl i0 c (CHead d0 (Bind Abbr) u0))).(\lambda 
(H21: (pr0 t0 t6)).(\lambda (H22: (subst0 i0 u0 t6 
t2)).(pr2_confluence__pr2_delta_delta c d d0 t0 t1 t2 t4 t6 u u0 i i0 H9 H10 
H11 H20 H21 H22)))) in (let TMP_20 \def (sym_eq T t7 t2 H19) in (eq_ind T t2 
TMP_18 TMP_19 t7 TMP_20))))) in (let TMP_22 \def (sym_eq T t5 t0 H18) in 
(eq_ind T t0 TMP_15 TMP_21 t5 TMP_22))))) in (let TMP_24 \def (sym_eq C c1 c 
H15) in (eq_ind C c TMP_12 TMP_23 c1 TMP_24 H16 H17 H12 H13 H14)))))))]) in 
(let TMP_43 \def (refl_equal C c) in (let TMP_44 \def (refl_equal T t0) in 
(let TMP_45 \def (refl_equal T t2) in (H12 TMP_43 TMP_44 TMP_45)))))))) in 
(let TMP_47 \def (sym_eq T t t1 H8) in (eq_ind T t1 TMP_9 TMP_46 t 
TMP_47))))) in (let TMP_49 \def (sym_eq T t3 t0 H7) in (eq_ind T t0 TMP_6 
TMP_48 t3 TMP_49))))) in (let TMP_51 \def (sym_eq C c0 c H4) in (eq_ind C c 
TMP_3 TMP_50 c0 TMP_51 H5 H6 H1 H2 H3)))))))]) in (let TMP_100 \def 
(refl_equal C c) in (let TMP_101 \def (refl_equal T t0) in (let TMP_102 \def 
(refl_equal T t1) in (H1 TMP_100 TMP_101 TMP_102)))))))))).

