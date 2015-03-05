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

include "basic_1/pc3/left.ma".

include "basic_1/fsubst0/fwd.ma".

include "basic_1/csubst0/getl.ma".

theorem pc3_pr2_fsubst0:
 \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pr2 c1 t1 t) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t2 t)))))))))))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: (pr2 c1 t1 
t)).(let TMP_1 \def (\lambda (c: C).(\lambda (t0: T).(\lambda (t2: 
T).(\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: 
T).((fsubst0 i u c t0 c2 t3) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u)) \to (pc3 c2 t3 t2))))))))))) in (let TMP_47 \def (\lambda (c: 
C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: (pr0 t2 t3)).(\lambda (i: 
nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t0: T).(\lambda (H1: (fsubst0 
i u c t2 c2 t0)).(let TMP_2 \def (\lambda (c0: C).(\lambda (t4: T).(\forall 
(e: C).((getl i c (CHead e (Bind Abbr) u)) \to (pc3 c0 t4 t3))))) in (let 
TMP_21 \def (\lambda (t4: T).(\lambda (H2: (subst0 i u t2 t4)).(\lambda (e: 
C).(\lambda (H3: (getl i c (CHead e (Bind Abbr) u))).(let TMP_3 \def (pr0 t4 
t3) in (let TMP_4 \def (\lambda (w2: T).(pr0 t4 w2)) in (let TMP_5 \def 
(\lambda (w2: T).(subst0 i u t3 w2)) in (let TMP_6 \def (ex2 T TMP_4 TMP_5) 
in (let TMP_7 \def (pc3 c t4 t3) in (let TMP_9 \def (\lambda (H4: (pr0 t4 
t3)).(let TMP_8 \def (pr2_free c t4 t3 H4) in (pc3_pr2_r c t4 t3 TMP_8))) in 
(let TMP_18 \def (\lambda (H4: (ex2 T (\lambda (w2: T).(pr0 t4 w2)) (\lambda 
(w2: T).(subst0 i u t3 w2)))).(let TMP_10 \def (\lambda (w2: T).(pr0 t4 w2)) 
in (let TMP_11 \def (\lambda (w2: T).(subst0 i u t3 w2)) in (let TMP_12 \def 
(pc3 c t4 t3) in (let TMP_17 \def (\lambda (x: T).(\lambda (H5: (pr0 t4 
x)).(\lambda (H6: (subst0 i u t3 x)).(let TMP_13 \def (pr2_free c t4 x H5) in 
(let TMP_14 \def (pr0_refl t3) in (let TMP_15 \def (pr2_delta c e u i H3 t3 
t3 TMP_14 x H6) in (let TMP_16 \def (pc3_pr2_x c x t3 TMP_15) in (pc3_pr2_u c 
x t4 TMP_13 t3 TMP_16)))))))) in (ex2_ind T TMP_10 TMP_11 TMP_12 TMP_17 
H4)))))) in (let TMP_19 \def (pr0_refl u) in (let TMP_20 \def (pr0_subst0 t2 
t3 H0 u t4 i H2 u TMP_19) in (or_ind TMP_3 TMP_6 TMP_7 TMP_9 TMP_18 
TMP_20)))))))))))))) in (let TMP_23 \def (\lambda (c0: C).(\lambda (_: 
(csubst0 i u c c0)).(\lambda (e: C).(\lambda (_: (getl i c (CHead e (Bind 
Abbr) u))).(let TMP_22 \def (pr2_free c0 t2 t3 H0) in (pc3_pr2_r c0 t2 t3 
TMP_22)))))) in (let TMP_46 \def (\lambda (t4: T).(\lambda (H2: (subst0 i u 
t2 t4)).(\lambda (c0: C).(\lambda (H3: (csubst0 i u c c0)).(\lambda (e: 
C).(\lambda (H4: (getl i c (CHead e (Bind Abbr) u))).(let TMP_24 \def (pr0 t4 
t3) in (let TMP_25 \def (\lambda (w2: T).(pr0 t4 w2)) in (let TMP_26 \def 
(\lambda (w2: T).(subst0 i u t3 w2)) in (let TMP_27 \def (ex2 T TMP_25 
TMP_26) in (let TMP_28 \def (pc3 c0 t4 t3) in (let TMP_30 \def (\lambda (H5: 
(pr0 t4 t3)).(let TMP_29 \def (pr2_free c0 t4 t3 H5) in (pc3_pr2_r c0 t4 t3 
TMP_29))) in (let TMP_43 \def (\lambda (H5: (ex2 T (\lambda (w2: T).(pr0 t4 
w2)) (\lambda (w2: T).(subst0 i u t3 w2)))).(let TMP_31 \def (\lambda (w2: 
T).(pr0 t4 w2)) in (let TMP_32 \def (\lambda (w2: T).(subst0 i u t3 w2)) in 
(let TMP_33 \def (pc3 c0 t4 t3) in (let TMP_42 \def (\lambda (x: T).(\lambda 
(H6: (pr0 t4 x)).(\lambda (H7: (subst0 i u t3 x)).(let TMP_34 \def (pr2_free 
c0 t4 x H6) in (let TMP_35 \def (le_n i) in (let TMP_36 \def (Bind Abbr) in 
(let TMP_37 \def (CHead e TMP_36 u) in (let TMP_38 \def (csubst0_getl_ge i i 
TMP_35 c c0 u H3 TMP_37 H4) in (let TMP_39 \def (pr0_refl t3) in (let TMP_40 
\def (pr2_delta c0 e u i TMP_38 t3 t3 TMP_39 x H7) in (let TMP_41 \def 
(pc3_pr2_x c0 x t3 TMP_40) in (pc3_pr2_u c0 x t4 TMP_34 t3 TMP_41)))))))))))) 
in (ex2_ind T TMP_31 TMP_32 TMP_33 TMP_42 H5)))))) in (let TMP_44 \def 
(pr0_refl u) in (let TMP_45 \def (pr0_subst0 t2 t3 H0 u t4 i H2 u TMP_44) in 
(or_ind TMP_24 TMP_27 TMP_28 TMP_30 TMP_43 TMP_45)))))))))))))))) in 
(fsubst0_ind i u c t2 TMP_2 TMP_21 TMP_23 TMP_46 c2 t0 H1)))))))))))))) in 
(let TMP_549 \def (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t2: 
T).(\lambda (t3: T).(\lambda (H1: (pr0 t2 t3)).(\lambda (t0: T).(\lambda (H2: 
(subst0 i u t3 t0)).(\lambda (i0: nat).(\lambda (u0: T).(\lambda (c2: 
C).(\lambda (t4: T).(\lambda (H3: (fsubst0 i0 u0 c t2 c2 t4)).(let TMP_48 
\def (\lambda (c0: C).(\lambda (t5: T).(\forall (e: C).((getl i0 c (CHead e 
(Bind Abbr) u0)) \to (pc3 c0 t5 t0))))) in (let TMP_55 \def (\lambda (t5: 
T).(\lambda (H4: (subst0 i0 u0 t2 t5)).(\lambda (e: C).(\lambda (H5: (getl i0 
c (CHead e (Bind Abbr) u0))).(let TMP_49 \def (pr0_refl t2) in (let TMP_50 
\def (pr2_delta c e u0 i0 H5 t2 t2 TMP_49 t5 H4) in (let TMP_51 \def 
(pc3_pr2_r c t2 t5 TMP_50) in (let TMP_52 \def (pc3_s c t5 t2 TMP_51) in (let 
TMP_53 \def (pr2_delta c d u i H0 t2 t3 H1 t0 H2) in (let TMP_54 \def 
(pc3_pr2_r c t2 t0 TMP_53) in (pc3_t t2 c t5 TMP_52 t0 TMP_54))))))))))) in 
(let TMP_284 \def (\lambda (c0: C).(\lambda (H4: (csubst0 i0 u0 c 
c0)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) u0))).(let 
TMP_56 \def (pc3 c0 t2 t0) in (let TMP_278 \def (\lambda (H6: (lt i i0)).(let 
TMP_57 \def (Bind Abbr) in (let TMP_58 \def (CHead d TMP_57 u) in (let H7 
\def (csubst0_getl_lt i0 i H6 c c0 u0 H4 TMP_58 H0) in (let TMP_59 \def (Bind 
Abbr) in (let TMP_60 \def (CHead d TMP_59 u) in (let TMP_61 \def (getl i c0 
TMP_60) in (let TMP_66 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_62 \def (Bind Abbr) in (let TMP_63 \def (CHead d 
TMP_62 u) in (let TMP_64 \def (Bind b) in (let TMP_65 \def (CHead e0 TMP_64 
u1) in (eq C TMP_63 TMP_65))))))))) in (let TMP_69 \def (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(let TMP_67 \def (Bind b) 
in (let TMP_68 \def (CHead e0 TMP_67 w) in (getl i c0 TMP_68))))))) in (let 
TMP_72 \def (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: 
T).(let TMP_70 \def (S i) in (let TMP_71 \def (minus i0 TMP_70) in (subst0 
TMP_71 u0 u1 w))))))) in (let TMP_73 \def (ex3_4 B C T T TMP_66 TMP_69 
TMP_72) in (let TMP_78 \def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(let TMP_74 \def (Bind Abbr) in (let TMP_75 \def (CHead d 
TMP_74 u) in (let TMP_76 \def (Bind b) in (let TMP_77 \def (CHead e1 TMP_76 
u1) in (eq C TMP_75 TMP_77))))))))) in (let TMP_81 \def (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_79 \def (Bind 
b) in (let TMP_80 \def (CHead e2 TMP_79 u1) in (getl i c0 TMP_80))))))) in 
(let TMP_84 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(let TMP_82 \def (S i) in (let TMP_83 \def (minus i0 TMP_82) in 
(csubst0 TMP_83 u0 e1 e2))))))) in (let TMP_85 \def (ex3_4 B C C T TMP_78 
TMP_81 TMP_84) in (let TMP_90 \def (\lambda (b: B).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_86 \def (Bind Abbr) in (let 
TMP_87 \def (CHead d TMP_86 u) in (let TMP_88 \def (Bind b) in (let TMP_89 
\def (CHead e1 TMP_88 u1) in (eq C TMP_87 TMP_89)))))))))) in (let TMP_93 
\def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(let TMP_91 \def (Bind b) in (let TMP_92 \def (CHead e2 
TMP_91 w) in (getl i c0 TMP_92)))))))) in (let TMP_96 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(let 
TMP_94 \def (S i) in (let TMP_95 \def (minus i0 TMP_94) in (subst0 TMP_95 u0 
u1 w)))))))) in (let TMP_99 \def (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(let TMP_97 \def (S i) in (let TMP_98 
\def (minus i0 TMP_97) in (csubst0 TMP_98 u0 e1 e2)))))))) in (let TMP_100 
\def (ex4_5 B C C T T TMP_90 TMP_93 TMP_96 TMP_99) in (let TMP_101 \def (pc3 
c0 t2 t0) in (let TMP_103 \def (\lambda (H8: (getl i c0 (CHead d (Bind Abbr) 
u))).(let TMP_102 \def (pr2_delta c0 d u i H8 t2 t3 H1 t0 H2) in (pc3_pr2_r 
c0 t2 t0 TMP_102))) in (let TMP_168 \def (\lambda (H8: (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(let TMP_108 \def (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_104 \def (Bind Abbr) in 
(let TMP_105 \def (CHead d TMP_104 u) in (let TMP_106 \def (Bind b) in (let 
TMP_107 \def (CHead e0 TMP_106 u1) in (eq C TMP_105 TMP_107))))))))) in (let 
TMP_111 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(let TMP_109 \def (Bind b) in (let TMP_110 \def (CHead e0 TMP_109 w) in 
(getl i c0 TMP_110))))))) in (let TMP_114 \def (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(let TMP_112 \def (S i) in (let TMP_113 
\def (minus i0 TMP_112) in (subst0 TMP_113 u0 u1 w))))))) in (let TMP_115 
\def (pc3 c0 t2 t0) in (let TMP_167 \def (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) 
u) (CHead x1 (Bind x0) x2))).(\lambda (H10: (getl i c0 (CHead x1 (Bind x0) 
x3))).(\lambda (H11: (subst0 (minus i0 (S i)) u0 x2 x3)).(let TMP_116 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ _) 
\Rightarrow c3])) in (let TMP_117 \def (Bind Abbr) in (let TMP_118 \def 
(CHead d TMP_117 u) in (let TMP_119 \def (Bind x0) in (let TMP_120 \def 
(CHead x1 TMP_119 x2) in (let H12 \def (f_equal C C TMP_116 TMP_118 TMP_120 
H9) in (let TMP_121 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) in (let TMP_122 \def (Bind 
Abbr) in (let TMP_123 \def (CHead d TMP_122 u) in (let TMP_124 \def (Bind x0) 
in (let TMP_125 \def (CHead x1 TMP_124 x2) in (let H13 \def (f_equal C B 
TMP_121 TMP_123 TMP_125 H9) in (let TMP_126 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u | (CHead _ _ t5) \Rightarrow t5])) in (let 
TMP_127 \def (Bind Abbr) in (let TMP_128 \def (CHead d TMP_127 u) in (let 
TMP_129 \def (Bind x0) in (let TMP_130 \def (CHead x1 TMP_129 x2) in (let H14 
\def (f_equal C T TMP_126 TMP_128 TMP_130 H9) in (let TMP_165 \def (\lambda 
(H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let TMP_133 \def (\lambda 
(t5: T).(let TMP_131 \def (S i) in (let TMP_132 \def (minus i0 TMP_131) in 
(subst0 TMP_132 u0 t5 x3)))) in (let H17 \def (eq_ind_r T x2 TMP_133 H11 u 
H14) in (let TMP_136 \def (\lambda (c3: C).(let TMP_134 \def (Bind x0) in 
(let TMP_135 \def (CHead c3 TMP_134 x3) in (getl i c0 TMP_135)))) in (let H18 
\def (eq_ind_r C x1 TMP_136 H10 d H16) in (let TMP_139 \def (\lambda (b: 
B).(let TMP_137 \def (Bind b) in (let TMP_138 \def (CHead d TMP_137 x3) in 
(getl i c0 TMP_138)))) in (let H19 \def (eq_ind_r B x0 TMP_139 H18 Abbr H15) 
in (let TMP_140 \def (\lambda (t5: T).(subst0 i x3 t3 t5)) in (let TMP_145 
\def (\lambda (t5: T).(let TMP_141 \def (S i) in (let TMP_142 \def (minus i0 
TMP_141) in (let TMP_143 \def (plus TMP_142 i) in (let TMP_144 \def (S 
TMP_143) in (subst0 TMP_144 u0 t0 t5)))))) in (let TMP_146 \def (pc3 c0 t2 
t0) in (let TMP_161 \def (\lambda (x: T).(\lambda (H20: (subst0 i x3 t3 
x)).(\lambda (H21: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
TMP_147 \def (S i) in (let TMP_148 \def (minus i0 TMP_147) in (let TMP_149 
\def (plus TMP_148 i) in (let TMP_150 \def (S TMP_149) in (let TMP_151 \def 
(\lambda (n: nat).(subst0 n u0 t0 x)) in (let TMP_152 \def (lt_plus_minus_r i 
i0 H6) in (let H22 \def (eq_ind_r nat TMP_150 TMP_151 H21 i0 TMP_152) in (let 
TMP_153 \def (pr2_delta c0 d x3 i H19 t2 t3 H1 x H20) in (let TMP_154 \def 
(le_n i0) in (let TMP_155 \def (Bind Abbr) in (let TMP_156 \def (CHead e 
TMP_155 u0) in (let TMP_157 \def (csubst0_getl_ge i0 i0 TMP_154 c c0 u0 H4 
TMP_156 H5) in (let TMP_158 \def (pr0_refl t0) in (let TMP_159 \def 
(pr2_delta c0 e u0 i0 TMP_157 t0 t0 TMP_158 x H22) in (let TMP_160 \def 
(pc3_pr2_x c0 x t0 TMP_159) in (pc3_pr2_u c0 x t2 TMP_153 t0 
TMP_160))))))))))))))))))) in (let TMP_162 \def (S i) in (let TMP_163 \def 
(minus i0 TMP_162) in (let TMP_164 \def (subst0_subst0_back t3 t0 u i H2 x3 
u0 TMP_163 H17) in (ex2_ind T TMP_140 TMP_145 TMP_146 TMP_161 
TMP_164)))))))))))))))) in (let TMP_166 \def (TMP_165 H13) in (TMP_166 
H12)))))))))))))))))))))))))))) in (ex3_4_ind B C T T TMP_108 TMP_111 TMP_114 
TMP_115 TMP_167 H8))))))) in (let TMP_209 \def (\lambda (H8: (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(let TMP_173 \def (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(let TMP_169 \def (Bind 
Abbr) in (let TMP_170 \def (CHead d TMP_169 u) in (let TMP_171 \def (Bind b) 
in (let TMP_172 \def (CHead e1 TMP_171 u1) in (eq C TMP_170 TMP_172))))))))) 
in (let TMP_176 \def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u1: T).(let TMP_174 \def (Bind b) in (let TMP_175 \def (CHead e2 
TMP_174 u1) in (getl i c0 TMP_175))))))) in (let TMP_179 \def (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(let TMP_177 \def (S i) 
in (let TMP_178 \def (minus i0 TMP_177) in (csubst0 TMP_178 u0 e1 e2))))))) 
in (let TMP_180 \def (pc3 c0 t2 t0) in (let TMP_208 \def (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H9: (eq C 
(CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 
(CHead x2 (Bind x0) x3))).(\lambda (H11: (csubst0 (minus i0 (S i)) u0 x1 
x2)).(let TMP_181 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_182 \def (Bind Abbr) in (let 
TMP_183 \def (CHead d TMP_182 u) in (let TMP_184 \def (Bind x0) in (let 
TMP_185 \def (CHead x1 TMP_184 x3) in (let H12 \def (f_equal C C TMP_181 
TMP_183 TMP_185 H9) in (let TMP_186 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in (let TMP_187 \def (Bind 
Abbr) in (let TMP_188 \def (CHead d TMP_187 u) in (let TMP_189 \def (Bind x0) 
in (let TMP_190 \def (CHead x1 TMP_189 x3) in (let H13 \def (f_equal C B 
TMP_186 TMP_188 TMP_190 H9) in (let TMP_191 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u | (CHead _ _ t5) \Rightarrow t5])) in (let 
TMP_192 \def (Bind Abbr) in (let TMP_193 \def (CHead d TMP_192 u) in (let 
TMP_194 \def (Bind x0) in (let TMP_195 \def (CHead x1 TMP_194 x3) in (let H14 
\def (f_equal C T TMP_191 TMP_193 TMP_195 H9) in (let TMP_206 \def (\lambda 
(H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let TMP_198 \def (\lambda 
(t5: T).(let TMP_196 \def (Bind x0) in (let TMP_197 \def (CHead x2 TMP_196 
t5) in (getl i c0 TMP_197)))) in (let H17 \def (eq_ind_r T x3 TMP_198 H10 u 
H14) in (let TMP_201 \def (\lambda (c3: C).(let TMP_199 \def (S i) in (let 
TMP_200 \def (minus i0 TMP_199) in (csubst0 TMP_200 u0 c3 x2)))) in (let H18 
\def (eq_ind_r C x1 TMP_201 H11 d H16) in (let TMP_204 \def (\lambda (b: 
B).(let TMP_202 \def (Bind b) in (let TMP_203 \def (CHead x2 TMP_202 u) in 
(getl i c0 TMP_203)))) in (let H19 \def (eq_ind_r B x0 TMP_204 H17 Abbr H15) 
in (let TMP_205 \def (pr2_delta c0 x2 u i H19 t2 t3 H1 t0 H2) in (pc3_pr2_r 
c0 t2 t0 TMP_205)))))))))) in (let TMP_207 \def (TMP_206 H13) in (TMP_207 
H12)))))))))))))))))))))))))))) in (ex3_4_ind B C C T TMP_173 TMP_176 TMP_179 
TMP_180 TMP_208 H8))))))) in (let TMP_277 \def (\lambda (H8: (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))))).(let TMP_214 \def (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let 
TMP_210 \def (Bind Abbr) in (let TMP_211 \def (CHead d TMP_210 u) in (let 
TMP_212 \def (Bind b) in (let TMP_213 \def (CHead e1 TMP_212 u1) in (eq C 
TMP_211 TMP_213)))))))))) in (let TMP_217 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(let TMP_215 \def (Bind 
b) in (let TMP_216 \def (CHead e2 TMP_215 w) in (getl i c0 TMP_216)))))))) in 
(let TMP_220 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(let TMP_218 \def (S i) in (let TMP_219 \def (minus 
i0 TMP_218) in (subst0 TMP_219 u0 u1 w)))))))) in (let TMP_223 \def (\lambda 
(_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let 
TMP_221 \def (S i) in (let TMP_222 \def (minus i0 TMP_221) in (csubst0 
TMP_222 u0 e1 e2)))))))) in (let TMP_224 \def (pc3 c0 t2 t0) in (let TMP_276 
\def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) x4))).(\lambda 
(H11: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H12: (csubst0 (minus i0 
(S i)) u0 x1 x2)).(let TMP_225 \def (\lambda (e0: C).(match e0 with [(CSort 
_) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_226 \def 
(Bind Abbr) in (let TMP_227 \def (CHead d TMP_226 u) in (let TMP_228 \def 
(Bind x0) in (let TMP_229 \def (CHead x1 TMP_228 x3) in (let H13 \def 
(f_equal C C TMP_225 TMP_227 TMP_229 H9) in (let TMP_230 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_231 \def (Bind Abbr) in (let TMP_232 \def (CHead d TMP_231 u) in 
(let TMP_233 \def (Bind x0) in (let TMP_234 \def (CHead x1 TMP_233 x3) in 
(let H14 \def (f_equal C B TMP_230 TMP_232 TMP_234 H9) in (let TMP_235 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | (CHead _ _ t5) 
\Rightarrow t5])) in (let TMP_236 \def (Bind Abbr) in (let TMP_237 \def 
(CHead d TMP_236 u) in (let TMP_238 \def (Bind x0) in (let TMP_239 \def 
(CHead x1 TMP_238 x3) in (let H15 \def (f_equal C T TMP_235 TMP_237 TMP_239 
H9) in (let TMP_274 \def (\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C 
d x1)).(let TMP_242 \def (\lambda (t5: T).(let TMP_240 \def (S i) in (let 
TMP_241 \def (minus i0 TMP_240) in (subst0 TMP_241 u0 t5 x4)))) in (let H18 
\def (eq_ind_r T x3 TMP_242 H11 u H15) in (let TMP_245 \def (\lambda (c3: 
C).(let TMP_243 \def (S i) in (let TMP_244 \def (minus i0 TMP_243) in 
(csubst0 TMP_244 u0 c3 x2)))) in (let H19 \def (eq_ind_r C x1 TMP_245 H12 d 
H17) in (let TMP_248 \def (\lambda (b: B).(let TMP_246 \def (Bind b) in (let 
TMP_247 \def (CHead x2 TMP_246 x4) in (getl i c0 TMP_247)))) in (let H20 \def 
(eq_ind_r B x0 TMP_248 H10 Abbr H16) in (let TMP_249 \def (\lambda (t5: 
T).(subst0 i x4 t3 t5)) in (let TMP_254 \def (\lambda (t5: T).(let TMP_250 
\def (S i) in (let TMP_251 \def (minus i0 TMP_250) in (let TMP_252 \def (plus 
TMP_251 i) in (let TMP_253 \def (S TMP_252) in (subst0 TMP_253 u0 t0 t5)))))) 
in (let TMP_255 \def (pc3 c0 t2 t0) in (let TMP_270 \def (\lambda (x: 
T).(\lambda (H21: (subst0 i x4 t3 x)).(\lambda (H22: (subst0 (S (plus (minus 
i0 (S i)) i)) u0 t0 x)).(let TMP_256 \def (S i) in (let TMP_257 \def (minus 
i0 TMP_256) in (let TMP_258 \def (plus TMP_257 i) in (let TMP_259 \def (S 
TMP_258) in (let TMP_260 \def (\lambda (n: nat).(subst0 n u0 t0 x)) in (let 
TMP_261 \def (lt_plus_minus_r i i0 H6) in (let H23 \def (eq_ind_r nat TMP_259 
TMP_260 H22 i0 TMP_261) in (let TMP_262 \def (pr2_delta c0 x2 x4 i H20 t2 t3 
H1 x H21) in (let TMP_263 \def (le_n i0) in (let TMP_264 \def (Bind Abbr) in 
(let TMP_265 \def (CHead e TMP_264 u0) in (let TMP_266 \def (csubst0_getl_ge 
i0 i0 TMP_263 c c0 u0 H4 TMP_265 H5) in (let TMP_267 \def (pr0_refl t0) in 
(let TMP_268 \def (pr2_delta c0 e u0 i0 TMP_266 t0 t0 TMP_267 x H23) in (let 
TMP_269 \def (pc3_pr2_x c0 x t0 TMP_268) in (pc3_pr2_u c0 x t2 TMP_262 t0 
TMP_269))))))))))))))))))) in (let TMP_271 \def (S i) in (let TMP_272 \def 
(minus i0 TMP_271) in (let TMP_273 \def (subst0_subst0_back t3 t0 u i H2 x4 
u0 TMP_272 H18) in (ex2_ind T TMP_249 TMP_254 TMP_255 TMP_270 
TMP_273)))))))))))))))) in (let TMP_275 \def (TMP_274 H14) in (TMP_275 
H13)))))))))))))))))))))))))))))) in (ex4_5_ind B C C T T TMP_214 TMP_217 
TMP_220 TMP_223 TMP_224 TMP_276 H8)))))))) in (or4_ind TMP_61 TMP_73 TMP_85 
TMP_100 TMP_101 TMP_103 TMP_168 TMP_209 TMP_277 H7)))))))))))))))))))))))))) 
in (let TMP_283 \def (\lambda (H6: (le i0 i)).(let TMP_279 \def (Bind Abbr) 
in (let TMP_280 \def (CHead d TMP_279 u) in (let TMP_281 \def 
(csubst0_getl_ge i0 i H6 c c0 u0 H4 TMP_280 H0) in (let TMP_282 \def 
(pr2_delta c0 d u i TMP_281 t2 t3 H1 t0 H2) in (pc3_pr2_r c0 t2 t0 
TMP_282)))))) in (lt_le_e i i0 TMP_56 TMP_278 TMP_283)))))))) in (let TMP_548 
\def (\lambda (t5: T).(\lambda (H4: (subst0 i0 u0 t2 t5)).(\lambda (c0: 
C).(\lambda (H5: (csubst0 i0 u0 c c0)).(\lambda (e: C).(\lambda (H6: (getl i0 
c (CHead e (Bind Abbr) u0))).(let TMP_285 \def (pc3 c0 t5 t0) in (let TMP_535 
\def (\lambda (H7: (lt i i0)).(let TMP_286 \def (Bind Abbr) in (let TMP_287 
\def (CHead d TMP_286 u) in (let H8 \def (csubst0_getl_lt i0 i H7 c c0 u0 H5 
TMP_287 H0) in (let TMP_288 \def (Bind Abbr) in (let TMP_289 \def (CHead d 
TMP_288 u) in (let TMP_290 \def (getl i c0 TMP_289) in (let TMP_295 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(let 
TMP_291 \def (Bind Abbr) in (let TMP_292 \def (CHead d TMP_291 u) in (let 
TMP_293 \def (Bind b) in (let TMP_294 \def (CHead e0 TMP_293 u1) in (eq C 
TMP_292 TMP_294))))))))) in (let TMP_298 \def (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(let TMP_296 \def (Bind b) in (let TMP_297 
\def (CHead e0 TMP_296 w) in (getl i c0 TMP_297))))))) in (let TMP_301 \def 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(let TMP_299 
\def (S i) in (let TMP_300 \def (minus i0 TMP_299) in (subst0 TMP_300 u0 u1 
w))))))) in (let TMP_302 \def (ex3_4 B C T T TMP_295 TMP_298 TMP_301) in (let 
TMP_307 \def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(let TMP_303 \def (Bind Abbr) in (let TMP_304 \def (CHead d TMP_303 u) in 
(let TMP_305 \def (Bind b) in (let TMP_306 \def (CHead e1 TMP_305 u1) in (eq 
C TMP_304 TMP_306))))))))) in (let TMP_310 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_308 \def (Bind b) in (let 
TMP_309 \def (CHead e2 TMP_308 u1) in (getl i c0 TMP_309))))))) in (let 
TMP_313 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(let TMP_311 \def (S i) in (let TMP_312 \def (minus i0 TMP_311) in 
(csubst0 TMP_312 u0 e1 e2))))))) in (let TMP_314 \def (ex3_4 B C C T TMP_307 
TMP_310 TMP_313) in (let TMP_319 \def (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_315 \def (Bind 
Abbr) in (let TMP_316 \def (CHead d TMP_315 u) in (let TMP_317 \def (Bind b) 
in (let TMP_318 \def (CHead e1 TMP_317 u1) in (eq C TMP_316 TMP_318)))))))))) 
in (let TMP_322 \def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(let TMP_320 \def (Bind b) in (let TMP_321 
\def (CHead e2 TMP_320 w) in (getl i c0 TMP_321)))))))) in (let TMP_325 \def 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: 
T).(let TMP_323 \def (S i) in (let TMP_324 \def (minus i0 TMP_323) in (subst0 
TMP_324 u0 u1 w)))))))) in (let TMP_328 \def (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let TMP_326 \def (S i) 
in (let TMP_327 \def (minus i0 TMP_326) in (csubst0 TMP_327 u0 e1 e2)))))))) 
in (let TMP_329 \def (ex4_5 B C C T T TMP_319 TMP_322 TMP_325 TMP_328) in 
(let TMP_330 \def (pc3 c0 t5 t0) in (let TMP_339 \def (\lambda (H9: (getl i 
c0 (CHead d (Bind Abbr) u))).(let TMP_331 \def (le_n i0) in (let TMP_332 \def 
(Bind Abbr) in (let TMP_333 \def (CHead e TMP_332 u0) in (let TMP_334 \def 
(csubst0_getl_ge i0 i0 TMP_331 c c0 u0 H5 TMP_333 H6) in (let TMP_335 \def 
(pr0_refl t2) in (let TMP_336 \def (pr2_delta c0 e u0 i0 TMP_334 t2 t2 
TMP_335 t5 H4) in (let TMP_337 \def (pr2_delta c0 d u i H9 t2 t3 H1 t0 H2) in 
(let TMP_338 \def (pc3_pr2_r c0 t2 t0 TMP_337) in (pc3_pr2_u2 c0 t2 t5 
TMP_336 t0 TMP_338)))))))))) in (let TMP_411 \def (\lambda (H9: (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(let TMP_344 \def (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_340 \def (Bind Abbr) in 
(let TMP_341 \def (CHead d TMP_340 u) in (let TMP_342 \def (Bind b) in (let 
TMP_343 \def (CHead e0 TMP_342 u1) in (eq C TMP_341 TMP_343))))))))) in (let 
TMP_347 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(let TMP_345 \def (Bind b) in (let TMP_346 \def (CHead e0 TMP_345 w) in 
(getl i c0 TMP_346))))))) in (let TMP_350 \def (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(let TMP_348 \def (S i) in (let TMP_349 
\def (minus i0 TMP_348) in (subst0 TMP_349 u0 u1 w))))))) in (let TMP_351 
\def (pc3 c0 t5 t0) in (let TMP_410 \def (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x2))).(\lambda (H11: (getl i c0 (CHead x1 (Bind 
x0) x3))).(\lambda (H12: (subst0 (minus i0 (S i)) u0 x2 x3)).(let TMP_352 
\def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ 
_) \Rightarrow c3])) in (let TMP_353 \def (Bind Abbr) in (let TMP_354 \def 
(CHead d TMP_353 u) in (let TMP_355 \def (Bind x0) in (let TMP_356 \def 
(CHead x1 TMP_355 x2) in (let H13 \def (f_equal C C TMP_352 TMP_354 TMP_356 
H10) in (let TMP_357 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) in (let TMP_358 \def (Bind 
Abbr) in (let TMP_359 \def (CHead d TMP_358 u) in (let TMP_360 \def (Bind x0) 
in (let TMP_361 \def (CHead x1 TMP_360 x2) in (let H14 \def (f_equal C B 
TMP_357 TMP_359 TMP_361 H10) in (let TMP_362 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u | (CHead _ _ t6) \Rightarrow t6])) in (let 
TMP_363 \def (Bind Abbr) in (let TMP_364 \def (CHead d TMP_363 u) in (let 
TMP_365 \def (Bind x0) in (let TMP_366 \def (CHead x1 TMP_365 x2) in (let H15 
\def (f_equal C T TMP_362 TMP_364 TMP_366 H10) in (let TMP_408 \def (\lambda 
(H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let TMP_369 \def (\lambda 
(t6: T).(let TMP_367 \def (S i) in (let TMP_368 \def (minus i0 TMP_367) in 
(subst0 TMP_368 u0 t6 x3)))) in (let H18 \def (eq_ind_r T x2 TMP_369 H12 u 
H15) in (let TMP_372 \def (\lambda (c3: C).(let TMP_370 \def (Bind x0) in 
(let TMP_371 \def (CHead c3 TMP_370 x3) in (getl i c0 TMP_371)))) in (let H19 
\def (eq_ind_r C x1 TMP_372 H11 d H17) in (let TMP_375 \def (\lambda (b: 
B).(let TMP_373 \def (Bind b) in (let TMP_374 \def (CHead d TMP_373 x3) in 
(getl i c0 TMP_374)))) in (let H20 \def (eq_ind_r B x0 TMP_375 H19 Abbr H16) 
in (let TMP_376 \def (\lambda (t6: T).(subst0 i x3 t3 t6)) in (let TMP_381 
\def (\lambda (t6: T).(let TMP_377 \def (S i) in (let TMP_378 \def (minus i0 
TMP_377) in (let TMP_379 \def (plus TMP_378 i) in (let TMP_380 \def (S 
TMP_379) in (subst0 TMP_380 u0 t0 t6)))))) in (let TMP_382 \def (pc3 c0 t5 
t0) in (let TMP_404 \def (\lambda (x: T).(\lambda (H21: (subst0 i x3 t3 
x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
TMP_383 \def (S i) in (let TMP_384 \def (minus i0 TMP_383) in (let TMP_385 
\def (plus TMP_384 i) in (let TMP_386 \def (S TMP_385) in (let TMP_387 \def 
(\lambda (n: nat).(subst0 n u0 t0 x)) in (let TMP_388 \def (lt_plus_minus_r i 
i0 H7) in (let H23 \def (eq_ind_r nat TMP_386 TMP_387 H22 i0 TMP_388) in (let 
TMP_389 \def (le_n i0) in (let TMP_390 \def (Bind Abbr) in (let TMP_391 \def 
(CHead e TMP_390 u0) in (let TMP_392 \def (csubst0_getl_ge i0 i0 TMP_389 c c0 
u0 H5 TMP_391 H6) in (let TMP_393 \def (pr0_refl t2) in (let TMP_394 \def 
(pr2_delta c0 e u0 i0 TMP_392 t2 t2 TMP_393 t5 H4) in (let TMP_395 \def 
(pr2_delta c0 d x3 i H20 t2 t3 H1 x H21) in (let TMP_396 \def (le_n i0) in 
(let TMP_397 \def (Bind Abbr) in (let TMP_398 \def (CHead e TMP_397 u0) in 
(let TMP_399 \def (csubst0_getl_ge i0 i0 TMP_396 c c0 u0 H5 TMP_398 H6) in 
(let TMP_400 \def (pr0_refl t0) in (let TMP_401 \def (pr2_delta c0 e u0 i0 
TMP_399 t0 t0 TMP_400 x H23) in (let TMP_402 \def (pc3_pr2_x c0 x t0 TMP_401) 
in (let TMP_403 \def (pc3_pr2_u c0 x t2 TMP_395 t0 TMP_402) in (pc3_pr2_u2 c0 
t2 t5 TMP_394 t0 TMP_403)))))))))))))))))))))))))) in (let TMP_405 \def (S i) 
in (let TMP_406 \def (minus i0 TMP_405) in (let TMP_407 \def 
(subst0_subst0_back t3 t0 u i H2 x3 u0 TMP_406 H18) in (ex2_ind T TMP_376 
TMP_381 TMP_382 TMP_404 TMP_407)))))))))))))))) in (let TMP_409 \def (TMP_408 
H14) in (TMP_409 H13)))))))))))))))))))))))))))) in (ex3_4_ind B C T T 
TMP_344 TMP_347 TMP_350 TMP_351 TMP_410 H9))))))) in (let TMP_459 \def 
(\lambda (H9: (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(let TMP_416 
\def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(let 
TMP_412 \def (Bind Abbr) in (let TMP_413 \def (CHead d TMP_412 u) in (let 
TMP_414 \def (Bind b) in (let TMP_415 \def (CHead e1 TMP_414 u1) in (eq C 
TMP_413 TMP_415))))))))) in (let TMP_419 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_417 \def (Bind b) in (let 
TMP_418 \def (CHead e2 TMP_417 u1) in (getl i c0 TMP_418))))))) in (let 
TMP_422 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(let TMP_420 \def (S i) in (let TMP_421 \def (minus i0 TMP_420) in 
(csubst0 TMP_421 u0 e1 e2))))))) in (let TMP_423 \def (pc3 c0 t5 t0) in (let 
TMP_458 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) x3))).(\lambda (H12: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let TMP_424 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) 
in (let TMP_425 \def (Bind Abbr) in (let TMP_426 \def (CHead d TMP_425 u) in 
(let TMP_427 \def (Bind x0) in (let TMP_428 \def (CHead x1 TMP_427 x3) in 
(let H13 \def (f_equal C C TMP_424 TMP_426 TMP_428 H10) in (let TMP_429 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) in (let TMP_430 \def (Bind Abbr) in (let TMP_431 \def (CHead d 
TMP_430 u) in (let TMP_432 \def (Bind x0) in (let TMP_433 \def (CHead x1 
TMP_432 x3) in (let H14 \def (f_equal C B TMP_429 TMP_431 TMP_433 H10) in 
(let TMP_434 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | 
(CHead _ _ t6) \Rightarrow t6])) in (let TMP_435 \def (Bind Abbr) in (let 
TMP_436 \def (CHead d TMP_435 u) in (let TMP_437 \def (Bind x0) in (let 
TMP_438 \def (CHead x1 TMP_437 x3) in (let H15 \def (f_equal C T TMP_434 
TMP_436 TMP_438 H10) in (let TMP_456 \def (\lambda (H16: (eq B Abbr 
x0)).(\lambda (H17: (eq C d x1)).(let TMP_441 \def (\lambda (t6: T).(let 
TMP_439 \def (Bind x0) in (let TMP_440 \def (CHead x2 TMP_439 t6) in (getl i 
c0 TMP_440)))) in (let H18 \def (eq_ind_r T x3 TMP_441 H11 u H15) in (let 
TMP_444 \def (\lambda (c3: C).(let TMP_442 \def (S i) in (let TMP_443 \def 
(minus i0 TMP_442) in (csubst0 TMP_443 u0 c3 x2)))) in (let H19 \def 
(eq_ind_r C x1 TMP_444 H12 d H17) in (let TMP_447 \def (\lambda (b: B).(let 
TMP_445 \def (Bind b) in (let TMP_446 \def (CHead x2 TMP_445 u) in (getl i c0 
TMP_446)))) in (let H20 \def (eq_ind_r B x0 TMP_447 H18 Abbr H16) in (let 
TMP_448 \def (le_n i0) in (let TMP_449 \def (Bind Abbr) in (let TMP_450 \def 
(CHead e TMP_449 u0) in (let TMP_451 \def (csubst0_getl_ge i0 i0 TMP_448 c c0 
u0 H5 TMP_450 H6) in (let TMP_452 \def (pr0_refl t2) in (let TMP_453 \def 
(pr2_delta c0 e u0 i0 TMP_451 t2 t2 TMP_452 t5 H4) in (let TMP_454 \def 
(pr2_delta c0 x2 u i H20 t2 t3 H1 t0 H2) in (let TMP_455 \def (pc3_pr2_r c0 
t2 t0 TMP_454) in (pc3_pr2_u2 c0 t2 t5 TMP_453 t0 TMP_455))))))))))))))))) in 
(let TMP_457 \def (TMP_456 H14) in (TMP_457 H13)))))))))))))))))))))))))))) 
in (ex3_4_ind B C C T TMP_416 TMP_419 TMP_422 TMP_423 TMP_458 H9))))))) in 
(let TMP_534 \def (\lambda (H9: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i0 (S i)) u0 e1 e2)))))))).(let TMP_464 \def (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_460 \def 
(Bind Abbr) in (let TMP_461 \def (CHead d TMP_460 u) in (let TMP_462 \def 
(Bind b) in (let TMP_463 \def (CHead e1 TMP_462 u1) in (eq C TMP_461 
TMP_463)))))))))) in (let TMP_467 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(let TMP_465 \def (Bind 
b) in (let TMP_466 \def (CHead e2 TMP_465 w) in (getl i c0 TMP_466)))))))) in 
(let TMP_470 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(let TMP_468 \def (S i) in (let TMP_469 \def (minus 
i0 TMP_468) in (subst0 TMP_469 u0 u1 w)))))))) in (let TMP_473 \def (\lambda 
(_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let 
TMP_471 \def (S i) in (let TMP_472 \def (minus i0 TMP_471) in (csubst0 
TMP_472 u0 e1 e2)))))))) in (let TMP_474 \def (pc3 c0 t5 t0) in (let TMP_533 
\def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) x4))).(\lambda 
(H12: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H13: (csubst0 (minus i0 
(S i)) u0 x1 x2)).(let TMP_475 \def (\lambda (e0: C).(match e0 with [(CSort 
_) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_476 \def 
(Bind Abbr) in (let TMP_477 \def (CHead d TMP_476 u) in (let TMP_478 \def 
(Bind x0) in (let TMP_479 \def (CHead x1 TMP_478 x3) in (let H14 \def 
(f_equal C C TMP_475 TMP_477 TMP_479 H10) in (let TMP_480 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_481 \def (Bind Abbr) in (let TMP_482 \def (CHead d TMP_481 u) in 
(let TMP_483 \def (Bind x0) in (let TMP_484 \def (CHead x1 TMP_483 x3) in 
(let H15 \def (f_equal C B TMP_480 TMP_482 TMP_484 H10) in (let TMP_485 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | (CHead _ _ t6) 
\Rightarrow t6])) in (let TMP_486 \def (Bind Abbr) in (let TMP_487 \def 
(CHead d TMP_486 u) in (let TMP_488 \def (Bind x0) in (let TMP_489 \def 
(CHead x1 TMP_488 x3) in (let H16 \def (f_equal C T TMP_485 TMP_487 TMP_489 
H10) in (let TMP_531 \def (\lambda (H17: (eq B Abbr x0)).(\lambda (H18: (eq C 
d x1)).(let TMP_492 \def (\lambda (t6: T).(let TMP_490 \def (S i) in (let 
TMP_491 \def (minus i0 TMP_490) in (subst0 TMP_491 u0 t6 x4)))) in (let H19 
\def (eq_ind_r T x3 TMP_492 H12 u H16) in (let TMP_495 \def (\lambda (c3: 
C).(let TMP_493 \def (S i) in (let TMP_494 \def (minus i0 TMP_493) in 
(csubst0 TMP_494 u0 c3 x2)))) in (let H20 \def (eq_ind_r C x1 TMP_495 H13 d 
H18) in (let TMP_498 \def (\lambda (b: B).(let TMP_496 \def (Bind b) in (let 
TMP_497 \def (CHead x2 TMP_496 x4) in (getl i c0 TMP_497)))) in (let H21 \def 
(eq_ind_r B x0 TMP_498 H11 Abbr H17) in (let TMP_499 \def (\lambda (t6: 
T).(subst0 i x4 t3 t6)) in (let TMP_504 \def (\lambda (t6: T).(let TMP_500 
\def (S i) in (let TMP_501 \def (minus i0 TMP_500) in (let TMP_502 \def (plus 
TMP_501 i) in (let TMP_503 \def (S TMP_502) in (subst0 TMP_503 u0 t0 t6)))))) 
in (let TMP_505 \def (pc3 c0 t5 t0) in (let TMP_527 \def (\lambda (x: 
T).(\lambda (H22: (subst0 i x4 t3 x)).(\lambda (H23: (subst0 (S (plus (minus 
i0 (S i)) i)) u0 t0 x)).(let TMP_506 \def (S i) in (let TMP_507 \def (minus 
i0 TMP_506) in (let TMP_508 \def (plus TMP_507 i) in (let TMP_509 \def (S 
TMP_508) in (let TMP_510 \def (\lambda (n: nat).(subst0 n u0 t0 x)) in (let 
TMP_511 \def (lt_plus_minus_r i i0 H7) in (let H24 \def (eq_ind_r nat TMP_509 
TMP_510 H23 i0 TMP_511) in (let TMP_512 \def (le_n i0) in (let TMP_513 \def 
(Bind Abbr) in (let TMP_514 \def (CHead e TMP_513 u0) in (let TMP_515 \def 
(csubst0_getl_ge i0 i0 TMP_512 c c0 u0 H5 TMP_514 H6) in (let TMP_516 \def 
(pr0_refl t2) in (let TMP_517 \def (pr2_delta c0 e u0 i0 TMP_515 t2 t2 
TMP_516 t5 H4) in (let TMP_518 \def (pr2_delta c0 x2 x4 i H21 t2 t3 H1 x H22) 
in (let TMP_519 \def (le_n i0) in (let TMP_520 \def (Bind Abbr) in (let 
TMP_521 \def (CHead e TMP_520 u0) in (let TMP_522 \def (csubst0_getl_ge i0 i0 
TMP_519 c c0 u0 H5 TMP_521 H6) in (let TMP_523 \def (pr0_refl t0) in (let 
TMP_524 \def (pr2_delta c0 e u0 i0 TMP_522 t0 t0 TMP_523 x H24) in (let 
TMP_525 \def (pc3_pr2_x c0 x t0 TMP_524) in (let TMP_526 \def (pc3_pr2_u c0 x 
t2 TMP_518 t0 TMP_525) in (pc3_pr2_u2 c0 t2 t5 TMP_517 t0 
TMP_526)))))))))))))))))))))))))) in (let TMP_528 \def (S i) in (let TMP_529 
\def (minus i0 TMP_528) in (let TMP_530 \def (subst0_subst0_back t3 t0 u i H2 
x4 u0 TMP_529 H19) in (ex2_ind T TMP_499 TMP_504 TMP_505 TMP_527 
TMP_530)))))))))))))))) in (let TMP_532 \def (TMP_531 H15) in (TMP_532 
H14)))))))))))))))))))))))))))))) in (ex4_5_ind B C C T T TMP_464 TMP_467 
TMP_470 TMP_473 TMP_474 TMP_533 H9)))))))) in (or4_ind TMP_290 TMP_302 
TMP_314 TMP_329 TMP_330 TMP_339 TMP_411 TMP_459 TMP_534 
H8)))))))))))))))))))))))))) in (let TMP_547 \def (\lambda (H7: (le i0 
i)).(let TMP_536 \def (le_n i0) in (let TMP_537 \def (Bind Abbr) in (let 
TMP_538 \def (CHead e TMP_537 u0) in (let TMP_539 \def (csubst0_getl_ge i0 i0 
TMP_536 c c0 u0 H5 TMP_538 H6) in (let TMP_540 \def (pr0_refl t2) in (let 
TMP_541 \def (pr2_delta c0 e u0 i0 TMP_539 t2 t2 TMP_540 t5 H4) in (let 
TMP_542 \def (Bind Abbr) in (let TMP_543 \def (CHead d TMP_542 u) in (let 
TMP_544 \def (csubst0_getl_ge i0 i H7 c c0 u0 H5 TMP_543 H0) in (let TMP_545 
\def (pr2_delta c0 d u i TMP_544 t2 t3 H1 t0 H2) in (let TMP_546 \def 
(pc3_pr2_r c0 t2 t0 TMP_545) in (pc3_pr2_u2 c0 t2 t5 TMP_541 t0 
TMP_546))))))))))))) in (lt_le_e i i0 TMP_285 TMP_535 TMP_547)))))))))) in 
(fsubst0_ind i0 u0 c t2 TMP_48 TMP_55 TMP_284 TMP_548 c2 t4 
H3)))))))))))))))))))) in (pr2_ind TMP_1 TMP_47 TMP_549 c1 t1 t H))))))).

theorem pc3_pr2_fsubst0_back:
 \forall (c1: C).(\forall (t: T).(\forall (t1: T).((pr2 c1 t t1) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t t2)))))))))))
\def
 \lambda (c1: C).(\lambda (t: T).(\lambda (t1: T).(\lambda (H: (pr2 c1 t 
t1)).(let TMP_1 \def (\lambda (c: C).(\lambda (t0: T).(\lambda (t2: 
T).(\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: 
T).((fsubst0 i u c t2 c2 t3) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u)) \to (pc3 c2 t0 t3))))))))))) in (let TMP_19 \def (\lambda (c: 
C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: (pr0 t2 t3)).(\lambda (i: 
nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t0: T).(\lambda (H1: (fsubst0 
i u c t3 c2 t0)).(let TMP_2 \def (\lambda (c0: C).(\lambda (t4: T).(\forall 
(e: C).((getl i c (CHead e (Bind Abbr) u)) \to (pc3 c0 t2 t4))))) in (let 
TMP_7 \def (\lambda (t4: T).(\lambda (H2: (subst0 i u t3 t4)).(\lambda (e: 
C).(\lambda (H3: (getl i c (CHead e (Bind Abbr) u))).(let TMP_3 \def 
(pr2_free c t2 t3 H0) in (let TMP_4 \def (pr0_refl t3) in (let TMP_5 \def 
(pr2_delta c e u i H3 t3 t3 TMP_4 t4 H2) in (let TMP_6 \def (pc3_pr2_r c t3 
t4 TMP_5) in (pc3_pr2_u c t3 t2 TMP_3 t4 TMP_6))))))))) in (let TMP_9 \def 
(\lambda (c0: C).(\lambda (_: (csubst0 i u c c0)).(\lambda (e: C).(\lambda 
(_: (getl i c (CHead e (Bind Abbr) u))).(let TMP_8 \def (pr2_free c0 t2 t3 
H0) in (pc3_pr2_r c0 t2 t3 TMP_8)))))) in (let TMP_18 \def (\lambda (t4: 
T).(\lambda (H2: (subst0 i u t3 t4)).(\lambda (c0: C).(\lambda (H3: (csubst0 
i u c c0)).(\lambda (e: C).(\lambda (H4: (getl i c (CHead e (Bind Abbr) 
u))).(let TMP_10 \def (pr2_free c0 t2 t3 H0) in (let TMP_11 \def (le_n i) in 
(let TMP_12 \def (Bind Abbr) in (let TMP_13 \def (CHead e TMP_12 u) in (let 
TMP_14 \def (csubst0_getl_ge i i TMP_11 c c0 u H3 TMP_13 H4) in (let TMP_15 
\def (pr0_refl t3) in (let TMP_16 \def (pr2_delta c0 e u i TMP_14 t3 t3 
TMP_15 t4 H2) in (let TMP_17 \def (pc3_pr2_r c0 t3 t4 TMP_16) in (pc3_pr2_u 
c0 t3 t2 TMP_10 t4 TMP_17))))))))))))))) in (fsubst0_ind i u c t3 TMP_2 TMP_7 
TMP_9 TMP_18 c2 t0 H1)))))))))))))) in (let TMP_529 \def (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H1: 
(pr0 t2 t3)).(\lambda (t0: T).(\lambda (H2: (subst0 i u t3 t0)).(\lambda (i0: 
nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda (t4: T).(\lambda (H3: 
(fsubst0 i0 u0 c t0 c2 t4)).(let TMP_20 \def (\lambda (c0: C).(\lambda (t5: 
T).(\forall (e: C).((getl i0 c (CHead e (Bind Abbr) u0)) \to (pc3 c0 t2 
t5))))) in (let TMP_31 \def (\lambda (t5: T).(\lambda (H4: (subst0 i0 u0 t0 
t5)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) u0))).(let 
TMP_21 \def (pr2_free c t2 t3 H1) in (let TMP_22 \def (pr3_pr2 c t2 t3 
TMP_21) in (let TMP_23 \def (pc3_pr3_r c t2 t3 TMP_22) in (let TMP_24 \def 
(pr0_refl t3) in (let TMP_25 \def (pr2_delta c d u i H0 t3 t3 TMP_24 t0 H2) 
in (let TMP_26 \def (pr0_refl t0) in (let TMP_27 \def (pr2_delta c e u0 i0 H5 
t0 t0 TMP_26 t5 H4) in (let TMP_28 \def (pr3_pr2 c t0 t5 TMP_27) in (let 
TMP_29 \def (pr3_sing c t0 t3 TMP_25 t5 TMP_28) in (let TMP_30 \def 
(pc3_pr3_r c t3 t5 TMP_29) in (pc3_t t3 c t2 TMP_23 t5 TMP_30))))))))))))))) 
in (let TMP_260 \def (\lambda (c0: C).(\lambda (H4: (csubst0 i0 u0 c 
c0)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) u0))).(let 
TMP_32 \def (pc3 c0 t2 t0) in (let TMP_254 \def (\lambda (H6: (lt i i0)).(let 
TMP_33 \def (Bind Abbr) in (let TMP_34 \def (CHead d TMP_33 u) in (let H7 
\def (csubst0_getl_lt i0 i H6 c c0 u0 H4 TMP_34 H0) in (let TMP_35 \def (Bind 
Abbr) in (let TMP_36 \def (CHead d TMP_35 u) in (let TMP_37 \def (getl i c0 
TMP_36) in (let TMP_42 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_38 \def (Bind Abbr) in (let TMP_39 \def (CHead d 
TMP_38 u) in (let TMP_40 \def (Bind b) in (let TMP_41 \def (CHead e0 TMP_40 
u1) in (eq C TMP_39 TMP_41))))))))) in (let TMP_45 \def (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(let TMP_43 \def (Bind b) 
in (let TMP_44 \def (CHead e0 TMP_43 w) in (getl i c0 TMP_44))))))) in (let 
TMP_48 \def (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: 
T).(let TMP_46 \def (S i) in (let TMP_47 \def (minus i0 TMP_46) in (subst0 
TMP_47 u0 u1 w))))))) in (let TMP_49 \def (ex3_4 B C T T TMP_42 TMP_45 
TMP_48) in (let TMP_54 \def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(let TMP_50 \def (Bind Abbr) in (let TMP_51 \def (CHead d 
TMP_50 u) in (let TMP_52 \def (Bind b) in (let TMP_53 \def (CHead e1 TMP_52 
u1) in (eq C TMP_51 TMP_53))))))))) in (let TMP_57 \def (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_55 \def (Bind 
b) in (let TMP_56 \def (CHead e2 TMP_55 u1) in (getl i c0 TMP_56))))))) in 
(let TMP_60 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(let TMP_58 \def (S i) in (let TMP_59 \def (minus i0 TMP_58) in 
(csubst0 TMP_59 u0 e1 e2))))))) in (let TMP_61 \def (ex3_4 B C C T TMP_54 
TMP_57 TMP_60) in (let TMP_66 \def (\lambda (b: B).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_62 \def (Bind Abbr) in (let 
TMP_63 \def (CHead d TMP_62 u) in (let TMP_64 \def (Bind b) in (let TMP_65 
\def (CHead e1 TMP_64 u1) in (eq C TMP_63 TMP_65)))))))))) in (let TMP_69 
\def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(let TMP_67 \def (Bind b) in (let TMP_68 \def (CHead e2 
TMP_67 w) in (getl i c0 TMP_68)))))))) in (let TMP_72 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(let 
TMP_70 \def (S i) in (let TMP_71 \def (minus i0 TMP_70) in (subst0 TMP_71 u0 
u1 w)))))))) in (let TMP_75 \def (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(let TMP_73 \def (S i) in (let TMP_74 
\def (minus i0 TMP_73) in (csubst0 TMP_74 u0 e1 e2)))))))) in (let TMP_76 
\def (ex4_5 B C C T T TMP_66 TMP_69 TMP_72 TMP_75) in (let TMP_77 \def (pc3 
c0 t2 t0) in (let TMP_79 \def (\lambda (H8: (getl i c0 (CHead d (Bind Abbr) 
u))).(let TMP_78 \def (pr2_delta c0 d u i H8 t2 t3 H1 t0 H2) in (pc3_pr2_r c0 
t2 t0 TMP_78))) in (let TMP_144 \def (\lambda (H8: (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(let TMP_84 \def (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_80 \def (Bind Abbr) in (let 
TMP_81 \def (CHead d TMP_80 u) in (let TMP_82 \def (Bind b) in (let TMP_83 
\def (CHead e0 TMP_82 u1) in (eq C TMP_81 TMP_83))))))))) in (let TMP_87 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(let TMP_85 
\def (Bind b) in (let TMP_86 \def (CHead e0 TMP_85 w) in (getl i c0 
TMP_86))))))) in (let TMP_90 \def (\lambda (_: B).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(let TMP_88 \def (S i) in (let TMP_89 \def (minus i0 
TMP_88) in (subst0 TMP_89 u0 u1 w))))))) in (let TMP_91 \def (pc3 c0 t2 t0) 
in (let TMP_143 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x2))).(\lambda (H10: (getl i c0 (CHead x1 (Bind x0) x3))).(\lambda 
(H11: (subst0 (minus i0 (S i)) u0 x2 x3)).(let TMP_92 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) 
in (let TMP_93 \def (Bind Abbr) in (let TMP_94 \def (CHead d TMP_93 u) in 
(let TMP_95 \def (Bind x0) in (let TMP_96 \def (CHead x1 TMP_95 x2) in (let 
H12 \def (f_equal C C TMP_92 TMP_94 TMP_96 H9) in (let TMP_97 \def (\lambda 
(e0: C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) in (let TMP_98 \def (Bind Abbr) in (let TMP_99 \def (CHead d TMP_98 
u) in (let TMP_100 \def (Bind x0) in (let TMP_101 \def (CHead x1 TMP_100 x2) 
in (let H13 \def (f_equal C B TMP_97 TMP_99 TMP_101 H9) in (let TMP_102 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | (CHead _ _ t5) 
\Rightarrow t5])) in (let TMP_103 \def (Bind Abbr) in (let TMP_104 \def 
(CHead d TMP_103 u) in (let TMP_105 \def (Bind x0) in (let TMP_106 \def 
(CHead x1 TMP_105 x2) in (let H14 \def (f_equal C T TMP_102 TMP_104 TMP_106 
H9) in (let TMP_141 \def (\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C 
d x1)).(let TMP_109 \def (\lambda (t5: T).(let TMP_107 \def (S i) in (let 
TMP_108 \def (minus i0 TMP_107) in (subst0 TMP_108 u0 t5 x3)))) in (let H17 
\def (eq_ind_r T x2 TMP_109 H11 u H14) in (let TMP_112 \def (\lambda (c3: 
C).(let TMP_110 \def (Bind x0) in (let TMP_111 \def (CHead c3 TMP_110 x3) in 
(getl i c0 TMP_111)))) in (let H18 \def (eq_ind_r C x1 TMP_112 H10 d H16) in 
(let TMP_115 \def (\lambda (b: B).(let TMP_113 \def (Bind b) in (let TMP_114 
\def (CHead d TMP_113 x3) in (getl i c0 TMP_114)))) in (let H19 \def 
(eq_ind_r B x0 TMP_115 H18 Abbr H15) in (let TMP_116 \def (\lambda (t5: 
T).(subst0 i x3 t3 t5)) in (let TMP_121 \def (\lambda (t5: T).(let TMP_117 
\def (S i) in (let TMP_118 \def (minus i0 TMP_117) in (let TMP_119 \def (plus 
TMP_118 i) in (let TMP_120 \def (S TMP_119) in (subst0 TMP_120 u0 t0 t5)))))) 
in (let TMP_122 \def (pc3 c0 t2 t0) in (let TMP_137 \def (\lambda (x: 
T).(\lambda (H20: (subst0 i x3 t3 x)).(\lambda (H21: (subst0 (S (plus (minus 
i0 (S i)) i)) u0 t0 x)).(let TMP_123 \def (S i) in (let TMP_124 \def (minus 
i0 TMP_123) in (let TMP_125 \def (plus TMP_124 i) in (let TMP_126 \def (S 
TMP_125) in (let TMP_127 \def (\lambda (n: nat).(subst0 n u0 t0 x)) in (let 
TMP_128 \def (lt_plus_minus_r i i0 H6) in (let H22 \def (eq_ind_r nat TMP_126 
TMP_127 H21 i0 TMP_128) in (let TMP_129 \def (pr2_delta c0 d x3 i H19 t2 t3 
H1 x H20) in (let TMP_130 \def (le_n i0) in (let TMP_131 \def (Bind Abbr) in 
(let TMP_132 \def (CHead e TMP_131 u0) in (let TMP_133 \def (csubst0_getl_ge 
i0 i0 TMP_130 c c0 u0 H4 TMP_132 H5) in (let TMP_134 \def (pr0_refl t0) in 
(let TMP_135 \def (pr2_delta c0 e u0 i0 TMP_133 t0 t0 TMP_134 x H22) in (let 
TMP_136 \def (pc3_pr2_x c0 x t0 TMP_135) in (pc3_pr2_u c0 x t2 TMP_129 t0 
TMP_136))))))))))))))))))) in (let TMP_138 \def (S i) in (let TMP_139 \def 
(minus i0 TMP_138) in (let TMP_140 \def (subst0_subst0_back t3 t0 u i H2 x3 
u0 TMP_139 H17) in (ex2_ind T TMP_116 TMP_121 TMP_122 TMP_137 
TMP_140)))))))))))))))) in (let TMP_142 \def (TMP_141 H13) in (TMP_142 
H12)))))))))))))))))))))))))))) in (ex3_4_ind B C T T TMP_84 TMP_87 TMP_90 
TMP_91 TMP_143 H8))))))) in (let TMP_185 \def (\lambda (H8: (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(let TMP_149 \def (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(let TMP_145 \def (Bind 
Abbr) in (let TMP_146 \def (CHead d TMP_145 u) in (let TMP_147 \def (Bind b) 
in (let TMP_148 \def (CHead e1 TMP_147 u1) in (eq C TMP_146 TMP_148))))))))) 
in (let TMP_152 \def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u1: T).(let TMP_150 \def (Bind b) in (let TMP_151 \def (CHead e2 
TMP_150 u1) in (getl i c0 TMP_151))))))) in (let TMP_155 \def (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(let TMP_153 \def (S i) 
in (let TMP_154 \def (minus i0 TMP_153) in (csubst0 TMP_154 u0 e1 e2))))))) 
in (let TMP_156 \def (pc3 c0 t2 t0) in (let TMP_184 \def (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H9: (eq C 
(CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 
(CHead x2 (Bind x0) x3))).(\lambda (H11: (csubst0 (minus i0 (S i)) u0 x1 
x2)).(let TMP_157 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow 
d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_158 \def (Bind Abbr) in (let 
TMP_159 \def (CHead d TMP_158 u) in (let TMP_160 \def (Bind x0) in (let 
TMP_161 \def (CHead x1 TMP_160 x3) in (let H12 \def (f_equal C C TMP_157 
TMP_159 TMP_161 H9) in (let TMP_162 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind 
b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in (let TMP_163 \def (Bind 
Abbr) in (let TMP_164 \def (CHead d TMP_163 u) in (let TMP_165 \def (Bind x0) 
in (let TMP_166 \def (CHead x1 TMP_165 x3) in (let H13 \def (f_equal C B 
TMP_162 TMP_164 TMP_166 H9) in (let TMP_167 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u | (CHead _ _ t5) \Rightarrow t5])) in (let 
TMP_168 \def (Bind Abbr) in (let TMP_169 \def (CHead d TMP_168 u) in (let 
TMP_170 \def (Bind x0) in (let TMP_171 \def (CHead x1 TMP_170 x3) in (let H14 
\def (f_equal C T TMP_167 TMP_169 TMP_171 H9) in (let TMP_182 \def (\lambda 
(H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let TMP_174 \def (\lambda 
(t5: T).(let TMP_172 \def (Bind x0) in (let TMP_173 \def (CHead x2 TMP_172 
t5) in (getl i c0 TMP_173)))) in (let H17 \def (eq_ind_r T x3 TMP_174 H10 u 
H14) in (let TMP_177 \def (\lambda (c3: C).(let TMP_175 \def (S i) in (let 
TMP_176 \def (minus i0 TMP_175) in (csubst0 TMP_176 u0 c3 x2)))) in (let H18 
\def (eq_ind_r C x1 TMP_177 H11 d H16) in (let TMP_180 \def (\lambda (b: 
B).(let TMP_178 \def (Bind b) in (let TMP_179 \def (CHead x2 TMP_178 u) in 
(getl i c0 TMP_179)))) in (let H19 \def (eq_ind_r B x0 TMP_180 H17 Abbr H15) 
in (let TMP_181 \def (pr2_delta c0 x2 u i H19 t2 t3 H1 t0 H2) in (pc3_pr2_r 
c0 t2 t0 TMP_181)))))))))) in (let TMP_183 \def (TMP_182 H13) in (TMP_183 
H12)))))))))))))))))))))))))))) in (ex3_4_ind B C C T TMP_149 TMP_152 TMP_155 
TMP_156 TMP_184 H8))))))) in (let TMP_253 \def (\lambda (H8: (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))))).(let TMP_190 \def (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let 
TMP_186 \def (Bind Abbr) in (let TMP_187 \def (CHead d TMP_186 u) in (let 
TMP_188 \def (Bind b) in (let TMP_189 \def (CHead e1 TMP_188 u1) in (eq C 
TMP_187 TMP_189)))))))))) in (let TMP_193 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(let TMP_191 \def (Bind 
b) in (let TMP_192 \def (CHead e2 TMP_191 w) in (getl i c0 TMP_192)))))))) in 
(let TMP_196 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(let TMP_194 \def (S i) in (let TMP_195 \def (minus 
i0 TMP_194) in (subst0 TMP_195 u0 u1 w)))))))) in (let TMP_199 \def (\lambda 
(_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let 
TMP_197 \def (S i) in (let TMP_198 \def (minus i0 TMP_197) in (csubst0 
TMP_198 u0 e1 e2)))))))) in (let TMP_200 \def (pc3 c0 t2 t0) in (let TMP_252 
\def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) x4))).(\lambda 
(H11: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H12: (csubst0 (minus i0 
(S i)) u0 x1 x2)).(let TMP_201 \def (\lambda (e0: C).(match e0 with [(CSort 
_) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_202 \def 
(Bind Abbr) in (let TMP_203 \def (CHead d TMP_202 u) in (let TMP_204 \def 
(Bind x0) in (let TMP_205 \def (CHead x1 TMP_204 x3) in (let H13 \def 
(f_equal C C TMP_201 TMP_203 TMP_205 H9) in (let TMP_206 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_207 \def (Bind Abbr) in (let TMP_208 \def (CHead d TMP_207 u) in 
(let TMP_209 \def (Bind x0) in (let TMP_210 \def (CHead x1 TMP_209 x3) in 
(let H14 \def (f_equal C B TMP_206 TMP_208 TMP_210 H9) in (let TMP_211 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | (CHead _ _ t5) 
\Rightarrow t5])) in (let TMP_212 \def (Bind Abbr) in (let TMP_213 \def 
(CHead d TMP_212 u) in (let TMP_214 \def (Bind x0) in (let TMP_215 \def 
(CHead x1 TMP_214 x3) in (let H15 \def (f_equal C T TMP_211 TMP_213 TMP_215 
H9) in (let TMP_250 \def (\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C 
d x1)).(let TMP_218 \def (\lambda (t5: T).(let TMP_216 \def (S i) in (let 
TMP_217 \def (minus i0 TMP_216) in (subst0 TMP_217 u0 t5 x4)))) in (let H18 
\def (eq_ind_r T x3 TMP_218 H11 u H15) in (let TMP_221 \def (\lambda (c3: 
C).(let TMP_219 \def (S i) in (let TMP_220 \def (minus i0 TMP_219) in 
(csubst0 TMP_220 u0 c3 x2)))) in (let H19 \def (eq_ind_r C x1 TMP_221 H12 d 
H17) in (let TMP_224 \def (\lambda (b: B).(let TMP_222 \def (Bind b) in (let 
TMP_223 \def (CHead x2 TMP_222 x4) in (getl i c0 TMP_223)))) in (let H20 \def 
(eq_ind_r B x0 TMP_224 H10 Abbr H16) in (let TMP_225 \def (\lambda (t5: 
T).(subst0 i x4 t3 t5)) in (let TMP_230 \def (\lambda (t5: T).(let TMP_226 
\def (S i) in (let TMP_227 \def (minus i0 TMP_226) in (let TMP_228 \def (plus 
TMP_227 i) in (let TMP_229 \def (S TMP_228) in (subst0 TMP_229 u0 t0 t5)))))) 
in (let TMP_231 \def (pc3 c0 t2 t0) in (let TMP_246 \def (\lambda (x: 
T).(\lambda (H21: (subst0 i x4 t3 x)).(\lambda (H22: (subst0 (S (plus (minus 
i0 (S i)) i)) u0 t0 x)).(let TMP_232 \def (S i) in (let TMP_233 \def (minus 
i0 TMP_232) in (let TMP_234 \def (plus TMP_233 i) in (let TMP_235 \def (S 
TMP_234) in (let TMP_236 \def (\lambda (n: nat).(subst0 n u0 t0 x)) in (let 
TMP_237 \def (lt_plus_minus_r i i0 H6) in (let H23 \def (eq_ind_r nat TMP_235 
TMP_236 H22 i0 TMP_237) in (let TMP_238 \def (pr2_delta c0 x2 x4 i H20 t2 t3 
H1 x H21) in (let TMP_239 \def (le_n i0) in (let TMP_240 \def (Bind Abbr) in 
(let TMP_241 \def (CHead e TMP_240 u0) in (let TMP_242 \def (csubst0_getl_ge 
i0 i0 TMP_239 c c0 u0 H4 TMP_241 H5) in (let TMP_243 \def (pr0_refl t0) in 
(let TMP_244 \def (pr2_delta c0 e u0 i0 TMP_242 t0 t0 TMP_243 x H23) in (let 
TMP_245 \def (pc3_pr2_x c0 x t0 TMP_244) in (pc3_pr2_u c0 x t2 TMP_238 t0 
TMP_245))))))))))))))))))) in (let TMP_247 \def (S i) in (let TMP_248 \def 
(minus i0 TMP_247) in (let TMP_249 \def (subst0_subst0_back t3 t0 u i H2 x4 
u0 TMP_248 H18) in (ex2_ind T TMP_225 TMP_230 TMP_231 TMP_246 
TMP_249)))))))))))))))) in (let TMP_251 \def (TMP_250 H14) in (TMP_251 
H13)))))))))))))))))))))))))))))) in (ex4_5_ind B C C T T TMP_190 TMP_193 
TMP_196 TMP_199 TMP_200 TMP_252 H8)))))))) in (or4_ind TMP_37 TMP_49 TMP_61 
TMP_76 TMP_77 TMP_79 TMP_144 TMP_185 TMP_253 H7)))))))))))))))))))))))))) in 
(let TMP_259 \def (\lambda (H6: (le i0 i)).(let TMP_255 \def (Bind Abbr) in 
(let TMP_256 \def (CHead d TMP_255 u) in (let TMP_257 \def (csubst0_getl_ge 
i0 i H6 c c0 u0 H4 TMP_256 H0) in (let TMP_258 \def (pr2_delta c0 d u i 
TMP_257 t2 t3 H1 t0 H2) in (pc3_pr2_r c0 t2 t0 TMP_258)))))) in (lt_le_e i i0 
TMP_32 TMP_254 TMP_259)))))))) in (let TMP_528 \def (\lambda (t5: T).(\lambda 
(H4: (subst0 i0 u0 t0 t5)).(\lambda (c0: C).(\lambda (H5: (csubst0 i0 u0 c 
c0)).(\lambda (e: C).(\lambda (H6: (getl i0 c (CHead e (Bind Abbr) u0))).(let 
TMP_261 \def (pc3 c0 t2 t5) in (let TMP_515 \def (\lambda (H7: (lt i 
i0)).(let TMP_262 \def (Bind Abbr) in (let TMP_263 \def (CHead d TMP_262 u) 
in (let H8 \def (csubst0_getl_lt i0 i H7 c c0 u0 H5 TMP_263 H0) in (let 
TMP_264 \def (Bind Abbr) in (let TMP_265 \def (CHead d TMP_264 u) in (let 
TMP_266 \def (getl i c0 TMP_265) in (let TMP_271 \def (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_267 \def (Bind 
Abbr) in (let TMP_268 \def (CHead d TMP_267 u) in (let TMP_269 \def (Bind b) 
in (let TMP_270 \def (CHead e0 TMP_269 u1) in (eq C TMP_268 TMP_270))))))))) 
in (let TMP_274 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(let TMP_272 \def (Bind b) in (let TMP_273 \def (CHead e0 
TMP_272 w) in (getl i c0 TMP_273))))))) in (let TMP_277 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(let TMP_275 \def (S i) 
in (let TMP_276 \def (minus i0 TMP_275) in (subst0 TMP_276 u0 u1 w))))))) in 
(let TMP_278 \def (ex3_4 B C T T TMP_271 TMP_274 TMP_277) in (let TMP_283 
\def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(let 
TMP_279 \def (Bind Abbr) in (let TMP_280 \def (CHead d TMP_279 u) in (let 
TMP_281 \def (Bind b) in (let TMP_282 \def (CHead e1 TMP_281 u1) in (eq C 
TMP_280 TMP_282))))))))) in (let TMP_286 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_284 \def (Bind b) in (let 
TMP_285 \def (CHead e2 TMP_284 u1) in (getl i c0 TMP_285))))))) in (let 
TMP_289 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(let TMP_287 \def (S i) in (let TMP_288 \def (minus i0 TMP_287) in 
(csubst0 TMP_288 u0 e1 e2))))))) in (let TMP_290 \def (ex3_4 B C C T TMP_283 
TMP_286 TMP_289) in (let TMP_295 \def (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_291 \def (Bind 
Abbr) in (let TMP_292 \def (CHead d TMP_291 u) in (let TMP_293 \def (Bind b) 
in (let TMP_294 \def (CHead e1 TMP_293 u1) in (eq C TMP_292 TMP_294)))))))))) 
in (let TMP_298 \def (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(let TMP_296 \def (Bind b) in (let TMP_297 
\def (CHead e2 TMP_296 w) in (getl i c0 TMP_297)))))))) in (let TMP_301 \def 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: 
T).(let TMP_299 \def (S i) in (let TMP_300 \def (minus i0 TMP_299) in (subst0 
TMP_300 u0 u1 w)))))))) in (let TMP_304 \def (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let TMP_302 \def (S i) 
in (let TMP_303 \def (minus i0 TMP_302) in (csubst0 TMP_303 u0 e1 e2)))))))) 
in (let TMP_305 \def (ex4_5 B C C T T TMP_295 TMP_298 TMP_301 TMP_304) in 
(let TMP_306 \def (pc3 c0 t2 t5) in (let TMP_319 \def (\lambda (H9: (getl i 
c0 (CHead d (Bind Abbr) u))).(let TMP_307 \def (pr2_free c0 t2 t3 H1) in (let 
TMP_308 \def (pr0_refl t3) in (let TMP_309 \def (pr2_delta c0 d u i H9 t3 t3 
TMP_308 t0 H2) in (let TMP_310 \def (le_n i0) in (let TMP_311 \def (Bind 
Abbr) in (let TMP_312 \def (CHead e TMP_311 u0) in (let TMP_313 \def 
(csubst0_getl_ge i0 i0 TMP_310 c c0 u0 H5 TMP_312 H6) in (let TMP_314 \def 
(pr0_refl t0) in (let TMP_315 \def (pr2_delta c0 e u0 i0 TMP_313 t0 t0 
TMP_314 t5 H4) in (let TMP_316 \def (pr3_pr2 c0 t0 t5 TMP_315) in (let 
TMP_317 \def (pr3_sing c0 t0 t3 TMP_309 t5 TMP_316) in (let TMP_318 \def 
(pc3_pr3_r c0 t3 t5 TMP_317) in (pc3_pr2_u c0 t3 t2 TMP_307 t5 
TMP_318)))))))))))))) in (let TMP_391 \def (\lambda (H9: (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(let TMP_324 \def (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_320 \def (Bind Abbr) in 
(let TMP_321 \def (CHead d TMP_320 u) in (let TMP_322 \def (Bind b) in (let 
TMP_323 \def (CHead e0 TMP_322 u1) in (eq C TMP_321 TMP_323))))))))) in (let 
TMP_327 \def (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(let TMP_325 \def (Bind b) in (let TMP_326 \def (CHead e0 TMP_325 w) in 
(getl i c0 TMP_326))))))) in (let TMP_330 \def (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(let TMP_328 \def (S i) in (let TMP_329 
\def (minus i0 TMP_328) in (subst0 TMP_329 u0 u1 w))))))) in (let TMP_331 
\def (pc3 c0 t2 t5) in (let TMP_390 \def (\lambda (x0: B).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x2))).(\lambda (H11: (getl i c0 (CHead x1 (Bind 
x0) x3))).(\lambda (H12: (subst0 (minus i0 (S i)) u0 x2 x3)).(let TMP_332 
\def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ 
_) \Rightarrow c3])) in (let TMP_333 \def (Bind Abbr) in (let TMP_334 \def 
(CHead d TMP_333 u) in (let TMP_335 \def (Bind x0) in (let TMP_336 \def 
(CHead x1 TMP_335 x2) in (let H13 \def (f_equal C C TMP_332 TMP_334 TMP_336 
H10) in (let TMP_337 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) in (let TMP_338 \def (Bind 
Abbr) in (let TMP_339 \def (CHead d TMP_338 u) in (let TMP_340 \def (Bind x0) 
in (let TMP_341 \def (CHead x1 TMP_340 x2) in (let H14 \def (f_equal C B 
TMP_337 TMP_339 TMP_341 H10) in (let TMP_342 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u | (CHead _ _ t6) \Rightarrow t6])) in (let 
TMP_343 \def (Bind Abbr) in (let TMP_344 \def (CHead d TMP_343 u) in (let 
TMP_345 \def (Bind x0) in (let TMP_346 \def (CHead x1 TMP_345 x2) in (let H15 
\def (f_equal C T TMP_342 TMP_344 TMP_346 H10) in (let TMP_388 \def (\lambda 
(H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let TMP_349 \def (\lambda 
(t6: T).(let TMP_347 \def (S i) in (let TMP_348 \def (minus i0 TMP_347) in 
(subst0 TMP_348 u0 t6 x3)))) in (let H18 \def (eq_ind_r T x2 TMP_349 H12 u 
H15) in (let TMP_352 \def (\lambda (c3: C).(let TMP_350 \def (Bind x0) in 
(let TMP_351 \def (CHead c3 TMP_350 x3) in (getl i c0 TMP_351)))) in (let H19 
\def (eq_ind_r C x1 TMP_352 H11 d H17) in (let TMP_355 \def (\lambda (b: 
B).(let TMP_353 \def (Bind b) in (let TMP_354 \def (CHead d TMP_353 x3) in 
(getl i c0 TMP_354)))) in (let H20 \def (eq_ind_r B x0 TMP_355 H19 Abbr H16) 
in (let TMP_356 \def (\lambda (t6: T).(subst0 i x3 t3 t6)) in (let TMP_361 
\def (\lambda (t6: T).(let TMP_357 \def (S i) in (let TMP_358 \def (minus i0 
TMP_357) in (let TMP_359 \def (plus TMP_358 i) in (let TMP_360 \def (S 
TMP_359) in (subst0 TMP_360 u0 t0 t6)))))) in (let TMP_362 \def (pc3 c0 t2 
t5) in (let TMP_384 \def (\lambda (x: T).(\lambda (H21: (subst0 i x3 t3 
x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
TMP_363 \def (S i) in (let TMP_364 \def (minus i0 TMP_363) in (let TMP_365 
\def (plus TMP_364 i) in (let TMP_366 \def (S TMP_365) in (let TMP_367 \def 
(\lambda (n: nat).(subst0 n u0 t0 x)) in (let TMP_368 \def (lt_plus_minus_r i 
i0 H7) in (let H23 \def (eq_ind_r nat TMP_366 TMP_367 H22 i0 TMP_368) in (let 
TMP_369 \def (pr2_delta c0 d x3 i H20 t2 t3 H1 x H21) in (let TMP_370 \def 
(le_n i0) in (let TMP_371 \def (Bind Abbr) in (let TMP_372 \def (CHead e 
TMP_371 u0) in (let TMP_373 \def (csubst0_getl_ge i0 i0 TMP_370 c c0 u0 H5 
TMP_372 H6) in (let TMP_374 \def (pr0_refl t0) in (let TMP_375 \def 
(pr2_delta c0 e u0 i0 TMP_373 t0 t0 TMP_374 x H23) in (let TMP_376 \def (le_n 
i0) in (let TMP_377 \def (Bind Abbr) in (let TMP_378 \def (CHead e TMP_377 
u0) in (let TMP_379 \def (csubst0_getl_ge i0 i0 TMP_376 c c0 u0 H5 TMP_378 
H6) in (let TMP_380 \def (pr0_refl t0) in (let TMP_381 \def (pr2_delta c0 e 
u0 i0 TMP_379 t0 t0 TMP_380 t5 H4) in (let TMP_382 \def (pc3_pr2_r c0 t0 t5 
TMP_381) in (let TMP_383 \def (pc3_pr2_u2 c0 t0 x TMP_375 t5 TMP_382) in 
(pc3_pr2_u c0 x t2 TMP_369 t5 TMP_383)))))))))))))))))))))))))) in (let 
TMP_385 \def (S i) in (let TMP_386 \def (minus i0 TMP_385) in (let TMP_387 
\def (subst0_subst0_back t3 t0 u i H2 x3 u0 TMP_386 H18) in (ex2_ind T 
TMP_356 TMP_361 TMP_362 TMP_384 TMP_387)))))))))))))))) in (let TMP_389 \def 
(TMP_388 H14) in (TMP_389 H13)))))))))))))))))))))))))))) in (ex3_4_ind B C T 
T TMP_324 TMP_327 TMP_330 TMP_331 TMP_390 H9))))))) in (let TMP_439 \def 
(\lambda (H9: (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(let TMP_396 
\def (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(let 
TMP_392 \def (Bind Abbr) in (let TMP_393 \def (CHead d TMP_392 u) in (let 
TMP_394 \def (Bind b) in (let TMP_395 \def (CHead e1 TMP_394 u1) in (eq C 
TMP_393 TMP_395))))))))) in (let TMP_399 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u1: T).(let TMP_397 \def (Bind b) in (let 
TMP_398 \def (CHead e2 TMP_397 u1) in (getl i c0 TMP_398))))))) in (let 
TMP_402 \def (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(let TMP_400 \def (S i) in (let TMP_401 \def (minus i0 TMP_400) in 
(csubst0 TMP_401 u0 e1 e2))))))) in (let TMP_403 \def (pc3 c0 t2 t5) in (let 
TMP_438 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) x3))).(\lambda (H12: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let TMP_404 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) 
in (let TMP_405 \def (Bind Abbr) in (let TMP_406 \def (CHead d TMP_405 u) in 
(let TMP_407 \def (Bind x0) in (let TMP_408 \def (CHead x1 TMP_407 x3) in 
(let H13 \def (f_equal C C TMP_404 TMP_406 TMP_408 H10) in (let TMP_409 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) in (let TMP_410 \def (Bind Abbr) in (let TMP_411 \def (CHead d 
TMP_410 u) in (let TMP_412 \def (Bind x0) in (let TMP_413 \def (CHead x1 
TMP_412 x3) in (let H14 \def (f_equal C B TMP_409 TMP_411 TMP_413 H10) in 
(let TMP_414 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | 
(CHead _ _ t6) \Rightarrow t6])) in (let TMP_415 \def (Bind Abbr) in (let 
TMP_416 \def (CHead d TMP_415 u) in (let TMP_417 \def (Bind x0) in (let 
TMP_418 \def (CHead x1 TMP_417 x3) in (let H15 \def (f_equal C T TMP_414 
TMP_416 TMP_418 H10) in (let TMP_436 \def (\lambda (H16: (eq B Abbr 
x0)).(\lambda (H17: (eq C d x1)).(let TMP_421 \def (\lambda (t6: T).(let 
TMP_419 \def (Bind x0) in (let TMP_420 \def (CHead x2 TMP_419 t6) in (getl i 
c0 TMP_420)))) in (let H18 \def (eq_ind_r T x3 TMP_421 H11 u H15) in (let 
TMP_424 \def (\lambda (c3: C).(let TMP_422 \def (S i) in (let TMP_423 \def 
(minus i0 TMP_422) in (csubst0 TMP_423 u0 c3 x2)))) in (let H19 \def 
(eq_ind_r C x1 TMP_424 H12 d H17) in (let TMP_427 \def (\lambda (b: B).(let 
TMP_425 \def (Bind b) in (let TMP_426 \def (CHead x2 TMP_425 u) in (getl i c0 
TMP_426)))) in (let H20 \def (eq_ind_r B x0 TMP_427 H18 Abbr H16) in (let 
TMP_428 \def (pr2_delta c0 x2 u i H20 t2 t3 H1 t0 H2) in (let TMP_429 \def 
(le_n i0) in (let TMP_430 \def (Bind Abbr) in (let TMP_431 \def (CHead e 
TMP_430 u0) in (let TMP_432 \def (csubst0_getl_ge i0 i0 TMP_429 c c0 u0 H5 
TMP_431 H6) in (let TMP_433 \def (pr0_refl t0) in (let TMP_434 \def 
(pr2_delta c0 e u0 i0 TMP_432 t0 t0 TMP_433 t5 H4) in (let TMP_435 \def 
(pc3_pr2_r c0 t0 t5 TMP_434) in (pc3_pr2_u c0 t0 t2 TMP_428 t5 
TMP_435))))))))))))))))) in (let TMP_437 \def (TMP_436 H14) in (TMP_437 
H13)))))))))))))))))))))))))))) in (ex3_4_ind B C C T TMP_396 TMP_399 TMP_402 
TMP_403 TMP_438 H9))))))) in (let TMP_514 \def (\lambda (H9: (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))))).(let TMP_444 \def (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let 
TMP_440 \def (Bind Abbr) in (let TMP_441 \def (CHead d TMP_440 u) in (let 
TMP_442 \def (Bind b) in (let TMP_443 \def (CHead e1 TMP_442 u1) in (eq C 
TMP_441 TMP_443)))))))))) in (let TMP_447 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(let TMP_445 \def (Bind 
b) in (let TMP_446 \def (CHead e2 TMP_445 w) in (getl i c0 TMP_446)))))))) in 
(let TMP_450 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(let TMP_448 \def (S i) in (let TMP_449 \def (minus 
i0 TMP_448) in (subst0 TMP_449 u0 u1 w)))))))) in (let TMP_453 \def (\lambda 
(_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(let 
TMP_451 \def (S i) in (let TMP_452 \def (minus i0 TMP_451) in (csubst0 
TMP_452 u0 e1 e2)))))))) in (let TMP_454 \def (pc3 c0 t2 t5) in (let TMP_513 
\def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) x4))).(\lambda 
(H12: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H13: (csubst0 (minus i0 
(S i)) u0 x1 x2)).(let TMP_455 \def (\lambda (e0: C).(match e0 with [(CSort 
_) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) in (let TMP_456 \def 
(Bind Abbr) in (let TMP_457 \def (CHead d TMP_456 u) in (let TMP_458 \def 
(Bind x0) in (let TMP_459 \def (CHead x1 TMP_458 x3) in (let H14 \def 
(f_equal C C TMP_455 TMP_457 TMP_459 H10) in (let TMP_460 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_461 \def (Bind Abbr) in (let TMP_462 \def (CHead d TMP_461 u) in 
(let TMP_463 \def (Bind x0) in (let TMP_464 \def (CHead x1 TMP_463 x3) in 
(let H15 \def (f_equal C B TMP_460 TMP_462 TMP_464 H10) in (let TMP_465 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u | (CHead _ _ t6) 
\Rightarrow t6])) in (let TMP_466 \def (Bind Abbr) in (let TMP_467 \def 
(CHead d TMP_466 u) in (let TMP_468 \def (Bind x0) in (let TMP_469 \def 
(CHead x1 TMP_468 x3) in (let H16 \def (f_equal C T TMP_465 TMP_467 TMP_469 
H10) in (let TMP_511 \def (\lambda (H17: (eq B Abbr x0)).(\lambda (H18: (eq C 
d x1)).(let TMP_472 \def (\lambda (t6: T).(let TMP_470 \def (S i) in (let 
TMP_471 \def (minus i0 TMP_470) in (subst0 TMP_471 u0 t6 x4)))) in (let H19 
\def (eq_ind_r T x3 TMP_472 H12 u H16) in (let TMP_475 \def (\lambda (c3: 
C).(let TMP_473 \def (S i) in (let TMP_474 \def (minus i0 TMP_473) in 
(csubst0 TMP_474 u0 c3 x2)))) in (let H20 \def (eq_ind_r C x1 TMP_475 H13 d 
H18) in (let TMP_478 \def (\lambda (b: B).(let TMP_476 \def (Bind b) in (let 
TMP_477 \def (CHead x2 TMP_476 x4) in (getl i c0 TMP_477)))) in (let H21 \def 
(eq_ind_r B x0 TMP_478 H11 Abbr H17) in (let TMP_479 \def (\lambda (t6: 
T).(subst0 i x4 t3 t6)) in (let TMP_484 \def (\lambda (t6: T).(let TMP_480 
\def (S i) in (let TMP_481 \def (minus i0 TMP_480) in (let TMP_482 \def (plus 
TMP_481 i) in (let TMP_483 \def (S TMP_482) in (subst0 TMP_483 u0 t0 t6)))))) 
in (let TMP_485 \def (pc3 c0 t2 t5) in (let TMP_507 \def (\lambda (x: 
T).(\lambda (H22: (subst0 i x4 t3 x)).(\lambda (H23: (subst0 (S (plus (minus 
i0 (S i)) i)) u0 t0 x)).(let TMP_486 \def (S i) in (let TMP_487 \def (minus 
i0 TMP_486) in (let TMP_488 \def (plus TMP_487 i) in (let TMP_489 \def (S 
TMP_488) in (let TMP_490 \def (\lambda (n: nat).(subst0 n u0 t0 x)) in (let 
TMP_491 \def (lt_plus_minus_r i i0 H7) in (let H24 \def (eq_ind_r nat TMP_489 
TMP_490 H23 i0 TMP_491) in (let TMP_492 \def (pr2_delta c0 x2 x4 i H21 t2 t3 
H1 x H22) in (let TMP_493 \def (le_n i0) in (let TMP_494 \def (Bind Abbr) in 
(let TMP_495 \def (CHead e TMP_494 u0) in (let TMP_496 \def (csubst0_getl_ge 
i0 i0 TMP_493 c c0 u0 H5 TMP_495 H6) in (let TMP_497 \def (pr0_refl t0) in 
(let TMP_498 \def (pr2_delta c0 e u0 i0 TMP_496 t0 t0 TMP_497 x H24) in (let 
TMP_499 \def (le_n i0) in (let TMP_500 \def (Bind Abbr) in (let TMP_501 \def 
(CHead e TMP_500 u0) in (let TMP_502 \def (csubst0_getl_ge i0 i0 TMP_499 c c0 
u0 H5 TMP_501 H6) in (let TMP_503 \def (pr0_refl t0) in (let TMP_504 \def 
(pr2_delta c0 e u0 i0 TMP_502 t0 t0 TMP_503 t5 H4) in (let TMP_505 \def 
(pc3_pr2_r c0 t0 t5 TMP_504) in (let TMP_506 \def (pc3_pr2_u2 c0 t0 x TMP_498 
t5 TMP_505) in (pc3_pr2_u c0 x t2 TMP_492 t5 
TMP_506)))))))))))))))))))))))))) in (let TMP_508 \def (S i) in (let TMP_509 
\def (minus i0 TMP_508) in (let TMP_510 \def (subst0_subst0_back t3 t0 u i H2 
x4 u0 TMP_509 H19) in (ex2_ind T TMP_479 TMP_484 TMP_485 TMP_507 
TMP_510)))))))))))))))) in (let TMP_512 \def (TMP_511 H15) in (TMP_512 
H14)))))))))))))))))))))))))))))) in (ex4_5_ind B C C T T TMP_444 TMP_447 
TMP_450 TMP_453 TMP_454 TMP_513 H9)))))))) in (or4_ind TMP_266 TMP_278 
TMP_290 TMP_305 TMP_306 TMP_319 TMP_391 TMP_439 TMP_514 
H8)))))))))))))))))))))))))) in (let TMP_527 \def (\lambda (H7: (le i0 
i)).(let TMP_516 \def (Bind Abbr) in (let TMP_517 \def (CHead d TMP_516 u) in 
(let TMP_518 \def (csubst0_getl_ge i0 i H7 c c0 u0 H5 TMP_517 H0) in (let 
TMP_519 \def (pr2_delta c0 d u i TMP_518 t2 t3 H1 t0 H2) in (let TMP_520 \def 
(le_n i0) in (let TMP_521 \def (Bind Abbr) in (let TMP_522 \def (CHead e 
TMP_521 u0) in (let TMP_523 \def (csubst0_getl_ge i0 i0 TMP_520 c c0 u0 H5 
TMP_522 H6) in (let TMP_524 \def (pr0_refl t0) in (let TMP_525 \def 
(pr2_delta c0 e u0 i0 TMP_523 t0 t0 TMP_524 t5 H4) in (let TMP_526 \def 
(pc3_pr2_r c0 t0 t5 TMP_525) in (pc3_pr2_u c0 t0 t2 TMP_519 t5 
TMP_526))))))))))))) in (lt_le_e i i0 TMP_261 TMP_515 TMP_527)))))))))) in 
(fsubst0_ind i0 u0 c t0 TMP_20 TMP_31 TMP_260 TMP_528 c2 t4 
H3)))))))))))))))))))) in (pr2_ind TMP_1 TMP_19 TMP_529 c1 t t1 H))))))).

theorem pc3_fsubst0:
 \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pc3 c1 t1 t) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t2 t)))))))))))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: (pc3 c1 t1 
t)).(let TMP_1 \def (\lambda (t0: T).(\lambda (t2: T).(\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: T).((fsubst0 i u c1 t0 c2 
t3) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t3 
t2)))))))))) in (let TMP_14 \def (\lambda (t0: T).(\lambda (i: nat).(\lambda 
(u: T).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H0: (fsubst0 i u c1 t0 c2 
t2)).(let TMP_2 \def (\lambda (c: C).(\lambda (t3: T).(\forall (e: C).((getl 
i c1 (CHead e (Bind Abbr) u)) \to (pc3 c t3 t0))))) in (let TMP_5 \def 
(\lambda (t3: T).(\lambda (H1: (subst0 i u t0 t3)).(\lambda (e: C).(\lambda 
(H2: (getl i c1 (CHead e (Bind Abbr) u))).(let TMP_3 \def (pr0_refl t0) in 
(let TMP_4 \def (pr2_delta c1 e u i H2 t0 t0 TMP_3 t3 H1) in (pc3_pr2_x c1 t3 
t0 TMP_4))))))) in (let TMP_6 \def (\lambda (c0: C).(\lambda (_: (csubst0 i u 
c1 c0)).(\lambda (e: C).(\lambda (_: (getl i c1 (CHead e (Bind Abbr) 
u))).(pc3_refl c0 t0))))) in (let TMP_13 \def (\lambda (t3: T).(\lambda (H1: 
(subst0 i u t0 t3)).(\lambda (c0: C).(\lambda (H2: (csubst0 i u c1 
c0)).(\lambda (e: C).(\lambda (H3: (getl i c1 (CHead e (Bind Abbr) u))).(let 
TMP_7 \def (le_n i) in (let TMP_8 \def (Bind Abbr) in (let TMP_9 \def (CHead 
e TMP_8 u) in (let TMP_10 \def (csubst0_getl_ge i i TMP_7 c1 c0 u H2 TMP_9 
H3) in (let TMP_11 \def (pr0_refl t0) in (let TMP_12 \def (pr2_delta c0 e u i 
TMP_10 t0 t0 TMP_11 t3 H1) in (pc3_pr2_x c0 t3 t0 TMP_12))))))))))))) in 
(fsubst0_ind i u c1 t0 TMP_2 TMP_5 TMP_6 TMP_13 c2 t2 H0))))))))))) in (let 
TMP_29 \def (\lambda (t0: T).(\lambda (t2: T).(\lambda (H0: (pr2 c1 t0 
t2)).(\lambda (t3: T).(\lambda (H1: (pc3 c1 t2 t3)).(\lambda (H2: ((\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t4: T).((fsubst0 i u c1 
t2 c2 t4) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t4 t3)))))))))).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: 
C).(\lambda (t4: T).(\lambda (H3: (fsubst0 i u c1 t0 c2 t4)).(let TMP_15 \def 
(\lambda (c: C).(\lambda (t5: T).(\forall (e: C).((getl i c1 (CHead e (Bind 
Abbr) u)) \to (pc3 c t5 t3))))) in (let TMP_18 \def (\lambda (t5: T).(\lambda 
(H4: (subst0 i u t0 t5)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e 
(Bind Abbr) u))).(let TMP_16 \def (fsubst0_snd i u c1 t0 t5 H4) in (let 
TMP_17 \def (pc3_pr2_fsubst0 c1 t0 t2 H0 i u c1 t5 TMP_16 e H5) in (pc3_t t2 
c1 t5 TMP_17 t3 H1))))))) in (let TMP_23 \def (\lambda (c0: C).(\lambda (H4: 
(csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e (Bind 
Abbr) u))).(let TMP_19 \def (fsubst0_fst i u c1 t0 c0 H4) in (let TMP_20 \def 
(pc3_pr2_fsubst0 c1 t0 t2 H0 i u c0 t0 TMP_19 e H5) in (let TMP_21 \def 
(fsubst0_fst i u c1 t2 c0 H4) in (let TMP_22 \def (H2 i u c0 t2 TMP_21 e H5) 
in (pc3_t t2 c0 t0 TMP_20 t3 TMP_22))))))))) in (let TMP_28 \def (\lambda 
(t5: T).(\lambda (H4: (subst0 i u t0 t5)).(\lambda (c0: C).(\lambda (H5: 
(csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H6: (getl i c1 (CHead e (Bind 
Abbr) u))).(let TMP_24 \def (fsubst0_both i u c1 t0 t5 H4 c0 H5) in (let 
TMP_25 \def (pc3_pr2_fsubst0 c1 t0 t2 H0 i u c0 t5 TMP_24 e H6) in (let 
TMP_26 \def (fsubst0_fst i u c1 t2 c0 H5) in (let TMP_27 \def (H2 i u c0 t2 
TMP_26 e H6) in (pc3_t t2 c0 t5 TMP_25 t3 TMP_27))))))))))) in (fsubst0_ind i 
u c1 t0 TMP_15 TMP_18 TMP_23 TMP_28 c2 t4 H3)))))))))))))))) in (let TMP_47 
\def (\lambda (t0: T).(\lambda (t2: T).(\lambda (H0: (pr2 c1 t0 t2)).(\lambda 
(t3: T).(\lambda (H1: (pc3 c1 t0 t3)).(\lambda (H2: ((\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t4: T).((fsubst0 i u c1 t0 c2 
t4) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t4 
t3)))))))))).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t4: 
T).(\lambda (H3: (fsubst0 i u c1 t2 c2 t4)).(let TMP_30 \def (\lambda (c: 
C).(\lambda (t5: T).(\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to 
(pc3 c t5 t3))))) in (let TMP_34 \def (\lambda (t5: T).(\lambda (H4: (subst0 
i u t2 t5)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e (Bind Abbr) 
u))).(let TMP_31 \def (fsubst0_snd i u c1 t2 t5 H4) in (let TMP_32 \def 
(pc3_pr2_fsubst0_back c1 t0 t2 H0 i u c1 t5 TMP_31 e H5) in (let TMP_33 \def 
(pc3_s c1 t5 t0 TMP_32) in (pc3_t t0 c1 t5 TMP_33 t3 H1)))))))) in (let 
TMP_40 \def (\lambda (c0: C).(\lambda (H4: (csubst0 i u c1 c0)).(\lambda (e: 
C).(\lambda (H5: (getl i c1 (CHead e (Bind Abbr) u))).(let TMP_35 \def 
(fsubst0_fst i u c1 t2 c0 H4) in (let TMP_36 \def (pc3_pr2_fsubst0_back c1 t0 
t2 H0 i u c0 t2 TMP_35 e H5) in (let TMP_37 \def (pc3_s c0 t2 t0 TMP_36) in 
(let TMP_38 \def (fsubst0_fst i u c1 t0 c0 H4) in (let TMP_39 \def (H2 i u c0 
t0 TMP_38 e H5) in (pc3_t t0 c0 t2 TMP_37 t3 TMP_39)))))))))) in (let TMP_46 
\def (\lambda (t5: T).(\lambda (H4: (subst0 i u t2 t5)).(\lambda (c0: 
C).(\lambda (H5: (csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H6: (getl i 
c1 (CHead e (Bind Abbr) u))).(let TMP_41 \def (fsubst0_both i u c1 t2 t5 H4 
c0 H5) in (let TMP_42 \def (pc3_pr2_fsubst0_back c1 t0 t2 H0 i u c0 t5 TMP_41 
e H6) in (let TMP_43 \def (pc3_s c0 t5 t0 TMP_42) in (let TMP_44 \def 
(fsubst0_fst i u c1 t0 c0 H5) in (let TMP_45 \def (H2 i u c0 t0 TMP_44 e H6) 
in (pc3_t t0 c0 t5 TMP_43 t3 TMP_45)))))))))))) in (fsubst0_ind i u c1 t2 
TMP_30 TMP_34 TMP_40 TMP_46 c2 t4 H3)))))))))))))))) in (pc3_ind_left c1 
TMP_1 TMP_14 TMP_29 TMP_47 t1 t H)))))))).

