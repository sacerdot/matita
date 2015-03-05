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

include "basic_1/csubt/clear.ma".

include "basic_1/csubt/drop.ma".

include "basic_1/getl/clear.ma".

theorem csubt_getl_abbr:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csubt g 
c1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n 
c2 (CHead d2 (Bind Abbr) u)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abbr) u))).(let TMP_1 \def 
(Bind Abbr) in (let TMP_2 \def (CHead d1 TMP_1 u) in (let H0 \def 
(getl_gen_all c1 TMP_2 n H) in (let TMP_3 \def (\lambda (e: C).(drop n O c1 
e)) in (let TMP_6 \def (\lambda (e: C).(let TMP_4 \def (Bind Abbr) in (let 
TMP_5 \def (CHead d1 TMP_4 u) in (clear e TMP_5)))) in (let TMP_11 \def 
(\forall (c2: C).((csubt g c1 c2) \to (let TMP_7 \def (\lambda (d2: C).(csubt 
g d1 d2)) in (let TMP_10 \def (\lambda (d2: C).(let TMP_8 \def (Bind Abbr) in 
(let TMP_9 \def (CHead d2 TMP_8 u) in (getl n c2 TMP_9)))) in (ex2 C TMP_7 
TMP_10))))) in (let TMP_209 \def (\lambda (x: C).(\lambda (H1: (drop n O c1 
x)).(\lambda (H2: (clear x (CHead d1 (Bind Abbr) u))).(let TMP_16 \def 
(\lambda (c: C).((drop n O c1 c) \to ((clear c (CHead d1 (Bind Abbr) u)) \to 
(\forall (c2: C).((csubt g c1 c2) \to (let TMP_12 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_15 \def (\lambda (d2: C).(let TMP_13 \def 
(Bind Abbr) in (let TMP_14 \def (CHead d2 TMP_13 u) in (getl n c2 TMP_14)))) 
in (ex2 C TMP_12 TMP_15)))))))) in (let TMP_24 \def (\lambda (n0: 
nat).(\lambda (_: (drop n O c1 (CSort n0))).(\lambda (H4: (clear (CSort n0) 
(CHead d1 (Bind Abbr) u))).(let TMP_17 \def (Bind Abbr) in (let TMP_18 \def 
(CHead d1 TMP_17 u) in (let TMP_23 \def (\forall (c2: C).((csubt g c1 c2) \to 
(let TMP_19 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_22 \def 
(\lambda (d2: C).(let TMP_20 \def (Bind Abbr) in (let TMP_21 \def (CHead d2 
TMP_20 u) in (getl n c2 TMP_21)))) in (ex2 C TMP_19 TMP_22))))) in 
(clear_gen_sort TMP_18 n0 H4 TMP_23))))))) in (let TMP_208 \def (\lambda (x0: 
C).(\lambda (_: (((drop n O c1 x0) \to ((clear x0 (CHead d1 (Bind Abbr) u)) 
\to (\forall (c2: C).((csubt g c1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u)))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (H3: (drop n O c1 (CHead x0 k t))).(\lambda 
(H4: (clear (CHead x0 k t) (CHead d1 (Bind Abbr) u))).(let TMP_29 \def 
(\lambda (k0: K).((drop n O c1 (CHead x0 k0 t)) \to ((clear (CHead x0 k0 t) 
(CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csubt g c1 c2) \to (let 
TMP_25 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_28 \def (\lambda 
(d2: C).(let TMP_26 \def (Bind Abbr) in (let TMP_27 \def (CHead d2 TMP_26 u) 
in (getl n c2 TMP_27)))) in (ex2 C TMP_25 TMP_28)))))))) in (let TMP_86 \def 
(\lambda (b: B).(\lambda (H5: (drop n O c1 (CHead x0 (Bind b) t))).(\lambda 
(H6: (clear (CHead x0 (Bind b) t) (CHead d1 (Bind Abbr) u))).(let TMP_30 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow d1 | (CHead c _ _) 
\Rightarrow c])) in (let TMP_31 \def (Bind Abbr) in (let TMP_32 \def (CHead 
d1 TMP_31 u) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead x0 
TMP_33 t) in (let TMP_35 \def (Bind Abbr) in (let TMP_36 \def (CHead d1 
TMP_35 u) in (let TMP_37 \def (clear_gen_bind b x0 TMP_36 t H6) in (let H7 
\def (f_equal C C TMP_30 TMP_32 TMP_34 TMP_37) in (let TMP_38 \def (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow 
(match k0 with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_39 \def (Bind Abbr) in (let TMP_40 \def (CHead d1 TMP_39 u) in (let 
TMP_41 \def (Bind b) in (let TMP_42 \def (CHead x0 TMP_41 t) in (let TMP_43 
\def (Bind Abbr) in (let TMP_44 \def (CHead d1 TMP_43 u) in (let TMP_45 \def 
(clear_gen_bind b x0 TMP_44 t H6) in (let H8 \def (f_equal C B TMP_38 TMP_40 
TMP_42 TMP_45) in (let TMP_46 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_47 \def (Bind 
Abbr) in (let TMP_48 \def (CHead d1 TMP_47 u) in (let TMP_49 \def (Bind b) in 
(let TMP_50 \def (CHead x0 TMP_49 t) in (let TMP_51 \def (Bind Abbr) in (let 
TMP_52 \def (CHead d1 TMP_51 u) in (let TMP_53 \def (clear_gen_bind b x0 
TMP_52 t H6) in (let H9 \def (f_equal C T TMP_46 TMP_48 TMP_50 TMP_53) in 
(let TMP_84 \def (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 
x0)).(\lambda (c2: C).(\lambda (H12: (csubt g c1 c2)).(let TMP_56 \def 
(\lambda (t0: T).(let TMP_54 \def (Bind b) in (let TMP_55 \def (CHead x0 
TMP_54 t0) in (drop n O c1 TMP_55)))) in (let H13 \def (eq_ind_r T t TMP_56 
H5 u H9) in (let TMP_59 \def (\lambda (b0: B).(let TMP_57 \def (Bind b0) in 
(let TMP_58 \def (CHead x0 TMP_57 u) in (drop n O c1 TMP_58)))) in (let H14 
\def (eq_ind_r B b TMP_59 H13 Abbr H10) in (let TMP_62 \def (\lambda (c: 
C).(let TMP_60 \def (Bind Abbr) in (let TMP_61 \def (CHead c TMP_60 u) in 
(drop n O c1 TMP_61)))) in (let H15 \def (eq_ind_r C x0 TMP_62 H14 d1 H11) in 
(let TMP_63 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_66 \def 
(\lambda (d2: C).(let TMP_64 \def (Bind Abbr) in (let TMP_65 \def (CHead d2 
TMP_64 u) in (drop n O c2 TMP_65)))) in (let TMP_67 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_70 \def (\lambda (d2: C).(let TMP_68 \def 
(Bind Abbr) in (let TMP_69 \def (CHead d2 TMP_68 u) in (getl n c2 TMP_69)))) 
in (let TMP_71 \def (ex2 C TMP_67 TMP_70) in (let TMP_82 \def (\lambda (x1: 
C).(\lambda (H16: (csubt g d1 x1)).(\lambda (H17: (drop n O c2 (CHead x1 
(Bind Abbr) u))).(let TMP_72 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_75 \def (\lambda (d2: C).(let TMP_73 \def (Bind Abbr) in (let TMP_74 \def 
(CHead d2 TMP_73 u) in (getl n c2 TMP_74)))) in (let TMP_76 \def (Bind Abbr) 
in (let TMP_77 \def (CHead x1 TMP_76 u) in (let TMP_78 \def (Bind Abbr) in 
(let TMP_79 \def (CHead x1 TMP_78 u) in (let TMP_80 \def (clear_bind Abbr x1 
u) in (let TMP_81 \def (getl_intro n c2 TMP_77 TMP_79 H17 TMP_80) in 
(ex_intro2 C TMP_72 TMP_75 x1 H16 TMP_81)))))))))))) in (let TMP_83 \def 
(csubt_drop_abbr g n c1 c2 H12 d1 u H15) in (ex2_ind C TMP_63 TMP_66 TMP_71 
TMP_82 TMP_83)))))))))))))))))) in (let TMP_85 \def (TMP_84 H8) in (TMP_85 
H7))))))))))))))))))))))))))))))))) in (let TMP_207 \def (\lambda (f: 
F).(\lambda (H5: (drop n O c1 (CHead x0 (Flat f) t))).(\lambda (H6: (clear 
(CHead x0 (Flat f) t) (CHead d1 (Bind Abbr) u))).(let H7 \def H5 in (let 
TMP_91 \def (\lambda (c: C).((drop n O c (CHead x0 (Flat f) t)) \to (\forall 
(c2: C).((csubt g c c2) \to (let TMP_87 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_90 \def (\lambda (d2: C).(let TMP_88 \def (Bind Abbr) in 
(let TMP_89 \def (CHead d2 TMP_88 u) in (getl n c2 TMP_89)))) in (ex2 C 
TMP_87 TMP_90))))))) in (let TMP_96 \def (\lambda (n0: nat).(\forall (x1: 
C).((drop n0 O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csubt g x1 
c2) \to (let TMP_92 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_95 
\def (\lambda (d2: C).(let TMP_93 \def (Bind Abbr) in (let TMP_94 \def (CHead 
d2 TMP_93 u) in (getl n0 c2 TMP_94)))) in (ex2 C TMP_92 TMP_95)))))))) in 
(let TMP_143 \def (\lambda (x1: C).(\lambda (H8: (drop O O x1 (CHead x0 (Flat 
f) t))).(\lambda (c2: C).(\lambda (H9: (csubt g x1 c2)).(let TMP_97 \def 
(\lambda (c: C).(csubt g c c2)) in (let TMP_98 \def (Flat f) in (let TMP_99 
\def (CHead x0 TMP_98 t) in (let TMP_100 \def (Flat f) in (let TMP_101 \def 
(CHead x0 TMP_100 t) in (let TMP_102 \def (drop_gen_refl x1 TMP_101 H8) in 
(let H10 \def (eq_ind C x1 TMP_97 H9 TMP_99 TMP_102) in (let TMP_103 \def 
(Bind Abbr) in (let TMP_104 \def (CHead d1 TMP_103 u) in (let TMP_105 \def 
(Bind Abbr) in (let TMP_106 \def (CHead d1 TMP_105 u) in (let TMP_107 \def 
(clear_gen_flat f x0 TMP_106 t H6) in (let H_y \def (clear_flat x0 TMP_104 
TMP_107 f t) in (let TMP_108 \def (Flat f) in (let TMP_109 \def (CHead x0 
TMP_108 t) in (let TMP_110 \def (Bind Abbr) in (let TMP_111 \def (CHead d1 
TMP_110 u) in (let H11 \def (csubt_clear_conf g TMP_109 c2 H10 TMP_111 H_y) 
in (let TMP_114 \def (\lambda (e2: C).(let TMP_112 \def (Bind Abbr) in (let 
TMP_113 \def (CHead d1 TMP_112 u) in (csubt g TMP_113 e2)))) in (let TMP_115 
\def (\lambda (e2: C).(clear c2 e2)) in (let TMP_116 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_119 \def (\lambda (d2: C).(let TMP_117 \def 
(Bind Abbr) in (let TMP_118 \def (CHead d2 TMP_117 u) in (getl O c2 
TMP_118)))) in (let TMP_120 \def (ex2 C TMP_116 TMP_119) in (let TMP_142 \def 
(\lambda (x2: C).(\lambda (H12: (csubt g (CHead d1 (Bind Abbr) u) 
x2)).(\lambda (H13: (clear c2 x2)).(let H14 \def (csubt_gen_abbr g d1 x2 u 
H12) in (let TMP_123 \def (\lambda (e2: C).(let TMP_121 \def (Bind Abbr) in 
(let TMP_122 \def (CHead e2 TMP_121 u) in (eq C x2 TMP_122)))) in (let 
TMP_124 \def (\lambda (e2: C).(csubt g d1 e2)) in (let TMP_125 \def (\lambda 
(d2: C).(csubt g d1 d2)) in (let TMP_128 \def (\lambda (d2: C).(let TMP_126 
\def (Bind Abbr) in (let TMP_127 \def (CHead d2 TMP_126 u) in (getl O c2 
TMP_127)))) in (let TMP_129 \def (ex2 C TMP_125 TMP_128) in (let TMP_141 \def 
(\lambda (x3: C).(\lambda (H15: (eq C x2 (CHead x3 (Bind Abbr) u))).(\lambda 
(H16: (csubt g d1 x3)).(let TMP_130 \def (\lambda (c: C).(clear c2 c)) in 
(let TMP_131 \def (Bind Abbr) in (let TMP_132 \def (CHead x3 TMP_131 u) in 
(let H17 \def (eq_ind C x2 TMP_130 H13 TMP_132 H15) in (let TMP_133 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_136 \def (\lambda (d2: C).(let 
TMP_134 \def (Bind Abbr) in (let TMP_135 \def (CHead d2 TMP_134 u) in (getl O 
c2 TMP_135)))) in (let TMP_137 \def (Bind Abbr) in (let TMP_138 \def (CHead 
x3 TMP_137 u) in (let TMP_139 \def (drop_refl c2) in (let TMP_140 \def 
(getl_intro O c2 TMP_138 c2 TMP_139 H17) in (ex_intro2 C TMP_133 TMP_136 x3 
H16 TMP_140)))))))))))))) in (ex2_ind C TMP_123 TMP_124 TMP_129 TMP_141 
H14))))))))))) in (ex2_ind C TMP_114 TMP_115 TMP_120 TMP_142 
H11))))))))))))))))))))))))))))) in (let TMP_205 \def (\lambda (n0: 
nat).(\lambda (H8: ((\forall (x1: C).((drop n0 O x1 (CHead x0 (Flat f) t)) 
\to (\forall (c2: C).((csubt g x1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abbr) u)))))))))).(\lambda 
(x1: C).(\lambda (H9: (drop (S n0) O x1 (CHead x0 (Flat f) t))).(\lambda (c2: 
C).(\lambda (H10: (csubt g x1 c2)).(let TMP_144 \def (Flat f) in (let TMP_145 
\def (CHead x0 TMP_144 t) in (let H11 \def (drop_clear x1 TMP_145 n0 H9) in 
(let TMP_148 \def (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(let 
TMP_146 \def (Bind b) in (let TMP_147 \def (CHead e TMP_146 v) in (clear x1 
TMP_147)))))) in (let TMP_151 \def (\lambda (_: B).(\lambda (e: C).(\lambda 
(_: T).(let TMP_149 \def (Flat f) in (let TMP_150 \def (CHead x0 TMP_149 t) 
in (drop n0 O e TMP_150)))))) in (let TMP_152 \def (\lambda (d2: C).(csubt g 
d1 d2)) in (let TMP_156 \def (\lambda (d2: C).(let TMP_153 \def (S n0) in 
(let TMP_154 \def (Bind Abbr) in (let TMP_155 \def (CHead d2 TMP_154 u) in 
(getl TMP_153 c2 TMP_155))))) in (let TMP_157 \def (ex2 C TMP_152 TMP_156) in 
(let TMP_204 \def (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda 
(H12: (clear x1 (CHead x3 (Bind x2) x4))).(\lambda (H13: (drop n0 O x3 (CHead 
x0 (Flat f) t))).(let TMP_158 \def (Bind x2) in (let TMP_159 \def (CHead x3 
TMP_158 x4) in (let H14 \def (csubt_clear_conf g x1 c2 H10 TMP_159 H12) in 
(let TMP_162 \def (\lambda (e2: C).(let TMP_160 \def (Bind x2) in (let 
TMP_161 \def (CHead x3 TMP_160 x4) in (csubt g TMP_161 e2)))) in (let TMP_163 
\def (\lambda (e2: C).(clear c2 e2)) in (let TMP_164 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_168 \def (\lambda (d2: C).(let TMP_165 \def 
(S n0) in (let TMP_166 \def (Bind Abbr) in (let TMP_167 \def (CHead d2 
TMP_166 u) in (getl TMP_165 c2 TMP_167))))) in (let TMP_169 \def (ex2 C 
TMP_164 TMP_168) in (let TMP_203 \def (\lambda (x5: C).(\lambda (H15: (csubt 
g (CHead x3 (Bind x2) x4) x5)).(\lambda (H16: (clear c2 x5)).(let H17 \def 
(csubt_gen_bind g x2 x3 x5 x4 H15) in (let TMP_172 \def (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_170 \def (Bind b2) in (let 
TMP_171 \def (CHead e2 TMP_170 v2) in (eq C x5 TMP_171)))))) in (let TMP_173 
\def (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g x3 e2)))) in 
(let TMP_174 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_178 \def 
(\lambda (d2: C).(let TMP_175 \def (S n0) in (let TMP_176 \def (Bind Abbr) in 
(let TMP_177 \def (CHead d2 TMP_176 u) in (getl TMP_175 c2 TMP_177))))) in 
(let TMP_179 \def (ex2 C TMP_174 TMP_178) in (let TMP_202 \def (\lambda (x6: 
B).(\lambda (x7: C).(\lambda (x8: T).(\lambda (H18: (eq C x5 (CHead x7 (Bind 
x6) x8))).(\lambda (H19: (csubt g x3 x7)).(let TMP_180 \def (\lambda (c: 
C).(clear c2 c)) in (let TMP_181 \def (Bind x6) in (let TMP_182 \def (CHead 
x7 TMP_181 x8) in (let H20 \def (eq_ind C x5 TMP_180 H16 TMP_182 H18) in (let 
H21 \def (H8 x3 H13 x7 H19) in (let TMP_183 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_186 \def (\lambda (d2: C).(let TMP_184 \def (Bind Abbr) in 
(let TMP_185 \def (CHead d2 TMP_184 u) in (getl n0 x7 TMP_185)))) in (let 
TMP_187 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_191 \def (\lambda 
(d2: C).(let TMP_188 \def (S n0) in (let TMP_189 \def (Bind Abbr) in (let 
TMP_190 \def (CHead d2 TMP_189 u) in (getl TMP_188 c2 TMP_190))))) in (let 
TMP_192 \def (ex2 C TMP_187 TMP_191) in (let TMP_201 \def (\lambda (x9: 
C).(\lambda (H22: (csubt g d1 x9)).(\lambda (H23: (getl n0 x7 (CHead x9 (Bind 
Abbr) u))).(let TMP_193 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_197 \def (\lambda (d2: C).(let TMP_194 \def (S n0) in (let TMP_195 \def 
(Bind Abbr) in (let TMP_196 \def (CHead d2 TMP_195 u) in (getl TMP_194 c2 
TMP_196))))) in (let TMP_198 \def (Bind Abbr) in (let TMP_199 \def (CHead x9 
TMP_198 u) in (let TMP_200 \def (getl_clear_bind x6 c2 x7 x8 H20 TMP_199 n0 
H23) in (ex_intro2 C TMP_193 TMP_197 x9 H22 TMP_200))))))))) in (ex2_ind C 
TMP_183 TMP_186 TMP_192 TMP_201 H21))))))))))))))))) in (ex2_3_ind B C T 
TMP_172 TMP_173 TMP_179 TMP_202 H17))))))))))) in (ex2_ind C TMP_162 TMP_163 
TMP_169 TMP_203 H14))))))))))))))) in (ex2_3_ind B C T TMP_148 TMP_151 
TMP_157 TMP_204 H11)))))))))))))))) in (let TMP_206 \def (nat_ind TMP_96 
TMP_143 TMP_205 n) in (unintro C c1 TMP_91 TMP_206 H7)))))))))) in (K_ind 
TMP_29 TMP_86 TMP_207 k H3 H4)))))))))) in (C_ind TMP_16 TMP_24 TMP_208 x H1 
H2))))))) in (ex2_ind C TMP_3 TMP_6 TMP_11 TMP_209 H0))))))))))))).

theorem csubt_getl_abst:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (t: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csubt g 
c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (t: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abst) t))).(let TMP_1 \def 
(Bind Abst) in (let TMP_2 \def (CHead d1 TMP_1 t) in (let H0 \def 
(getl_gen_all c1 TMP_2 n H) in (let TMP_3 \def (\lambda (e: C).(drop n O c1 
e)) in (let TMP_6 \def (\lambda (e: C).(let TMP_4 \def (Bind Abst) in (let 
TMP_5 \def (CHead d1 TMP_4 t) in (clear e TMP_5)))) in (let TMP_19 \def 
(\forall (c2: C).((csubt g c1 c2) \to (let TMP_7 \def (\lambda (d2: C).(csubt 
g d1 d2)) in (let TMP_10 \def (\lambda (d2: C).(let TMP_8 \def (Bind Abst) in 
(let TMP_9 \def (CHead d2 TMP_8 t) in (getl n c2 TMP_9)))) in (let TMP_11 
\def (ex2 C TMP_7 TMP_10) in (let TMP_12 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_15 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_13 \def (Bind Abbr) in (let TMP_14 \def (CHead d2 TMP_13 u) in 
(getl n c2 TMP_14))))) in (let TMP_16 \def (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) in (let TMP_17 \def (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t))) in (let TMP_18 \def (ex4_2 C T TMP_12 TMP_15 TMP_16 TMP_17) in 
(or TMP_11 TMP_18))))))))))) in (let TMP_579 \def (\lambda (x: C).(\lambda 
(H1: (drop n O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind Abst) t))).(let 
TMP_32 \def (\lambda (c: C).((drop n O c1 c) \to ((clear c (CHead d1 (Bind 
Abst) t)) \to (\forall (c2: C).((csubt g c1 c2) \to (let TMP_20 \def (\lambda 
(d2: C).(csubt g d1 d2)) in (let TMP_23 \def (\lambda (d2: C).(let TMP_21 
\def (Bind Abst) in (let TMP_22 \def (CHead d2 TMP_21 t) in (getl n c2 
TMP_22)))) in (let TMP_24 \def (ex2 C TMP_20 TMP_23) in (let TMP_25 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_28 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_26 \def (Bind Abbr) in (let TMP_27 
\def (CHead d2 TMP_26 u) in (getl n c2 TMP_27))))) in (let TMP_29 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_30 \def (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_31 \def (ex4_2 C T 
TMP_25 TMP_28 TMP_29 TMP_30) in (or TMP_24 TMP_31)))))))))))))) in (let 
TMP_48 \def (\lambda (n0: nat).(\lambda (_: (drop n O c1 (CSort 
n0))).(\lambda (H4: (clear (CSort n0) (CHead d1 (Bind Abst) t))).(let TMP_33 
\def (Bind Abst) in (let TMP_34 \def (CHead d1 TMP_33 t) in (let TMP_47 \def 
(\forall (c2: C).((csubt g c1 c2) \to (let TMP_35 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_38 \def (\lambda (d2: C).(let TMP_36 \def 
(Bind Abst) in (let TMP_37 \def (CHead d2 TMP_36 t) in (getl n c2 TMP_37)))) 
in (let TMP_39 \def (ex2 C TMP_35 TMP_38) in (let TMP_40 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_43 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_41 \def (Bind Abbr) in (let TMP_42 \def (CHead d2 
TMP_41 u) in (getl n c2 TMP_42))))) in (let TMP_44 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_45 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_46 \def (ex4_2 C T TMP_40 
TMP_43 TMP_44 TMP_45) in (or TMP_39 TMP_46))))))))))) in (clear_gen_sort 
TMP_34 n0 H4 TMP_47))))))) in (let TMP_578 \def (\lambda (x0: C).(\lambda (_: 
(((drop n O c1 x0) \to ((clear x0 (CHead d1 (Bind Abst) t)) \to (\forall (c2: 
C).((csubt g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))).(\lambda (k: 
K).(\lambda (t0: T).(\lambda (H3: (drop n O c1 (CHead x0 k t0))).(\lambda 
(H4: (clear (CHead x0 k t0) (CHead d1 (Bind Abst) t))).(let TMP_61 \def 
(\lambda (k0: K).((drop n O c1 (CHead x0 k0 t0)) \to ((clear (CHead x0 k0 t0) 
(CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csubt g c1 c2) \to (let 
TMP_49 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_52 \def (\lambda 
(d2: C).(let TMP_50 \def (Bind Abst) in (let TMP_51 \def (CHead d2 TMP_50 t) 
in (getl n c2 TMP_51)))) in (let TMP_53 \def (ex2 C TMP_49 TMP_52) in (let 
TMP_54 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_57 
\def (\lambda (d2: C).(\lambda (u: T).(let TMP_55 \def (Bind Abbr) in (let 
TMP_56 \def (CHead d2 TMP_55 u) in (getl n c2 TMP_56))))) in (let TMP_58 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_59 \def (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_60 \def (ex4_2 C T 
TMP_54 TMP_57 TMP_58 TMP_59) in (or TMP_53 TMP_60)))))))))))))) in (let 
TMP_211 \def (\lambda (b: B).(\lambda (H5: (drop n O c1 (CHead x0 (Bind b) 
t0))).(\lambda (H6: (clear (CHead x0 (Bind b) t0) (CHead d1 (Bind Abst) 
t))).(let TMP_62 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow d1 
| (CHead c _ _) \Rightarrow c])) in (let TMP_63 \def (Bind Abst) in (let 
TMP_64 \def (CHead d1 TMP_63 t) in (let TMP_65 \def (Bind b) in (let TMP_66 
\def (CHead x0 TMP_65 t0) in (let TMP_67 \def (Bind Abst) in (let TMP_68 \def 
(CHead d1 TMP_67 t) in (let TMP_69 \def (clear_gen_bind b x0 TMP_68 t0 H6) in 
(let H7 \def (f_equal C C TMP_62 TMP_64 TMP_66 TMP_69) in (let TMP_70 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow Abst | (CHead _ k0 _) 
\Rightarrow (match k0 with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
Abst])])) in (let TMP_71 \def (Bind Abst) in (let TMP_72 \def (CHead d1 
TMP_71 t) in (let TMP_73 \def (Bind b) in (let TMP_74 \def (CHead x0 TMP_73 
t0) in (let TMP_75 \def (Bind Abst) in (let TMP_76 \def (CHead d1 TMP_75 t) 
in (let TMP_77 \def (clear_gen_bind b x0 TMP_76 t0 H6) in (let H8 \def 
(f_equal C B TMP_70 TMP_72 TMP_74 TMP_77) in (let TMP_78 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow t | (CHead _ _ t1) \Rightarrow t1])) 
in (let TMP_79 \def (Bind Abst) in (let TMP_80 \def (CHead d1 TMP_79 t) in 
(let TMP_81 \def (Bind b) in (let TMP_82 \def (CHead x0 TMP_81 t0) in (let 
TMP_83 \def (Bind Abst) in (let TMP_84 \def (CHead d1 TMP_83 t) in (let 
TMP_85 \def (clear_gen_bind b x0 TMP_84 t0 H6) in (let H9 \def (f_equal C T 
TMP_78 TMP_80 TMP_82 TMP_85) in (let TMP_209 \def (\lambda (H10: (eq B Abst 
b)).(\lambda (H11: (eq C d1 x0)).(\lambda (c2: C).(\lambda (H12: (csubt g c1 
c2)).(let TMP_88 \def (\lambda (t1: T).(let TMP_86 \def (Bind b) in (let 
TMP_87 \def (CHead x0 TMP_86 t1) in (drop n O c1 TMP_87)))) in (let H13 \def 
(eq_ind_r T t0 TMP_88 H5 t H9) in (let TMP_91 \def (\lambda (b0: B).(let 
TMP_89 \def (Bind b0) in (let TMP_90 \def (CHead x0 TMP_89 t) in (drop n O c1 
TMP_90)))) in (let H14 \def (eq_ind_r B b TMP_91 H13 Abst H10) in (let TMP_94 
\def (\lambda (c: C).(let TMP_92 \def (Bind Abst) in (let TMP_93 \def (CHead 
c TMP_92 t) in (drop n O c1 TMP_93)))) in (let H15 \def (eq_ind_r C x0 TMP_94 
H14 d1 H11) in (let TMP_95 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_98 \def (\lambda (d2: C).(let TMP_96 \def (Bind Abst) in (let TMP_97 \def 
(CHead d2 TMP_96 t) in (drop n O c2 TMP_97)))) in (let TMP_99 \def (ex2 C 
TMP_95 TMP_98) in (let TMP_100 \def (\lambda (d2: C).(\lambda (_: T).(csubt g 
d1 d2))) in (let TMP_103 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_101 
\def (Bind Abbr) in (let TMP_102 \def (CHead d2 TMP_101 u) in (drop n O c2 
TMP_102))))) in (let TMP_104 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) in (let TMP_105 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) 
in (let TMP_106 \def (ex4_2 C T TMP_100 TMP_103 TMP_104 TMP_105) in (let 
TMP_107 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_110 \def (\lambda 
(d2: C).(let TMP_108 \def (Bind Abst) in (let TMP_109 \def (CHead d2 TMP_108 
t) in (getl n c2 TMP_109)))) in (let TMP_111 \def (ex2 C TMP_107 TMP_110) in 
(let TMP_112 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_115 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_113 \def (Bind Abbr) 
in (let TMP_114 \def (CHead d2 TMP_113 u) in (getl n c2 TMP_114))))) in (let 
TMP_116 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_117 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_118 \def 
(ex4_2 C T TMP_112 TMP_115 TMP_116 TMP_117) in (let TMP_119 \def (or TMP_111 
TMP_118) in (let TMP_161 \def (\lambda (H16: (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) t))))).(let 
TMP_120 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_123 \def (\lambda 
(d2: C).(let TMP_121 \def (Bind Abst) in (let TMP_122 \def (CHead d2 TMP_121 
t) in (drop n O c2 TMP_122)))) in (let TMP_124 \def (\lambda (d2: C).(csubt g 
d1 d2)) in (let TMP_127 \def (\lambda (d2: C).(let TMP_125 \def (Bind Abst) 
in (let TMP_126 \def (CHead d2 TMP_125 t) in (getl n c2 TMP_126)))) in (let 
TMP_128 \def (ex2 C TMP_124 TMP_127) in (let TMP_129 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_132 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_130 \def (Bind Abbr) in (let TMP_131 \def (CHead 
d2 TMP_130 u) in (getl n c2 TMP_131))))) in (let TMP_133 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_134 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_135 \def (ex4_2 C T TMP_129 
TMP_132 TMP_133 TMP_134) in (let TMP_136 \def (or TMP_128 TMP_135) in (let 
TMP_160 \def (\lambda (x1: C).(\lambda (H17: (csubt g d1 x1)).(\lambda (H18: 
(drop n O c2 (CHead x1 (Bind Abst) t))).(let TMP_137 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_140 \def (\lambda (d2: C).(let TMP_138 \def 
(Bind Abst) in (let TMP_139 \def (CHead d2 TMP_138 t) in (getl n c2 
TMP_139)))) in (let TMP_141 \def (ex2 C TMP_137 TMP_140) in (let TMP_142 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_145 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_143 \def (Bind Abbr) in (let 
TMP_144 \def (CHead d2 TMP_143 u) in (getl n c2 TMP_144))))) in (let TMP_146 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_147 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_148 \def (ex4_2 
C T TMP_142 TMP_145 TMP_146 TMP_147) in (let TMP_149 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_152 \def (\lambda (d2: C).(let TMP_150 \def 
(Bind Abst) in (let TMP_151 \def (CHead d2 TMP_150 t) in (getl n c2 
TMP_151)))) in (let TMP_153 \def (Bind Abst) in (let TMP_154 \def (CHead x1 
TMP_153 t) in (let TMP_155 \def (Bind Abst) in (let TMP_156 \def (CHead x1 
TMP_155 t) in (let TMP_157 \def (clear_bind Abst x1 t) in (let TMP_158 \def 
(getl_intro n c2 TMP_154 TMP_156 H18 TMP_157) in (let TMP_159 \def (ex_intro2 
C TMP_149 TMP_152 x1 H17 TMP_158) in (or_introl TMP_141 TMP_148 
TMP_159))))))))))))))))))))) in (ex2_ind C TMP_120 TMP_123 TMP_136 TMP_160 
H16)))))))))))))) in (let TMP_207 \def (\lambda (H16: (ex4_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(let 
TMP_162 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_165 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_163 \def (Bind Abbr) 
in (let TMP_164 \def (CHead d2 TMP_163 u) in (drop n O c2 TMP_164))))) in 
(let TMP_166 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let 
TMP_167 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let 
TMP_168 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_171 \def (\lambda 
(d2: C).(let TMP_169 \def (Bind Abst) in (let TMP_170 \def (CHead d2 TMP_169 
t) in (getl n c2 TMP_170)))) in (let TMP_172 \def (ex2 C TMP_168 TMP_171) in 
(let TMP_173 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_176 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_174 \def (Bind Abbr) 
in (let TMP_175 \def (CHead d2 TMP_174 u) in (getl n c2 TMP_175))))) in (let 
TMP_177 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_178 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_179 \def 
(ex4_2 C T TMP_173 TMP_176 TMP_177 TMP_178) in (let TMP_180 \def (or TMP_172 
TMP_179) in (let TMP_206 \def (\lambda (x1: C).(\lambda (x2: T).(\lambda 
(H17: (csubt g d1 x1)).(\lambda (H18: (drop n O c2 (CHead x1 (Bind Abbr) 
x2))).(\lambda (H19: (ty3 g d1 x2 t)).(\lambda (H20: (ty3 g x1 x2 t)).(let 
TMP_181 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_184 \def (\lambda 
(d2: C).(let TMP_182 \def (Bind Abst) in (let TMP_183 \def (CHead d2 TMP_182 
t) in (getl n c2 TMP_183)))) in (let TMP_185 \def (ex2 C TMP_181 TMP_184) in 
(let TMP_186 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_189 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_187 \def (Bind Abbr) 
in (let TMP_188 \def (CHead d2 TMP_187 u) in (getl n c2 TMP_188))))) in (let 
TMP_190 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_191 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_192 \def 
(ex4_2 C T TMP_186 TMP_189 TMP_190 TMP_191) in (let TMP_193 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_196 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_194 \def (Bind Abbr) in (let TMP_195 \def (CHead 
d2 TMP_194 u) in (getl n c2 TMP_195))))) in (let TMP_197 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_198 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_199 \def (Bind Abbr) in (let 
TMP_200 \def (CHead x1 TMP_199 x2) in (let TMP_201 \def (Bind Abbr) in (let 
TMP_202 \def (CHead x1 TMP_201 x2) in (let TMP_203 \def (clear_bind Abbr x1 
x2) in (let TMP_204 \def (getl_intro n c2 TMP_200 TMP_202 H18 TMP_203) in 
(let TMP_205 \def (ex4_2_intro C T TMP_193 TMP_196 TMP_197 TMP_198 x1 x2 H17 
TMP_204 H19 H20) in (or_intror TMP_185 TMP_192 
TMP_205)))))))))))))))))))))))))) in (ex4_2_ind C T TMP_162 TMP_165 TMP_166 
TMP_167 TMP_180 TMP_206 H16)))))))))))))))) in (let TMP_208 \def 
(csubt_drop_abst g n c1 c2 H12 d1 t H15) in (or_ind TMP_99 TMP_106 TMP_119 
TMP_161 TMP_207 TMP_208))))))))))))))))))))))))))))))) in (let TMP_210 \def 
(TMP_209 H8) in (TMP_210 H7))))))))))))))))))))))))))))))))) in (let TMP_577 
\def (\lambda (f: F).(\lambda (H5: (drop n O c1 (CHead x0 (Flat f) 
t0))).(\lambda (H6: (clear (CHead x0 (Flat f) t0) (CHead d1 (Bind Abst) 
t))).(let H7 \def H5 in (let TMP_224 \def (\lambda (c: C).((drop n O c (CHead 
x0 (Flat f) t0)) \to (\forall (c2: C).((csubt g c c2) \to (let TMP_212 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_215 \def (\lambda (d2: C).(let 
TMP_213 \def (Bind Abst) in (let TMP_214 \def (CHead d2 TMP_213 t) in (getl n 
c2 TMP_214)))) in (let TMP_216 \def (ex2 C TMP_212 TMP_215) in (let TMP_217 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_220 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_218 \def (Bind Abbr) in (let 
TMP_219 \def (CHead d2 TMP_218 u) in (getl n c2 TMP_219))))) in (let TMP_221 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_222 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_223 \def (ex4_2 
C T TMP_217 TMP_220 TMP_221 TMP_222) in (or TMP_216 TMP_223))))))))))))) in 
(let TMP_237 \def (\lambda (n0: nat).(\forall (x1: C).((drop n0 O x1 (CHead 
x0 (Flat f) t0)) \to (\forall (c2: C).((csubt g x1 c2) \to (let TMP_225 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_228 \def (\lambda (d2: C).(let 
TMP_226 \def (Bind Abst) in (let TMP_227 \def (CHead d2 TMP_226 t) in (getl 
n0 c2 TMP_227)))) in (let TMP_229 \def (ex2 C TMP_225 TMP_228) in (let 
TMP_230 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_233 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_231 \def (Bind Abbr) 
in (let TMP_232 \def (CHead d2 TMP_231 u) in (getl n0 c2 TMP_232))))) in (let 
TMP_234 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_235 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_236 \def 
(ex4_2 C T TMP_230 TMP_233 TMP_234 TMP_235) in (or TMP_229 
TMP_236)))))))))))))) in (let TMP_386 \def (\lambda (x1: C).(\lambda (H8: 
(drop O O x1 (CHead x0 (Flat f) t0))).(\lambda (c2: C).(\lambda (H9: (csubt g 
x1 c2)).(let TMP_238 \def (\lambda (c: C).(csubt g c c2)) in (let TMP_239 
\def (Flat f) in (let TMP_240 \def (CHead x0 TMP_239 t0) in (let TMP_241 \def 
(Flat f) in (let TMP_242 \def (CHead x0 TMP_241 t0) in (let TMP_243 \def 
(drop_gen_refl x1 TMP_242 H8) in (let H10 \def (eq_ind C x1 TMP_238 H9 
TMP_240 TMP_243) in (let TMP_244 \def (Bind Abst) in (let TMP_245 \def (CHead 
d1 TMP_244 t) in (let TMP_246 \def (Bind Abst) in (let TMP_247 \def (CHead d1 
TMP_246 t) in (let TMP_248 \def (clear_gen_flat f x0 TMP_247 t0 H6) in (let 
H_y \def (clear_flat x0 TMP_245 TMP_248 f t0) in (let TMP_249 \def (Flat f) 
in (let TMP_250 \def (CHead x0 TMP_249 t0) in (let TMP_251 \def (Bind Abst) 
in (let TMP_252 \def (CHead d1 TMP_251 t) in (let H11 \def (csubt_clear_conf 
g TMP_250 c2 H10 TMP_252 H_y) in (let TMP_255 \def (\lambda (e2: C).(let 
TMP_253 \def (Bind Abst) in (let TMP_254 \def (CHead d1 TMP_253 t) in (csubt 
g TMP_254 e2)))) in (let TMP_256 \def (\lambda (e2: C).(clear c2 e2)) in (let 
TMP_257 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_260 \def (\lambda 
(d2: C).(let TMP_258 \def (Bind Abst) in (let TMP_259 \def (CHead d2 TMP_258 
t) in (getl O c2 TMP_259)))) in (let TMP_261 \def (ex2 C TMP_257 TMP_260) in 
(let TMP_262 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_265 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_263 \def (Bind Abbr) 
in (let TMP_264 \def (CHead d2 TMP_263 u) in (getl O c2 TMP_264))))) in (let 
TMP_266 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_267 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_268 \def 
(ex4_2 C T TMP_262 TMP_265 TMP_266 TMP_267) in (let TMP_269 \def (or TMP_261 
TMP_268) in (let TMP_385 \def (\lambda (x2: C).(\lambda (H12: (csubt g (CHead 
d1 (Bind Abst) t) x2)).(\lambda (H13: (clear c2 x2)).(let H14 \def 
(csubt_gen_abst g d1 x2 t H12) in (let TMP_272 \def (\lambda (e2: C).(let 
TMP_270 \def (Bind Abst) in (let TMP_271 \def (CHead e2 TMP_270 t) in (eq C 
x2 TMP_271)))) in (let TMP_273 \def (\lambda (e2: C).(csubt g d1 e2)) in (let 
TMP_274 \def (ex2 C TMP_272 TMP_273) in (let TMP_277 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_275 \def (Bind Abbr) in (let TMP_276 \def (CHead 
e2 TMP_275 v2) in (eq C x2 TMP_276))))) in (let TMP_278 \def (\lambda (e2: 
C).(\lambda (_: T).(csubt g d1 e2))) in (let TMP_279 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g d1 v2 t))) in (let TMP_280 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 t))) in (let TMP_281 \def (ex4_2 C T TMP_277 
TMP_278 TMP_279 TMP_280) in (let TMP_282 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_285 \def (\lambda (d2: C).(let TMP_283 \def (Bind Abst) in 
(let TMP_284 \def (CHead d2 TMP_283 t) in (getl O c2 TMP_284)))) in (let 
TMP_286 \def (ex2 C TMP_282 TMP_285) in (let TMP_287 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_290 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_288 \def (Bind Abbr) in (let TMP_289 \def (CHead 
d2 TMP_288 u) in (getl O c2 TMP_289))))) in (let TMP_291 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_292 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_293 \def (ex4_2 C T TMP_287 
TMP_290 TMP_291 TMP_292) in (let TMP_294 \def (or TMP_286 TMP_293) in (let 
TMP_337 \def (\lambda (H15: (ex2 C (\lambda (e2: C).(eq C x2 (CHead e2 (Bind 
Abst) t))) (\lambda (e2: C).(csubt g d1 e2)))).(let TMP_297 \def (\lambda 
(e2: C).(let TMP_295 \def (Bind Abst) in (let TMP_296 \def (CHead e2 TMP_295 
t) in (eq C x2 TMP_296)))) in (let TMP_298 \def (\lambda (e2: C).(csubt g d1 
e2)) in (let TMP_299 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_302 
\def (\lambda (d2: C).(let TMP_300 \def (Bind Abst) in (let TMP_301 \def 
(CHead d2 TMP_300 t) in (getl O c2 TMP_301)))) in (let TMP_303 \def (ex2 C 
TMP_299 TMP_302) in (let TMP_304 \def (\lambda (d2: C).(\lambda (_: T).(csubt 
g d1 d2))) in (let TMP_307 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_305 
\def (Bind Abbr) in (let TMP_306 \def (CHead d2 TMP_305 u) in (getl O c2 
TMP_306))))) in (let TMP_308 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) in (let TMP_309 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) 
in (let TMP_310 \def (ex4_2 C T TMP_304 TMP_307 TMP_308 TMP_309) in (let 
TMP_311 \def (or TMP_303 TMP_310) in (let TMP_336 \def (\lambda (x3: 
C).(\lambda (H16: (eq C x2 (CHead x3 (Bind Abst) t))).(\lambda (H17: (csubt g 
d1 x3)).(let TMP_312 \def (\lambda (c: C).(clear c2 c)) in (let TMP_313 \def 
(Bind Abst) in (let TMP_314 \def (CHead x3 TMP_313 t) in (let H18 \def 
(eq_ind C x2 TMP_312 H13 TMP_314 H16) in (let TMP_315 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_318 \def (\lambda (d2: C).(let TMP_316 \def 
(Bind Abst) in (let TMP_317 \def (CHead d2 TMP_316 t) in (getl O c2 
TMP_317)))) in (let TMP_319 \def (ex2 C TMP_315 TMP_318) in (let TMP_320 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_323 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_321 \def (Bind Abbr) in (let 
TMP_322 \def (CHead d2 TMP_321 u) in (getl O c2 TMP_322))))) in (let TMP_324 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_325 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_326 \def (ex4_2 
C T TMP_320 TMP_323 TMP_324 TMP_325) in (let TMP_327 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_330 \def (\lambda (d2: C).(let TMP_328 \def 
(Bind Abst) in (let TMP_329 \def (CHead d2 TMP_328 t) in (getl O c2 
TMP_329)))) in (let TMP_331 \def (Bind Abst) in (let TMP_332 \def (CHead x3 
TMP_331 t) in (let TMP_333 \def (drop_refl c2) in (let TMP_334 \def 
(getl_intro O c2 TMP_332 c2 TMP_333 H18) in (let TMP_335 \def (ex_intro2 C 
TMP_327 TMP_330 x3 H17 TMP_334) in (or_introl TMP_319 TMP_326 
TMP_335))))))))))))))))))))))) in (ex2_ind C TMP_297 TMP_298 TMP_311 TMP_336 
H15)))))))))))))) in (let TMP_384 \def (\lambda (H15: (ex4_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C x2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g d1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
d1 v2 t))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))))).(let TMP_340 
\def (\lambda (e2: C).(\lambda (v2: T).(let TMP_338 \def (Bind Abbr) in (let 
TMP_339 \def (CHead e2 TMP_338 v2) in (eq C x2 TMP_339))))) in (let TMP_341 
\def (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) in (let TMP_342 \def 
(\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) in (let TMP_343 \def 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))) in (let TMP_344 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_347 \def (\lambda (d2: C).(let 
TMP_345 \def (Bind Abst) in (let TMP_346 \def (CHead d2 TMP_345 t) in (getl O 
c2 TMP_346)))) in (let TMP_348 \def (ex2 C TMP_344 TMP_347) in (let TMP_349 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_352 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_350 \def (Bind Abbr) in (let 
TMP_351 \def (CHead d2 TMP_350 u) in (getl O c2 TMP_351))))) in (let TMP_353 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_354 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_355 \def (ex4_2 
C T TMP_349 TMP_352 TMP_353 TMP_354) in (let TMP_356 \def (or TMP_348 
TMP_355) in (let TMP_383 \def (\lambda (x3: C).(\lambda (x4: T).(\lambda 
(H16: (eq C x2 (CHead x3 (Bind Abbr) x4))).(\lambda (H17: (csubt g d1 
x3)).(\lambda (H18: (ty3 g d1 x4 t)).(\lambda (H19: (ty3 g x3 x4 t)).(let 
TMP_357 \def (\lambda (c: C).(clear c2 c)) in (let TMP_358 \def (Bind Abbr) 
in (let TMP_359 \def (CHead x3 TMP_358 x4) in (let H20 \def (eq_ind C x2 
TMP_357 H13 TMP_359 H16) in (let TMP_360 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_363 \def (\lambda (d2: C).(let TMP_361 \def (Bind Abst) in 
(let TMP_362 \def (CHead d2 TMP_361 t) in (getl O c2 TMP_362)))) in (let 
TMP_364 \def (ex2 C TMP_360 TMP_363) in (let TMP_365 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_368 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_366 \def (Bind Abbr) in (let TMP_367 \def (CHead 
d2 TMP_366 u) in (getl O c2 TMP_367))))) in (let TMP_369 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_370 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_371 \def (ex4_2 C T TMP_365 
TMP_368 TMP_369 TMP_370) in (let TMP_372 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_375 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_373 \def (Bind Abbr) in (let TMP_374 \def (CHead d2 TMP_373 u) in 
(getl O c2 TMP_374))))) in (let TMP_376 \def (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) in (let TMP_377 \def (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))) in (let TMP_378 \def (Bind Abbr) in (let TMP_379 \def 
(CHead x3 TMP_378 x4) in (let TMP_380 \def (drop_refl c2) in (let TMP_381 
\def (getl_intro O c2 TMP_379 c2 TMP_380 H20) in (let TMP_382 \def 
(ex4_2_intro C T TMP_372 TMP_375 TMP_376 TMP_377 x3 x4 H17 TMP_381 H18 H19) 
in (or_intror TMP_364 TMP_371 TMP_382)))))))))))))))))))))))))))) in 
(ex4_2_ind C T TMP_340 TMP_341 TMP_342 TMP_343 TMP_356 TMP_383 
H15)))))))))))))))) in (or_ind TMP_274 TMP_281 TMP_294 TMP_337 TMP_384 
H14)))))))))))))))))))))))) in (ex2_ind C TMP_255 TMP_256 TMP_269 TMP_385 
H11))))))))))))))))))))))))))))))))))) in (let TMP_575 \def (\lambda (n0: 
nat).(\lambda (H8: ((\forall (x1: C).((drop n0 O x1 (CHead x0 (Flat f) t0)) 
\to (\forall (c2: C).((csubt g x1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n0 c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))))))))).(\lambda (x1: C).(\lambda (H9: (drop (S n0) O x1 (CHead x0 (Flat 
f) t0))).(\lambda (c2: C).(\lambda (H10: (csubt g x1 c2)).(let TMP_387 \def 
(Flat f) in (let TMP_388 \def (CHead x0 TMP_387 t0) in (let H11 \def 
(drop_clear x1 TMP_388 n0 H9) in (let TMP_391 \def (\lambda (b: B).(\lambda 
(e: C).(\lambda (v: T).(let TMP_389 \def (Bind b) in (let TMP_390 \def (CHead 
e TMP_389 v) in (clear x1 TMP_390)))))) in (let TMP_394 \def (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(let TMP_392 \def (Flat f) in (let TMP_393 
\def (CHead x0 TMP_392 t0) in (drop n0 O e TMP_393)))))) in (let TMP_395 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_399 \def (\lambda (d2: C).(let 
TMP_396 \def (S n0) in (let TMP_397 \def (Bind Abst) in (let TMP_398 \def 
(CHead d2 TMP_397 t) in (getl TMP_396 c2 TMP_398))))) in (let TMP_400 \def 
(ex2 C TMP_395 TMP_399) in (let TMP_401 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_405 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_402 \def (S n0) in (let TMP_403 \def (Bind Abbr) in (let TMP_404 
\def (CHead d2 TMP_403 u) in (getl TMP_402 c2 TMP_404)))))) in (let TMP_406 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_407 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_408 \def (ex4_2 
C T TMP_401 TMP_405 TMP_406 TMP_407) in (let TMP_409 \def (or TMP_400 
TMP_408) in (let TMP_574 \def (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: 
T).(\lambda (H12: (clear x1 (CHead x3 (Bind x2) x4))).(\lambda (H13: (drop n0 
O x3 (CHead x0 (Flat f) t0))).(let TMP_410 \def (Bind x2) in (let TMP_411 
\def (CHead x3 TMP_410 x4) in (let H14 \def (csubt_clear_conf g x1 c2 H10 
TMP_411 H12) in (let TMP_414 \def (\lambda (e2: C).(let TMP_412 \def (Bind 
x2) in (let TMP_413 \def (CHead x3 TMP_412 x4) in (csubt g TMP_413 e2)))) in 
(let TMP_415 \def (\lambda (e2: C).(clear c2 e2)) in (let TMP_416 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_420 \def (\lambda (d2: C).(let 
TMP_417 \def (S n0) in (let TMP_418 \def (Bind Abst) in (let TMP_419 \def 
(CHead d2 TMP_418 t) in (getl TMP_417 c2 TMP_419))))) in (let TMP_421 \def 
(ex2 C TMP_416 TMP_420) in (let TMP_422 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_426 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_423 \def (S n0) in (let TMP_424 \def (Bind Abbr) in (let TMP_425 
\def (CHead d2 TMP_424 u) in (getl TMP_423 c2 TMP_425)))))) in (let TMP_427 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_428 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_429 \def (ex4_2 
C T TMP_422 TMP_426 TMP_427 TMP_428) in (let TMP_430 \def (or TMP_421 
TMP_429) in (let TMP_573 \def (\lambda (x5: C).(\lambda (H15: (csubt g (CHead 
x3 (Bind x2) x4) x5)).(\lambda (H16: (clear c2 x5)).(let H17 \def 
(csubt_gen_bind g x2 x3 x5 x4 H15) in (let TMP_433 \def (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_431 \def (Bind b2) in (let 
TMP_432 \def (CHead e2 TMP_431 v2) in (eq C x5 TMP_432)))))) in (let TMP_434 
\def (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g x3 e2)))) in 
(let TMP_435 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_439 \def 
(\lambda (d2: C).(let TMP_436 \def (S n0) in (let TMP_437 \def (Bind Abst) in 
(let TMP_438 \def (CHead d2 TMP_437 t) in (getl TMP_436 c2 TMP_438))))) in 
(let TMP_440 \def (ex2 C TMP_435 TMP_439) in (let TMP_441 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_445 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_442 \def (S n0) in (let TMP_443 \def (Bind Abbr) 
in (let TMP_444 \def (CHead d2 TMP_443 u) in (getl TMP_442 c2 TMP_444)))))) 
in (let TMP_446 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let 
TMP_447 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let 
TMP_448 \def (ex4_2 C T TMP_441 TMP_445 TMP_446 TMP_447) in (let TMP_449 \def 
(or TMP_440 TMP_448) in (let TMP_572 \def (\lambda (x6: B).(\lambda (x7: 
C).(\lambda (x8: T).(\lambda (H18: (eq C x5 (CHead x7 (Bind x6) 
x8))).(\lambda (H19: (csubt g x3 x7)).(let TMP_450 \def (\lambda (c: 
C).(clear c2 c)) in (let TMP_451 \def (Bind x6) in (let TMP_452 \def (CHead 
x7 TMP_451 x8) in (let H20 \def (eq_ind C x5 TMP_450 H16 TMP_452 H18) in (let 
H21 \def (H8 x3 H13 x7 H19) in (let TMP_453 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_456 \def (\lambda (d2: C).(let TMP_454 \def (Bind Abst) in 
(let TMP_455 \def (CHead d2 TMP_454 t) in (getl n0 x7 TMP_455)))) in (let 
TMP_457 \def (ex2 C TMP_453 TMP_456) in (let TMP_458 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_461 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_459 \def (Bind Abbr) in (let TMP_460 \def (CHead 
d2 TMP_459 u) in (getl n0 x7 TMP_460))))) in (let TMP_462 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_463 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_464 \def (ex4_2 C T TMP_458 
TMP_461 TMP_462 TMP_463) in (let TMP_465 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_469 \def (\lambda (d2: C).(let TMP_466 \def (S n0) in (let 
TMP_467 \def (Bind Abst) in (let TMP_468 \def (CHead d2 TMP_467 t) in (getl 
TMP_466 c2 TMP_468))))) in (let TMP_470 \def (ex2 C TMP_465 TMP_469) in (let 
TMP_471 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_475 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_472 \def (S n0) in 
(let TMP_473 \def (Bind Abbr) in (let TMP_474 \def (CHead d2 TMP_473 u) in 
(getl TMP_472 c2 TMP_474)))))) in (let TMP_476 \def (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) in (let TMP_477 \def (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))) in (let TMP_478 \def (ex4_2 C T TMP_471 TMP_475 TMP_476 
TMP_477) in (let TMP_479 \def (or TMP_470 TMP_478) in (let TMP_523 \def 
(\lambda (H22: (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n0 x7 (CHead d2 (Bind Abst) t))))).(let TMP_480 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_483 \def (\lambda (d2: C).(let TMP_481 \def 
(Bind Abst) in (let TMP_482 \def (CHead d2 TMP_481 t) in (getl n0 x7 
TMP_482)))) in (let TMP_484 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_488 \def (\lambda (d2: C).(let TMP_485 \def (S n0) in (let TMP_486 \def 
(Bind Abst) in (let TMP_487 \def (CHead d2 TMP_486 t) in (getl TMP_485 c2 
TMP_487))))) in (let TMP_489 \def (ex2 C TMP_484 TMP_488) in (let TMP_490 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_494 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_491 \def (S n0) in (let TMP_492 
\def (Bind Abbr) in (let TMP_493 \def (CHead d2 TMP_492 u) in (getl TMP_491 
c2 TMP_493)))))) in (let TMP_495 \def (\lambda (_: C).(\lambda (u: T).(ty3 g 
d1 u t))) in (let TMP_496 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))) in (let TMP_497 \def (ex4_2 C T TMP_490 TMP_494 TMP_495 TMP_496) in (let 
TMP_498 \def (or TMP_489 TMP_497) in (let TMP_522 \def (\lambda (x9: 
C).(\lambda (H23: (csubt g d1 x9)).(\lambda (H24: (getl n0 x7 (CHead x9 (Bind 
Abst) t))).(let TMP_499 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_503 \def (\lambda (d2: C).(let TMP_500 \def (S n0) in (let TMP_501 \def 
(Bind Abst) in (let TMP_502 \def (CHead d2 TMP_501 t) in (getl TMP_500 c2 
TMP_502))))) in (let TMP_504 \def (ex2 C TMP_499 TMP_503) in (let TMP_505 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_509 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_506 \def (S n0) in (let TMP_507 
\def (Bind Abbr) in (let TMP_508 \def (CHead d2 TMP_507 u) in (getl TMP_506 
c2 TMP_508)))))) in (let TMP_510 \def (\lambda (_: C).(\lambda (u: T).(ty3 g 
d1 u t))) in (let TMP_511 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))) in (let TMP_512 \def (ex4_2 C T TMP_505 TMP_509 TMP_510 TMP_511) in (let 
TMP_513 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_517 \def (\lambda 
(d2: C).(let TMP_514 \def (S n0) in (let TMP_515 \def (Bind Abst) in (let 
TMP_516 \def (CHead d2 TMP_515 t) in (getl TMP_514 c2 TMP_516))))) in (let 
TMP_518 \def (Bind Abst) in (let TMP_519 \def (CHead x9 TMP_518 t) in (let 
TMP_520 \def (getl_clear_bind x6 c2 x7 x8 H20 TMP_519 n0 H24) in (let TMP_521 
\def (ex_intro2 C TMP_513 TMP_517 x9 H23 TMP_520) in (or_introl TMP_504 
TMP_512 TMP_521)))))))))))))))))) in (ex2_ind C TMP_480 TMP_483 TMP_498 
TMP_522 H22)))))))))))))) in (let TMP_571 \def (\lambda (H22: (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n0 x7 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(let 
TMP_524 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_527 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_525 \def (Bind Abbr) 
in (let TMP_526 \def (CHead d2 TMP_525 u) in (getl n0 x7 TMP_526))))) in (let 
TMP_528 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_529 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_530 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_534 \def (\lambda (d2: C).(let 
TMP_531 \def (S n0) in (let TMP_532 \def (Bind Abst) in (let TMP_533 \def 
(CHead d2 TMP_532 t) in (getl TMP_531 c2 TMP_533))))) in (let TMP_535 \def 
(ex2 C TMP_530 TMP_534) in (let TMP_536 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_540 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_537 \def (S n0) in (let TMP_538 \def (Bind Abbr) in (let TMP_539 
\def (CHead d2 TMP_538 u) in (getl TMP_537 c2 TMP_539)))))) in (let TMP_541 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_542 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_543 \def (ex4_2 
C T TMP_536 TMP_540 TMP_541 TMP_542) in (let TMP_544 \def (or TMP_535 
TMP_543) in (let TMP_570 \def (\lambda (x9: C).(\lambda (x10: T).(\lambda 
(H23: (csubt g d1 x9)).(\lambda (H24: (getl n0 x7 (CHead x9 (Bind Abbr) 
x10))).(\lambda (H25: (ty3 g d1 x10 t)).(\lambda (H26: (ty3 g x9 x10 t)).(let 
TMP_545 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_549 \def (\lambda 
(d2: C).(let TMP_546 \def (S n0) in (let TMP_547 \def (Bind Abst) in (let 
TMP_548 \def (CHead d2 TMP_547 t) in (getl TMP_546 c2 TMP_548))))) in (let 
TMP_550 \def (ex2 C TMP_545 TMP_549) in (let TMP_551 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_555 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_552 \def (S n0) in (let TMP_553 \def (Bind Abbr) 
in (let TMP_554 \def (CHead d2 TMP_553 u) in (getl TMP_552 c2 TMP_554)))))) 
in (let TMP_556 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let 
TMP_557 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let 
TMP_558 \def (ex4_2 C T TMP_551 TMP_555 TMP_556 TMP_557) in (let TMP_559 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_563 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_560 \def (S n0) in (let TMP_561 
\def (Bind Abbr) in (let TMP_562 \def (CHead d2 TMP_561 u) in (getl TMP_560 
c2 TMP_562)))))) in (let TMP_564 \def (\lambda (_: C).(\lambda (u: T).(ty3 g 
d1 u t))) in (let TMP_565 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))) in (let TMP_566 \def (Bind Abbr) in (let TMP_567 \def (CHead x9 TMP_566 
x10) in (let TMP_568 \def (getl_clear_bind x6 c2 x7 x8 H20 TMP_567 n0 H24) in 
(let TMP_569 \def (ex4_2_intro C T TMP_559 TMP_563 TMP_564 TMP_565 x9 x10 H23 
TMP_568 H25 H26) in (or_intror TMP_550 TMP_558 TMP_569))))))))))))))))))))))) 
in (ex4_2_ind C T TMP_524 TMP_527 TMP_528 TMP_529 TMP_544 TMP_570 
H22)))))))))))))))) in (or_ind TMP_457 TMP_464 TMP_479 TMP_523 TMP_571 
H21)))))))))))))))))))))))))))))) in (ex2_3_ind B C T TMP_433 TMP_434 TMP_449 
TMP_572 H17))))))))))))))))) in (ex2_ind C TMP_414 TMP_415 TMP_430 TMP_573 
H14))))))))))))))))))))) in (ex2_3_ind B C T TMP_391 TMP_394 TMP_409 TMP_574 
H11)))))))))))))))))))))) in (let TMP_576 \def (nat_ind TMP_237 TMP_386 
TMP_575 n) in (unintro C c1 TMP_224 TMP_576 H7)))))))))) in (K_ind TMP_61 
TMP_211 TMP_577 k H3 H4)))))))))) in (C_ind TMP_32 TMP_48 TMP_578 x H1 
H2))))))) in (ex2_ind C TMP_3 TMP_6 TMP_19 TMP_579 H0))))))))))))).

