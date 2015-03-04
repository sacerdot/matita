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

include "basic_1/ex2/defs.ma".

include "basic_1/nf2/defs.ma".

include "basic_1/pr2/fwd.ma".

include "basic_1/arity/fwd.ma".

theorem ex2_nf2:
 nf2 ex2_c ex2_t
\def
 \lambda (t2: T).(\lambda (H: (pr2 (CSort O) (THead (Flat Appl) (TSort O) 
(TSort O)) t2)).(let TMP_1 \def (CSort O) in (let TMP_2 \def (TSort O) in 
(let TMP_3 \def (TSort O) in (let H0 \def (pr2_gen_appl TMP_1 TMP_2 TMP_3 t2 
H) in (let TMP_6 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_4 \def (Flat 
Appl) in (let TMP_5 \def (THead TMP_4 u2 t3) in (eq T t2 TMP_5))))) in (let 
TMP_9 \def (\lambda (u2: T).(\lambda (_: T).(let TMP_7 \def (CSort O) in (let 
TMP_8 \def (TSort O) in (pr2 TMP_7 TMP_8 u2))))) in (let TMP_12 \def (\lambda 
(_: T).(\lambda (t3: T).(let TMP_10 \def (CSort O) in (let TMP_11 \def (TSort 
O) in (pr2 TMP_10 TMP_11 t3))))) in (let TMP_13 \def (ex3_2 T T TMP_6 TMP_9 
TMP_12) in (let TMP_17 \def (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(let TMP_14 \def (TSort O) in (let TMP_15 \def (Bind Abst) 
in (let TMP_16 \def (THead TMP_15 y1 z1) in (eq T TMP_14 TMP_16)))))))) in 
(let TMP_20 \def (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(let TMP_18 \def (Bind Abbr) in (let TMP_19 \def (THead TMP_18 u2 t3) 
in (eq T t2 TMP_19))))))) in (let TMP_23 \def (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(let TMP_21 \def (CSort O) in (let TMP_22 
\def (TSort O) in (pr2 TMP_21 TMP_22 u2))))))) in (let TMP_27 \def (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u: T).(let TMP_24 \def (CSort O) in (let TMP_25 \def (Bind b) in 
(let TMP_26 \def (CHead TMP_24 TMP_25 u) in (pr2 TMP_26 z1 t3)))))))))) in 
(let TMP_28 \def (ex4_4 T T T T TMP_17 TMP_20 TMP_23 TMP_27) in (let TMP_30 
\def (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(let TMP_29 \def (eq B b Abst) in (not TMP_29)))))))) 
in (let TMP_34 \def (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(let TMP_31 \def (TSort O) 
in (let TMP_32 \def (Bind b) in (let TMP_33 \def (THead TMP_32 y1 z1) in (eq 
T TMP_31 TMP_33)))))))))) in (let TMP_41 \def (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(let 
TMP_35 \def (Bind b) in (let TMP_36 \def (Flat Appl) in (let TMP_37 \def (S 
O) in (let TMP_38 \def (lift TMP_37 O u2) in (let TMP_39 \def (THead TMP_36 
TMP_38 z2) in (let TMP_40 \def (THead TMP_35 y2 TMP_39) in (eq T t2 
TMP_40))))))))))))) in (let TMP_44 \def (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(let 
TMP_42 \def (CSort O) in (let TMP_43 \def (TSort O) in (pr2 TMP_42 TMP_43 
u2))))))))) in (let TMP_46 \def (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(let TMP_45 \def (CSort 
O) in (pr2 TMP_45 y1 y2)))))))) in (let TMP_50 \def (\lambda (b: B).(\lambda 
(_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: 
T).(let TMP_47 \def (CSort O) in (let TMP_48 \def (Bind b) in (let TMP_49 
\def (CHead TMP_47 TMP_48 y2) in (pr2 TMP_49 z1 z2)))))))))) in (let TMP_51 
\def (ex6_6 B T T T T T TMP_30 TMP_34 TMP_41 TMP_44 TMP_46 TMP_50) in (let 
TMP_52 \def (Flat Appl) in (let TMP_53 \def (TSort O) in (let TMP_54 \def 
(TSort O) in (let TMP_55 \def (THead TMP_52 TMP_53 TMP_54) in (let TMP_56 
\def (eq T TMP_55 t2) in (let TMP_99 \def (\lambda (H1: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 (CSort O) (TSort O) t3))))).(let TMP_59 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_57 \def (Flat Appl) in (let TMP_58 \def (THead 
TMP_57 u2 t3) in (eq T t2 TMP_58))))) in (let TMP_62 \def (\lambda (u2: 
T).(\lambda (_: T).(let TMP_60 \def (CSort O) in (let TMP_61 \def (TSort O) 
in (pr2 TMP_60 TMP_61 u2))))) in (let TMP_65 \def (\lambda (_: T).(\lambda 
(t3: T).(let TMP_63 \def (CSort O) in (let TMP_64 \def (TSort O) in (pr2 
TMP_63 TMP_64 t3))))) in (let TMP_66 \def (Flat Appl) in (let TMP_67 \def 
(TSort O) in (let TMP_68 \def (TSort O) in (let TMP_69 \def (THead TMP_66 
TMP_67 TMP_68) in (let TMP_70 \def (eq T TMP_69 t2) in (let TMP_98 \def 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H2: (eq T t2 (THead (Flat Appl) 
x0 x1))).(\lambda (H3: (pr2 (CSort O) (TSort O) x0)).(\lambda (H4: (pr2 
(CSort O) (TSort O) x1)).(let TMP_73 \def (\lambda (t: T).(let TMP_71 \def 
(Flat Appl) in (let TMP_72 \def (THead TMP_71 x0 t) in (eq T t2 TMP_72)))) in 
(let TMP_74 \def (TSort O) in (let TMP_75 \def (CSort O) in (let TMP_76 \def 
(pr2_gen_sort TMP_75 x1 O H4) in (let H5 \def (eq_ind T x1 TMP_73 H2 TMP_74 
TMP_76) in (let TMP_80 \def (\lambda (t: T).(let TMP_77 \def (Flat Appl) in 
(let TMP_78 \def (TSort O) in (let TMP_79 \def (THead TMP_77 t TMP_78) in (eq 
T t2 TMP_79))))) in (let TMP_81 \def (TSort O) in (let TMP_82 \def (CSort O) 
in (let TMP_83 \def (pr2_gen_sort TMP_82 x0 O H3) in (let H6 \def (eq_ind T 
x0 TMP_80 H5 TMP_81 TMP_83) in (let TMP_84 \def (Flat Appl) in (let TMP_85 
\def (TSort O) in (let TMP_86 \def (TSort O) in (let TMP_87 \def (THead 
TMP_84 TMP_85 TMP_86) in (let TMP_92 \def (\lambda (t: T).(let TMP_88 \def 
(Flat Appl) in (let TMP_89 \def (TSort O) in (let TMP_90 \def (TSort O) in 
(let TMP_91 \def (THead TMP_88 TMP_89 TMP_90) in (eq T TMP_91 t)))))) in (let 
TMP_93 \def (Flat Appl) in (let TMP_94 \def (TSort O) in (let TMP_95 \def 
(TSort O) in (let TMP_96 \def (THead TMP_93 TMP_94 TMP_95) in (let TMP_97 
\def (refl_equal T TMP_96) in (eq_ind_r T TMP_87 TMP_92 TMP_97 t2 
H6)))))))))))))))))))))))))) in (ex3_2_ind T T TMP_59 TMP_62 TMP_65 TMP_70 
TMP_98 H1))))))))))) in (let TMP_147 \def (\lambda (H1: (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TSort O) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 (CSort 
O) (TSort O) u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead (CSort O) 
(Bind b) u) z1 t3))))))))).(let TMP_103 \def (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(let TMP_100 \def (TSort O) in (let 
TMP_101 \def (Bind Abst) in (let TMP_102 \def (THead TMP_101 y1 z1) in (eq T 
TMP_100 TMP_102)))))))) in (let TMP_106 \def (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(let TMP_104 \def (Bind Abbr) in (let 
TMP_105 \def (THead TMP_104 u2 t3) in (eq T t2 TMP_105))))))) in (let TMP_109 
\def (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(let 
TMP_107 \def (CSort O) in (let TMP_108 \def (TSort O) in (pr2 TMP_107 TMP_108 
u2))))))) in (let TMP_113 \def (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(let TMP_110 \def (CSort 
O) in (let TMP_111 \def (Bind b) in (let TMP_112 \def (CHead TMP_110 TMP_111 
u) in (pr2 TMP_112 z1 t3)))))))))) in (let TMP_114 \def (Flat Appl) in (let 
TMP_115 \def (TSort O) in (let TMP_116 \def (TSort O) in (let TMP_117 \def 
(THead TMP_114 TMP_115 TMP_116) in (let TMP_118 \def (eq T TMP_117 t2) in 
(let TMP_146 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H2: (eq T (TSort O) (THead (Bind Abst) x0 x1))).(\lambda 
(H3: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (H4: (pr2 (CSort O) (TSort 
O) x2)).(\lambda (_: ((\forall (b: B).(\forall (u: T).(pr2 (CHead (CSort O) 
(Bind b) u) x1 x3))))).(let TMP_121 \def (\lambda (t: T).(let TMP_119 \def 
(Bind Abbr) in (let TMP_120 \def (THead TMP_119 t x3) in (eq T t2 TMP_120)))) 
in (let TMP_122 \def (TSort O) in (let TMP_123 \def (CSort O) in (let TMP_124 
\def (pr2_gen_sort TMP_123 x2 O H4) in (let H6 \def (eq_ind T x2 TMP_121 H3 
TMP_122 TMP_124) in (let TMP_125 \def (Bind Abbr) in (let TMP_126 \def (TSort 
O) in (let TMP_127 \def (THead TMP_125 TMP_126 x3) in (let TMP_132 \def 
(\lambda (t: T).(let TMP_128 \def (Flat Appl) in (let TMP_129 \def (TSort O) 
in (let TMP_130 \def (TSort O) in (let TMP_131 \def (THead TMP_128 TMP_129 
TMP_130) in (eq T TMP_131 t)))))) in (let TMP_133 \def (TSort O) in (let 
TMP_134 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let 
TMP_135 \def (Bind Abst) in (let TMP_136 \def (THead TMP_135 x0 x1) in (let 
H7 \def (eq_ind T TMP_133 TMP_134 I TMP_136 H2) in (let TMP_137 \def (Flat 
Appl) in (let TMP_138 \def (TSort O) in (let TMP_139 \def (TSort O) in (let 
TMP_140 \def (THead TMP_137 TMP_138 TMP_139) in (let TMP_141 \def (Bind Abbr) 
in (let TMP_142 \def (TSort O) in (let TMP_143 \def (THead TMP_141 TMP_142 
x3) in (let TMP_144 \def (eq T TMP_140 TMP_143) in (let TMP_145 \def 
(False_ind TMP_144 H7) in (eq_ind_r T TMP_127 TMP_132 TMP_145 t2 
H6)))))))))))))))))))))))))))))))) in (ex4_4_ind T T T T TMP_103 TMP_106 
TMP_109 TMP_113 TMP_118 TMP_146 H1)))))))))))) in (let TMP_215 \def (\lambda 
(H1: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (TSort O) (THead (Bind b) y1 z1)))))))) (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: 
T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S 
O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 (CSort O) y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead (CSort O) (Bind b) y2) z1 z2))))))))).(let TMP_149 \def (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(let TMP_148 \def (eq B b Abst) in (not TMP_148)))))))) in (let 
TMP_153 \def (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(let TMP_150 \def (TSort O) in (let 
TMP_151 \def (Bind b) in (let TMP_152 \def (THead TMP_151 y1 z1) in (eq T 
TMP_150 TMP_152)))))))))) in (let TMP_160 \def (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(let 
TMP_154 \def (Bind b) in (let TMP_155 \def (Flat Appl) in (let TMP_156 \def 
(S O) in (let TMP_157 \def (lift TMP_156 O u2) in (let TMP_158 \def (THead 
TMP_155 TMP_157 z2) in (let TMP_159 \def (THead TMP_154 y2 TMP_158) in (eq T 
t2 TMP_159))))))))))))) in (let TMP_163 \def (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(let 
TMP_161 \def (CSort O) in (let TMP_162 \def (TSort O) in (pr2 TMP_161 TMP_162 
u2))))))))) in (let TMP_165 \def (\lambda (_: B).(\lambda (y1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(let TMP_164 \def 
(CSort O) in (pr2 TMP_164 y1 y2)))))))) in (let TMP_169 \def (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(let TMP_166 \def (CSort O) in (let TMP_167 \def (Bind b) in (let 
TMP_168 \def (CHead TMP_166 TMP_167 y2) in (pr2 TMP_168 z1 z2)))))))))) in 
(let TMP_170 \def (Flat Appl) in (let TMP_171 \def (TSort O) in (let TMP_172 
\def (TSort O) in (let TMP_173 \def (THead TMP_170 TMP_171 TMP_172) in (let 
TMP_174 \def (eq T TMP_173 t2) in (let TMP_214 \def (\lambda (x0: B).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (_: (not (eq B x0 Abst))).(\lambda (H3: (eq T (TSort O) (THead 
(Bind x0) x1 x2))).(\lambda (H4: (eq T t2 (THead (Bind x0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3)))).(\lambda (H5: (pr2 (CSort O) (TSort O) 
x4)).(\lambda (H6: (pr2 (CSort O) x1 x5)).(\lambda (_: (pr2 (CHead (CSort O) 
(Bind x0) x5) x2 x3)).(let H_y \def (pr2_gen_csort x1 x5 O H6) in (let 
TMP_181 \def (\lambda (t: T).(let TMP_175 \def (Bind x0) in (let TMP_176 \def 
(Flat Appl) in (let TMP_177 \def (S O) in (let TMP_178 \def (lift TMP_177 O 
t) in (let TMP_179 \def (THead TMP_176 TMP_178 x3) in (let TMP_180 \def 
(THead TMP_175 x5 TMP_179) in (eq T t2 TMP_180)))))))) in (let TMP_182 \def 
(TSort O) in (let TMP_183 \def (CSort O) in (let TMP_184 \def (pr2_gen_sort 
TMP_183 x4 O H5) in (let H8 \def (eq_ind T x4 TMP_181 H4 TMP_182 TMP_184) in 
(let TMP_185 \def (Bind x0) in (let TMP_186 \def (Flat Appl) in (let TMP_187 
\def (S O) in (let TMP_188 \def (TSort O) in (let TMP_189 \def (lift TMP_187 
O TMP_188) in (let TMP_190 \def (THead TMP_186 TMP_189 x3) in (let TMP_191 
\def (THead TMP_185 x5 TMP_190) in (let TMP_196 \def (\lambda (t: T).(let 
TMP_192 \def (Flat Appl) in (let TMP_193 \def (TSort O) in (let TMP_194 \def 
(TSort O) in (let TMP_195 \def (THead TMP_192 TMP_193 TMP_194) in (eq T 
TMP_195 t)))))) in (let TMP_197 \def (TSort O) in (let TMP_198 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow 
False | (THead _ _ _) \Rightarrow False])) in (let TMP_199 \def (Bind x0) in 
(let TMP_200 \def (THead TMP_199 x1 x2) in (let H9 \def (eq_ind T TMP_197 
TMP_198 I TMP_200 H3) in (let TMP_201 \def (Flat Appl) in (let TMP_202 \def 
(TSort O) in (let TMP_203 \def (TSort O) in (let TMP_204 \def (THead TMP_201 
TMP_202 TMP_203) in (let TMP_205 \def (Bind x0) in (let TMP_206 \def (Flat 
Appl) in (let TMP_207 \def (S O) in (let TMP_208 \def (TSort O) in (let 
TMP_209 \def (lift TMP_207 O TMP_208) in (let TMP_210 \def (THead TMP_206 
TMP_209 x3) in (let TMP_211 \def (THead TMP_205 x5 TMP_210) in (let TMP_212 
\def (eq T TMP_204 TMP_211) in (let TMP_213 \def (False_ind TMP_212 H9) in 
(eq_ind_r T TMP_191 TMP_196 TMP_213 t2 
H8))))))))))))))))))))))))))))))))))))))))))))) in (ex6_6_ind B T T T T T 
TMP_149 TMP_153 TMP_160 TMP_163 TMP_165 TMP_169 TMP_174 TMP_214 
H1)))))))))))))) in (or3_ind TMP_13 TMP_28 TMP_51 TMP_56 TMP_99 TMP_147 
TMP_215 H0)))))))))))))))))))))))))))))).

theorem ex2_arity:
 \forall (g: G).(\forall (a: A).((arity g ex2_c ex2_t a) \to (\forall (P: 
Prop).P)))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (H: (arity g (CSort O) (THead (Flat 
Appl) (TSort O) (TSort O)) a)).(\lambda (P: Prop).(let TMP_1 \def (CSort O) 
in (let TMP_2 \def (TSort O) in (let TMP_3 \def (TSort O) in (let H0 \def 
(arity_gen_appl g TMP_1 TMP_2 TMP_3 a H) in (let TMP_6 \def (\lambda (a1: 
A).(let TMP_4 \def (CSort O) in (let TMP_5 \def (TSort O) in (arity g TMP_4 
TMP_5 a1)))) in (let TMP_10 \def (\lambda (a1: A).(let TMP_7 \def (CSort O) 
in (let TMP_8 \def (TSort O) in (let TMP_9 \def (AHead a1 a) in (arity g 
TMP_7 TMP_8 TMP_9))))) in (let TMP_24 \def (\lambda (x: A).(\lambda (_: 
(arity g (CSort O) (TSort O) x)).(\lambda (H2: (arity g (CSort O) (TSort O) 
(AHead x a))).(let TMP_11 \def (ASort O O) in (let TMP_12 \def (CSort O) in 
(let TMP_13 \def (AHead x a) in (let TMP_14 \def (arity_gen_sort g TMP_12 O 
TMP_13 H2) in (let H_x \def (leq_gen_head1 g x a TMP_11 TMP_14) in (let H3 
\def H_x in (let TMP_15 \def (\lambda (a3: A).(\lambda (_: A).(leq g x a3))) 
in (let TMP_16 \def (\lambda (_: A).(\lambda (a4: A).(leq g a a4))) in (let 
TMP_19 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_17 \def (ASort O O) in 
(let TMP_18 \def (AHead a3 a4) in (eq A TMP_17 TMP_18))))) in (let TMP_23 
\def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g x x0)).(\lambda 
(_: (leq g a x1)).(\lambda (H6: (eq A (ASort O O) (AHead x0 x1))).(let TMP_20 
\def (ASort O O) in (let TMP_21 \def (\lambda (ee: A).(match ee with [(ASort 
_ _) \Rightarrow True | (AHead _ _) \Rightarrow False])) in (let TMP_22 \def 
(AHead x0 x1) in (let H7 \def (eq_ind A TMP_20 TMP_21 I TMP_22 H6) in 
(False_ind P H7)))))))))) in (ex3_2_ind A A TMP_15 TMP_16 TMP_19 P TMP_23 
H3)))))))))))))) in (ex2_ind A TMP_6 TMP_10 P TMP_24 H0))))))))))).

