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

include "basic_1/csubc/fwd.ma".

include "basic_1/clear/fwd.ma".

theorem csubc_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).((clear c1 e1) \to (\forall 
(c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda 
(e2: C).(csubc g e1 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (e1: C).(\lambda (H: (clear c1 
e1)).(let TMP_3 \def (\lambda (c: C).(\lambda (c0: C).(\forall (c2: 
C).((csubc g c c2) \to (let TMP_1 \def (\lambda (e2: C).(clear c2 e2)) in 
(let TMP_2 \def (\lambda (e2: C).(csubc g c0 e2)) in (ex2 C TMP_1 
TMP_2))))))) in (let TMP_157 \def (\lambda (b: B).(\lambda (e: C).(\lambda 
(u: T).(\lambda (c2: C).(\lambda (H0: (csubc g (CHead e (Bind b) u) c2)).(let 
TMP_4 \def (Bind b) in (let H_x \def (csubc_gen_head_l g e c2 u TMP_4 H0) in 
(let H1 \def H_x in (let TMP_7 \def (\lambda (c3: C).(let TMP_5 \def (Bind b) 
in (let TMP_6 \def (CHead c3 TMP_5 u) in (eq C c2 TMP_6)))) in (let TMP_8 
\def (\lambda (c3: C).(csubc g e c3)) in (let TMP_9 \def (ex2 C TMP_7 TMP_8) 
in (let TMP_12 \def (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(let 
TMP_10 \def (Bind b) in (let TMP_11 \def (Bind Abst) in (eq K TMP_10 
TMP_11)))))) in (let TMP_15 \def (\lambda (c3: C).(\lambda (w: T).(\lambda 
(_: A).(let TMP_13 \def (Bind Abbr) in (let TMP_14 \def (CHead c3 TMP_13 w) 
in (eq C c2 TMP_14)))))) in (let TMP_16 \def (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g e c3)))) in (let TMP_18 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(let TMP_17 \def (asucc g a) in (sc3 g 
TMP_17 e u))))) in (let TMP_19 \def (\lambda (c3: C).(\lambda (w: T).(\lambda 
(a: A).(sc3 g a c3 w)))) in (let TMP_20 \def (ex5_3 C T A TMP_12 TMP_15 
TMP_16 TMP_18 TMP_19) in (let TMP_23 \def (\lambda (b0: B).(\lambda (c3: 
C).(\lambda (v2: T).(let TMP_21 \def (Bind b0) in (let TMP_22 \def (CHead c3 
TMP_21 v2) in (eq C c2 TMP_22)))))) in (let TMP_26 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(let TMP_24 \def (Bind b) in (let TMP_25 
\def (Bind Void) in (eq K TMP_24 TMP_25)))))) in (let TMP_28 \def (\lambda 
(b0: B).(\lambda (_: C).(\lambda (_: T).(let TMP_27 \def (eq B b0 Void) in 
(not TMP_27))))) in (let TMP_29 \def (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g e c3)))) in (let TMP_30 \def (ex4_3 B C T TMP_23 
TMP_26 TMP_28 TMP_29) in (let TMP_31 \def (\lambda (e2: C).(clear c2 e2)) in 
(let TMP_34 \def (\lambda (e2: C).(let TMP_32 \def (Bind b) in (let TMP_33 
\def (CHead e TMP_32 u) in (csubc g TMP_33 e2)))) in (let TMP_35 \def (ex2 C 
TMP_31 TMP_34) in (let TMP_65 \def (\lambda (H2: (ex2 C (\lambda (c3: C).(eq 
C c2 (CHead c3 (Bind b) u))) (\lambda (c3: C).(csubc g e c3)))).(let TMP_38 
\def (\lambda (c3: C).(let TMP_36 \def (Bind b) in (let TMP_37 \def (CHead c3 
TMP_36 u) in (eq C c2 TMP_37)))) in (let TMP_39 \def (\lambda (c3: C).(csubc 
g e c3)) in (let TMP_40 \def (\lambda (e2: C).(clear c2 e2)) in (let TMP_43 
\def (\lambda (e2: C).(let TMP_41 \def (Bind b) in (let TMP_42 \def (CHead e 
TMP_41 u) in (csubc g TMP_42 e2)))) in (let TMP_44 \def (ex2 C TMP_40 TMP_43) 
in (let TMP_64 \def (\lambda (x: C).(\lambda (H3: (eq C c2 (CHead x (Bind b) 
u))).(\lambda (H4: (csubc g e x)).(let TMP_45 \def (Bind b) in (let TMP_46 
\def (CHead x TMP_45 u) in (let TMP_51 \def (\lambda (c: C).(let TMP_47 \def 
(\lambda (e2: C).(clear c e2)) in (let TMP_50 \def (\lambda (e2: C).(let 
TMP_48 \def (Bind b) in (let TMP_49 \def (CHead e TMP_48 u) in (csubc g 
TMP_49 e2)))) in (ex2 C TMP_47 TMP_50)))) in (let TMP_54 \def (\lambda (e2: 
C).(let TMP_52 \def (Bind b) in (let TMP_53 \def (CHead x TMP_52 u) in (clear 
TMP_53 e2)))) in (let TMP_57 \def (\lambda (e2: C).(let TMP_55 \def (Bind b) 
in (let TMP_56 \def (CHead e TMP_55 u) in (csubc g TMP_56 e2)))) in (let 
TMP_58 \def (Bind b) in (let TMP_59 \def (CHead x TMP_58 u) in (let TMP_60 
\def (clear_bind b x u) in (let TMP_61 \def (Bind b) in (let TMP_62 \def 
(csubc_head g e x H4 TMP_61 u) in (let TMP_63 \def (ex_intro2 C TMP_54 TMP_57 
TMP_59 TMP_60 TMP_62) in (eq_ind_r C TMP_46 TMP_51 TMP_63 c2 
H3))))))))))))))) in (ex2_ind C TMP_38 TMP_39 TMP_44 TMP_64 H2)))))))) in 
(let TMP_111 \def (\lambda (H2: (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K (Bind b) (Bind Abst))))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(sc3 g (asucc g a) e u)))) (\lambda (c3: C).(\lambda 
(w: T).(\lambda (a: A).(sc3 g a c3 w)))))).(let TMP_68 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(let TMP_66 \def (Bind b) in (let TMP_67 
\def (Bind Abst) in (eq K TMP_66 TMP_67)))))) in (let TMP_71 \def (\lambda 
(c3: C).(\lambda (w: T).(\lambda (_: A).(let TMP_69 \def (Bind Abbr) in (let 
TMP_70 \def (CHead c3 TMP_69 w) in (eq C c2 TMP_70)))))) in (let TMP_72 \def 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) in (let 
TMP_74 \def (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(let TMP_73 \def 
(asucc g a) in (sc3 g TMP_73 e u))))) in (let TMP_75 \def (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_76 \def 
(\lambda (e2: C).(clear c2 e2)) in (let TMP_79 \def (\lambda (e2: C).(let 
TMP_77 \def (Bind b) in (let TMP_78 \def (CHead e TMP_77 u) in (csubc g 
TMP_78 e2)))) in (let TMP_80 \def (ex2 C TMP_76 TMP_79) in (let TMP_110 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: A).(\lambda (H3: (eq K (Bind 
b) (Bind Abst))).(\lambda (H4: (eq C c2 (CHead x0 (Bind Abbr) x1))).(\lambda 
(H5: (csubc g e x0)).(\lambda (H6: (sc3 g (asucc g x2) e u)).(\lambda (H7: 
(sc3 g x2 x0 x1)).(let TMP_81 \def (Bind Abbr) in (let TMP_82 \def (CHead x0 
TMP_81 x1) in (let TMP_87 \def (\lambda (c: C).(let TMP_83 \def (\lambda (e2: 
C).(clear c e2)) in (let TMP_86 \def (\lambda (e2: C).(let TMP_84 \def (Bind 
b) in (let TMP_85 \def (CHead e TMP_84 u) in (csubc g TMP_85 e2)))) in (ex2 C 
TMP_83 TMP_86)))) in (let TMP_88 \def (\lambda (e0: K).(match e0 with [(Bind 
b0) \Rightarrow b0 | (Flat _) \Rightarrow b])) in (let TMP_89 \def (Bind b) 
in (let TMP_90 \def (Bind Abst) in (let H8 \def (f_equal K B TMP_88 TMP_89 
TMP_90 H3) in (let TMP_97 \def (\lambda (b0: B).(let TMP_93 \def (\lambda 
(e2: C).(let TMP_91 \def (Bind Abbr) in (let TMP_92 \def (CHead x0 TMP_91 x1) 
in (clear TMP_92 e2)))) in (let TMP_96 \def (\lambda (e2: C).(let TMP_94 \def 
(Bind b0) in (let TMP_95 \def (CHead e TMP_94 u) in (csubc g TMP_95 e2)))) in 
(ex2 C TMP_93 TMP_96)))) in (let TMP_100 \def (\lambda (e2: C).(let TMP_98 
\def (Bind Abbr) in (let TMP_99 \def (CHead x0 TMP_98 x1) in (clear TMP_99 
e2)))) in (let TMP_103 \def (\lambda (e2: C).(let TMP_101 \def (Bind Abst) in 
(let TMP_102 \def (CHead e TMP_101 u) in (csubc g TMP_102 e2)))) in (let 
TMP_104 \def (Bind Abbr) in (let TMP_105 \def (CHead x0 TMP_104 x1) in (let 
TMP_106 \def (clear_bind Abbr x0 x1) in (let TMP_107 \def (csubc_abst g e x0 
H5 u x2 H6 x1 H7) in (let TMP_108 \def (ex_intro2 C TMP_100 TMP_103 TMP_105 
TMP_106 TMP_107) in (let TMP_109 \def (eq_ind_r B Abst TMP_97 TMP_108 b H8) 
in (eq_ind_r C TMP_82 TMP_87 TMP_109 c2 H4))))))))))))))))))))))))) in 
(ex5_3_ind C T A TMP_68 TMP_71 TMP_72 TMP_74 TMP_75 TMP_80 TMP_110 
H2))))))))))) in (let TMP_156 \def (\lambda (H2: (ex4_3 B C T (\lambda (b0: 
B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b0) v2))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind b) (Bind 
Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g e 
c3)))))).(let TMP_114 \def (\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: 
T).(let TMP_112 \def (Bind b0) in (let TMP_113 \def (CHead c3 TMP_112 v2) in 
(eq C c2 TMP_113)))))) in (let TMP_117 \def (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(let TMP_115 \def (Bind b) in (let TMP_116 \def (Bind 
Void) in (eq K TMP_115 TMP_116)))))) in (let TMP_119 \def (\lambda (b0: 
B).(\lambda (_: C).(\lambda (_: T).(let TMP_118 \def (eq B b0 Void) in (not 
TMP_118))))) in (let TMP_120 \def (\lambda (_: B).(\lambda (c3: C).(\lambda 
(_: T).(csubc g e c3)))) in (let TMP_121 \def (\lambda (e2: C).(clear c2 e2)) 
in (let TMP_124 \def (\lambda (e2: C).(let TMP_122 \def (Bind b) in (let 
TMP_123 \def (CHead e TMP_122 u) in (csubc g TMP_123 e2)))) in (let TMP_125 
\def (ex2 C TMP_121 TMP_124) in (let TMP_155 \def (\lambda (x0: B).(\lambda 
(x1: C).(\lambda (x2: T).(\lambda (H3: (eq C c2 (CHead x1 (Bind x0) 
x2))).(\lambda (H4: (eq K (Bind b) (Bind Void))).(\lambda (H5: (not (eq B x0 
Void))).(\lambda (H6: (csubc g e x1)).(let TMP_126 \def (Bind x0) in (let 
TMP_127 \def (CHead x1 TMP_126 x2) in (let TMP_132 \def (\lambda (c: C).(let 
TMP_128 \def (\lambda (e2: C).(clear c e2)) in (let TMP_131 \def (\lambda 
(e2: C).(let TMP_129 \def (Bind b) in (let TMP_130 \def (CHead e TMP_129 u) 
in (csubc g TMP_130 e2)))) in (ex2 C TMP_128 TMP_131)))) in (let TMP_133 \def 
(\lambda (e0: K).(match e0 with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow b])) in (let TMP_134 \def (Bind b) in (let TMP_135 \def (Bind 
Void) in (let H7 \def (f_equal K B TMP_133 TMP_134 TMP_135 H4) in (let 
TMP_142 \def (\lambda (b0: B).(let TMP_138 \def (\lambda (e2: C).(let TMP_136 
\def (Bind x0) in (let TMP_137 \def (CHead x1 TMP_136 x2) in (clear TMP_137 
e2)))) in (let TMP_141 \def (\lambda (e2: C).(let TMP_139 \def (Bind b0) in 
(let TMP_140 \def (CHead e TMP_139 u) in (csubc g TMP_140 e2)))) in (ex2 C 
TMP_138 TMP_141)))) in (let TMP_145 \def (\lambda (e2: C).(let TMP_143 \def 
(Bind x0) in (let TMP_144 \def (CHead x1 TMP_143 x2) in (clear TMP_144 e2)))) 
in (let TMP_148 \def (\lambda (e2: C).(let TMP_146 \def (Bind Void) in (let 
TMP_147 \def (CHead e TMP_146 u) in (csubc g TMP_147 e2)))) in (let TMP_149 
\def (Bind x0) in (let TMP_150 \def (CHead x1 TMP_149 x2) in (let TMP_151 
\def (clear_bind x0 x1 x2) in (let TMP_152 \def (csubc_void g e x1 H6 x0 H5 u 
x2) in (let TMP_153 \def (ex_intro2 C TMP_145 TMP_148 TMP_150 TMP_151 
TMP_152) in (let TMP_154 \def (eq_ind_r B Void TMP_142 TMP_153 b H7) in 
(eq_ind_r C TMP_127 TMP_132 TMP_154 c2 H3)))))))))))))))))))))))) in 
(ex4_3_ind B C T TMP_114 TMP_117 TMP_119 TMP_120 TMP_125 TMP_155 H2)))))))))) 
in (or3_ind TMP_9 TMP_20 TMP_30 TMP_35 TMP_65 TMP_111 TMP_156 
H1))))))))))))))))))))))))))))) in (let TMP_273 \def (\lambda (e: C).(\lambda 
(c: C).(\lambda (_: (clear e c)).(\lambda (H1: ((\forall (c2: C).((csubc g e 
c2) \to (ex2 C (\lambda (e2: C).(clear c2 e2)) (\lambda (e2: C).(csubc g c 
e2))))))).(\lambda (f: F).(\lambda (u: T).(\lambda (c2: C).(\lambda (H2: 
(csubc g (CHead e (Flat f) u) c2)).(let TMP_158 \def (Flat f) in (let H_x 
\def (csubc_gen_head_l g e c2 u TMP_158 H2) in (let H3 \def H_x in (let 
TMP_161 \def (\lambda (c3: C).(let TMP_159 \def (Flat f) in (let TMP_160 \def 
(CHead c3 TMP_159 u) in (eq C c2 TMP_160)))) in (let TMP_162 \def (\lambda 
(c3: C).(csubc g e c3)) in (let TMP_163 \def (ex2 C TMP_161 TMP_162) in (let 
TMP_166 \def (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(let TMP_164 
\def (Flat f) in (let TMP_165 \def (Bind Abst) in (eq K TMP_164 TMP_165)))))) 
in (let TMP_169 \def (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(let 
TMP_167 \def (Bind Abbr) in (let TMP_168 \def (CHead c3 TMP_167 w) in (eq C 
c2 TMP_168)))))) in (let TMP_170 \def (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g e c3)))) in (let TMP_172 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(let TMP_171 \def (asucc g a) in (sc3 g 
TMP_171 e u))))) in (let TMP_173 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_174 \def (ex5_3 C T A 
TMP_166 TMP_169 TMP_170 TMP_172 TMP_173) in (let TMP_177 \def (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_175 \def (Bind b) in (let 
TMP_176 \def (CHead c3 TMP_175 v2) in (eq C c2 TMP_176)))))) in (let TMP_180 
\def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_178 \def (Flat 
f) in (let TMP_179 \def (Bind Void) in (eq K TMP_178 TMP_179)))))) in (let 
TMP_182 \def (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(let TMP_181 
\def (eq B b Void) in (not TMP_181))))) in (let TMP_183 \def (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g e c3)))) in (let TMP_184 \def 
(ex4_3 B C T TMP_177 TMP_180 TMP_182 TMP_183) in (let TMP_185 \def (\lambda 
(e2: C).(clear c2 e2)) in (let TMP_186 \def (\lambda (e2: C).(csubc g c e2)) 
in (let TMP_187 \def (ex2 C TMP_185 TMP_186) in (let TMP_215 \def (\lambda 
(H4: (ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 (Flat f) u))) (\lambda (c3: 
C).(csubc g e c3)))).(let TMP_190 \def (\lambda (c3: C).(let TMP_188 \def 
(Flat f) in (let TMP_189 \def (CHead c3 TMP_188 u) in (eq C c2 TMP_189)))) in 
(let TMP_191 \def (\lambda (c3: C).(csubc g e c3)) in (let TMP_192 \def 
(\lambda (e2: C).(clear c2 e2)) in (let TMP_193 \def (\lambda (e2: C).(csubc 
g c e2)) in (let TMP_194 \def (ex2 C TMP_192 TMP_193) in (let TMP_214 \def 
(\lambda (x: C).(\lambda (H5: (eq C c2 (CHead x (Flat f) u))).(\lambda (H6: 
(csubc g e x)).(let TMP_195 \def (Flat f) in (let TMP_196 \def (CHead x 
TMP_195 u) in (let TMP_199 \def (\lambda (c0: C).(let TMP_197 \def (\lambda 
(e2: C).(clear c0 e2)) in (let TMP_198 \def (\lambda (e2: C).(csubc g c e2)) 
in (ex2 C TMP_197 TMP_198)))) in (let H_x0 \def (H1 x H6) in (let H7 \def 
H_x0 in (let TMP_200 \def (\lambda (e2: C).(clear x e2)) in (let TMP_201 \def 
(\lambda (e2: C).(csubc g c e2)) in (let TMP_204 \def (\lambda (e2: C).(let 
TMP_202 \def (Flat f) in (let TMP_203 \def (CHead x TMP_202 u) in (clear 
TMP_203 e2)))) in (let TMP_205 \def (\lambda (e2: C).(csubc g c e2)) in (let 
TMP_206 \def (ex2 C TMP_204 TMP_205) in (let TMP_212 \def (\lambda (x0: 
C).(\lambda (H8: (clear x x0)).(\lambda (H9: (csubc g c x0)).(let TMP_209 
\def (\lambda (e2: C).(let TMP_207 \def (Flat f) in (let TMP_208 \def (CHead 
x TMP_207 u) in (clear TMP_208 e2)))) in (let TMP_210 \def (\lambda (e2: 
C).(csubc g c e2)) in (let TMP_211 \def (clear_flat x x0 H8 f u) in 
(ex_intro2 C TMP_209 TMP_210 x0 TMP_211 H9))))))) in (let TMP_213 \def 
(ex2_ind C TMP_200 TMP_201 TMP_206 TMP_212 H7) in (eq_ind_r C TMP_196 TMP_199 
TMP_213 c2 H5)))))))))))))))) in (ex2_ind C TMP_190 TMP_191 TMP_194 TMP_214 
H4)))))))) in (let TMP_244 \def (\lambda (H4: (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K (Flat f) (Bind Abst))))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g e c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) e u)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))))).(let TMP_218 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(let TMP_216 \def (Flat f) in 
(let TMP_217 \def (Bind Abst) in (eq K TMP_216 TMP_217)))))) in (let TMP_221 
\def (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(let TMP_219 \def (Bind 
Abbr) in (let TMP_220 \def (CHead c3 TMP_219 w) in (eq C c2 TMP_220)))))) in 
(let TMP_222 \def (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g e 
c3)))) in (let TMP_224 \def (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(let TMP_223 \def (asucc g a) in (sc3 g TMP_223 e u))))) in (let TMP_225 
\def (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) in 
(let TMP_226 \def (\lambda (e2: C).(clear c2 e2)) in (let TMP_227 \def 
(\lambda (e2: C).(csubc g c e2)) in (let TMP_228 \def (ex2 C TMP_226 TMP_227) 
in (let TMP_243 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
A).(\lambda (H5: (eq K (Flat f) (Bind Abst))).(\lambda (H6: (eq C c2 (CHead 
x0 (Bind Abbr) x1))).(\lambda (_: (csubc g e x0)).(\lambda (_: (sc3 g (asucc 
g x2) e u)).(\lambda (_: (sc3 g x2 x0 x1)).(let TMP_229 \def (Bind Abbr) in 
(let TMP_230 \def (CHead x0 TMP_229 x1) in (let TMP_233 \def (\lambda (c0: 
C).(let TMP_231 \def (\lambda (e2: C).(clear c0 e2)) in (let TMP_232 \def 
(\lambda (e2: C).(csubc g c e2)) in (ex2 C TMP_231 TMP_232)))) in (let 
TMP_234 \def (Flat f) in (let TMP_235 \def (\lambda (ee: K).(match ee with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])) in (let TMP_236 
\def (Bind Abst) in (let H10 \def (eq_ind K TMP_234 TMP_235 I TMP_236 H5) in 
(let TMP_239 \def (\lambda (e2: C).(let TMP_237 \def (Bind Abbr) in (let 
TMP_238 \def (CHead x0 TMP_237 x1) in (clear TMP_238 e2)))) in (let TMP_240 
\def (\lambda (e2: C).(csubc g c e2)) in (let TMP_241 \def (ex2 C TMP_239 
TMP_240) in (let TMP_242 \def (False_ind TMP_241 H10) in (eq_ind_r C TMP_230 
TMP_233 TMP_242 c2 H6)))))))))))))))))))) in (ex5_3_ind C T A TMP_218 TMP_221 
TMP_222 TMP_224 TMP_225 TMP_228 TMP_243 H4))))))))))) in (let TMP_272 \def 
(\lambda (H4: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Flat f) (Bind Void))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g e c3)))))).(let TMP_247 \def (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_245 \def (Bind b) in (let 
TMP_246 \def (CHead c3 TMP_245 v2) in (eq C c2 TMP_246)))))) in (let TMP_250 
\def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_248 \def (Flat 
f) in (let TMP_249 \def (Bind Void) in (eq K TMP_248 TMP_249)))))) in (let 
TMP_252 \def (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(let TMP_251 
\def (eq B b Void) in (not TMP_251))))) in (let TMP_253 \def (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g e c3)))) in (let TMP_254 \def 
(\lambda (e2: C).(clear c2 e2)) in (let TMP_255 \def (\lambda (e2: C).(csubc 
g c e2)) in (let TMP_256 \def (ex2 C TMP_254 TMP_255) in (let TMP_271 \def 
(\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H5: (eq C c2 
(CHead x1 (Bind x0) x2))).(\lambda (H6: (eq K (Flat f) (Bind Void))).(\lambda 
(_: (not (eq B x0 Void))).(\lambda (_: (csubc g e x1)).(let TMP_257 \def 
(Bind x0) in (let TMP_258 \def (CHead x1 TMP_257 x2) in (let TMP_261 \def 
(\lambda (c0: C).(let TMP_259 \def (\lambda (e2: C).(clear c0 e2)) in (let 
TMP_260 \def (\lambda (e2: C).(csubc g c e2)) in (ex2 C TMP_259 TMP_260)))) 
in (let TMP_262 \def (Flat f) in (let TMP_263 \def (\lambda (ee: K).(match ee 
with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])) in (let 
TMP_264 \def (Bind Void) in (let H9 \def (eq_ind K TMP_262 TMP_263 I TMP_264 
H6) in (let TMP_267 \def (\lambda (e2: C).(let TMP_265 \def (Bind x0) in (let 
TMP_266 \def (CHead x1 TMP_265 x2) in (clear TMP_266 e2)))) in (let TMP_268 
\def (\lambda (e2: C).(csubc g c e2)) in (let TMP_269 \def (ex2 C TMP_267 
TMP_268) in (let TMP_270 \def (False_ind TMP_269 H9) in (eq_ind_r C TMP_258 
TMP_261 TMP_270 c2 H5))))))))))))))))))) in (ex4_3_ind B C T TMP_247 TMP_250 
TMP_252 TMP_253 TMP_256 TMP_271 H4)))))))))) in (or3_ind TMP_163 TMP_174 
TMP_184 TMP_187 TMP_215 TMP_244 TMP_272 H3)))))))))))))))))))))))))))))))) in 
(clear_ind TMP_3 TMP_157 TMP_273 c1 e1 H))))))).

