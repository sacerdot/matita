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

include "basic_1/csubst1/props.ma".

include "basic_1/csubst0/getl.ma".

include "basic_1/subst1/props.ma".

include "basic_1/drop/props.ma".

theorem csubst1_getl_ge:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c1 
e) \to (getl n c2 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 c2)).(let 
TMP_1 \def (\lambda (c: C).(\forall (e: C).((getl n c1 e) \to (getl n c e)))) 
in (let TMP_2 \def (\lambda (e: C).(\lambda (H1: (getl n c1 e)).H1)) in (let 
TMP_3 \def (\lambda (c3: C).(\lambda (H1: (csubst0 i v c1 c3)).(\lambda (e: 
C).(\lambda (H2: (getl n c1 e)).(csubst0_getl_ge i n H c1 c3 v H1 e H2))))) 
in (csubst1_ind i v c1 TMP_1 TMP_2 TMP_3 c2 H0)))))))))).

theorem csubst1_getl_lt:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e1: C).((getl n c1 
e1) \to (ex2 C (\lambda (e2: C).(csubst1 (minus i n) v e1 e2)) (\lambda (e2: 
C).(getl n c2 e2)))))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 c2)).(let 
TMP_4 \def (\lambda (c: C).(\forall (e1: C).((getl n c1 e1) \to (let TMP_2 
\def (\lambda (e2: C).(let TMP_1 \def (minus i n) in (csubst1 TMP_1 v e1 
e2))) in (let TMP_3 \def (\lambda (e2: C).(getl n c e2)) in (ex2 C TMP_2 
TMP_3)))))) in (let TMP_23 \def (\lambda (e1: C).(\lambda (H1: (getl n c1 
e1)).(let TMP_5 \def (S n) in (let TMP_6 \def (minus i TMP_5) in (let TMP_7 
\def (S TMP_6) in (let TMP_10 \def (\lambda (n0: nat).(let TMP_8 \def 
(\lambda (e2: C).(csubst1 n0 v e1 e2)) in (let TMP_9 \def (\lambda (e2: 
C).(getl n c1 e2)) in (ex2 C TMP_8 TMP_9)))) in (let TMP_14 \def (\lambda 
(e2: C).(let TMP_11 \def (S n) in (let TMP_12 \def (minus i TMP_11) in (let 
TMP_13 \def (S TMP_12) in (csubst1 TMP_13 v e1 e2))))) in (let TMP_15 \def 
(\lambda (e2: C).(getl n c1 e2)) in (let TMP_16 \def (S n) in (let TMP_17 
\def (minus i TMP_16) in (let TMP_18 \def (S TMP_17) in (let TMP_19 \def 
(csubst1_refl TMP_18 v e1) in (let TMP_20 \def (ex_intro2 C TMP_14 TMP_15 e1 
TMP_19 H1) in (let TMP_21 \def (minus i n) in (let TMP_22 \def (minus_x_Sy i 
n H) in (eq_ind_r nat TMP_7 TMP_10 TMP_20 TMP_21 TMP_22)))))))))))))))) in 
(let TMP_224 \def (\lambda (c3: C).(\lambda (H1: (csubst0 i v c1 
c3)).(\lambda (e1: C).(\lambda (H2: (getl n c1 e1)).(let TMP_24 \def (S n) in 
(let TMP_25 \def (minus i TMP_24) in (let TMP_26 \def (S TMP_25) in (let 
TMP_29 \def (\lambda (n0: nat).(let TMP_27 \def (\lambda (e2: C).(csubst1 n0 
v e1 e2)) in (let TMP_28 \def (\lambda (e2: C).(getl n c3 e2)) in (ex2 C 
TMP_27 TMP_28)))) in (let H3 \def (csubst0_getl_lt i n H c1 c3 v H1 e1 H2) in 
(let TMP_30 \def (getl n c3 e1) in (let TMP_33 \def (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(let TMP_31 \def (Bind b) in (let 
TMP_32 \def (CHead e0 TMP_31 u) in (eq C e1 TMP_32))))))) in (let TMP_36 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(let TMP_34 
\def (Bind b) in (let TMP_35 \def (CHead e0 TMP_34 w) in (getl n c3 
TMP_35))))))) in (let TMP_39 \def (\lambda (_: B).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(let TMP_37 \def (S n) in (let TMP_38 \def (minus i 
TMP_37) in (subst0 TMP_38 v u w))))))) in (let TMP_40 \def (ex3_4 B C T T 
TMP_33 TMP_36 TMP_39) in (let TMP_43 \def (\lambda (b: B).(\lambda (e2: 
C).(\lambda (_: C).(\lambda (u: T).(let TMP_41 \def (Bind b) in (let TMP_42 
\def (CHead e2 TMP_41 u) in (eq C e1 TMP_42))))))) in (let TMP_46 \def 
(\lambda (b: B).(\lambda (_: C).(\lambda (e3: C).(\lambda (u: T).(let TMP_44 
\def (Bind b) in (let TMP_45 \def (CHead e3 TMP_44 u) in (getl n c3 
TMP_45))))))) in (let TMP_49 \def (\lambda (_: B).(\lambda (e2: C).(\lambda 
(e3: C).(\lambda (_: T).(let TMP_47 \def (S n) in (let TMP_48 \def (minus i 
TMP_47) in (csubst0 TMP_48 v e2 e3))))))) in (let TMP_50 \def (ex3_4 B C C T 
TMP_43 TMP_46 TMP_49) in (let TMP_53 \def (\lambda (b: B).(\lambda (e2: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(let TMP_51 \def (Bind b) 
in (let TMP_52 \def (CHead e2 TMP_51 u) in (eq C e1 TMP_52)))))))) in (let 
TMP_56 \def (\lambda (b: B).(\lambda (_: C).(\lambda (e3: C).(\lambda (_: 
T).(\lambda (w: T).(let TMP_54 \def (Bind b) in (let TMP_55 \def (CHead e3 
TMP_54 w) in (getl n c3 TMP_55)))))))) in (let TMP_59 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(let 
TMP_57 \def (S n) in (let TMP_58 \def (minus i TMP_57) in (subst0 TMP_58 v u 
w)))))))) in (let TMP_62 \def (\lambda (_: B).(\lambda (e2: C).(\lambda (e3: 
C).(\lambda (_: T).(\lambda (_: T).(let TMP_60 \def (S n) in (let TMP_61 \def 
(minus i TMP_60) in (csubst0 TMP_61 v e2 e3)))))))) in (let TMP_63 \def 
(ex4_5 B C C T T TMP_53 TMP_56 TMP_59 TMP_62) in (let TMP_67 \def (\lambda 
(e2: C).(let TMP_64 \def (S n) in (let TMP_65 \def (minus i TMP_64) in (let 
TMP_66 \def (S TMP_65) in (csubst1 TMP_66 v e1 e2))))) in (let TMP_68 \def 
(\lambda (e2: C).(getl n c3 e2)) in (let TMP_69 \def (ex2 C TMP_67 TMP_68) in 
(let TMP_79 \def (\lambda (H4: (getl n c3 e1)).(let TMP_73 \def (\lambda (e2: 
C).(let TMP_70 \def (S n) in (let TMP_71 \def (minus i TMP_70) in (let TMP_72 
\def (S TMP_71) in (csubst1 TMP_72 v e1 e2))))) in (let TMP_74 \def (\lambda 
(e2: C).(getl n c3 e2)) in (let TMP_75 \def (S n) in (let TMP_76 \def (minus 
i TMP_75) in (let TMP_77 \def (S TMP_76) in (let TMP_78 \def (csubst1_refl 
TMP_77 v e1) in (ex_intro2 C TMP_73 TMP_74 e1 TMP_78 H4)))))))) in (let 
TMP_125 \def (\lambda (H4: (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e1 (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w))))))).(let TMP_82 \def 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(let TMP_80 
\def (Bind b) in (let TMP_81 \def (CHead e0 TMP_80 u) in (eq C e1 
TMP_81))))))) in (let TMP_85 \def (\lambda (b: B).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(let TMP_83 \def (Bind b) in (let TMP_84 \def (CHead 
e0 TMP_83 w) in (getl n c3 TMP_84))))))) in (let TMP_88 \def (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(let TMP_86 \def (S n) in 
(let TMP_87 \def (minus i TMP_86) in (subst0 TMP_87 v u w))))))) in (let 
TMP_92 \def (\lambda (e2: C).(let TMP_89 \def (S n) in (let TMP_90 \def 
(minus i TMP_89) in (let TMP_91 \def (S TMP_90) in (csubst1 TMP_91 v e1 
e2))))) in (let TMP_93 \def (\lambda (e2: C).(getl n c3 e2)) in (let TMP_94 
\def (ex2 C TMP_92 TMP_93) in (let TMP_124 \def (\lambda (x0: B).(\lambda 
(x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H5: (eq C e1 (CHead x1 
(Bind x0) x2))).(\lambda (H6: (getl n c3 (CHead x1 (Bind x0) x3))).(\lambda 
(H7: (subst0 (minus i (S n)) v x2 x3)).(let TMP_95 \def (Bind x0) in (let 
TMP_96 \def (CHead x1 TMP_95 x2) in (let TMP_102 \def (\lambda (c: C).(let 
TMP_100 \def (\lambda (e2: C).(let TMP_97 \def (S n) in (let TMP_98 \def 
(minus i TMP_97) in (let TMP_99 \def (S TMP_98) in (csubst1 TMP_99 v c 
e2))))) in (let TMP_101 \def (\lambda (e2: C).(getl n c3 e2)) in (ex2 C 
TMP_100 TMP_101)))) in (let TMP_108 \def (\lambda (e2: C).(let TMP_103 \def 
(S n) in (let TMP_104 \def (minus i TMP_103) in (let TMP_105 \def (S TMP_104) 
in (let TMP_106 \def (Bind x0) in (let TMP_107 \def (CHead x1 TMP_106 x2) in 
(csubst1 TMP_105 v TMP_107 e2))))))) in (let TMP_109 \def (\lambda (e2: 
C).(getl n c3 e2)) in (let TMP_110 \def (Bind x0) in (let TMP_111 \def (CHead 
x1 TMP_110 x3) in (let TMP_112 \def (S n) in (let TMP_113 \def (minus i 
TMP_112) in (let TMP_114 \def (S TMP_113) in (let TMP_115 \def (Bind x0) in 
(let TMP_116 \def (CHead x1 TMP_115 x2) in (let TMP_117 \def (Bind x0) in 
(let TMP_118 \def (CHead x1 TMP_117 x3) in (let TMP_119 \def (S n) in (let 
TMP_120 \def (minus i TMP_119) in (let TMP_121 \def (csubst0_snd_bind x0 
TMP_120 v x2 x3 H7 x1) in (let TMP_122 \def (csubst1_sing TMP_114 v TMP_116 
TMP_118 TMP_121) in (let TMP_123 \def (ex_intro2 C TMP_108 TMP_109 TMP_111 
TMP_122 H6) in (eq_ind_r C TMP_96 TMP_102 TMP_123 e1 
H5))))))))))))))))))))))))))) in (ex3_4_ind B C T T TMP_82 TMP_85 TMP_88 
TMP_94 TMP_124 H4))))))))) in (let TMP_171 \def (\lambda (H4: (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e2: C).(\lambda (_: C).(\lambda (u: T).(eq C e1 
(CHead e2 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e3: 
C).(\lambda (u: T).(getl n c3 (CHead e3 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e2 e3))))))).(let TMP_128 \def (\lambda (b: B).(\lambda (e2: C).(\lambda 
(_: C).(\lambda (u: T).(let TMP_126 \def (Bind b) in (let TMP_127 \def (CHead 
e2 TMP_126 u) in (eq C e1 TMP_127))))))) in (let TMP_131 \def (\lambda (b: 
B).(\lambda (_: C).(\lambda (e3: C).(\lambda (u: T).(let TMP_129 \def (Bind 
b) in (let TMP_130 \def (CHead e3 TMP_129 u) in (getl n c3 TMP_130))))))) in 
(let TMP_134 \def (\lambda (_: B).(\lambda (e2: C).(\lambda (e3: C).(\lambda 
(_: T).(let TMP_132 \def (S n) in (let TMP_133 \def (minus i TMP_132) in 
(csubst0 TMP_133 v e2 e3))))))) in (let TMP_138 \def (\lambda (e2: C).(let 
TMP_135 \def (S n) in (let TMP_136 \def (minus i TMP_135) in (let TMP_137 
\def (S TMP_136) in (csubst1 TMP_137 v e1 e2))))) in (let TMP_139 \def 
(\lambda (e2: C).(getl n c3 e2)) in (let TMP_140 \def (ex2 C TMP_138 TMP_139) 
in (let TMP_170 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
C).(\lambda (x3: T).(\lambda (H5: (eq C e1 (CHead x1 (Bind x0) x3))).(\lambda 
(H6: (getl n c3 (CHead x2 (Bind x0) x3))).(\lambda (H7: (csubst0 (minus i (S 
n)) v x1 x2)).(let TMP_141 \def (Bind x0) in (let TMP_142 \def (CHead x1 
TMP_141 x3) in (let TMP_148 \def (\lambda (c: C).(let TMP_146 \def (\lambda 
(e2: C).(let TMP_143 \def (S n) in (let TMP_144 \def (minus i TMP_143) in 
(let TMP_145 \def (S TMP_144) in (csubst1 TMP_145 v c e2))))) in (let TMP_147 
\def (\lambda (e2: C).(getl n c3 e2)) in (ex2 C TMP_146 TMP_147)))) in (let 
TMP_154 \def (\lambda (e2: C).(let TMP_149 \def (S n) in (let TMP_150 \def 
(minus i TMP_149) in (let TMP_151 \def (S TMP_150) in (let TMP_152 \def (Bind 
x0) in (let TMP_153 \def (CHead x1 TMP_152 x3) in (csubst1 TMP_151 v TMP_153 
e2))))))) in (let TMP_155 \def (\lambda (e2: C).(getl n c3 e2)) in (let 
TMP_156 \def (Bind x0) in (let TMP_157 \def (CHead x2 TMP_156 x3) in (let 
TMP_158 \def (S n) in (let TMP_159 \def (minus i TMP_158) in (let TMP_160 
\def (S TMP_159) in (let TMP_161 \def (Bind x0) in (let TMP_162 \def (CHead 
x1 TMP_161 x3) in (let TMP_163 \def (Bind x0) in (let TMP_164 \def (CHead x2 
TMP_163 x3) in (let TMP_165 \def (S n) in (let TMP_166 \def (minus i TMP_165) 
in (let TMP_167 \def (csubst0_fst_bind x0 TMP_166 x1 x2 v H7 x3) in (let 
TMP_168 \def (csubst1_sing TMP_160 v TMP_162 TMP_164 TMP_167) in (let TMP_169 
\def (ex_intro2 C TMP_154 TMP_155 TMP_157 TMP_168 H6) in (eq_ind_r C TMP_142 
TMP_148 TMP_169 e1 H5))))))))))))))))))))))))))) in (ex3_4_ind B C C T 
TMP_128 TMP_131 TMP_134 TMP_140 TMP_170 H4))))))))) in (let TMP_220 \def 
(\lambda (H4: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e2: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e1 (CHead e2 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e3: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c3 (CHead e3 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e2 e3)))))))).(let TMP_174 \def 
(\lambda (b: B).(\lambda (e2: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(let TMP_172 \def (Bind b) in (let TMP_173 \def (CHead e2 TMP_172 u) in 
(eq C e1 TMP_173)))))))) in (let TMP_177 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (e3: C).(\lambda (_: T).(\lambda (w: T).(let TMP_175 \def (Bind 
b) in (let TMP_176 \def (CHead e3 TMP_175 w) in (getl n c3 TMP_176)))))))) in 
(let TMP_180 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(let TMP_178 \def (S n) in (let TMP_179 \def (minus i 
TMP_178) in (subst0 TMP_179 v u w)))))))) in (let TMP_183 \def (\lambda (_: 
B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: T).(\lambda (_: T).(let 
TMP_181 \def (S n) in (let TMP_182 \def (minus i TMP_181) in (csubst0 TMP_182 
v e2 e3)))))))) in (let TMP_187 \def (\lambda (e2: C).(let TMP_184 \def (S n) 
in (let TMP_185 \def (minus i TMP_184) in (let TMP_186 \def (S TMP_185) in 
(csubst1 TMP_186 v e1 e2))))) in (let TMP_188 \def (\lambda (e2: C).(getl n 
c3 e2)) in (let TMP_189 \def (ex2 C TMP_187 TMP_188) in (let TMP_219 \def 
(\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda 
(x4: T).(\lambda (H5: (eq C e1 (CHead x1 (Bind x0) x3))).(\lambda (H6: (getl 
n c3 (CHead x2 (Bind x0) x4))).(\lambda (H7: (subst0 (minus i (S n)) v x3 
x4)).(\lambda (H8: (csubst0 (minus i (S n)) v x1 x2)).(let TMP_190 \def (Bind 
x0) in (let TMP_191 \def (CHead x1 TMP_190 x3) in (let TMP_197 \def (\lambda 
(c: C).(let TMP_195 \def (\lambda (e2: C).(let TMP_192 \def (S n) in (let 
TMP_193 \def (minus i TMP_192) in (let TMP_194 \def (S TMP_193) in (csubst1 
TMP_194 v c e2))))) in (let TMP_196 \def (\lambda (e2: C).(getl n c3 e2)) in 
(ex2 C TMP_195 TMP_196)))) in (let TMP_203 \def (\lambda (e2: C).(let TMP_198 
\def (S n) in (let TMP_199 \def (minus i TMP_198) in (let TMP_200 \def (S 
TMP_199) in (let TMP_201 \def (Bind x0) in (let TMP_202 \def (CHead x1 
TMP_201 x3) in (csubst1 TMP_200 v TMP_202 e2))))))) in (let TMP_204 \def 
(\lambda (e2: C).(getl n c3 e2)) in (let TMP_205 \def (Bind x0) in (let 
TMP_206 \def (CHead x2 TMP_205 x4) in (let TMP_207 \def (S n) in (let TMP_208 
\def (minus i TMP_207) in (let TMP_209 \def (S TMP_208) in (let TMP_210 \def 
(Bind x0) in (let TMP_211 \def (CHead x1 TMP_210 x3) in (let TMP_212 \def 
(Bind x0) in (let TMP_213 \def (CHead x2 TMP_212 x4) in (let TMP_214 \def (S 
n) in (let TMP_215 \def (minus i TMP_214) in (let TMP_216 \def 
(csubst0_both_bind x0 TMP_215 v x3 x4 H7 x1 x2 H8) in (let TMP_217 \def 
(csubst1_sing TMP_209 v TMP_211 TMP_213 TMP_216) in (let TMP_218 \def 
(ex_intro2 C TMP_203 TMP_204 TMP_206 TMP_217 H6) in (eq_ind_r C TMP_191 
TMP_197 TMP_218 e1 H5))))))))))))))))))))))))))))) in (ex4_5_ind B C C T T 
TMP_174 TMP_177 TMP_180 TMP_183 TMP_189 TMP_219 H4)))))))))) in (let TMP_221 
\def (or4_ind TMP_30 TMP_40 TMP_50 TMP_63 TMP_69 TMP_79 TMP_125 TMP_171 
TMP_220 H3) in (let TMP_222 \def (minus i n) in (let TMP_223 \def (minus_x_Sy 
i n H) in (eq_ind_r nat TMP_26 TMP_29 TMP_221 TMP_222 
TMP_223)))))))))))))))))))))))))))))))))) in (csubst1_ind i v c1 TMP_4 TMP_23 
TMP_224 c2 H0)))))))))).

theorem csubst1_getl_ge_back:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c2 
e) \to (getl n c1 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 c2)).(let 
TMP_1 \def (\lambda (c: C).(\forall (e: C).((getl n c e) \to (getl n c1 e)))) 
in (let TMP_2 \def (\lambda (e: C).(\lambda (H1: (getl n c1 e)).H1)) in (let 
TMP_3 \def (\lambda (c3: C).(\lambda (H1: (csubst0 i v c1 c3)).(\lambda (e: 
C).(\lambda (H2: (getl n c3 e)).(csubst0_getl_ge_back i n H c1 c3 v H1 e 
H2))))) in (csubst1_ind i v c1 TMP_1 TMP_2 TMP_3 c2 H0)))))))))).

theorem getl_csubst1:
 \forall (d: nat).(\forall (c: C).(\forall (e: C).(\forall (u: T).((getl d c 
(CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: 
C).(csubst1 d u c a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) d a0 
a))))))))
\def
 \lambda (d: nat).(let TMP_4 \def (\lambda (n: nat).(\forall (c: C).(\forall 
(e: C).(\forall (u: T).((getl n c (CHead e (Bind Abbr) u)) \to (let TMP_1 
\def (\lambda (a0: C).(\lambda (_: C).(csubst1 n u c a0))) in (let TMP_3 \def 
(\lambda (a0: C).(\lambda (a: C).(let TMP_2 \def (S O) in (drop TMP_2 n a0 
a)))) in (ex2_2 C C TMP_1 TMP_3)))))))) in (let TMP_141 \def (\lambda (c: 
C).(let TMP_8 \def (\lambda (c0: C).(\forall (e: C).(\forall (u: T).((getl O 
c0 (CHead e (Bind Abbr) u)) \to (let TMP_5 \def (\lambda (a0: C).(\lambda (_: 
C).(csubst1 O u c0 a0))) in (let TMP_7 \def (\lambda (a0: C).(\lambda (a: 
C).(let TMP_6 \def (S O) in (drop TMP_6 O a0 a)))) in (ex2_2 C C TMP_5 
TMP_7))))))) in (let TMP_16 \def (\lambda (n: nat).(\lambda (e: C).(\lambda 
(u: T).(\lambda (H: (getl O (CSort n) (CHead e (Bind Abbr) u))).(let TMP_9 
\def (Bind Abbr) in (let TMP_10 \def (CHead e TMP_9 u) in (let TMP_12 \def 
(\lambda (a0: C).(\lambda (_: C).(let TMP_11 \def (CSort n) in (csubst1 O u 
TMP_11 a0)))) in (let TMP_14 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_13 \def (S O) in (drop TMP_13 O a0 a)))) in (let TMP_15 \def (ex2_2 C C 
TMP_12 TMP_14) in (getl_gen_sort n O TMP_10 H TMP_15)))))))))) in (let 
TMP_140 \def (\lambda (c0: C).(\lambda (H: ((\forall (e: C).(\forall (u: 
T).((getl O c0 (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 O u c0 a0))) (\lambda (a0: C).(\lambda (a: 
C).(drop (S O) O a0 a))))))))).(\lambda (k: K).(let TMP_21 \def (\lambda (k0: 
K).(\forall (t: T).(\forall (e: C).(\forall (u: T).((getl O (CHead c0 k0 t) 
(CHead e (Bind Abbr) u)) \to (let TMP_18 \def (\lambda (a0: C).(\lambda (_: 
C).(let TMP_17 \def (CHead c0 k0 t) in (csubst1 O u TMP_17 a0)))) in (let 
TMP_20 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_19 \def (S O) in (drop 
TMP_19 O a0 a)))) in (ex2_2 C C TMP_18 TMP_20)))))))) in (let TMP_90 \def 
(\lambda (b: B).(\lambda (t: T).(\lambda (e: C).(\lambda (u: T).(\lambda (H0: 
(getl O (CHead c0 (Bind b) t) (CHead e (Bind Abbr) u))).(let TMP_22 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow e | (CHead c1 _ _) 
\Rightarrow c1])) in (let TMP_23 \def (Bind Abbr) in (let TMP_24 \def (CHead 
e TMP_23 u) in (let TMP_25 \def (Bind b) in (let TMP_26 \def (CHead c0 TMP_25 
t) in (let TMP_27 \def (Bind Abbr) in (let TMP_28 \def (CHead e TMP_27 u) in 
(let TMP_29 \def (Bind b) in (let TMP_30 \def (CHead c0 TMP_29 t) in (let 
TMP_31 \def (Bind Abbr) in (let TMP_32 \def (CHead e TMP_31 u) in (let TMP_33 
\def (getl_gen_O TMP_30 TMP_32 H0) in (let TMP_34 \def (clear_gen_bind b c0 
TMP_28 t TMP_33) in (let H1 \def (f_equal C C TMP_22 TMP_24 TMP_26 TMP_34) in 
(let TMP_35 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow Abbr 
| (CHead _ k0 _) \Rightarrow (match k0 with [(Bind b0) \Rightarrow b0 | (Flat 
_) \Rightarrow Abbr])])) in (let TMP_36 \def (Bind Abbr) in (let TMP_37 \def 
(CHead e TMP_36 u) in (let TMP_38 \def (Bind b) in (let TMP_39 \def (CHead c0 
TMP_38 t) in (let TMP_40 \def (Bind Abbr) in (let TMP_41 \def (CHead e TMP_40 
u) in (let TMP_42 \def (Bind b) in (let TMP_43 \def (CHead c0 TMP_42 t) in 
(let TMP_44 \def (Bind Abbr) in (let TMP_45 \def (CHead e TMP_44 u) in (let 
TMP_46 \def (getl_gen_O TMP_43 TMP_45 H0) in (let TMP_47 \def (clear_gen_bind 
b c0 TMP_41 t TMP_46) in (let H2 \def (f_equal C B TMP_35 TMP_37 TMP_39 
TMP_47) in (let TMP_48 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_49 \def (Bind 
Abbr) in (let TMP_50 \def (CHead e TMP_49 u) in (let TMP_51 \def (Bind b) in 
(let TMP_52 \def (CHead c0 TMP_51 t) in (let TMP_53 \def (Bind Abbr) in (let 
TMP_54 \def (CHead e TMP_53 u) in (let TMP_55 \def (Bind b) in (let TMP_56 
\def (CHead c0 TMP_55 t) in (let TMP_57 \def (Bind Abbr) in (let TMP_58 \def 
(CHead e TMP_57 u) in (let TMP_59 \def (getl_gen_O TMP_56 TMP_58 H0) in (let 
TMP_60 \def (clear_gen_bind b c0 TMP_54 t TMP_59) in (let H3 \def (f_equal C 
T TMP_48 TMP_50 TMP_52 TMP_60) in (let TMP_88 \def (\lambda (H4: (eq B Abbr 
b)).(\lambda (_: (eq C e c0)).(let TMP_66 \def (\lambda (t0: T).(let TMP_63 
\def (\lambda (a0: C).(\lambda (_: C).(let TMP_61 \def (Bind b) in (let 
TMP_62 \def (CHead c0 TMP_61 t) in (csubst1 O t0 TMP_62 a0))))) in (let 
TMP_65 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_64 \def (S O) in (drop 
TMP_64 O a0 a)))) in (ex2_2 C C TMP_63 TMP_65)))) in (let TMP_72 \def 
(\lambda (b0: B).(let TMP_69 \def (\lambda (a0: C).(\lambda (_: C).(let 
TMP_67 \def (Bind b0) in (let TMP_68 \def (CHead c0 TMP_67 t) in (csubst1 O t 
TMP_68 a0))))) in (let TMP_71 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_70 \def (S O) in (drop TMP_70 O a0 a)))) in (ex2_2 C C TMP_69 TMP_71)))) 
in (let TMP_75 \def (\lambda (a0: C).(\lambda (_: C).(let TMP_73 \def (Bind 
Abbr) in (let TMP_74 \def (CHead c0 TMP_73 t) in (csubst1 O t TMP_74 a0))))) 
in (let TMP_77 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_76 \def (S O) 
in (drop TMP_76 O a0 a)))) in (let TMP_78 \def (Bind Abbr) in (let TMP_79 
\def (CHead c0 TMP_78 t) in (let TMP_80 \def (Bind Abbr) in (let TMP_81 \def 
(CHead c0 TMP_80 t) in (let TMP_82 \def (csubst1_refl O t TMP_81) in (let 
TMP_83 \def (Bind Abbr) in (let TMP_84 \def (drop_refl c0) in (let TMP_85 
\def (drop_drop TMP_83 O c0 c0 TMP_84 t) in (let TMP_86 \def (ex2_2_intro C C 
TMP_75 TMP_77 TMP_79 c0 TMP_82 TMP_85) in (let TMP_87 \def (eq_ind B Abbr 
TMP_72 TMP_86 b H4) in (eq_ind_r T t TMP_66 TMP_87 u H3))))))))))))))))) in 
(let TMP_89 \def (TMP_88 H2) in (TMP_89 
H1)))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_139 \def 
(\lambda (f: F).(\lambda (t: T).(\lambda (e: C).(\lambda (u: T).(\lambda (H0: 
(getl O (CHead c0 (Flat f) t) (CHead e (Bind Abbr) u))).(let H_x \def 
(subst1_ex u t O) in (let H1 \def H_x in (let TMP_93 \def (\lambda (t2: 
T).(let TMP_91 \def (S O) in (let TMP_92 \def (lift TMP_91 O t2) in (subst1 O 
u t TMP_92)))) in (let TMP_96 \def (\lambda (a0: C).(\lambda (_: C).(let 
TMP_94 \def (Flat f) in (let TMP_95 \def (CHead c0 TMP_94 t) in (csubst1 O u 
TMP_95 a0))))) in (let TMP_98 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_97 \def (S O) in (drop TMP_97 O a0 a)))) in (let TMP_99 \def (ex2_2 C C 
TMP_96 TMP_98) in (let TMP_138 \def (\lambda (x: T).(\lambda (H2: (subst1 O u 
t (lift (S O) O x))).(let TMP_100 \def (Bind Abbr) in (let TMP_101 \def 
(CHead e TMP_100 u) in (let TMP_102 \def (drop_refl c0) in (let TMP_103 \def 
(Bind Abbr) in (let TMP_104 \def (CHead e TMP_103 u) in (let TMP_105 \def 
(Flat f) in (let TMP_106 \def (CHead c0 TMP_105 t) in (let TMP_107 \def (Bind 
Abbr) in (let TMP_108 \def (CHead e TMP_107 u) in (let TMP_109 \def 
(getl_gen_O TMP_106 TMP_108 H0) in (let TMP_110 \def (clear_gen_flat f c0 
TMP_104 t TMP_109) in (let TMP_111 \def (getl_intro O c0 TMP_101 c0 TMP_102 
TMP_110) in (let H3 \def (H e u TMP_111) in (let TMP_112 \def (\lambda (a0: 
C).(\lambda (_: C).(csubst1 O u c0 a0))) in (let TMP_114 \def (\lambda (a0: 
C).(\lambda (a: C).(let TMP_113 \def (S O) in (drop TMP_113 O a0 a)))) in 
(let TMP_117 \def (\lambda (a0: C).(\lambda (_: C).(let TMP_115 \def (Flat f) 
in (let TMP_116 \def (CHead c0 TMP_115 t) in (csubst1 O u TMP_116 a0))))) in 
(let TMP_119 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_118 \def (S O) in 
(drop TMP_118 O a0 a)))) in (let TMP_120 \def (ex2_2 C C TMP_117 TMP_119) in 
(let TMP_137 \def (\lambda (x0: C).(\lambda (x1: C).(\lambda (H4: (csubst1 O 
u c0 x0)).(\lambda (H5: (drop (S O) O x0 x1)).(let TMP_123 \def (\lambda (a0: 
C).(\lambda (_: C).(let TMP_121 \def (Flat f) in (let TMP_122 \def (CHead c0 
TMP_121 t) in (csubst1 O u TMP_122 a0))))) in (let TMP_125 \def (\lambda (a0: 
C).(\lambda (a: C).(let TMP_124 \def (S O) in (drop TMP_124 O a0 a)))) in 
(let TMP_126 \def (Flat f) in (let TMP_127 \def (S O) in (let TMP_128 \def 
(lift TMP_127 O x) in (let TMP_129 \def (CHead x0 TMP_126 TMP_128) in (let 
TMP_130 \def (S O) in (let TMP_131 \def (lift TMP_130 O x) in (let TMP_132 
\def (csubst1_flat f O u t TMP_131 H2 c0 x0 H4) in (let TMP_133 \def (Flat f) 
in (let TMP_134 \def (S O) in (let TMP_135 \def (lift TMP_134 O x) in (let 
TMP_136 \def (drop_drop TMP_133 O x0 x1 H5 TMP_135) in (ex2_2_intro C C 
TMP_123 TMP_125 TMP_129 x1 TMP_132 TMP_136)))))))))))))))))) in (ex2_2_ind C 
C TMP_112 TMP_114 TMP_120 TMP_137 H3)))))))))))))))))))))) in (ex_ind T 
TMP_93 TMP_99 TMP_138 H1))))))))))))) in (K_ind TMP_21 TMP_90 TMP_139 
k))))))) in (C_ind TMP_8 TMP_16 TMP_140 c))))) in (let TMP_269 \def (\lambda 
(n: nat).(\lambda (H: ((\forall (c: C).(\forall (e: C).(\forall (u: T).((getl 
n c (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: 
C).(csubst1 n u c a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) n a0 
a)))))))))).(\lambda (c: C).(let TMP_147 \def (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).((getl (S n) c0 (CHead e (Bind Abbr) u)) \to (let TMP_143 
\def (\lambda (a0: C).(\lambda (_: C).(let TMP_142 \def (S n) in (csubst1 
TMP_142 u c0 a0)))) in (let TMP_146 \def (\lambda (a0: C).(\lambda (a: 
C).(let TMP_144 \def (S O) in (let TMP_145 \def (S n) in (drop TMP_144 
TMP_145 a0 a))))) in (ex2_2 C C TMP_143 TMP_146))))))) in (let TMP_158 \def 
(\lambda (n0: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (H0: (getl (S n) 
(CSort n0) (CHead e (Bind Abbr) u))).(let TMP_148 \def (S n) in (let TMP_149 
\def (Bind Abbr) in (let TMP_150 \def (CHead e TMP_149 u) in (let TMP_153 
\def (\lambda (a0: C).(\lambda (_: C).(let TMP_151 \def (S n) in (let TMP_152 
\def (CSort n0) in (csubst1 TMP_151 u TMP_152 a0))))) in (let TMP_156 \def 
(\lambda (a0: C).(\lambda (a: C).(let TMP_154 \def (S O) in (let TMP_155 \def 
(S n) in (drop TMP_154 TMP_155 a0 a))))) in (let TMP_157 \def (ex2_2 C C 
TMP_153 TMP_156) in (getl_gen_sort n0 TMP_148 TMP_150 H0 TMP_157))))))))))) 
in (let TMP_268 \def (\lambda (c0: C).(\lambda (H0: ((\forall (e: C).(\forall 
(u: T).((getl (S n) c0 (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 (S n) u c0 a0))) (\lambda (a0: C).(\lambda (a: 
C).(drop (S O) (S n) a0 a))))))))).(\lambda (k: K).(let TMP_165 \def (\lambda 
(k0: K).(\forall (t: T).(\forall (e: C).(\forall (u: T).((getl (S n) (CHead 
c0 k0 t) (CHead e (Bind Abbr) u)) \to (let TMP_161 \def (\lambda (a0: 
C).(\lambda (_: C).(let TMP_159 \def (S n) in (let TMP_160 \def (CHead c0 k0 
t) in (csubst1 TMP_159 u TMP_160 a0))))) in (let TMP_164 \def (\lambda (a0: 
C).(\lambda (a: C).(let TMP_162 \def (S O) in (let TMP_163 \def (S n) in 
(drop TMP_162 TMP_163 a0 a))))) in (ex2_2 C C TMP_161 TMP_164)))))))) in (let 
TMP_212 \def (\lambda (b: B).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (H1: (getl (S n) (CHead c0 (Bind b) t) (CHead e (Bind Abbr) 
u))).(let H_x \def (subst1_ex u t n) in (let H2 \def H_x in (let TMP_168 \def 
(\lambda (t2: T).(let TMP_166 \def (S O) in (let TMP_167 \def (lift TMP_166 n 
t2) in (subst1 n u t TMP_167)))) in (let TMP_172 \def (\lambda (a0: 
C).(\lambda (_: C).(let TMP_169 \def (S n) in (let TMP_170 \def (Bind b) in 
(let TMP_171 \def (CHead c0 TMP_170 t) in (csubst1 TMP_169 u TMP_171 a0)))))) 
in (let TMP_175 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_173 \def (S O) 
in (let TMP_174 \def (S n) in (drop TMP_173 TMP_174 a0 a))))) in (let TMP_176 
\def (ex2_2 C C TMP_172 TMP_175) in (let TMP_211 \def (\lambda (x: 
T).(\lambda (H3: (subst1 n u t (lift (S O) n x))).(let TMP_177 \def (Bind b) 
in (let TMP_178 \def (Bind Abbr) in (let TMP_179 \def (CHead e TMP_178 u) in 
(let TMP_180 \def (getl_gen_S TMP_177 c0 TMP_179 t n H1) in (let H4 \def (H 
c0 e u TMP_180) in (let TMP_181 \def (\lambda (a0: C).(\lambda (_: 
C).(csubst1 n u c0 a0))) in (let TMP_183 \def (\lambda (a0: C).(\lambda (a: 
C).(let TMP_182 \def (S O) in (drop TMP_182 n a0 a)))) in (let TMP_187 \def 
(\lambda (a0: C).(\lambda (_: C).(let TMP_184 \def (S n) in (let TMP_185 \def 
(Bind b) in (let TMP_186 \def (CHead c0 TMP_185 t) in (csubst1 TMP_184 u 
TMP_186 a0)))))) in (let TMP_190 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_188 \def (S O) in (let TMP_189 \def (S n) in (drop TMP_188 TMP_189 a0 
a))))) in (let TMP_191 \def (ex2_2 C C TMP_187 TMP_190) in (let TMP_210 \def 
(\lambda (x0: C).(\lambda (x1: C).(\lambda (H5: (csubst1 n u c0 x0)).(\lambda 
(H6: (drop (S O) n x0 x1)).(let TMP_195 \def (\lambda (a0: C).(\lambda (_: 
C).(let TMP_192 \def (S n) in (let TMP_193 \def (Bind b) in (let TMP_194 \def 
(CHead c0 TMP_193 t) in (csubst1 TMP_192 u TMP_194 a0)))))) in (let TMP_198 
\def (\lambda (a0: C).(\lambda (a: C).(let TMP_196 \def (S O) in (let TMP_197 
\def (S n) in (drop TMP_196 TMP_197 a0 a))))) in (let TMP_199 \def (Bind b) 
in (let TMP_200 \def (S O) in (let TMP_201 \def (lift TMP_200 n x) in (let 
TMP_202 \def (CHead x0 TMP_199 TMP_201) in (let TMP_203 \def (Bind b) in (let 
TMP_204 \def (CHead x1 TMP_203 x) in (let TMP_205 \def (S O) in (let TMP_206 
\def (lift TMP_205 n x) in (let TMP_207 \def (csubst1_bind b n u t TMP_206 H3 
c0 x0 H5) in (let TMP_208 \def (S O) in (let TMP_209 \def (drop_skip_bind 
TMP_208 n x0 x1 H6 b x) in (ex2_2_intro C C TMP_195 TMP_198 TMP_202 TMP_204 
TMP_207 TMP_209)))))))))))))))))) in (ex2_2_ind C C TMP_181 TMP_183 TMP_191 
TMP_210 H4)))))))))))))) in (ex_ind T TMP_168 TMP_176 TMP_211 H2))))))))))))) 
in (let TMP_267 \def (\lambda (f: F).(\lambda (t: T).(\lambda (e: C).(\lambda 
(u: T).(\lambda (H1: (getl (S n) (CHead c0 (Flat f) t) (CHead e (Bind Abbr) 
u))).(let TMP_213 \def (S n) in (let H_x \def (subst1_ex u t TMP_213) in (let 
H2 \def H_x in (let TMP_218 \def (\lambda (t2: T).(let TMP_214 \def (S n) in 
(let TMP_215 \def (S O) in (let TMP_216 \def (S n) in (let TMP_217 \def (lift 
TMP_215 TMP_216 t2) in (subst1 TMP_214 u t TMP_217)))))) in (let TMP_222 \def 
(\lambda (a0: C).(\lambda (_: C).(let TMP_219 \def (S n) in (let TMP_220 \def 
(Flat f) in (let TMP_221 \def (CHead c0 TMP_220 t) in (csubst1 TMP_219 u 
TMP_221 a0)))))) in (let TMP_225 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_223 \def (S O) in (let TMP_224 \def (S n) in (drop TMP_223 TMP_224 a0 
a))))) in (let TMP_226 \def (ex2_2 C C TMP_222 TMP_225) in (let TMP_266 \def 
(\lambda (x: T).(\lambda (H3: (subst1 (S n) u t (lift (S O) (S n) x))).(let 
TMP_227 \def (Flat f) in (let TMP_228 \def (Bind Abbr) in (let TMP_229 \def 
(CHead e TMP_228 u) in (let TMP_230 \def (getl_gen_S TMP_227 c0 TMP_229 t n 
H1) in (let H4 \def (H0 e u TMP_230) in (let TMP_232 \def (\lambda (a0: 
C).(\lambda (_: C).(let TMP_231 \def (S n) in (csubst1 TMP_231 u c0 a0)))) in 
(let TMP_235 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_233 \def (S O) in 
(let TMP_234 \def (S n) in (drop TMP_233 TMP_234 a0 a))))) in (let TMP_239 
\def (\lambda (a0: C).(\lambda (_: C).(let TMP_236 \def (S n) in (let TMP_237 
\def (Flat f) in (let TMP_238 \def (CHead c0 TMP_237 t) in (csubst1 TMP_236 u 
TMP_238 a0)))))) in (let TMP_242 \def (\lambda (a0: C).(\lambda (a: C).(let 
TMP_240 \def (S O) in (let TMP_241 \def (S n) in (drop TMP_240 TMP_241 a0 
a))))) in (let TMP_243 \def (ex2_2 C C TMP_239 TMP_242) in (let TMP_265 \def 
(\lambda (x0: C).(\lambda (x1: C).(\lambda (H5: (csubst1 (S n) u c0 
x0)).(\lambda (H6: (drop (S O) (S n) x0 x1)).(let TMP_247 \def (\lambda (a0: 
C).(\lambda (_: C).(let TMP_244 \def (S n) in (let TMP_245 \def (Flat f) in 
(let TMP_246 \def (CHead c0 TMP_245 t) in (csubst1 TMP_244 u TMP_246 a0)))))) 
in (let TMP_250 \def (\lambda (a0: C).(\lambda (a: C).(let TMP_248 \def (S O) 
in (let TMP_249 \def (S n) in (drop TMP_248 TMP_249 a0 a))))) in (let TMP_251 
\def (Flat f) in (let TMP_252 \def (S O) in (let TMP_253 \def (S n) in (let 
TMP_254 \def (lift TMP_252 TMP_253 x) in (let TMP_255 \def (CHead x0 TMP_251 
TMP_254) in (let TMP_256 \def (Flat f) in (let TMP_257 \def (CHead x1 TMP_256 
x) in (let TMP_258 \def (S n) in (let TMP_259 \def (S O) in (let TMP_260 \def 
(S n) in (let TMP_261 \def (lift TMP_259 TMP_260 x) in (let TMP_262 \def 
(csubst1_flat f TMP_258 u t TMP_261 H3 c0 x0 H5) in (let TMP_263 \def (S O) 
in (let TMP_264 \def (drop_skip_flat TMP_263 n x0 x1 H6 f x) in (ex2_2_intro 
C C TMP_247 TMP_250 TMP_255 TMP_257 TMP_262 TMP_264))))))))))))))))))))) in 
(ex2_2_ind C C TMP_232 TMP_235 TMP_243 TMP_265 H4)))))))))))))) in (ex_ind T 
TMP_218 TMP_226 TMP_266 H2)))))))))))))) in (K_ind TMP_165 TMP_212 TMP_267 
k))))))) in (C_ind TMP_147 TMP_158 TMP_268 c))))))) in (nat_ind TMP_4 TMP_141 
TMP_269 d)))).

