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

include "basic_1/ty3/fwd.ma".

include "basic_1/pc3/fwd.ma".

theorem ty3_lift:
 \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((ty3 g e 
t1 t2) \to (\forall (c: C).(\forall (d: nat).(\forall (h: nat).((drop h d c 
e) \to (ty3 g c (lift h d t1) (lift h d t2))))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g e t1 t2)).(let TMP_3 \def (\lambda (c: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (c0: C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) 
\to (let TMP_1 \def (lift h d t) in (let TMP_2 \def (lift h d t0) in (ty3 g 
c0 TMP_1 TMP_2)))))))))) in (let TMP_11 \def (\lambda (c: C).(\lambda (t0: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c t0 t)).(\lambda (H1: ((\forall (c0: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 (lift h 
d t0) (lift h d t)))))))).(\lambda (u: T).(\lambda (t3: T).(\lambda (_: (ty3 
g c u t3)).(\lambda (H3: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d u) (lift h d 
t3)))))))).(\lambda (H4: (pc3 c t3 t0)).(\lambda (c0: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H5: (drop h d c0 c)).(let TMP_4 \def (lift h 
d t0) in (let TMP_5 \def (lift h d t) in (let TMP_6 \def (H1 c0 d h H5) in 
(let TMP_7 \def (lift h d u) in (let TMP_8 \def (lift h d t3) in (let TMP_9 
\def (H3 c0 d h H5) in (let TMP_10 \def (pc3_lift c0 c h d H5 t3 t0 H4) in 
(ty3_conv g c0 TMP_4 TMP_5 TMP_6 TMP_7 TMP_8 TMP_9 
TMP_10)))))))))))))))))))))) in (let TMP_31 \def (\lambda (c: C).(\lambda (m: 
nat).(\lambda (c0: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (_: (drop 
h d c0 c)).(let TMP_12 \def (TSort m) in (let TMP_16 \def (\lambda (t: 
T).(let TMP_13 \def (next g m) in (let TMP_14 \def (TSort TMP_13) in (let 
TMP_15 \def (lift h d TMP_14) in (ty3 g c0 t TMP_15))))) in (let TMP_17 \def 
(next g m) in (let TMP_18 \def (TSort TMP_17) in (let TMP_20 \def (\lambda 
(t: T).(let TMP_19 \def (TSort m) in (ty3 g c0 TMP_19 t))) in (let TMP_21 
\def (ty3_sort g c0 m) in (let TMP_22 \def (next g m) in (let TMP_23 \def 
(TSort TMP_22) in (let TMP_24 \def (lift h d TMP_23) in (let TMP_25 \def 
(next g m) in (let TMP_26 \def (lift_sort TMP_25 h d) in (let TMP_27 \def 
(eq_ind_r T TMP_18 TMP_20 TMP_21 TMP_24 TMP_26) in (let TMP_28 \def (TSort m) 
in (let TMP_29 \def (lift h d TMP_28) in (let TMP_30 \def (lift_sort m h d) 
in (eq_ind_r T TMP_12 TMP_16 TMP_27 TMP_29 TMP_30)))))))))))))))))))))) in 
(let TMP_233 \def (\lambda (n: nat).(\lambda (c: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (H0: (getl n c (CHead d (Bind Abbr) u))).(\lambda (t: 
T).(\lambda (H1: (ty3 g d u t)).(\lambda (H2: ((\forall (c0: C).(\forall (d0: 
nat).(\forall (h: nat).((drop h d0 c0 d) \to (ty3 g c0 (lift h d0 u) (lift h 
d0 t)))))))).(\lambda (c0: C).(\lambda (d0: nat).(\lambda (h: nat).(\lambda 
(H3: (drop h d0 c0 c)).(let TMP_32 \def (TLRef n) in (let TMP_33 \def (lift h 
d0 TMP_32) in (let TMP_34 \def (S n) in (let TMP_35 \def (lift TMP_34 O t) in 
(let TMP_36 \def (lift h d0 TMP_35) in (let TMP_37 \def (ty3 g c0 TMP_33 
TMP_36) in (let TMP_159 \def (\lambda (H4: (lt n d0)).(let TMP_38 \def (S n) 
in (let TMP_39 \def (S d0) in (let TMP_40 \def (S n) in (let TMP_41 \def (S 
TMP_40) in (let TMP_42 \def (S d0) in (let TMP_43 \def (S n) in (let TMP_44 
\def (le_n_S TMP_43 d0 H4) in (let TMP_45 \def (le_S TMP_41 TMP_42 TMP_44) in 
(let TMP_46 \def (le_S_n TMP_38 TMP_39 TMP_45) in (let TMP_47 \def (le_S_n n 
d0 TMP_46) in (let TMP_48 \def (Bind Abbr) in (let TMP_49 \def (CHead d 
TMP_48 u) in (let H5 \def (drop_getl_trans_le n d0 TMP_47 c0 c h H3 TMP_49 
H0) in (let TMP_50 \def (\lambda (e0: C).(\lambda (_: C).(drop n O c0 e0))) 
in (let TMP_52 \def (\lambda (e0: C).(\lambda (e1: C).(let TMP_51 \def (minus 
d0 n) in (drop h TMP_51 e0 e1)))) in (let TMP_55 \def (\lambda (_: 
C).(\lambda (e1: C).(let TMP_53 \def (Bind Abbr) in (let TMP_54 \def (CHead d 
TMP_53 u) in (clear e1 TMP_54))))) in (let TMP_56 \def (TLRef n) in (let 
TMP_57 \def (lift h d0 TMP_56) in (let TMP_58 \def (S n) in (let TMP_59 \def 
(lift TMP_58 O t) in (let TMP_60 \def (lift h d0 TMP_59) in (let TMP_61 \def 
(ty3 g c0 TMP_57 TMP_60) in (let TMP_158 \def (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop n O c0 x0)).(\lambda (H7: (drop h (minus d0 n) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abbr) u))).(let TMP_62 \def 
(minus d0 n) in (let TMP_63 \def (\lambda (n0: nat).(drop h n0 x0 x1)) in 
(let TMP_64 \def (S n) in (let TMP_65 \def (minus d0 TMP_64) in (let TMP_66 
\def (S TMP_65) in (let TMP_67 \def (minus_x_Sy d0 n H4) in (let H9 \def 
(eq_ind nat TMP_62 TMP_63 H7 TMP_66 TMP_67) in (let TMP_68 \def (S n) in (let 
TMP_69 \def (minus d0 TMP_68) in (let H10 \def (drop_clear_S x1 x0 h TMP_69 
H9 Abbr d u H8) in (let TMP_75 \def (\lambda (c1: C).(let TMP_70 \def (Bind 
Abbr) in (let TMP_71 \def (S n) in (let TMP_72 \def (minus d0 TMP_71) in (let 
TMP_73 \def (lift h TMP_72 u) in (let TMP_74 \def (CHead c1 TMP_70 TMP_73) in 
(clear x0 TMP_74))))))) in (let TMP_78 \def (\lambda (c1: C).(let TMP_76 \def 
(S n) in (let TMP_77 \def (minus d0 TMP_76) in (drop h TMP_77 c1 d)))) in 
(let TMP_79 \def (TLRef n) in (let TMP_80 \def (lift h d0 TMP_79) in (let 
TMP_81 \def (S n) in (let TMP_82 \def (lift TMP_81 O t) in (let TMP_83 \def 
(lift h d0 TMP_82) in (let TMP_84 \def (ty3 g c0 TMP_80 TMP_83) in (let 
TMP_157 \def (\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abbr) 
(lift h (minus d0 (S n)) u)))).(\lambda (H12: (drop h (minus d0 (S n)) x 
d)).(let TMP_85 \def (TLRef n) in (let TMP_89 \def (\lambda (t0: T).(let 
TMP_86 \def (S n) in (let TMP_87 \def (lift TMP_86 O t) in (let TMP_88 \def 
(lift h d0 TMP_87) in (ty3 g c0 t0 TMP_88))))) in (let TMP_90 \def (S n) in 
(let TMP_91 \def (S n) in (let TMP_92 \def (minus d0 TMP_91) in (let TMP_93 
\def (plus TMP_90 TMP_92) in (let TMP_98 \def (\lambda (n0: nat).(let TMP_94 
\def (TLRef n) in (let TMP_95 \def (S n) in (let TMP_96 \def (lift TMP_95 O 
t) in (let TMP_97 \def (lift h n0 TMP_96) in (ty3 g c0 TMP_94 TMP_97)))))) in 
(let TMP_99 \def (S n) in (let TMP_100 \def (S n) in (let TMP_101 \def (minus 
d0 TMP_100) in (let TMP_102 \def (lift h TMP_101 t) in (let TMP_103 \def 
(lift TMP_99 O TMP_102) in (let TMP_105 \def (\lambda (t0: T).(let TMP_104 
\def (TLRef n) in (ty3 g c0 TMP_104 t0))) in (let TMP_112 \def (\lambda (_: 
nat).(let TMP_106 \def (TLRef n) in (let TMP_107 \def (S n) in (let TMP_108 
\def (S n) in (let TMP_109 \def (minus d0 TMP_108) in (let TMP_110 \def (lift 
h TMP_109 t) in (let TMP_111 \def (lift TMP_107 O TMP_110) in (ty3 g c0 
TMP_106 TMP_111)))))))) in (let TMP_113 \def (S n) in (let TMP_114 \def 
(minus d0 TMP_113) in (let TMP_115 \def (lift h TMP_114 u) in (let TMP_116 
\def (Bind Abbr) in (let TMP_117 \def (S n) in (let TMP_118 \def (minus d0 
TMP_117) in (let TMP_119 \def (lift h TMP_118 u) in (let TMP_120 \def (CHead 
x TMP_116 TMP_119) in (let TMP_121 \def (getl_intro n c0 TMP_120 x0 H6 H11) 
in (let TMP_122 \def (S n) in (let TMP_123 \def (minus d0 TMP_122) in (let 
TMP_124 \def (lift h TMP_123 t) in (let TMP_125 \def (S n) in (let TMP_126 
\def (minus d0 TMP_125) in (let TMP_127 \def (H2 x TMP_126 h H12) in (let 
TMP_128 \def (ty3_abbr g n c0 x TMP_115 TMP_121 TMP_124 TMP_127) in (let 
TMP_129 \def (S n) in (let TMP_130 \def (S n) in (let TMP_131 \def (minus d0 
TMP_130) in (let TMP_132 \def (plus TMP_129 TMP_131) in (let TMP_133 \def (S 
n) in (let TMP_134 \def (le_plus_minus TMP_133 d0 H4) in (let TMP_135 \def 
(eq_ind nat d0 TMP_112 TMP_128 TMP_132 TMP_134) in (let TMP_136 \def (S n) in 
(let TMP_137 \def (S n) in (let TMP_138 \def (minus d0 TMP_137) in (let 
TMP_139 \def (plus TMP_136 TMP_138) in (let TMP_140 \def (S n) in (let 
TMP_141 \def (lift TMP_140 O t) in (let TMP_142 \def (lift h TMP_139 TMP_141) 
in (let TMP_143 \def (S n) in (let TMP_144 \def (S n) in (let TMP_145 \def 
(minus d0 TMP_144) in (let TMP_146 \def (S n) in (let TMP_147 \def (minus d0 
TMP_146) in (let TMP_148 \def (le_O_n TMP_147) in (let TMP_149 \def (lift_d t 
h TMP_143 TMP_145 O TMP_148) in (let TMP_150 \def (eq_ind_r T TMP_103 TMP_105 
TMP_135 TMP_142 TMP_149) in (let TMP_151 \def (S n) in (let TMP_152 \def 
(le_plus_minus_r TMP_151 d0 H4) in (let TMP_153 \def (eq_ind nat TMP_93 
TMP_98 TMP_150 d0 TMP_152) in (let TMP_154 \def (TLRef n) in (let TMP_155 
\def (lift h d0 TMP_154) in (let TMP_156 \def (lift_lref_lt n h d0 H4) in 
(eq_ind_r T TMP_85 TMP_89 TMP_153 TMP_155 
TMP_156)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex2_ind C TMP_75 TMP_78 TMP_84 TMP_157 H10))))))))))))))))))))))))) in 
(ex3_2_ind C C TMP_50 TMP_52 TMP_55 TMP_61 TMP_158 
H5))))))))))))))))))))))))) in (let TMP_232 \def (\lambda (H4: (le d0 
n)).(let TMP_160 \def (plus n h) in (let TMP_161 \def (TLRef TMP_160) in (let 
TMP_165 \def (\lambda (t0: T).(let TMP_162 \def (S n) in (let TMP_163 \def 
(lift TMP_162 O t) in (let TMP_164 \def (lift h d0 TMP_163) in (ty3 g c0 t0 
TMP_164))))) in (let TMP_166 \def (S n) in (let TMP_172 \def (\lambda (_: 
nat).(let TMP_167 \def (plus n h) in (let TMP_168 \def (TLRef TMP_167) in 
(let TMP_169 \def (S n) in (let TMP_170 \def (lift TMP_169 O t) in (let 
TMP_171 \def (lift h d0 TMP_170) in (ty3 g c0 TMP_168 TMP_171))))))) in (let 
TMP_173 \def (S n) in (let TMP_174 \def (plus h TMP_173) in (let TMP_175 \def 
(lift TMP_174 O t) in (let TMP_178 \def (\lambda (t0: T).(let TMP_176 \def 
(plus n h) in (let TMP_177 \def (TLRef TMP_176) in (ty3 g c0 TMP_177 t0)))) 
in (let TMP_179 \def (S n) in (let TMP_180 \def (plus TMP_179 h) in (let 
TMP_184 \def (\lambda (n0: nat).(let TMP_181 \def (plus n h) in (let TMP_182 
\def (TLRef TMP_181) in (let TMP_183 \def (lift n0 O t) in (ty3 g c0 TMP_182 
TMP_183))))) in (let TMP_185 \def (plus n h) in (let TMP_186 \def (Bind Abbr) 
in (let TMP_187 \def (CHead d TMP_186 u) in (let TMP_188 \def 
(drop_getl_trans_ge n c0 c d0 h H3 TMP_187 H0 H4) in (let TMP_189 \def 
(ty3_abbr g TMP_185 c0 d u TMP_188 t H1) in (let TMP_190 \def (S n) in (let 
TMP_191 \def (plus h TMP_190) in (let TMP_192 \def (S n) in (let TMP_193 \def 
(plus_sym h TMP_192) in (let TMP_194 \def (eq_ind_r nat TMP_180 TMP_184 
TMP_189 TMP_191 TMP_193) in (let TMP_195 \def (S n) in (let TMP_196 \def 
(lift TMP_195 O t) in (let TMP_197 \def (lift h d0 TMP_196) in (let TMP_198 
\def (S n) in (let TMP_199 \def (S n) in (let TMP_200 \def (S d0) in (let 
TMP_201 \def (S n) in (let TMP_202 \def (le_n_S d0 n H4) in (let TMP_203 \def 
(le_S TMP_200 TMP_201 TMP_202) in (let TMP_204 \def (le_S_n d0 TMP_199 
TMP_203) in (let TMP_205 \def (le_O_n d0) in (let TMP_206 \def (lift_free t 
TMP_198 h O d0 TMP_204 TMP_205) in (let TMP_207 \def (eq_ind_r T TMP_175 
TMP_178 TMP_194 TMP_197 TMP_206) in (let TMP_208 \def (S O) in (let TMP_209 
\def (plus n TMP_208) in (let TMP_210 \def (S O) in (let TMP_211 \def (plus 
TMP_210 n) in (let TMP_213 \def (\lambda (n0: nat).(let TMP_212 \def (S n) in 
(eq nat TMP_212 n0))) in (let TMP_214 \def (S n) in (let TMP_215 \def (S O) 
in (let TMP_216 \def (plus TMP_215 n) in (let TMP_217 \def (S O) in (let 
TMP_218 \def (plus TMP_217 n) in (let TMP_219 \def (le_n TMP_218) in (let 
TMP_220 \def (S n) in (let TMP_221 \def (le_n TMP_220) in (let TMP_222 \def 
(le_antisym TMP_214 TMP_216 TMP_219 TMP_221) in (let TMP_223 \def (S O) in 
(let TMP_224 \def (plus n TMP_223) in (let TMP_225 \def (S O) in (let TMP_226 
\def (plus_sym n TMP_225) in (let TMP_227 \def (eq_ind_r nat TMP_211 TMP_213 
TMP_222 TMP_224 TMP_226) in (let TMP_228 \def (eq_ind nat TMP_166 TMP_172 
TMP_207 TMP_209 TMP_227) in (let TMP_229 \def (TLRef n) in (let TMP_230 \def 
(lift h d0 TMP_229) in (let TMP_231 \def (lift_lref_ge n h d0 H4) in 
(eq_ind_r T TMP_161 TMP_165 TMP_228 TMP_230 
TMP_231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(lt_le_e n d0 TMP_37 TMP_159 TMP_232))))))))))))))))))))) in (let TMP_435 
\def (\lambda (n: nat).(\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (H0: (getl n c (CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda 
(H1: (ty3 g d u t)).(\lambda (H2: ((\forall (c0: C).(\forall (d0: 
nat).(\forall (h: nat).((drop h d0 c0 d) \to (ty3 g c0 (lift h d0 u) (lift h 
d0 t)))))))).(\lambda (c0: C).(\lambda (d0: nat).(\lambda (h: nat).(\lambda 
(H3: (drop h d0 c0 c)).(let TMP_234 \def (TLRef n) in (let TMP_235 \def (lift 
h d0 TMP_234) in (let TMP_236 \def (S n) in (let TMP_237 \def (lift TMP_236 O 
u) in (let TMP_238 \def (lift h d0 TMP_237) in (let TMP_239 \def (ty3 g c0 
TMP_235 TMP_238) in (let TMP_361 \def (\lambda (H4: (lt n d0)).(let TMP_240 
\def (S n) in (let TMP_241 \def (S d0) in (let TMP_242 \def (S n) in (let 
TMP_243 \def (S TMP_242) in (let TMP_244 \def (S d0) in (let TMP_245 \def (S 
n) in (let TMP_246 \def (le_n_S TMP_245 d0 H4) in (let TMP_247 \def (le_S 
TMP_243 TMP_244 TMP_246) in (let TMP_248 \def (le_S_n TMP_240 TMP_241 
TMP_247) in (let TMP_249 \def (le_S_n n d0 TMP_248) in (let TMP_250 \def 
(Bind Abst) in (let TMP_251 \def (CHead d TMP_250 u) in (let H5 \def 
(drop_getl_trans_le n d0 TMP_249 c0 c h H3 TMP_251 H0) in (let TMP_252 \def 
(\lambda (e0: C).(\lambda (_: C).(drop n O c0 e0))) in (let TMP_254 \def 
(\lambda (e0: C).(\lambda (e1: C).(let TMP_253 \def (minus d0 n) in (drop h 
TMP_253 e0 e1)))) in (let TMP_257 \def (\lambda (_: C).(\lambda (e1: C).(let 
TMP_255 \def (Bind Abst) in (let TMP_256 \def (CHead d TMP_255 u) in (clear 
e1 TMP_256))))) in (let TMP_258 \def (TLRef n) in (let TMP_259 \def (lift h 
d0 TMP_258) in (let TMP_260 \def (S n) in (let TMP_261 \def (lift TMP_260 O 
u) in (let TMP_262 \def (lift h d0 TMP_261) in (let TMP_263 \def (ty3 g c0 
TMP_259 TMP_262) in (let TMP_360 \def (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop n O c0 x0)).(\lambda (H7: (drop h (minus d0 n) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abst) u))).(let TMP_264 \def 
(minus d0 n) in (let TMP_265 \def (\lambda (n0: nat).(drop h n0 x0 x1)) in 
(let TMP_266 \def (S n) in (let TMP_267 \def (minus d0 TMP_266) in (let 
TMP_268 \def (S TMP_267) in (let TMP_269 \def (minus_x_Sy d0 n H4) in (let H9 
\def (eq_ind nat TMP_264 TMP_265 H7 TMP_268 TMP_269) in (let TMP_270 \def (S 
n) in (let TMP_271 \def (minus d0 TMP_270) in (let H10 \def (drop_clear_S x1 
x0 h TMP_271 H9 Abst d u H8) in (let TMP_277 \def (\lambda (c1: C).(let 
TMP_272 \def (Bind Abst) in (let TMP_273 \def (S n) in (let TMP_274 \def 
(minus d0 TMP_273) in (let TMP_275 \def (lift h TMP_274 u) in (let TMP_276 
\def (CHead c1 TMP_272 TMP_275) in (clear x0 TMP_276))))))) in (let TMP_280 
\def (\lambda (c1: C).(let TMP_278 \def (S n) in (let TMP_279 \def (minus d0 
TMP_278) in (drop h TMP_279 c1 d)))) in (let TMP_281 \def (TLRef n) in (let 
TMP_282 \def (lift h d0 TMP_281) in (let TMP_283 \def (S n) in (let TMP_284 
\def (lift TMP_283 O u) in (let TMP_285 \def (lift h d0 TMP_284) in (let 
TMP_286 \def (ty3 g c0 TMP_282 TMP_285) in (let TMP_359 \def (\lambda (x: 
C).(\lambda (H11: (clear x0 (CHead x (Bind Abst) (lift h (minus d0 (S n)) 
u)))).(\lambda (H12: (drop h (minus d0 (S n)) x d)).(let TMP_287 \def (TLRef 
n) in (let TMP_291 \def (\lambda (t0: T).(let TMP_288 \def (S n) in (let 
TMP_289 \def (lift TMP_288 O u) in (let TMP_290 \def (lift h d0 TMP_289) in 
(ty3 g c0 t0 TMP_290))))) in (let TMP_292 \def (S n) in (let TMP_293 \def (S 
n) in (let TMP_294 \def (minus d0 TMP_293) in (let TMP_295 \def (plus TMP_292 
TMP_294) in (let TMP_300 \def (\lambda (n0: nat).(let TMP_296 \def (TLRef n) 
in (let TMP_297 \def (S n) in (let TMP_298 \def (lift TMP_297 O u) in (let 
TMP_299 \def (lift h n0 TMP_298) in (ty3 g c0 TMP_296 TMP_299)))))) in (let 
TMP_301 \def (S n) in (let TMP_302 \def (S n) in (let TMP_303 \def (minus d0 
TMP_302) in (let TMP_304 \def (lift h TMP_303 u) in (let TMP_305 \def (lift 
TMP_301 O TMP_304) in (let TMP_307 \def (\lambda (t0: T).(let TMP_306 \def 
(TLRef n) in (ty3 g c0 TMP_306 t0))) in (let TMP_314 \def (\lambda (_: 
nat).(let TMP_308 \def (TLRef n) in (let TMP_309 \def (S n) in (let TMP_310 
\def (S n) in (let TMP_311 \def (minus d0 TMP_310) in (let TMP_312 \def (lift 
h TMP_311 u) in (let TMP_313 \def (lift TMP_309 O TMP_312) in (ty3 g c0 
TMP_308 TMP_313)))))))) in (let TMP_315 \def (S n) in (let TMP_316 \def 
(minus d0 TMP_315) in (let TMP_317 \def (lift h TMP_316 u) in (let TMP_318 
\def (Bind Abst) in (let TMP_319 \def (S n) in (let TMP_320 \def (minus d0 
TMP_319) in (let TMP_321 \def (lift h TMP_320 u) in (let TMP_322 \def (CHead 
x TMP_318 TMP_321) in (let TMP_323 \def (getl_intro n c0 TMP_322 x0 H6 H11) 
in (let TMP_324 \def (S n) in (let TMP_325 \def (minus d0 TMP_324) in (let 
TMP_326 \def (lift h TMP_325 t) in (let TMP_327 \def (S n) in (let TMP_328 
\def (minus d0 TMP_327) in (let TMP_329 \def (H2 x TMP_328 h H12) in (let 
TMP_330 \def (ty3_abst g n c0 x TMP_317 TMP_323 TMP_326 TMP_329) in (let 
TMP_331 \def (S n) in (let TMP_332 \def (S n) in (let TMP_333 \def (minus d0 
TMP_332) in (let TMP_334 \def (plus TMP_331 TMP_333) in (let TMP_335 \def (S 
n) in (let TMP_336 \def (le_plus_minus TMP_335 d0 H4) in (let TMP_337 \def 
(eq_ind nat d0 TMP_314 TMP_330 TMP_334 TMP_336) in (let TMP_338 \def (S n) in 
(let TMP_339 \def (S n) in (let TMP_340 \def (minus d0 TMP_339) in (let 
TMP_341 \def (plus TMP_338 TMP_340) in (let TMP_342 \def (S n) in (let 
TMP_343 \def (lift TMP_342 O u) in (let TMP_344 \def (lift h TMP_341 TMP_343) 
in (let TMP_345 \def (S n) in (let TMP_346 \def (S n) in (let TMP_347 \def 
(minus d0 TMP_346) in (let TMP_348 \def (S n) in (let TMP_349 \def (minus d0 
TMP_348) in (let TMP_350 \def (le_O_n TMP_349) in (let TMP_351 \def (lift_d u 
h TMP_345 TMP_347 O TMP_350) in (let TMP_352 \def (eq_ind_r T TMP_305 TMP_307 
TMP_337 TMP_344 TMP_351) in (let TMP_353 \def (S n) in (let TMP_354 \def 
(le_plus_minus_r TMP_353 d0 H4) in (let TMP_355 \def (eq_ind nat TMP_295 
TMP_300 TMP_352 d0 TMP_354) in (let TMP_356 \def (TLRef n) in (let TMP_357 
\def (lift h d0 TMP_356) in (let TMP_358 \def (lift_lref_lt n h d0 H4) in 
(eq_ind_r T TMP_287 TMP_291 TMP_355 TMP_357 
TMP_358)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex2_ind C TMP_277 TMP_280 TMP_286 TMP_359 H10))))))))))))))))))))))))) in 
(ex3_2_ind C C TMP_252 TMP_254 TMP_257 TMP_263 TMP_360 
H5))))))))))))))))))))))))) in (let TMP_434 \def (\lambda (H4: (le d0 
n)).(let TMP_362 \def (plus n h) in (let TMP_363 \def (TLRef TMP_362) in (let 
TMP_367 \def (\lambda (t0: T).(let TMP_364 \def (S n) in (let TMP_365 \def 
(lift TMP_364 O u) in (let TMP_366 \def (lift h d0 TMP_365) in (ty3 g c0 t0 
TMP_366))))) in (let TMP_368 \def (S n) in (let TMP_374 \def (\lambda (_: 
nat).(let TMP_369 \def (plus n h) in (let TMP_370 \def (TLRef TMP_369) in 
(let TMP_371 \def (S n) in (let TMP_372 \def (lift TMP_371 O u) in (let 
TMP_373 \def (lift h d0 TMP_372) in (ty3 g c0 TMP_370 TMP_373))))))) in (let 
TMP_375 \def (S n) in (let TMP_376 \def (plus h TMP_375) in (let TMP_377 \def 
(lift TMP_376 O u) in (let TMP_380 \def (\lambda (t0: T).(let TMP_378 \def 
(plus n h) in (let TMP_379 \def (TLRef TMP_378) in (ty3 g c0 TMP_379 t0)))) 
in (let TMP_381 \def (S n) in (let TMP_382 \def (plus TMP_381 h) in (let 
TMP_386 \def (\lambda (n0: nat).(let TMP_383 \def (plus n h) in (let TMP_384 
\def (TLRef TMP_383) in (let TMP_385 \def (lift n0 O u) in (ty3 g c0 TMP_384 
TMP_385))))) in (let TMP_387 \def (plus n h) in (let TMP_388 \def (Bind Abst) 
in (let TMP_389 \def (CHead d TMP_388 u) in (let TMP_390 \def 
(drop_getl_trans_ge n c0 c d0 h H3 TMP_389 H0 H4) in (let TMP_391 \def 
(ty3_abst g TMP_387 c0 d u TMP_390 t H1) in (let TMP_392 \def (S n) in (let 
TMP_393 \def (plus h TMP_392) in (let TMP_394 \def (S n) in (let TMP_395 \def 
(plus_sym h TMP_394) in (let TMP_396 \def (eq_ind_r nat TMP_382 TMP_386 
TMP_391 TMP_393 TMP_395) in (let TMP_397 \def (S n) in (let TMP_398 \def 
(lift TMP_397 O u) in (let TMP_399 \def (lift h d0 TMP_398) in (let TMP_400 
\def (S n) in (let TMP_401 \def (S n) in (let TMP_402 \def (S d0) in (let 
TMP_403 \def (S n) in (let TMP_404 \def (le_n_S d0 n H4) in (let TMP_405 \def 
(le_S TMP_402 TMP_403 TMP_404) in (let TMP_406 \def (le_S_n d0 TMP_401 
TMP_405) in (let TMP_407 \def (le_O_n d0) in (let TMP_408 \def (lift_free u 
TMP_400 h O d0 TMP_406 TMP_407) in (let TMP_409 \def (eq_ind_r T TMP_377 
TMP_380 TMP_396 TMP_399 TMP_408) in (let TMP_410 \def (S O) in (let TMP_411 
\def (plus n TMP_410) in (let TMP_412 \def (S O) in (let TMP_413 \def (plus 
TMP_412 n) in (let TMP_415 \def (\lambda (n0: nat).(let TMP_414 \def (S n) in 
(eq nat TMP_414 n0))) in (let TMP_416 \def (S n) in (let TMP_417 \def (S O) 
in (let TMP_418 \def (plus TMP_417 n) in (let TMP_419 \def (S O) in (let 
TMP_420 \def (plus TMP_419 n) in (let TMP_421 \def (le_n TMP_420) in (let 
TMP_422 \def (S n) in (let TMP_423 \def (le_n TMP_422) in (let TMP_424 \def 
(le_antisym TMP_416 TMP_418 TMP_421 TMP_423) in (let TMP_425 \def (S O) in 
(let TMP_426 \def (plus n TMP_425) in (let TMP_427 \def (S O) in (let TMP_428 
\def (plus_sym n TMP_427) in (let TMP_429 \def (eq_ind_r nat TMP_413 TMP_415 
TMP_424 TMP_426 TMP_428) in (let TMP_430 \def (eq_ind nat TMP_368 TMP_374 
TMP_409 TMP_411 TMP_429) in (let TMP_431 \def (TLRef n) in (let TMP_432 \def 
(lift h d0 TMP_431) in (let TMP_433 \def (lift_lref_ge n h d0 H4) in 
(eq_ind_r T TMP_363 TMP_367 TMP_430 TMP_432 
TMP_433)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(lt_le_e n d0 TMP_239 TMP_361 TMP_434))))))))))))))))))))) in (let TMP_484 
\def (\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c u 
t)).(\lambda (H1: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d u) (lift h d t)))))))).(\lambda 
(b: B).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (ty3 g (CHead c (Bind 
b) u) t0 t3)).(\lambda (H3: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 (CHead c (Bind b) u)) \to (ty3 g c0 (lift h d t0) (lift h 
d t3)))))))).(\lambda (c0: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda 
(H4: (drop h d c0 c)).(let TMP_436 \def (Bind b) in (let TMP_437 \def (lift h 
d u) in (let TMP_438 \def (Bind b) in (let TMP_439 \def (s TMP_438 d) in (let 
TMP_440 \def (lift h TMP_439 t0) in (let TMP_441 \def (THead TMP_436 TMP_437 
TMP_440) in (let TMP_445 \def (\lambda (t4: T).(let TMP_442 \def (Bind b) in 
(let TMP_443 \def (THead TMP_442 u t3) in (let TMP_444 \def (lift h d 
TMP_443) in (ty3 g c0 t4 TMP_444))))) in (let TMP_446 \def (Bind b) in (let 
TMP_447 \def (lift h d u) in (let TMP_448 \def (Bind b) in (let TMP_449 \def 
(s TMP_448 d) in (let TMP_450 \def (lift h TMP_449 t3) in (let TMP_451 \def 
(THead TMP_446 TMP_447 TMP_450) in (let TMP_458 \def (\lambda (t4: T).(let 
TMP_452 \def (Bind b) in (let TMP_453 \def (lift h d u) in (let TMP_454 \def 
(Bind b) in (let TMP_455 \def (s TMP_454 d) in (let TMP_456 \def (lift h 
TMP_455 t0) in (let TMP_457 \def (THead TMP_452 TMP_453 TMP_456) in (ty3 g c0 
TMP_457 t4)))))))) in (let TMP_459 \def (lift h d u) in (let TMP_460 \def 
(lift h d t) in (let TMP_461 \def (H1 c0 d h H4) in (let TMP_462 \def (S d) 
in (let TMP_463 \def (lift h TMP_462 t0) in (let TMP_464 \def (S d) in (let 
TMP_465 \def (lift h TMP_464 t3) in (let TMP_466 \def (Bind b) in (let 
TMP_467 \def (lift h d u) in (let TMP_468 \def (CHead c0 TMP_466 TMP_467) in 
(let TMP_469 \def (S d) in (let TMP_470 \def (drop_skip_bind h d c0 c H4 b u) 
in (let TMP_471 \def (H3 TMP_468 TMP_469 h TMP_470) in (let TMP_472 \def 
(ty3_bind g c0 TMP_459 TMP_460 TMP_461 b TMP_463 TMP_465 TMP_471) in (let 
TMP_473 \def (Bind b) in (let TMP_474 \def (THead TMP_473 u t3) in (let 
TMP_475 \def (lift h d TMP_474) in (let TMP_476 \def (Bind b) in (let TMP_477 
\def (lift_head TMP_476 u t3 h d) in (let TMP_478 \def (eq_ind_r T TMP_451 
TMP_458 TMP_472 TMP_475 TMP_477) in (let TMP_479 \def (Bind b) in (let 
TMP_480 \def (THead TMP_479 u t0) in (let TMP_481 \def (lift h d TMP_480) in 
(let TMP_482 \def (Bind b) in (let TMP_483 \def (lift_head TMP_482 u t0 h d) 
in (eq_ind_r T TMP_441 TMP_445 TMP_478 TMP_481 
TMP_483)))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_577 
\def (\lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c w 
u)).(\lambda (H1: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d w) (lift h d u)))))))).(\lambda 
(v: T).(\lambda (t: T).(\lambda (_: (ty3 g c v (THead (Bind Abst) u 
t))).(\lambda (H3: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d v) (lift h d (THead (Bind Abst) 
u t))))))))).(\lambda (c0: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda 
(H4: (drop h d c0 c)).(let TMP_485 \def (Flat Appl) in (let TMP_486 \def 
(lift h d w) in (let TMP_487 \def (Flat Appl) in (let TMP_488 \def (s TMP_487 
d) in (let TMP_489 \def (lift h TMP_488 v) in (let TMP_490 \def (THead 
TMP_485 TMP_486 TMP_489) in (let TMP_496 \def (\lambda (t0: T).(let TMP_491 
\def (Flat Appl) in (let TMP_492 \def (Bind Abst) in (let TMP_493 \def (THead 
TMP_492 u t) in (let TMP_494 \def (THead TMP_491 w TMP_493) in (let TMP_495 
\def (lift h d TMP_494) in (ty3 g c0 t0 TMP_495))))))) in (let TMP_497 \def 
(Flat Appl) in (let TMP_498 \def (lift h d w) in (let TMP_499 \def (Flat 
Appl) in (let TMP_500 \def (s TMP_499 d) in (let TMP_501 \def (Bind Abst) in 
(let TMP_502 \def (THead TMP_501 u t) in (let TMP_503 \def (lift h TMP_500 
TMP_502) in (let TMP_504 \def (THead TMP_497 TMP_498 TMP_503) in (let TMP_511 
\def (\lambda (t0: T).(let TMP_505 \def (Flat Appl) in (let TMP_506 \def 
(lift h d w) in (let TMP_507 \def (Flat Appl) in (let TMP_508 \def (s TMP_507 
d) in (let TMP_509 \def (lift h TMP_508 v) in (let TMP_510 \def (THead 
TMP_505 TMP_506 TMP_509) in (ty3 g c0 TMP_510 t0)))))))) in (let TMP_512 \def 
(Bind Abst) in (let TMP_513 \def (Flat Appl) in (let TMP_514 \def (s TMP_513 
d) in (let TMP_515 \def (lift h TMP_514 u) in (let TMP_516 \def (Bind Abst) 
in (let TMP_517 \def (Flat Appl) in (let TMP_518 \def (s TMP_517 d) in (let 
TMP_519 \def (s TMP_516 TMP_518) in (let TMP_520 \def (lift h TMP_519 t) in 
(let TMP_521 \def (THead TMP_512 TMP_515 TMP_520) in (let TMP_531 \def 
(\lambda (t0: T).(let TMP_522 \def (Flat Appl) in (let TMP_523 \def (lift h d 
w) in (let TMP_524 \def (Flat Appl) in (let TMP_525 \def (s TMP_524 d) in 
(let TMP_526 \def (lift h TMP_525 v) in (let TMP_527 \def (THead TMP_522 
TMP_523 TMP_526) in (let TMP_528 \def (Flat Appl) in (let TMP_529 \def (lift 
h d w) in (let TMP_530 \def (THead TMP_528 TMP_529 t0) in (ty3 g c0 TMP_527 
TMP_530))))))))))) in (let TMP_532 \def (lift h d w) in (let TMP_533 \def 
(lift h d u) in (let TMP_534 \def (H1 c0 d h H4) in (let TMP_535 \def (lift h 
d v) in (let TMP_536 \def (S d) in (let TMP_537 \def (lift h TMP_536 t) in 
(let TMP_538 \def (Bind Abst) in (let TMP_539 \def (THead TMP_538 u t) in 
(let TMP_540 \def (lift h d TMP_539) in (let TMP_542 \def (\lambda (t0: 
T).(let TMP_541 \def (lift h d v) in (ty3 g c0 TMP_541 t0))) in (let TMP_543 
\def (H3 c0 d h H4) in (let TMP_544 \def (Bind Abst) in (let TMP_545 \def 
(lift h d u) in (let TMP_546 \def (S d) in (let TMP_547 \def (lift h TMP_546 
t) in (let TMP_548 \def (THead TMP_544 TMP_545 TMP_547) in (let TMP_549 \def 
(lift_bind Abst u t h d) in (let TMP_550 \def (eq_ind T TMP_540 TMP_542 
TMP_543 TMP_548 TMP_549) in (let TMP_551 \def (ty3_appl g c0 TMP_532 TMP_533 
TMP_534 TMP_535 TMP_537 TMP_550) in (let TMP_552 \def (Flat Appl) in (let 
TMP_553 \def (s TMP_552 d) in (let TMP_554 \def (Bind Abst) in (let TMP_555 
\def (THead TMP_554 u t) in (let TMP_556 \def (lift h TMP_553 TMP_555) in 
(let TMP_557 \def (Bind Abst) in (let TMP_558 \def (Flat Appl) in (let 
TMP_559 \def (s TMP_558 d) in (let TMP_560 \def (lift_head TMP_557 u t h 
TMP_559) in (let TMP_561 \def (eq_ind_r T TMP_521 TMP_531 TMP_551 TMP_556 
TMP_560) in (let TMP_562 \def (Flat Appl) in (let TMP_563 \def (Bind Abst) in 
(let TMP_564 \def (THead TMP_563 u t) in (let TMP_565 \def (THead TMP_562 w 
TMP_564) in (let TMP_566 \def (lift h d TMP_565) in (let TMP_567 \def (Flat 
Appl) in (let TMP_568 \def (Bind Abst) in (let TMP_569 \def (THead TMP_568 u 
t) in (let TMP_570 \def (lift_head TMP_567 w TMP_569 h d) in (let TMP_571 
\def (eq_ind_r T TMP_504 TMP_511 TMP_561 TMP_566 TMP_570) in (let TMP_572 
\def (Flat Appl) in (let TMP_573 \def (THead TMP_572 w v) in (let TMP_574 
\def (lift h d TMP_573) in (let TMP_575 \def (Flat Appl) in (let TMP_576 \def 
(lift_head TMP_575 w v h d) in (eq_ind_r T TMP_490 TMP_496 TMP_571 TMP_574 
TMP_576)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))) in (let TMP_624 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(t3: T).(\lambda (_: (ty3 g c t0 t3)).(\lambda (H1: ((\forall (c0: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 (lift h 
d t0) (lift h d t3)))))))).(\lambda (t4: T).(\lambda (_: (ty3 g c t3 
t4)).(\lambda (H3: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d t3) (lift h d 
t4)))))))).(\lambda (c0: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H4: 
(drop h d c0 c)).(let TMP_578 \def (Flat Cast) in (let TMP_579 \def (lift h d 
t3) in (let TMP_580 \def (Flat Cast) in (let TMP_581 \def (s TMP_580 d) in 
(let TMP_582 \def (lift h TMP_581 t0) in (let TMP_583 \def (THead TMP_578 
TMP_579 TMP_582) in (let TMP_587 \def (\lambda (t: T).(let TMP_584 \def (Flat 
Cast) in (let TMP_585 \def (THead TMP_584 t4 t3) in (let TMP_586 \def (lift h 
d TMP_585) in (ty3 g c0 t TMP_586))))) in (let TMP_588 \def (Flat Cast) in 
(let TMP_589 \def (lift h d t4) in (let TMP_590 \def (Flat Cast) in (let 
TMP_591 \def (s TMP_590 d) in (let TMP_592 \def (lift h TMP_591 t3) in (let 
TMP_593 \def (THead TMP_588 TMP_589 TMP_592) in (let TMP_600 \def (\lambda 
(t: T).(let TMP_594 \def (Flat Cast) in (let TMP_595 \def (lift h d t3) in 
(let TMP_596 \def (Flat Cast) in (let TMP_597 \def (s TMP_596 d) in (let 
TMP_598 \def (lift h TMP_597 t0) in (let TMP_599 \def (THead TMP_594 TMP_595 
TMP_598) in (ty3 g c0 TMP_599 t)))))))) in (let TMP_601 \def (Flat Cast) in 
(let TMP_602 \def (s TMP_601 d) in (let TMP_603 \def (lift h TMP_602 t0) in 
(let TMP_604 \def (Flat Cast) in (let TMP_605 \def (s TMP_604 d) in (let 
TMP_606 \def (lift h TMP_605 t3) in (let TMP_607 \def (Flat Cast) in (let 
TMP_608 \def (s TMP_607 d) in (let TMP_609 \def (H1 c0 TMP_608 h H4) in (let 
TMP_610 \def (lift h d t4) in (let TMP_611 \def (H3 c0 d h H4) in (let 
TMP_612 \def (ty3_cast g c0 TMP_603 TMP_606 TMP_609 TMP_610 TMP_611) in (let 
TMP_613 \def (Flat Cast) in (let TMP_614 \def (THead TMP_613 t4 t3) in (let 
TMP_615 \def (lift h d TMP_614) in (let TMP_616 \def (Flat Cast) in (let 
TMP_617 \def (lift_head TMP_616 t4 t3 h d) in (let TMP_618 \def (eq_ind_r T 
TMP_593 TMP_600 TMP_612 TMP_615 TMP_617) in (let TMP_619 \def (Flat Cast) in 
(let TMP_620 \def (THead TMP_619 t3 t0) in (let TMP_621 \def (lift h d 
TMP_620) in (let TMP_622 \def (Flat Cast) in (let TMP_623 \def (lift_head 
TMP_622 t3 t0 h d) in (eq_ind_r T TMP_583 TMP_587 TMP_618 TMP_621 
TMP_623)))))))))))))))))))))))))))))))))))))))))))))))))) in (ty3_ind g TMP_3 
TMP_11 TMP_31 TMP_233 TMP_435 TMP_484 TMP_577 TMP_624 e t1 t2 H))))))))))))).

theorem ty3_correct:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (ex T (\lambda (t: T).(ty3 g c t2 t)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(let TMP_2 \def (\lambda (c0: C).(\lambda (_: 
T).(\lambda (t0: T).(let TMP_1 \def (\lambda (t3: T).(ty3 g c0 t0 t3)) in (ex 
T TMP_1))))) in (let TMP_4 \def (\lambda (c0: C).(\lambda (t0: T).(\lambda 
(t: T).(\lambda (H0: (ty3 g c0 t0 t)).(\lambda (_: (ex T (\lambda (t3: 
T).(ty3 g c0 t t3)))).(\lambda (u: T).(\lambda (t3: T).(\lambda (_: (ty3 g c0 
u t3)).(\lambda (_: (ex T (\lambda (t4: T).(ty3 g c0 t3 t4)))).(\lambda (_: 
(pc3 c0 t3 t0)).(let TMP_3 \def (\lambda (t4: T).(ty3 g c0 t0 t4)) in 
(ex_intro T TMP_3 t H0)))))))))))) in (let TMP_13 \def (\lambda (c0: 
C).(\lambda (m: nat).(let TMP_7 \def (\lambda (t: T).(let TMP_5 \def (next g 
m) in (let TMP_6 \def (TSort TMP_5) in (ty3 g c0 TMP_6 t)))) in (let TMP_8 
\def (next g m) in (let TMP_9 \def (next g TMP_8) in (let TMP_10 \def (TSort 
TMP_9) in (let TMP_11 \def (next g m) in (let TMP_12 \def (ty3_sort g c0 
TMP_11) in (ex_intro T TMP_7 TMP_10 TMP_12))))))))) in (let TMP_28 \def 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H0: (getl n c0 (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (H2: (ex T (\lambda (t0: T).(ty3 g d t t0)))).(let H3 \def 
H2 in (let TMP_14 \def (\lambda (t0: T).(ty3 g d t t0)) in (let TMP_17 \def 
(\lambda (t0: T).(let TMP_15 \def (S n) in (let TMP_16 \def (lift TMP_15 O t) 
in (ty3 g c0 TMP_16 t0)))) in (let TMP_18 \def (ex T TMP_17) in (let TMP_27 
\def (\lambda (x: T).(\lambda (H4: (ty3 g d t x)).(let TMP_21 \def (\lambda 
(t0: T).(let TMP_19 \def (S n) in (let TMP_20 \def (lift TMP_19 O t) in (ty3 
g c0 TMP_20 t0)))) in (let TMP_22 \def (S n) in (let TMP_23 \def (lift TMP_22 
O x) in (let TMP_24 \def (S n) in (let TMP_25 \def (getl_drop Abbr c0 d u n 
H0) in (let TMP_26 \def (ty3_lift g d t x H4 c0 O TMP_24 TMP_25) in (ex_intro 
T TMP_21 TMP_23 TMP_26))))))))) in (ex_ind T TMP_14 TMP_18 TMP_27 
H3)))))))))))))) in (let TMP_37 \def (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind 
Abst) u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u t)).(\lambda (_: (ex T 
(\lambda (t0: T).(ty3 g d t t0)))).(let TMP_31 \def (\lambda (t0: T).(let 
TMP_29 \def (S n) in (let TMP_30 \def (lift TMP_29 O u) in (ty3 g c0 TMP_30 
t0)))) in (let TMP_32 \def (S n) in (let TMP_33 \def (lift TMP_32 O t) in 
(let TMP_34 \def (S n) in (let TMP_35 \def (getl_drop Abst c0 d u n H0) in 
(let TMP_36 \def (ty3_lift g d u t H1 c0 O TMP_34 TMP_35) in (ex_intro T 
TMP_31 TMP_33 TMP_36))))))))))))))) in (let TMP_52 \def (\lambda (c0: 
C).(\lambda (u: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u t)).(\lambda (_: 
(ex T (\lambda (t0: T).(ty3 g c0 t t0)))).(\lambda (b: B).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u) t0 
t3)).(\lambda (H3: (ex T (\lambda (t4: T).(ty3 g (CHead c0 (Bind b) u) t3 
t4)))).(let H4 \def H3 in (let TMP_40 \def (\lambda (t4: T).(let TMP_38 \def 
(Bind b) in (let TMP_39 \def (CHead c0 TMP_38 u) in (ty3 g TMP_39 t3 t4)))) 
in (let TMP_43 \def (\lambda (t4: T).(let TMP_41 \def (Bind b) in (let TMP_42 
\def (THead TMP_41 u t3) in (ty3 g c0 TMP_42 t4)))) in (let TMP_44 \def (ex T 
TMP_43) in (let TMP_51 \def (\lambda (x: T).(\lambda (H5: (ty3 g (CHead c0 
(Bind b) u) t3 x)).(let TMP_47 \def (\lambda (t4: T).(let TMP_45 \def (Bind 
b) in (let TMP_46 \def (THead TMP_45 u t3) in (ty3 g c0 TMP_46 t4)))) in (let 
TMP_48 \def (Bind b) in (let TMP_49 \def (THead TMP_48 u x) in (let TMP_50 
\def (ty3_bind g c0 u t H0 b t3 x H5) in (ex_intro T TMP_47 TMP_49 
TMP_50))))))) in (ex_ind T TMP_40 TMP_44 TMP_51 H4)))))))))))))))) in (let 
TMP_99 \def (\lambda (c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (H0: 
(ty3 g c0 w u)).(\lambda (H1: (ex T (\lambda (t: T).(ty3 g c0 u 
t)))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead (Bind 
Abst) u t))).(\lambda (H3: (ex T (\lambda (t0: T).(ty3 g c0 (THead (Bind 
Abst) u t) t0)))).(let H4 \def H1 in (let TMP_53 \def (\lambda (t0: T).(ty3 g 
c0 u t0)) in (let TMP_58 \def (\lambda (t0: T).(let TMP_54 \def (Flat Appl) 
in (let TMP_55 \def (Bind Abst) in (let TMP_56 \def (THead TMP_55 u t) in 
(let TMP_57 \def (THead TMP_54 w TMP_56) in (ty3 g c0 TMP_57 t0)))))) in (let 
TMP_59 \def (ex T TMP_58) in (let TMP_98 \def (\lambda (x: T).(\lambda (_: 
(ty3 g c0 u x)).(let H6 \def H3 in (let TMP_62 \def (\lambda (t0: T).(let 
TMP_60 \def (Bind Abst) in (let TMP_61 \def (THead TMP_60 u t) in (ty3 g c0 
TMP_61 t0)))) in (let TMP_67 \def (\lambda (t0: T).(let TMP_63 \def (Flat 
Appl) in (let TMP_64 \def (Bind Abst) in (let TMP_65 \def (THead TMP_64 u t) 
in (let TMP_66 \def (THead TMP_63 w TMP_65) in (ty3 g c0 TMP_66 t0)))))) in 
(let TMP_68 \def (ex T TMP_67) in (let TMP_97 \def (\lambda (x0: T).(\lambda 
(H7: (ty3 g c0 (THead (Bind Abst) u t) x0)).(let TMP_71 \def (\lambda (t3: 
T).(\lambda (_: T).(let TMP_69 \def (Bind Abst) in (let TMP_70 \def (THead 
TMP_69 u t3) in (pc3 c0 TMP_70 x0))))) in (let TMP_72 \def (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c0 u t0))) in (let TMP_75 \def (\lambda (t3: 
T).(\lambda (_: T).(let TMP_73 \def (Bind Abst) in (let TMP_74 \def (CHead c0 
TMP_73 u) in (ty3 g TMP_74 t t3))))) in (let TMP_80 \def (\lambda (t0: 
T).(let TMP_76 \def (Flat Appl) in (let TMP_77 \def (Bind Abst) in (let 
TMP_78 \def (THead TMP_77 u t) in (let TMP_79 \def (THead TMP_76 w TMP_78) in 
(ty3 g c0 TMP_79 t0)))))) in (let TMP_81 \def (ex T TMP_80) in (let TMP_95 
\def (\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c0 (THead (Bind 
Abst) u x1) x0)).(\lambda (H9: (ty3 g c0 u x2)).(\lambda (H10: (ty3 g (CHead 
c0 (Bind Abst) u) t x1)).(let TMP_86 \def (\lambda (t0: T).(let TMP_82 \def 
(Flat Appl) in (let TMP_83 \def (Bind Abst) in (let TMP_84 \def (THead TMP_83 
u t) in (let TMP_85 \def (THead TMP_82 w TMP_84) in (ty3 g c0 TMP_85 t0)))))) 
in (let TMP_87 \def (Flat Appl) in (let TMP_88 \def (Bind Abst) in (let 
TMP_89 \def (THead TMP_88 u x1) in (let TMP_90 \def (THead TMP_87 w TMP_89) 
in (let TMP_91 \def (Bind Abst) in (let TMP_92 \def (THead TMP_91 u t) in 
(let TMP_93 \def (ty3_bind g c0 u x2 H9 Abst t x1 H10) in (let TMP_94 \def 
(ty3_appl g c0 w u H0 TMP_92 x1 TMP_93) in (ex_intro T TMP_86 TMP_90 
TMP_94))))))))))))))) in (let TMP_96 \def (ty3_gen_bind g Abst c0 u t x0 H7) 
in (ex3_2_ind T T TMP_71 TMP_72 TMP_75 TMP_81 TMP_95 TMP_96)))))))))) in 
(ex_ind T TMP_62 TMP_68 TMP_97 H6)))))))) in (ex_ind T TMP_53 TMP_59 TMP_98 
H4))))))))))))))) in (let TMP_112 \def (\lambda (c0: C).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (_: (ty3 g c0 t0 t3)).(\lambda (_: (ex T 
(\lambda (t: T).(ty3 g c0 t3 t)))).(\lambda (t4: T).(\lambda (H2: (ty3 g c0 
t3 t4)).(\lambda (H3: (ex T (\lambda (t: T).(ty3 g c0 t4 t)))).(let H4 \def 
H3 in (let TMP_100 \def (\lambda (t: T).(ty3 g c0 t4 t)) in (let TMP_103 \def 
(\lambda (t: T).(let TMP_101 \def (Flat Cast) in (let TMP_102 \def (THead 
TMP_101 t4 t3) in (ty3 g c0 TMP_102 t)))) in (let TMP_104 \def (ex T TMP_103) 
in (let TMP_111 \def (\lambda (x: T).(\lambda (H5: (ty3 g c0 t4 x)).(let 
TMP_107 \def (\lambda (t: T).(let TMP_105 \def (Flat Cast) in (let TMP_106 
\def (THead TMP_105 t4 t3) in (ty3 g c0 TMP_106 t)))) in (let TMP_108 \def 
(Flat Cast) in (let TMP_109 \def (THead TMP_108 x t4) in (let TMP_110 \def 
(ty3_cast g c0 t3 t4 H2 x H5) in (ex_intro T TMP_107 TMP_109 TMP_110))))))) 
in (ex_ind T TMP_100 TMP_104 TMP_111 H4)))))))))))))) in (ty3_ind g TMP_2 
TMP_4 TMP_13 TMP_28 TMP_37 TMP_52 TMP_99 TMP_112 c t1 t2 H))))))))))))).

theorem ty3_unique:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((ty3 g c u t2) \to (pc3 c t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(let TMP_1 \def (\lambda (c0: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (t2: T).((ty3 g c0 t t2) \to (pc3 c0 t0 t2)))))) in (let 
TMP_4 \def (\lambda (c0: C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: 
(ty3 g c0 t2 t)).(\lambda (_: ((\forall (t3: T).((ty3 g c0 t2 t3) \to (pc3 c0 
t t3))))).(\lambda (u0: T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 u0 
t0)).(\lambda (H3: ((\forall (t3: T).((ty3 g c0 u0 t3) \to (pc3 c0 t0 
t3))))).(\lambda (H4: (pc3 c0 t0 t2)).(\lambda (t3: T).(\lambda (H5: (ty3 g 
c0 u0 t3)).(let TMP_2 \def (pc3_s c0 t2 t0 H4) in (let TMP_3 \def (H3 t3 H5) 
in (pc3_t t0 c0 t2 TMP_2 t3 TMP_3))))))))))))))) in (let TMP_5 \def (\lambda 
(c0: C).(\lambda (m: nat).(\lambda (t2: T).(\lambda (H0: (ty3 g c0 (TSort m) 
t2)).(ty3_gen_sort g c0 t2 m H0))))) in (let TMP_120 \def (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abbr) u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 
t)).(\lambda (H2: ((\forall (t2: T).((ty3 g d u0 t2) \to (pc3 d t 
t2))))).(\lambda (t2: T).(\lambda (H3: (ty3 g c0 (TLRef n) t2)).(let TMP_8 
\def (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(let TMP_6 \def (S n) 
in (let TMP_7 \def (lift TMP_6 O t0) in (pc3 c0 TMP_7 t2)))))) in (let TMP_11 
\def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_9 \def (Bind 
Abbr) in (let TMP_10 \def (CHead e TMP_9 u1) in (getl n c0 TMP_10)))))) in 
(let TMP_12 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e 
u1 t0)))) in (let TMP_13 \def (ex3_3 C T T TMP_8 TMP_11 TMP_12) in (let 
TMP_16 \def (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_14 \def 
(S n) in (let TMP_15 \def (lift TMP_14 O u1) in (pc3 c0 TMP_15 t2)))))) in 
(let TMP_19 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_17 
\def (Bind Abst) in (let TMP_18 \def (CHead e TMP_17 u1) in (getl n c0 
TMP_18)))))) in (let TMP_20 \def (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(ty3 g e u1 t0)))) in (let TMP_21 \def (ex3_3 C T T TMP_16 TMP_19 
TMP_20) in (let TMP_22 \def (S n) in (let TMP_23 \def (lift TMP_22 O t) in 
(let TMP_24 \def (pc3 c0 TMP_23 t2) in (let TMP_83 \def (\lambda (H4: (ex3_3 
C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O 
t0) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead 
e (Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 
g e u1 t0)))))).(let TMP_27 \def (\lambda (_: C).(\lambda (_: T).(\lambda 
(t0: T).(let TMP_25 \def (S n) in (let TMP_26 \def (lift TMP_25 O t0) in (pc3 
c0 TMP_26 t2)))))) in (let TMP_30 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_28 \def (Bind Abbr) in (let TMP_29 \def (CHead e 
TMP_28 u1) in (getl n c0 TMP_29)))))) in (let TMP_31 \def (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))) in (let TMP_32 \def 
(S n) in (let TMP_33 \def (lift TMP_32 O t) in (let TMP_34 \def (pc3 c0 
TMP_33 t2) in (let TMP_82 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (H5: (pc3 c0 (lift (S n) O x2) t2)).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abbr) x1))).(\lambda (H7: (ty3 g x0 x1 x2)).(let TMP_35 \def 
(Bind Abbr) in (let TMP_36 \def (CHead d TMP_35 u0) in (let TMP_37 \def 
(\lambda (c1: C).(getl n c0 c1)) in (let TMP_38 \def (Bind Abbr) in (let 
TMP_39 \def (CHead x0 TMP_38 x1) in (let TMP_40 \def (Bind Abbr) in (let 
TMP_41 \def (CHead d TMP_40 u0) in (let TMP_42 \def (Bind Abbr) in (let 
TMP_43 \def (CHead x0 TMP_42 x1) in (let TMP_44 \def (getl_mono c0 TMP_41 n 
H0 TMP_43 H6) in (let H8 \def (eq_ind C TMP_36 TMP_37 H0 TMP_39 TMP_44) in 
(let TMP_45 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow d | 
(CHead c1 _ _) \Rightarrow c1])) in (let TMP_46 \def (Bind Abbr) in (let 
TMP_47 \def (CHead d TMP_46 u0) in (let TMP_48 \def (Bind Abbr) in (let 
TMP_49 \def (CHead x0 TMP_48 x1) in (let TMP_50 \def (Bind Abbr) in (let 
TMP_51 \def (CHead d TMP_50 u0) in (let TMP_52 \def (Bind Abbr) in (let 
TMP_53 \def (CHead x0 TMP_52 x1) in (let TMP_54 \def (getl_mono c0 TMP_51 n 
H0 TMP_53 H6) in (let H9 \def (f_equal C C TMP_45 TMP_47 TMP_49 TMP_54) in 
(let TMP_55 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t0) \Rightarrow t0])) in (let TMP_56 \def (Bind Abbr) in (let 
TMP_57 \def (CHead d TMP_56 u0) in (let TMP_58 \def (Bind Abbr) in (let 
TMP_59 \def (CHead x0 TMP_58 x1) in (let TMP_60 \def (Bind Abbr) in (let 
TMP_61 \def (CHead d TMP_60 u0) in (let TMP_62 \def (Bind Abbr) in (let 
TMP_63 \def (CHead x0 TMP_62 x1) in (let TMP_64 \def (getl_mono c0 TMP_61 n 
H0 TMP_63 H6) in (let H10 \def (f_equal C T TMP_55 TMP_57 TMP_59 TMP_64) in 
(let TMP_81 \def (\lambda (H11: (eq C d x0)).(let TMP_67 \def (\lambda (t0: 
T).(let TMP_65 \def (Bind Abbr) in (let TMP_66 \def (CHead x0 TMP_65 t0) in 
(getl n c0 TMP_66)))) in (let H12 \def (eq_ind_r T x1 TMP_67 H8 u0 H10) in 
(let TMP_68 \def (\lambda (t0: T).(ty3 g x0 t0 x2)) in (let H13 \def 
(eq_ind_r T x1 TMP_68 H7 u0 H10) in (let TMP_71 \def (\lambda (c1: C).(let 
TMP_69 \def (Bind Abbr) in (let TMP_70 \def (CHead c1 TMP_69 u0) in (getl n 
c0 TMP_70)))) in (let H14 \def (eq_ind_r C x0 TMP_71 H12 d H11) in (let 
TMP_72 \def (\lambda (c1: C).(ty3 g c1 u0 x2)) in (let H15 \def (eq_ind_r C 
x0 TMP_72 H13 d H11) in (let TMP_73 \def (S n) in (let TMP_74 \def (lift 
TMP_73 O x2) in (let TMP_75 \def (S n) in (let TMP_76 \def (lift TMP_75 O t) 
in (let TMP_77 \def (S n) in (let TMP_78 \def (getl_drop Abbr c0 d u0 n H14) 
in (let TMP_79 \def (H2 x2 H15) in (let TMP_80 \def (pc3_lift c0 d TMP_77 O 
TMP_78 t x2 TMP_79) in (pc3_t TMP_74 c0 TMP_76 TMP_80 t2 H5)))))))))))))))))) 
in (TMP_81 H9))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind C T T 
TMP_27 TMP_30 TMP_31 TMP_34 TMP_82 H4))))))))) in (let TMP_118 \def (\lambda 
(H4: (ex3_3 C T T (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(pc3 c0 
(lift (S n) O u1) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(ty3 g e u1 t0)))))).(let TMP_86 \def (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(let TMP_84 \def (S n) in (let TMP_85 
\def (lift TMP_84 O u1) in (pc3 c0 TMP_85 t2)))))) in (let TMP_89 \def 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_87 \def (Bind Abst) 
in (let TMP_88 \def (CHead e TMP_87 u1) in (getl n c0 TMP_88)))))) in (let 
TMP_90 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 
t0)))) in (let TMP_91 \def (S n) in (let TMP_92 \def (lift TMP_91 O t) in 
(let TMP_93 \def (pc3 c0 TMP_92 t2) in (let TMP_117 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c0 (lift (S n) O x1) 
t2)).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abst) x1))).(\lambda (_: (ty3 g 
x0 x1 x2)).(let TMP_94 \def (Bind Abbr) in (let TMP_95 \def (CHead d TMP_94 
u0) in (let TMP_96 \def (\lambda (c1: C).(getl n c0 c1)) in (let TMP_97 \def 
(Bind Abst) in (let TMP_98 \def (CHead x0 TMP_97 x1) in (let TMP_99 \def 
(Bind Abbr) in (let TMP_100 \def (CHead d TMP_99 u0) in (let TMP_101 \def 
(Bind Abst) in (let TMP_102 \def (CHead x0 TMP_101 x1) in (let TMP_103 \def 
(getl_mono c0 TMP_100 n H0 TMP_102 H6) in (let H8 \def (eq_ind C TMP_95 
TMP_96 H0 TMP_98 TMP_103) in (let TMP_104 \def (Bind Abbr) in (let TMP_105 
\def (CHead d TMP_104 u0) in (let TMP_106 \def (\lambda (ee: C).(match ee 
with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k with 
[(Bind b) \Rightarrow (match b with [Abbr \Rightarrow True | Abst \Rightarrow 
False | Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) in (let 
TMP_107 \def (Bind Abst) in (let TMP_108 \def (CHead x0 TMP_107 x1) in (let 
TMP_109 \def (Bind Abbr) in (let TMP_110 \def (CHead d TMP_109 u0) in (let 
TMP_111 \def (Bind Abst) in (let TMP_112 \def (CHead x0 TMP_111 x1) in (let 
TMP_113 \def (getl_mono c0 TMP_110 n H0 TMP_112 H6) in (let H9 \def (eq_ind C 
TMP_105 TMP_106 I TMP_108 TMP_113) in (let TMP_114 \def (S n) in (let TMP_115 
\def (lift TMP_114 O t) in (let TMP_116 \def (pc3 c0 TMP_115 t2) in 
(False_ind TMP_116 H9)))))))))))))))))))))))))))))))) in (ex3_3_ind C T T 
TMP_86 TMP_89 TMP_90 TMP_93 TMP_117 H4))))))))) in (let TMP_119 \def 
(ty3_gen_lref g c0 t2 n H3) in (or_ind TMP_13 TMP_21 TMP_24 TMP_83 TMP_118 
TMP_119))))))))))))))))))))))))) in (let TMP_230 \def (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abst) u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 
t)).(\lambda (_: ((\forall (t2: T).((ty3 g d u0 t2) \to (pc3 d t 
t2))))).(\lambda (t2: T).(\lambda (H3: (ty3 g c0 (TLRef n) t2)).(let TMP_123 
\def (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(let TMP_121 \def (S n) 
in (let TMP_122 \def (lift TMP_121 O t0) in (pc3 c0 TMP_122 t2)))))) in (let 
TMP_126 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_124 
\def (Bind Abbr) in (let TMP_125 \def (CHead e TMP_124 u1) in (getl n c0 
TMP_125)))))) in (let TMP_127 \def (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(ty3 g e u1 t0)))) in (let TMP_128 \def (ex3_3 C T T TMP_123 TMP_126 
TMP_127) in (let TMP_131 \def (\lambda (_: C).(\lambda (u1: T).(\lambda (_: 
T).(let TMP_129 \def (S n) in (let TMP_130 \def (lift TMP_129 O u1) in (pc3 
c0 TMP_130 t2)))))) in (let TMP_134 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_132 \def (Bind Abst) in (let TMP_133 \def (CHead 
e TMP_132 u1) in (getl n c0 TMP_133)))))) in (let TMP_135 \def (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))) in (let TMP_136 \def 
(ex3_3 C T T TMP_131 TMP_134 TMP_135) in (let TMP_137 \def (S n) in (let 
TMP_138 \def (lift TMP_137 O u0) in (let TMP_139 \def (pc3 c0 TMP_138 t2) in 
(let TMP_174 \def (\lambda (H4: (ex3_3 C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda 
(u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))))).(let TMP_142 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(let TMP_140 \def (S n) in 
(let TMP_141 \def (lift TMP_140 O t0) in (pc3 c0 TMP_141 t2)))))) in (let 
TMP_145 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_143 
\def (Bind Abbr) in (let TMP_144 \def (CHead e TMP_143 u1) in (getl n c0 
TMP_144)))))) in (let TMP_146 \def (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(ty3 g e u1 t0)))) in (let TMP_147 \def (S n) in (let TMP_148 \def 
(lift TMP_147 O u0) in (let TMP_149 \def (pc3 c0 TMP_148 t2) in (let TMP_173 
\def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c0 
(lift (S n) O x2) t2)).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (ty3 g x0 x1 x2)).(let TMP_150 \def (Bind Abst) in (let 
TMP_151 \def (CHead d TMP_150 u0) in (let TMP_152 \def (\lambda (c1: C).(getl 
n c0 c1)) in (let TMP_153 \def (Bind Abbr) in (let TMP_154 \def (CHead x0 
TMP_153 x1) in (let TMP_155 \def (Bind Abst) in (let TMP_156 \def (CHead d 
TMP_155 u0) in (let TMP_157 \def (Bind Abbr) in (let TMP_158 \def (CHead x0 
TMP_157 x1) in (let TMP_159 \def (getl_mono c0 TMP_156 n H0 TMP_158 H6) in 
(let H8 \def (eq_ind C TMP_151 TMP_152 H0 TMP_154 TMP_159) in (let TMP_160 
\def (Bind Abst) in (let TMP_161 \def (CHead d TMP_160 u0) in (let TMP_162 
\def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ 
k _) \Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_163 \def (Bind Abbr) in (let TMP_164 
\def (CHead x0 TMP_163 x1) in (let TMP_165 \def (Bind Abst) in (let TMP_166 
\def (CHead d TMP_165 u0) in (let TMP_167 \def (Bind Abbr) in (let TMP_168 
\def (CHead x0 TMP_167 x1) in (let TMP_169 \def (getl_mono c0 TMP_166 n H0 
TMP_168 H6) in (let H9 \def (eq_ind C TMP_161 TMP_162 I TMP_164 TMP_169) in 
(let TMP_170 \def (S n) in (let TMP_171 \def (lift TMP_170 O u0) in (let 
TMP_172 \def (pc3 c0 TMP_171 t2) in (False_ind TMP_172 
H9)))))))))))))))))))))))))))))))) in (ex3_3_ind C T T TMP_142 TMP_145 
TMP_146 TMP_149 TMP_173 H4))))))))) in (let TMP_228 \def (\lambda (H4: (ex3_3 
C T T (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(pc3 c0 (lift (S n) O 
u1) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead 
e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 
g e u1 t0)))))).(let TMP_177 \def (\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(let TMP_175 \def (S n) in (let TMP_176 \def (lift TMP_175 O u1) in 
(pc3 c0 TMP_176 t2)))))) in (let TMP_180 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_178 \def (Bind Abst) in (let TMP_179 \def (CHead 
e TMP_178 u1) in (getl n c0 TMP_179)))))) in (let TMP_181 \def (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))) in (let TMP_182 \def 
(S n) in (let TMP_183 \def (lift TMP_182 O u0) in (let TMP_184 \def (pc3 c0 
TMP_183 t2) in (let TMP_227 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (H5: (pc3 c0 (lift (S n) O x1) t2)).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abst) x1))).(\lambda (H7: (ty3 g x0 x1 x2)).(let TMP_185 \def 
(Bind Abst) in (let TMP_186 \def (CHead d TMP_185 u0) in (let TMP_187 \def 
(\lambda (c1: C).(getl n c0 c1)) in (let TMP_188 \def (Bind Abst) in (let 
TMP_189 \def (CHead x0 TMP_188 x1) in (let TMP_190 \def (Bind Abst) in (let 
TMP_191 \def (CHead d TMP_190 u0) in (let TMP_192 \def (Bind Abst) in (let 
TMP_193 \def (CHead x0 TMP_192 x1) in (let TMP_194 \def (getl_mono c0 TMP_191 
n H0 TMP_193 H6) in (let H8 \def (eq_ind C TMP_186 TMP_187 H0 TMP_189 
TMP_194) in (let TMP_195 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_196 \def (Bind 
Abst) in (let TMP_197 \def (CHead d TMP_196 u0) in (let TMP_198 \def (Bind 
Abst) in (let TMP_199 \def (CHead x0 TMP_198 x1) in (let TMP_200 \def (Bind 
Abst) in (let TMP_201 \def (CHead d TMP_200 u0) in (let TMP_202 \def (Bind 
Abst) in (let TMP_203 \def (CHead x0 TMP_202 x1) in (let TMP_204 \def 
(getl_mono c0 TMP_201 n H0 TMP_203 H6) in (let H9 \def (f_equal C C TMP_195 
TMP_197 TMP_199 TMP_204) in (let TMP_205 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_206 
\def (Bind Abst) in (let TMP_207 \def (CHead d TMP_206 u0) in (let TMP_208 
\def (Bind Abst) in (let TMP_209 \def (CHead x0 TMP_208 x1) in (let TMP_210 
\def (Bind Abst) in (let TMP_211 \def (CHead d TMP_210 u0) in (let TMP_212 
\def (Bind Abst) in (let TMP_213 \def (CHead x0 TMP_212 x1) in (let TMP_214 
\def (getl_mono c0 TMP_211 n H0 TMP_213 H6) in (let H10 \def (f_equal C T 
TMP_205 TMP_207 TMP_209 TMP_214) in (let TMP_226 \def (\lambda (H11: (eq C d 
x0)).(let TMP_217 \def (\lambda (t0: T).(let TMP_215 \def (Bind Abst) in (let 
TMP_216 \def (CHead x0 TMP_215 t0) in (getl n c0 TMP_216)))) in (let H12 \def 
(eq_ind_r T x1 TMP_217 H8 u0 H10) in (let TMP_218 \def (\lambda (t0: T).(ty3 
g x0 t0 x2)) in (let H13 \def (eq_ind_r T x1 TMP_218 H7 u0 H10) in (let 
TMP_221 \def (\lambda (t0: T).(let TMP_219 \def (S n) in (let TMP_220 \def 
(lift TMP_219 O t0) in (pc3 c0 TMP_220 t2)))) in (let H14 \def (eq_ind_r T x1 
TMP_221 H5 u0 H10) in (let TMP_224 \def (\lambda (c1: C).(let TMP_222 \def 
(Bind Abst) in (let TMP_223 \def (CHead c1 TMP_222 u0) in (getl n c0 
TMP_223)))) in (let H15 \def (eq_ind_r C x0 TMP_224 H12 d H11) in (let 
TMP_225 \def (\lambda (c1: C).(ty3 g c1 u0 x2)) in (let H16 \def (eq_ind_r C 
x0 TMP_225 H13 d H11) in H14))))))))))) in (TMP_226 
H9))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind C T T TMP_177 
TMP_180 TMP_181 TMP_184 TMP_227 H4))))))))) in (let TMP_229 \def 
(ty3_gen_lref g c0 t2 n H3) in (or_ind TMP_128 TMP_136 TMP_139 TMP_174 
TMP_228 TMP_229))))))))))))))))))))))))) in (let TMP_250 \def (\lambda (c0: 
C).(\lambda (u0: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u0 t)).(\lambda 
(_: ((\forall (t2: T).((ty3 g c0 u0 t2) \to (pc3 c0 t t2))))).(\lambda (b: 
B).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u0) t0 t2)).(\lambda (H3: ((\forall (t3: T).((ty3 g (CHead c0 (Bind b) u0) t0 
t3) \to (pc3 (CHead c0 (Bind b) u0) t2 t3))))).(\lambda (t3: T).(\lambda (H4: 
(ty3 g c0 (THead (Bind b) u0 t0) t3)).(let TMP_233 \def (\lambda (t4: 
T).(\lambda (_: T).(let TMP_231 \def (Bind b) in (let TMP_232 \def (THead 
TMP_231 u0 t4) in (pc3 c0 TMP_232 t3))))) in (let TMP_234 \def (\lambda (_: 
T).(\lambda (t5: T).(ty3 g c0 u0 t5))) in (let TMP_237 \def (\lambda (t4: 
T).(\lambda (_: T).(let TMP_235 \def (Bind b) in (let TMP_236 \def (CHead c0 
TMP_235 u0) in (ty3 g TMP_236 t0 t4))))) in (let TMP_238 \def (Bind b) in 
(let TMP_239 \def (THead TMP_238 u0 t2) in (let TMP_240 \def (pc3 c0 TMP_239 
t3) in (let TMP_248 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (pc3 
c0 (THead (Bind b) u0 x0) t3)).(\lambda (_: (ty3 g c0 u0 x1)).(\lambda (H7: 
(ty3 g (CHead c0 (Bind b) u0) t0 x0)).(let TMP_241 \def (Bind b) in (let 
TMP_242 \def (THead TMP_241 u0 x0) in (let TMP_243 \def (Bind b) in (let 
TMP_244 \def (THead TMP_243 u0 t2) in (let TMP_245 \def (Bind b) in (let 
TMP_246 \def (H3 x0 H7) in (let TMP_247 \def (pc3_head_2 c0 u0 t2 x0 TMP_245 
TMP_246) in (pc3_t TMP_242 c0 TMP_244 TMP_247 t3 H5))))))))))))) in (let 
TMP_249 \def (ty3_gen_bind g b c0 u0 t0 t3 H4) in (ex3_2_ind T T TMP_233 
TMP_234 TMP_237 TMP_240 TMP_248 TMP_249))))))))))))))))))))) in (let TMP_283 
\def (\lambda (c0: C).(\lambda (w: T).(\lambda (u0: T).(\lambda (_: (ty3 g c0 
w u0)).(\lambda (_: ((\forall (t2: T).((ty3 g c0 w t2) \to (pc3 c0 u0 
t2))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead (Bind 
Abst) u0 t))).(\lambda (H3: ((\forall (t2: T).((ty3 g c0 v t2) \to (pc3 c0 
(THead (Bind Abst) u0 t) t2))))).(\lambda (t2: T).(\lambda (H4: (ty3 g c0 
(THead (Flat Appl) w v) t2)).(let TMP_255 \def (\lambda (u1: T).(\lambda (t0: 
T).(let TMP_251 \def (Flat Appl) in (let TMP_252 \def (Bind Abst) in (let 
TMP_253 \def (THead TMP_252 u1 t0) in (let TMP_254 \def (THead TMP_251 w 
TMP_253) in (pc3 c0 TMP_254 t2))))))) in (let TMP_258 \def (\lambda (u1: 
T).(\lambda (t0: T).(let TMP_256 \def (Bind Abst) in (let TMP_257 \def (THead 
TMP_256 u1 t0) in (ty3 g c0 v TMP_257))))) in (let TMP_259 \def (\lambda (u1: 
T).(\lambda (_: T).(ty3 g c0 w u1))) in (let TMP_260 \def (Flat Appl) in (let 
TMP_261 \def (Bind Abst) in (let TMP_262 \def (THead TMP_261 u0 t) in (let 
TMP_263 \def (THead TMP_260 w TMP_262) in (let TMP_264 \def (pc3 c0 TMP_263 
t2) in (let TMP_281 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (pc3 
c0 (THead (Flat Appl) w (THead (Bind Abst) x0 x1)) t2)).(\lambda (H6: (ty3 g 
c0 v (THead (Bind Abst) x0 x1))).(\lambda (_: (ty3 g c0 w x0)).(let TMP_265 
\def (Flat Appl) in (let TMP_266 \def (Bind Abst) in (let TMP_267 \def (THead 
TMP_266 x0 x1) in (let TMP_268 \def (THead TMP_265 w TMP_267) in (let TMP_269 
\def (Flat Appl) in (let TMP_270 \def (Bind Abst) in (let TMP_271 \def (THead 
TMP_270 u0 t) in (let TMP_272 \def (THead TMP_269 w TMP_271) in (let TMP_273 
\def (Bind Abst) in (let TMP_274 \def (THead TMP_273 u0 t) in (let TMP_275 
\def (Bind Abst) in (let TMP_276 \def (THead TMP_275 x0 x1) in (let TMP_277 
\def (Bind Abst) in (let TMP_278 \def (THead TMP_277 x0 x1) in (let TMP_279 
\def (H3 TMP_278 H6) in (let TMP_280 \def (pc3_thin_dx c0 TMP_274 TMP_276 
TMP_279 w Appl) in (pc3_t TMP_268 c0 TMP_272 TMP_280 t2 
H5)))))))))))))))))))))) in (let TMP_282 \def (ty3_gen_appl g c0 w v t2 H4) 
in (ex3_2_ind T T TMP_255 TMP_258 TMP_259 TMP_264 TMP_281 
TMP_282)))))))))))))))))))))) in (let TMP_301 \def (\lambda (c0: C).(\lambda 
(t0: T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t0 t2)).(\lambda (_: 
((\forall (t3: T).((ty3 g c0 t0 t3) \to (pc3 c0 t2 t3))))).(\lambda (t3: 
T).(\lambda (_: (ty3 g c0 t2 t3)).(\lambda (H3: ((\forall (t4: T).((ty3 g c0 
t2 t4) \to (pc3 c0 t3 t4))))).(\lambda (t4: T).(\lambda (H4: (ty3 g c0 (THead 
(Flat Cast) t2 t0) t4)).(let TMP_286 \def (\lambda (t5: T).(let TMP_284 \def 
(Flat Cast) in (let TMP_285 \def (THead TMP_284 t5 t2) in (pc3 c0 TMP_285 
t4)))) in (let TMP_287 \def (\lambda (_: T).(ty3 g c0 t0 t2)) in (let TMP_288 
\def (\lambda (t5: T).(ty3 g c0 t2 t5)) in (let TMP_289 \def (Flat Cast) in 
(let TMP_290 \def (THead TMP_289 t3 t2) in (let TMP_291 \def (pc3 c0 TMP_290 
t4) in (let TMP_299 \def (\lambda (x0: T).(\lambda (H5: (pc3 c0 (THead (Flat 
Cast) x0 t2) t4)).(\lambda (_: (ty3 g c0 t0 t2)).(\lambda (H7: (ty3 g c0 t2 
x0)).(let TMP_292 \def (Flat Cast) in (let TMP_293 \def (THead TMP_292 x0 t2) 
in (let TMP_294 \def (Flat Cast) in (let TMP_295 \def (THead TMP_294 t3 t2) 
in (let TMP_296 \def (H3 x0 H7) in (let TMP_297 \def (Flat Cast) in (let 
TMP_298 \def (pc3_head_1 c0 t3 x0 TMP_296 TMP_297 t2) in (pc3_t TMP_293 c0 
TMP_295 TMP_298 t4 H5)))))))))))) in (let TMP_300 \def (ty3_gen_cast g c0 t0 
t2 t4 H4) in (ex3_ind T TMP_286 TMP_287 TMP_288 TMP_291 TMP_299 
TMP_300))))))))))))))))))) in (ty3_ind g TMP_1 TMP_4 TMP_5 TMP_120 TMP_230 
TMP_250 TMP_283 TMP_301 c u t1 H))))))))))))).

theorem ty3_gen_abst_abst:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall 
(t2: T).((ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u t2)) \to (ex2 
T (\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) 
u) t1 t2))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u 
t2))).(let TMP_3 \def (\lambda (t: T).(let TMP_1 \def (Bind Abst) in (let 
TMP_2 \def (THead TMP_1 u t2) in (ty3 g c TMP_2 t)))) in (let TMP_4 \def 
(\lambda (w: T).(ty3 g c u w)) in (let TMP_7 \def (\lambda (_: T).(let TMP_5 
\def (Bind Abst) in (let TMP_6 \def (CHead c TMP_5 u) in (ty3 g TMP_6 t1 
t2)))) in (let TMP_8 \def (ex2 T TMP_4 TMP_7) in (let TMP_48 \def (\lambda 
(x: T).(\lambda (H0: (ty3 g c (THead (Bind Abst) u t2) x)).(let TMP_11 \def 
(\lambda (t3: T).(\lambda (_: T).(let TMP_9 \def (Bind Abst) in (let TMP_10 
\def (THead TMP_9 u t3) in (pc3 c TMP_10 x))))) in (let TMP_12 \def (\lambda 
(_: T).(\lambda (t: T).(ty3 g c u t))) in (let TMP_15 \def (\lambda (t3: 
T).(\lambda (_: T).(let TMP_13 \def (Bind Abst) in (let TMP_14 \def (CHead c 
TMP_13 u) in (ty3 g TMP_14 t2 t3))))) in (let TMP_16 \def (\lambda (w: 
T).(ty3 g c u w)) in (let TMP_19 \def (\lambda (_: T).(let TMP_17 \def (Bind 
Abst) in (let TMP_18 \def (CHead c TMP_17 u) in (ty3 g TMP_18 t1 t2)))) in 
(let TMP_20 \def (ex2 T TMP_16 TMP_19) in (let TMP_46 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (_: (pc3 c (THead (Bind Abst) u x0) x)).(\lambda 
(_: (ty3 g c u x1)).(\lambda (H3: (ty3 g (CHead c (Bind Abst) u) t2 x0)).(let 
TMP_25 \def (\lambda (t3: T).(\lambda (_: T).(let TMP_21 \def (Bind Abst) in 
(let TMP_22 \def (THead TMP_21 u t3) in (let TMP_23 \def (Bind Abst) in (let 
TMP_24 \def (THead TMP_23 u t2) in (pc3 c TMP_22 TMP_24))))))) in (let TMP_26 
\def (\lambda (_: T).(\lambda (t: T).(ty3 g c u t))) in (let TMP_29 \def 
(\lambda (t3: T).(\lambda (_: T).(let TMP_27 \def (Bind Abst) in (let TMP_28 
\def (CHead c TMP_27 u) in (ty3 g TMP_28 t1 t3))))) in (let TMP_30 \def 
(\lambda (w: T).(ty3 g c u w)) in (let TMP_33 \def (\lambda (_: T).(let 
TMP_31 \def (Bind Abst) in (let TMP_32 \def (CHead c TMP_31 u) in (ty3 g 
TMP_32 t1 t2)))) in (let TMP_34 \def (ex2 T TMP_30 TMP_33) in (let TMP_42 
\def (\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (pc3 c (THead (Bind 
Abst) u x2) (THead (Bind Abst) u t2))).(\lambda (H5: (ty3 g c u x3)).(\lambda 
(H6: (ty3 g (CHead c (Bind Abst) u) t1 x2)).(let H_y \def (pc3_gen_abst_shift 
c u x2 t2 H4) in (let TMP_35 \def (\lambda (w: T).(ty3 g c u w)) in (let 
TMP_38 \def (\lambda (_: T).(let TMP_36 \def (Bind Abst) in (let TMP_37 \def 
(CHead c TMP_36 u) in (ty3 g TMP_37 t1 t2)))) in (let TMP_39 \def (Bind Abst) 
in (let TMP_40 \def (CHead c TMP_39 u) in (let TMP_41 \def (ty3_conv g TMP_40 
t2 x0 H3 t1 x2 H6 H_y) in (ex_intro2 T TMP_35 TMP_38 x3 H5 TMP_41)))))))))))) 
in (let TMP_43 \def (Bind Abst) in (let TMP_44 \def (THead TMP_43 u t2) in 
(let TMP_45 \def (ty3_gen_bind g Abst c u t1 TMP_44 H) in (ex3_2_ind T T 
TMP_25 TMP_26 TMP_29 TMP_34 TMP_42 TMP_45)))))))))))))))) in (let TMP_47 \def 
(ty3_gen_bind g Abst c u t2 x H0) in (ex3_2_ind T T TMP_11 TMP_12 TMP_15 
TMP_20 TMP_46 TMP_47))))))))))) in (let TMP_49 \def (Bind Abst) in (let 
TMP_50 \def (THead TMP_49 u t1) in (let TMP_51 \def (Bind Abst) in (let 
TMP_52 \def (THead TMP_51 u t2) in (let TMP_53 \def (ty3_correct g c TMP_50 
TMP_52 H) in (ex_ind T TMP_3 TMP_8 TMP_48 TMP_53)))))))))))))))).

theorem ty3_typecheck:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (v: T).((ty3 g c t 
v) \to (ex T (\lambda (u: T).(ty3 g c (THead (Flat Cast) v t) u)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (v: T).(\lambda (H: 
(ty3 g c t v)).(let TMP_1 \def (\lambda (t0: T).(ty3 g c v t0)) in (let TMP_4 
\def (\lambda (u: T).(let TMP_2 \def (Flat Cast) in (let TMP_3 \def (THead 
TMP_2 v t) in (ty3 g c TMP_3 u)))) in (let TMP_5 \def (ex T TMP_4) in (let 
TMP_12 \def (\lambda (x: T).(\lambda (H0: (ty3 g c v x)).(let TMP_8 \def 
(\lambda (u: T).(let TMP_6 \def (Flat Cast) in (let TMP_7 \def (THead TMP_6 v 
t) in (ty3 g c TMP_7 u)))) in (let TMP_9 \def (Flat Cast) in (let TMP_10 \def 
(THead TMP_9 x v) in (let TMP_11 \def (ty3_cast g c t v H x H0) in (ex_intro 
T TMP_8 TMP_10 TMP_11))))))) in (let TMP_13 \def (ty3_correct g c t v H) in 
(ex_ind T TMP_1 TMP_5 TMP_12 TMP_13)))))))))).

theorem ty3_getl_subst0:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to (\forall (v0: T).(\forall (t0: T).(\forall (i: nat).((subst0 i v0 t 
t0) \to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c (CHead d 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v w)))))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(let TMP_2 \def (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
T).(\forall (v0: T).(\forall (t2: T).(\forall (i: nat).((subst0 i v0 t0 t2) 
\to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d 
(Bind b) v)) \to (let TMP_1 \def (\lambda (w: T).(ty3 g d v w)) in (ex T 
TMP_1))))))))))))) in (let TMP_3 \def (\lambda (c0: C).(\lambda (t2: 
T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t2 t0)).(\lambda (_: ((\forall 
(v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 t2 t1) \to (\forall 
(b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) v)) \to 
(ex T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (u0: T).(\lambda 
(t1: T).(\lambda (_: (ty3 g c0 u0 t1)).(\lambda (H3: ((\forall (v0: 
T).(\forall (t3: T).(\forall (i: nat).((subst0 i v0 u0 t3) \to (\forall (b: 
B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) v)) \to (ex 
T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (_: (pc3 c0 t1 
t2)).(\lambda (v0: T).(\lambda (t3: T).(\lambda (i: nat).(\lambda (H5: 
(subst0 i v0 u0 t3)).(\lambda (b: B).(\lambda (d: C).(\lambda (v: T).(\lambda 
(H6: (getl i c0 (CHead d (Bind b) v))).(H3 v0 t3 i H5 b d v 
H6))))))))))))))))))) in (let TMP_6 \def (\lambda (c0: C).(\lambda (m: 
nat).(\lambda (v0: T).(\lambda (t0: T).(\lambda (i: nat).(\lambda (H0: 
(subst0 i v0 (TSort m) t0)).(\lambda (b: B).(\lambda (d: C).(\lambda (v: 
T).(\lambda (_: (getl i c0 (CHead d (Bind b) v))).(let TMP_4 \def (\lambda 
(w: T).(ty3 g d v w)) in (let TMP_5 \def (ex T TMP_4) in (subst0_gen_sort v0 
t0 i m H0 TMP_5))))))))))))) in (let TMP_76 \def (\lambda (n: nat).(\lambda 
(c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n c0 (CHead d 
(Bind Abbr) u0))).(\lambda (t0: T).(\lambda (H1: (ty3 g d u0 t0)).(\lambda 
(_: ((\forall (v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 u0 t1) 
\to (\forall (b: B).(\forall (d0: C).(\forall (v: T).((getl i d (CHead d0 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d0 v w))))))))))))).(\lambda 
(v0: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (H3: (subst0 i v0 (TLRef 
n) t1)).(\lambda (b: B).(\lambda (d0: C).(\lambda (v: T).(\lambda (H4: (getl 
i c0 (CHead d0 (Bind b) v))).(let TMP_7 \def (eq nat n i) in (let TMP_8 \def 
(S n) in (let TMP_9 \def (lift TMP_8 O v0) in (let TMP_10 \def (eq T t1 
TMP_9) in (let TMP_11 \def (\lambda (w: T).(ty3 g d0 v w)) in (let TMP_12 
\def (ex T TMP_11) in (let TMP_74 \def (\lambda (H5: (eq nat n i)).(\lambda 
(_: (eq T t1 (lift (S n) O v0))).(let TMP_15 \def (\lambda (n0: nat).(let 
TMP_13 \def (Bind b) in (let TMP_14 \def (CHead d0 TMP_13 v) in (getl n0 c0 
TMP_14)))) in (let H7 \def (eq_ind_r nat i TMP_15 H4 n H5) in (let TMP_16 
\def (Bind Abbr) in (let TMP_17 \def (CHead d TMP_16 u0) in (let TMP_18 \def 
(\lambda (c1: C).(getl n c0 c1)) in (let TMP_19 \def (Bind b) in (let TMP_20 
\def (CHead d0 TMP_19 v) in (let TMP_21 \def (Bind Abbr) in (let TMP_22 \def 
(CHead d TMP_21 u0) in (let TMP_23 \def (Bind b) in (let TMP_24 \def (CHead 
d0 TMP_23 v) in (let TMP_25 \def (getl_mono c0 TMP_22 n H0 TMP_24 H7) in (let 
H8 \def (eq_ind C TMP_17 TMP_18 H0 TMP_20 TMP_25) in (let TMP_26 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow d | (CHead c1 _ _) 
\Rightarrow c1])) in (let TMP_27 \def (Bind Abbr) in (let TMP_28 \def (CHead 
d TMP_27 u0) in (let TMP_29 \def (Bind b) in (let TMP_30 \def (CHead d0 
TMP_29 v) in (let TMP_31 \def (Bind Abbr) in (let TMP_32 \def (CHead d TMP_31 
u0) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead d0 TMP_33 v) in 
(let TMP_35 \def (getl_mono c0 TMP_32 n H0 TMP_34 H7) in (let H9 \def 
(f_equal C C TMP_26 TMP_28 TMP_30 TMP_35) in (let TMP_36 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_37 \def (Bind Abbr) in (let TMP_38 \def (CHead d TMP_37 u0) in (let 
TMP_39 \def (Bind b) in (let TMP_40 \def (CHead d0 TMP_39 v) in (let TMP_41 
\def (Bind Abbr) in (let TMP_42 \def (CHead d TMP_41 u0) in (let TMP_43 \def 
(Bind b) in (let TMP_44 \def (CHead d0 TMP_43 v) in (let TMP_45 \def 
(getl_mono c0 TMP_42 n H0 TMP_44 H7) in (let H10 \def (f_equal C B TMP_36 
TMP_38 TMP_40 TMP_45) in (let TMP_46 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t2) \Rightarrow t2])) in (let TMP_47 
\def (Bind Abbr) in (let TMP_48 \def (CHead d TMP_47 u0) in (let TMP_49 \def 
(Bind b) in (let TMP_50 \def (CHead d0 TMP_49 v) in (let TMP_51 \def (Bind 
Abbr) in (let TMP_52 \def (CHead d TMP_51 u0) in (let TMP_53 \def (Bind b) in 
(let TMP_54 \def (CHead d0 TMP_53 v) in (let TMP_55 \def (getl_mono c0 TMP_52 
n H0 TMP_54 H7) in (let H11 \def (f_equal C T TMP_46 TMP_48 TMP_50 TMP_55) in 
(let TMP_72 \def (\lambda (H12: (eq B Abbr b)).(\lambda (H13: (eq C d 
d0)).(let TMP_58 \def (\lambda (t2: T).(let TMP_56 \def (Bind b) in (let 
TMP_57 \def (CHead d0 TMP_56 t2) in (getl n c0 TMP_57)))) in (let H14 \def 
(eq_ind_r T v TMP_58 H8 u0 H11) in (let TMP_60 \def (\lambda (t2: T).(let 
TMP_59 \def (\lambda (w: T).(ty3 g d0 t2 w)) in (ex T TMP_59))) in (let 
TMP_63 \def (\lambda (c1: C).(let TMP_61 \def (Bind b) in (let TMP_62 \def 
(CHead c1 TMP_61 u0) in (getl n c0 TMP_62)))) in (let H15 \def (eq_ind_r C d0 
TMP_63 H14 d H13) in (let TMP_65 \def (\lambda (c1: C).(let TMP_64 \def 
(\lambda (w: T).(ty3 g c1 u0 w)) in (ex T TMP_64))) in (let TMP_68 \def 
(\lambda (b0: B).(let TMP_66 \def (Bind b0) in (let TMP_67 \def (CHead d 
TMP_66 u0) in (getl n c0 TMP_67)))) in (let H16 \def (eq_ind_r B b TMP_68 H15 
Abbr H12) in (let TMP_69 \def (\lambda (w: T).(ty3 g d u0 w)) in (let TMP_70 
\def (ex_intro T TMP_69 t0 H1) in (let TMP_71 \def (eq_ind C d TMP_65 TMP_70 
d0 H13) in (eq_ind T u0 TMP_60 TMP_71 v H11)))))))))))))) in (let TMP_73 \def 
(TMP_72 H10) in (TMP_73 H9))))))))))))))))))))))))))))))))))))))))))))))))))) 
in (let TMP_75 \def (subst0_gen_lref v0 t1 i n H3) in (land_ind TMP_7 TMP_10 
TMP_12 TMP_74 TMP_75))))))))))))))))))))))))) in (let TMP_146 \def (\lambda 
(n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: 
(getl n c0 (CHead d (Bind Abst) u0))).(\lambda (t0: T).(\lambda (H1: (ty3 g d 
u0 t0)).(\lambda (_: ((\forall (v0: T).(\forall (t1: T).(\forall (i: 
nat).((subst0 i v0 u0 t1) \to (\forall (b: B).(\forall (d0: C).(\forall (v: 
T).((getl i d (CHead d0 (Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d0 v 
w))))))))))))).(\lambda (v0: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(H3: (subst0 i v0 (TLRef n) t1)).(\lambda (b: B).(\lambda (d0: C).(\lambda 
(v: T).(\lambda (H4: (getl i c0 (CHead d0 (Bind b) v))).(let TMP_77 \def (eq 
nat n i) in (let TMP_78 \def (S n) in (let TMP_79 \def (lift TMP_78 O v0) in 
(let TMP_80 \def (eq T t1 TMP_79) in (let TMP_81 \def (\lambda (w: T).(ty3 g 
d0 v w)) in (let TMP_82 \def (ex T TMP_81) in (let TMP_144 \def (\lambda (H5: 
(eq nat n i)).(\lambda (_: (eq T t1 (lift (S n) O v0))).(let TMP_85 \def 
(\lambda (n0: nat).(let TMP_83 \def (Bind b) in (let TMP_84 \def (CHead d0 
TMP_83 v) in (getl n0 c0 TMP_84)))) in (let H7 \def (eq_ind_r nat i TMP_85 H4 
n H5) in (let TMP_86 \def (Bind Abst) in (let TMP_87 \def (CHead d TMP_86 u0) 
in (let TMP_88 \def (\lambda (c1: C).(getl n c0 c1)) in (let TMP_89 \def 
(Bind b) in (let TMP_90 \def (CHead d0 TMP_89 v) in (let TMP_91 \def (Bind 
Abst) in (let TMP_92 \def (CHead d TMP_91 u0) in (let TMP_93 \def (Bind b) in 
(let TMP_94 \def (CHead d0 TMP_93 v) in (let TMP_95 \def (getl_mono c0 TMP_92 
n H0 TMP_94 H7) in (let H8 \def (eq_ind C TMP_87 TMP_88 H0 TMP_90 TMP_95) in 
(let TMP_96 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow d | 
(CHead c1 _ _) \Rightarrow c1])) in (let TMP_97 \def (Bind Abst) in (let 
TMP_98 \def (CHead d TMP_97 u0) in (let TMP_99 \def (Bind b) in (let TMP_100 
\def (CHead d0 TMP_99 v) in (let TMP_101 \def (Bind Abst) in (let TMP_102 
\def (CHead d TMP_101 u0) in (let TMP_103 \def (Bind b) in (let TMP_104 \def 
(CHead d0 TMP_103 v) in (let TMP_105 \def (getl_mono c0 TMP_102 n H0 TMP_104 
H7) in (let H9 \def (f_equal C C TMP_96 TMP_98 TMP_100 TMP_105) in (let 
TMP_106 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow Abst | 
(CHead _ k _) \Rightarrow (match k with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abst])])) in (let TMP_107 \def (Bind Abst) in (let TMP_108 \def 
(CHead d TMP_107 u0) in (let TMP_109 \def (Bind b) in (let TMP_110 \def 
(CHead d0 TMP_109 v) in (let TMP_111 \def (Bind Abst) in (let TMP_112 \def 
(CHead d TMP_111 u0) in (let TMP_113 \def (Bind b) in (let TMP_114 \def 
(CHead d0 TMP_113 v) in (let TMP_115 \def (getl_mono c0 TMP_112 n H0 TMP_114 
H7) in (let H10 \def (f_equal C B TMP_106 TMP_108 TMP_110 TMP_115) in (let 
TMP_116 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | (CHead 
_ _ t2) \Rightarrow t2])) in (let TMP_117 \def (Bind Abst) in (let TMP_118 
\def (CHead d TMP_117 u0) in (let TMP_119 \def (Bind b) in (let TMP_120 \def 
(CHead d0 TMP_119 v) in (let TMP_121 \def (Bind Abst) in (let TMP_122 \def 
(CHead d TMP_121 u0) in (let TMP_123 \def (Bind b) in (let TMP_124 \def 
(CHead d0 TMP_123 v) in (let TMP_125 \def (getl_mono c0 TMP_122 n H0 TMP_124 
H7) in (let H11 \def (f_equal C T TMP_116 TMP_118 TMP_120 TMP_125) in (let 
TMP_142 \def (\lambda (H12: (eq B Abst b)).(\lambda (H13: (eq C d d0)).(let 
TMP_128 \def (\lambda (t2: T).(let TMP_126 \def (Bind b) in (let TMP_127 \def 
(CHead d0 TMP_126 t2) in (getl n c0 TMP_127)))) in (let H14 \def (eq_ind_r T 
v TMP_128 H8 u0 H11) in (let TMP_130 \def (\lambda (t2: T).(let TMP_129 \def 
(\lambda (w: T).(ty3 g d0 t2 w)) in (ex T TMP_129))) in (let TMP_133 \def 
(\lambda (c1: C).(let TMP_131 \def (Bind b) in (let TMP_132 \def (CHead c1 
TMP_131 u0) in (getl n c0 TMP_132)))) in (let H15 \def (eq_ind_r C d0 TMP_133 
H14 d H13) in (let TMP_135 \def (\lambda (c1: C).(let TMP_134 \def (\lambda 
(w: T).(ty3 g c1 u0 w)) in (ex T TMP_134))) in (let TMP_138 \def (\lambda 
(b0: B).(let TMP_136 \def (Bind b0) in (let TMP_137 \def (CHead d TMP_136 u0) 
in (getl n c0 TMP_137)))) in (let H16 \def (eq_ind_r B b TMP_138 H15 Abst 
H12) in (let TMP_139 \def (\lambda (w: T).(ty3 g d u0 w)) in (let TMP_140 
\def (ex_intro T TMP_139 t0 H1) in (let TMP_141 \def (eq_ind C d TMP_135 
TMP_140 d0 H13) in (eq_ind T u0 TMP_130 TMP_141 v H11)))))))))))))) in (let 
TMP_143 \def (TMP_142 H10) in (TMP_143 
H9))))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_145 \def 
(subst0_gen_lref v0 t1 i n H3) in (land_ind TMP_77 TMP_80 TMP_82 TMP_144 
TMP_145))))))))))))))))))))))))) in (let TMP_205 \def (\lambda (c0: 
C).(\lambda (u0: T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 u0 t0)).(\lambda 
(H1: ((\forall (v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 u0 
t1) \to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (b: 
B).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u0) t1 t2)).(\lambda (H3: ((\forall (v0: T).(\forall (t3: T).(\forall (i: 
nat).((subst0 i v0 t1 t3) \to (\forall (b0: B).(\forall (d: C).(\forall (v: 
T).((getl i (CHead c0 (Bind b) u0) (CHead d (Bind b0) v)) \to (ex T (\lambda 
(w: T).(ty3 g d v w))))))))))))).(\lambda (v0: T).(\lambda (t3: T).(\lambda 
(i: nat).(\lambda (H4: (subst0 i v0 (THead (Bind b) u0 t1) t3)).(\lambda (b0: 
B).(\lambda (d: C).(\lambda (v: T).(\lambda (H5: (getl i c0 (CHead d (Bind 
b0) v))).(let TMP_149 \def (\lambda (u2: T).(let TMP_147 \def (Bind b) in 
(let TMP_148 \def (THead TMP_147 u2 t1) in (eq T t3 TMP_148)))) in (let 
TMP_150 \def (\lambda (u2: T).(subst0 i v0 u0 u2)) in (let TMP_151 \def (ex2 
T TMP_149 TMP_150) in (let TMP_154 \def (\lambda (t4: T).(let TMP_152 \def 
(Bind b) in (let TMP_153 \def (THead TMP_152 u0 t4) in (eq T t3 TMP_153)))) 
in (let TMP_157 \def (\lambda (t4: T).(let TMP_155 \def (Bind b) in (let 
TMP_156 \def (s TMP_155 i) in (subst0 TMP_156 v0 t1 t4)))) in (let TMP_158 
\def (ex2 T TMP_154 TMP_157) in (let TMP_161 \def (\lambda (u2: T).(\lambda 
(t4: T).(let TMP_159 \def (Bind b) in (let TMP_160 \def (THead TMP_159 u2 t4) 
in (eq T t3 TMP_160))))) in (let TMP_162 \def (\lambda (u2: T).(\lambda (_: 
T).(subst0 i v0 u0 u2))) in (let TMP_165 \def (\lambda (_: T).(\lambda (t4: 
T).(let TMP_163 \def (Bind b) in (let TMP_164 \def (s TMP_163 i) in (subst0 
TMP_164 v0 t1 t4))))) in (let TMP_166 \def (ex3_2 T T TMP_161 TMP_162 
TMP_165) in (let TMP_167 \def (\lambda (w: T).(ty3 g d v w)) in (let TMP_168 
\def (ex T TMP_167) in (let TMP_176 \def (\lambda (H6: (ex2 T (\lambda (u2: 
T).(eq T t3 (THead (Bind b) u2 t1))) (\lambda (u2: T).(subst0 i v0 u0 
u2)))).(let TMP_171 \def (\lambda (u2: T).(let TMP_169 \def (Bind b) in (let 
TMP_170 \def (THead TMP_169 u2 t1) in (eq T t3 TMP_170)))) in (let TMP_172 
\def (\lambda (u2: T).(subst0 i v0 u0 u2)) in (let TMP_173 \def (\lambda (w: 
T).(ty3 g d v w)) in (let TMP_174 \def (ex T TMP_173) in (let TMP_175 \def 
(\lambda (x: T).(\lambda (_: (eq T t3 (THead (Bind b) x t1))).(\lambda (H8: 
(subst0 i v0 u0 x)).(H1 v0 x i H8 b0 d v H5)))) in (ex2_ind T TMP_171 TMP_172 
TMP_174 TMP_175 H6))))))) in (let TMP_191 \def (\lambda (H6: (ex2 T (\lambda 
(t4: T).(eq T t3 (THead (Bind b) u0 t4))) (\lambda (t4: T).(subst0 (s (Bind 
b) i) v0 t1 t4)))).(let TMP_179 \def (\lambda (t4: T).(let TMP_177 \def (Bind 
b) in (let TMP_178 \def (THead TMP_177 u0 t4) in (eq T t3 TMP_178)))) in (let 
TMP_182 \def (\lambda (t4: T).(let TMP_180 \def (Bind b) in (let TMP_181 \def 
(s TMP_180 i) in (subst0 TMP_181 v0 t1 t4)))) in (let TMP_183 \def (\lambda 
(w: T).(ty3 g d v w)) in (let TMP_184 \def (ex T TMP_183) in (let TMP_190 
\def (\lambda (x: T).(\lambda (_: (eq T t3 (THead (Bind b) u0 x))).(\lambda 
(H8: (subst0 (s (Bind b) i) v0 t1 x)).(let TMP_185 \def (S i) in (let TMP_186 
\def (Bind b) in (let TMP_187 \def (Bind b0) in (let TMP_188 \def (CHead d 
TMP_187 v) in (let TMP_189 \def (getl_head TMP_186 i c0 TMP_188 H5 u0) in (H3 
v0 x TMP_185 H8 b0 d v TMP_189))))))))) in (ex2_ind T TMP_179 TMP_182 TMP_184 
TMP_190 H6))))))) in (let TMP_202 \def (\lambda (H6: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 u0 u2))) (\lambda (_: T).(\lambda (t4: 
T).(subst0 (s (Bind b) i) v0 t1 t4))))).(let TMP_194 \def (\lambda (u2: 
T).(\lambda (t4: T).(let TMP_192 \def (Bind b) in (let TMP_193 \def (THead 
TMP_192 u2 t4) in (eq T t3 TMP_193))))) in (let TMP_195 \def (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 u0 u2))) in (let TMP_198 \def (\lambda (_: 
T).(\lambda (t4: T).(let TMP_196 \def (Bind b) in (let TMP_197 \def (s 
TMP_196 i) in (subst0 TMP_197 v0 t1 t4))))) in (let TMP_199 \def (\lambda (w: 
T).(ty3 g d v w)) in (let TMP_200 \def (ex T TMP_199) in (let TMP_201 \def 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (eq T t3 (THead (Bind b) x0 
x1))).(\lambda (H8: (subst0 i v0 u0 x0)).(\lambda (_: (subst0 (s (Bind b) i) 
v0 t1 x1)).(H1 v0 x0 i H8 b0 d v H5)))))) in (ex3_2_ind T T TMP_194 TMP_195 
TMP_198 TMP_200 TMP_201 H6)))))))) in (let TMP_203 \def (Bind b) in (let 
TMP_204 \def (subst0_gen_head TMP_203 v0 u0 t1 t3 i H4) in (or3_ind TMP_151 
TMP_158 TMP_166 TMP_168 TMP_176 TMP_191 TMP_202 
TMP_204)))))))))))))))))))))))))))))))))))) in (let TMP_263 \def (\lambda 
(c0: C).(\lambda (w: T).(\lambda (u0: T).(\lambda (_: (ty3 g c0 w 
u0)).(\lambda (H1: ((\forall (v0: T).(\forall (t0: T).(\forall (i: 
nat).((subst0 i v0 w t0) \to (\forall (b: B).(\forall (d: C).(\forall (v: 
T).((getl i c0 (CHead d (Bind b) v)) \to (ex T (\lambda (w0: T).(ty3 g d v 
w0))))))))))))).(\lambda (v: T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 v 
(THead (Bind Abst) u0 t0))).(\lambda (H3: ((\forall (v0: T).(\forall (t1: 
T).(\forall (i: nat).((subst0 i v0 v t1) \to (\forall (b: B).(\forall (d: 
C).(\forall (v1: T).((getl i c0 (CHead d (Bind b) v1)) \to (ex T (\lambda 
(w0: T).(ty3 g d v1 w0))))))))))))).(\lambda (v0: T).(\lambda (t1: 
T).(\lambda (i: nat).(\lambda (H4: (subst0 i v0 (THead (Flat Appl) w v) 
t1)).(\lambda (b: B).(\lambda (d: C).(\lambda (v1: T).(\lambda (H5: (getl i 
c0 (CHead d (Bind b) v1))).(let TMP_208 \def (\lambda (u2: T).(let TMP_206 
\def (Flat Appl) in (let TMP_207 \def (THead TMP_206 u2 v) in (eq T t1 
TMP_207)))) in (let TMP_209 \def (\lambda (u2: T).(subst0 i v0 w u2)) in (let 
TMP_210 \def (ex2 T TMP_208 TMP_209) in (let TMP_213 \def (\lambda (t2: 
T).(let TMP_211 \def (Flat Appl) in (let TMP_212 \def (THead TMP_211 w t2) in 
(eq T t1 TMP_212)))) in (let TMP_216 \def (\lambda (t2: T).(let TMP_214 \def 
(Flat Appl) in (let TMP_215 \def (s TMP_214 i) in (subst0 TMP_215 v0 v t2)))) 
in (let TMP_217 \def (ex2 T TMP_213 TMP_216) in (let TMP_220 \def (\lambda 
(u2: T).(\lambda (t2: T).(let TMP_218 \def (Flat Appl) in (let TMP_219 \def 
(THead TMP_218 u2 t2) in (eq T t1 TMP_219))))) in (let TMP_221 \def (\lambda 
(u2: T).(\lambda (_: T).(subst0 i v0 w u2))) in (let TMP_224 \def (\lambda 
(_: T).(\lambda (t2: T).(let TMP_222 \def (Flat Appl) in (let TMP_223 \def (s 
TMP_222 i) in (subst0 TMP_223 v0 v t2))))) in (let TMP_225 \def (ex3_2 T T 
TMP_220 TMP_221 TMP_224) in (let TMP_226 \def (\lambda (w0: T).(ty3 g d v1 
w0)) in (let TMP_227 \def (ex T TMP_226) in (let TMP_235 \def (\lambda (H6: 
(ex2 T (\lambda (u2: T).(eq T t1 (THead (Flat Appl) u2 v))) (\lambda (u2: 
T).(subst0 i v0 w u2)))).(let TMP_230 \def (\lambda (u2: T).(let TMP_228 \def 
(Flat Appl) in (let TMP_229 \def (THead TMP_228 u2 v) in (eq T t1 TMP_229)))) 
in (let TMP_231 \def (\lambda (u2: T).(subst0 i v0 w u2)) in (let TMP_232 
\def (\lambda (w0: T).(ty3 g d v1 w0)) in (let TMP_233 \def (ex T TMP_232) in 
(let TMP_234 \def (\lambda (x: T).(\lambda (_: (eq T t1 (THead (Flat Appl) x 
v))).(\lambda (H8: (subst0 i v0 w x)).(H1 v0 x i H8 b d v1 H5)))) in (ex2_ind 
T TMP_230 TMP_231 TMP_233 TMP_234 H6))))))) in (let TMP_247 \def (\lambda 
(H6: (ex2 T (\lambda (t2: T).(eq T t1 (THead (Flat Appl) w t2))) (\lambda 
(t2: T).(subst0 (s (Flat Appl) i) v0 v t2)))).(let TMP_238 \def (\lambda (t2: 
T).(let TMP_236 \def (Flat Appl) in (let TMP_237 \def (THead TMP_236 w t2) in 
(eq T t1 TMP_237)))) in (let TMP_241 \def (\lambda (t2: T).(let TMP_239 \def 
(Flat Appl) in (let TMP_240 \def (s TMP_239 i) in (subst0 TMP_240 v0 v t2)))) 
in (let TMP_242 \def (\lambda (w0: T).(ty3 g d v1 w0)) in (let TMP_243 \def 
(ex T TMP_242) in (let TMP_246 \def (\lambda (x: T).(\lambda (_: (eq T t1 
(THead (Flat Appl) w x))).(\lambda (H8: (subst0 (s (Flat Appl) i) v0 v 
x)).(let TMP_244 \def (Flat Appl) in (let TMP_245 \def (s TMP_244 i) in (H3 
v0 x TMP_245 H8 b d v1 H5)))))) in (ex2_ind T TMP_238 TMP_241 TMP_243 TMP_246 
H6))))))) in (let TMP_260 \def (\lambda (H6: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T t1 (THead (Flat Appl) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 w u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s (Flat Appl) i) v0 v t2))))).(let TMP_250 \def (\lambda (u2: 
T).(\lambda (t2: T).(let TMP_248 \def (Flat Appl) in (let TMP_249 \def (THead 
TMP_248 u2 t2) in (eq T t1 TMP_249))))) in (let TMP_251 \def (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 w u2))) in (let TMP_254 \def (\lambda (_: 
T).(\lambda (t2: T).(let TMP_252 \def (Flat Appl) in (let TMP_253 \def (s 
TMP_252 i) in (subst0 TMP_253 v0 v t2))))) in (let TMP_255 \def (\lambda (w0: 
T).(ty3 g d v1 w0)) in (let TMP_256 \def (ex T TMP_255) in (let TMP_259 \def 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (eq T t1 (THead (Flat Appl) x0 
x1))).(\lambda (_: (subst0 i v0 w x0)).(\lambda (H9: (subst0 (s (Flat Appl) 
i) v0 v x1)).(let TMP_257 \def (Flat Appl) in (let TMP_258 \def (s TMP_257 i) 
in (H3 v0 x1 TMP_258 H9 b d v1 H5)))))))) in (ex3_2_ind T T TMP_250 TMP_251 
TMP_254 TMP_256 TMP_259 H6)))))))) in (let TMP_261 \def (Flat Appl) in (let 
TMP_262 \def (subst0_gen_head TMP_261 v0 w v t1 i H4) in (or3_ind TMP_210 
TMP_217 TMP_225 TMP_227 TMP_235 TMP_247 TMP_260 
TMP_262))))))))))))))))))))))))))))))))))) in (let TMP_319 \def (\lambda (c0: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t1 t2)).(\lambda 
(H1: ((\forall (v0: T).(\forall (t0: T).(\forall (i: nat).((subst0 i v0 t1 
t0) \to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda 
(t0: T).(\lambda (_: (ty3 g c0 t2 t0)).(\lambda (H3: ((\forall (v0: 
T).(\forall (t3: T).(\forall (i: nat).((subst0 i v0 t2 t3) \to (\forall (b: 
B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) v)) \to (ex 
T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (v0: T).(\lambda (t3: 
T).(\lambda (i: nat).(\lambda (H4: (subst0 i v0 (THead (Flat Cast) t2 t1) 
t3)).(\lambda (b: B).(\lambda (d: C).(\lambda (v: T).(\lambda (H5: (getl i c0 
(CHead d (Bind b) v))).(let TMP_266 \def (\lambda (u2: T).(let TMP_264 \def 
(Flat Cast) in (let TMP_265 \def (THead TMP_264 u2 t1) in (eq T t3 
TMP_265)))) in (let TMP_267 \def (\lambda (u2: T).(subst0 i v0 t2 u2)) in 
(let TMP_268 \def (ex2 T TMP_266 TMP_267) in (let TMP_271 \def (\lambda (t4: 
T).(let TMP_269 \def (Flat Cast) in (let TMP_270 \def (THead TMP_269 t2 t4) 
in (eq T t3 TMP_270)))) in (let TMP_274 \def (\lambda (t4: T).(let TMP_272 
\def (Flat Cast) in (let TMP_273 \def (s TMP_272 i) in (subst0 TMP_273 v0 t1 
t4)))) in (let TMP_275 \def (ex2 T TMP_271 TMP_274) in (let TMP_278 \def 
(\lambda (u2: T).(\lambda (t4: T).(let TMP_276 \def (Flat Cast) in (let 
TMP_277 \def (THead TMP_276 u2 t4) in (eq T t3 TMP_277))))) in (let TMP_279 
\def (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 t2 u2))) in (let TMP_282 
\def (\lambda (_: T).(\lambda (t4: T).(let TMP_280 \def (Flat Cast) in (let 
TMP_281 \def (s TMP_280 i) in (subst0 TMP_281 v0 t1 t4))))) in (let TMP_283 
\def (ex3_2 T T TMP_278 TMP_279 TMP_282) in (let TMP_284 \def (\lambda (w: 
T).(ty3 g d v w)) in (let TMP_285 \def (ex T TMP_284) in (let TMP_293 \def 
(\lambda (H6: (ex2 T (\lambda (u2: T).(eq T t3 (THead (Flat Cast) u2 t1))) 
(\lambda (u2: T).(subst0 i v0 t2 u2)))).(let TMP_288 \def (\lambda (u2: 
T).(let TMP_286 \def (Flat Cast) in (let TMP_287 \def (THead TMP_286 u2 t1) 
in (eq T t3 TMP_287)))) in (let TMP_289 \def (\lambda (u2: T).(subst0 i v0 t2 
u2)) in (let TMP_290 \def (\lambda (w: T).(ty3 g d v w)) in (let TMP_291 \def 
(ex T TMP_290) in (let TMP_292 \def (\lambda (x: T).(\lambda (_: (eq T t3 
(THead (Flat Cast) x t1))).(\lambda (H8: (subst0 i v0 t2 x)).(H3 v0 x i H8 b 
d v H5)))) in (ex2_ind T TMP_288 TMP_289 TMP_291 TMP_292 H6))))))) in (let 
TMP_305 \def (\lambda (H6: (ex2 T (\lambda (t4: T).(eq T t3 (THead (Flat 
Cast) t2 t4))) (\lambda (t4: T).(subst0 (s (Flat Cast) i) v0 t1 t4)))).(let 
TMP_296 \def (\lambda (t4: T).(let TMP_294 \def (Flat Cast) in (let TMP_295 
\def (THead TMP_294 t2 t4) in (eq T t3 TMP_295)))) in (let TMP_299 \def 
(\lambda (t4: T).(let TMP_297 \def (Flat Cast) in (let TMP_298 \def (s 
TMP_297 i) in (subst0 TMP_298 v0 t1 t4)))) in (let TMP_300 \def (\lambda (w: 
T).(ty3 g d v w)) in (let TMP_301 \def (ex T TMP_300) in (let TMP_304 \def 
(\lambda (x: T).(\lambda (_: (eq T t3 (THead (Flat Cast) t2 x))).(\lambda 
(H8: (subst0 (s (Flat Cast) i) v0 t1 x)).(let TMP_302 \def (Flat Cast) in 
(let TMP_303 \def (s TMP_302 i) in (H1 v0 x TMP_303 H8 b d v H5)))))) in 
(ex2_ind T TMP_296 TMP_299 TMP_301 TMP_304 H6))))))) in (let TMP_316 \def 
(\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Cast) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 t2 u2))) 
(\lambda (_: T).(\lambda (t4: T).(subst0 (s (Flat Cast) i) v0 t1 t4))))).(let 
TMP_308 \def (\lambda (u2: T).(\lambda (t4: T).(let TMP_306 \def (Flat Cast) 
in (let TMP_307 \def (THead TMP_306 u2 t4) in (eq T t3 TMP_307))))) in (let 
TMP_309 \def (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 t2 u2))) in (let 
TMP_312 \def (\lambda (_: T).(\lambda (t4: T).(let TMP_310 \def (Flat Cast) 
in (let TMP_311 \def (s TMP_310 i) in (subst0 TMP_311 v0 t1 t4))))) in (let 
TMP_313 \def (\lambda (w: T).(ty3 g d v w)) in (let TMP_314 \def (ex T 
TMP_313) in (let TMP_315 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: 
(eq T t3 (THead (Flat Cast) x0 x1))).(\lambda (H8: (subst0 i v0 t2 
x0)).(\lambda (_: (subst0 (s (Flat Cast) i) v0 t1 x1)).(H3 v0 x0 i H8 b d v 
H5)))))) in (ex3_2_ind T T TMP_308 TMP_309 TMP_312 TMP_314 TMP_315 H6)))))))) 
in (let TMP_317 \def (Flat Cast) in (let TMP_318 \def (subst0_gen_head 
TMP_317 v0 t2 t1 t3 i H4) in (or3_ind TMP_268 TMP_275 TMP_283 TMP_285 TMP_293 
TMP_305 TMP_316 TMP_318)))))))))))))))))))))))))))))))))) in (ty3_ind g TMP_2 
TMP_3 TMP_6 TMP_76 TMP_146 TMP_205 TMP_263 TMP_319 c t u H))))))))))))).

