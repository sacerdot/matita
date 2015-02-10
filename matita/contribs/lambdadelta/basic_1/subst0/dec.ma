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

include "basic_1/subst0/defs.ma".

include "basic_1/lift/props.ma".

theorem dnf_dec2:
 \forall (t: T).(\forall (d: nat).(or (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w t (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t (lift (S 
O) d v))))))
\def
 \lambda (t: T).(let TMP_9 \def (\lambda (t0: T).(\forall (d: nat).(let TMP_4 
\def (\forall (w: T).(let TMP_3 \def (\lambda (v: T).(let TMP_1 \def (S O) in 
(let TMP_2 \def (lift TMP_1 d v) in (subst0 d w t0 TMP_2)))) in (ex T 
TMP_3))) in (let TMP_7 \def (\lambda (v: T).(let TMP_5 \def (S O) in (let 
TMP_6 \def (lift TMP_5 d v) in (eq T t0 TMP_6)))) in (let TMP_8 \def (ex T 
TMP_7) in (or TMP_4 TMP_8)))))) in (let TMP_37 \def (\lambda (n: 
nat).(\lambda (d: nat).(let TMP_14 \def (\forall (w: T).(let TMP_13 \def 
(\lambda (v: T).(let TMP_10 \def (TSort n) in (let TMP_11 \def (S O) in (let 
TMP_12 \def (lift TMP_11 d v) in (subst0 d w TMP_10 TMP_12))))) in (ex T 
TMP_13))) in (let TMP_18 \def (\lambda (v: T).(let TMP_15 \def (TSort n) in 
(let TMP_16 \def (S O) in (let TMP_17 \def (lift TMP_16 d v) in (eq T TMP_15 
TMP_17))))) in (let TMP_19 \def (ex T TMP_18) in (let TMP_23 \def (\lambda 
(v: T).(let TMP_20 \def (TSort n) in (let TMP_21 \def (S O) in (let TMP_22 
\def (lift TMP_21 d v) in (eq T TMP_20 TMP_22))))) in (let TMP_24 \def (TSort 
n) in (let TMP_25 \def (TSort n) in (let TMP_27 \def (\lambda (t0: T).(let 
TMP_26 \def (TSort n) in (eq T TMP_26 t0))) in (let TMP_28 \def (TSort n) in 
(let TMP_29 \def (refl_equal T TMP_28) in (let TMP_30 \def (S O) in (let 
TMP_31 \def (TSort n) in (let TMP_32 \def (lift TMP_30 d TMP_31) in (let 
TMP_33 \def (S O) in (let TMP_34 \def (lift_sort n TMP_33 d) in (let TMP_35 
\def (eq_ind_r T TMP_25 TMP_27 TMP_29 TMP_32 TMP_34) in (let TMP_36 \def 
(ex_intro T TMP_23 TMP_24 TMP_35) in (or_intror TMP_14 TMP_19 
TMP_36))))))))))))))))))) in (let TMP_149 \def (\lambda (n: nat).(\lambda (d: 
nat).(let TMP_42 \def (\forall (w: T).(let TMP_41 \def (\lambda (v: T).(let 
TMP_38 \def (TLRef n) in (let TMP_39 \def (S O) in (let TMP_40 \def (lift 
TMP_39 d v) in (subst0 d w TMP_38 TMP_40))))) in (ex T TMP_41))) in (let 
TMP_46 \def (\lambda (v: T).(let TMP_43 \def (TLRef n) in (let TMP_44 \def (S 
O) in (let TMP_45 \def (lift TMP_44 d v) in (eq T TMP_43 TMP_45))))) in (let 
TMP_47 \def (ex T TMP_46) in (let TMP_48 \def (or TMP_42 TMP_47) in (let 
TMP_76 \def (\lambda (H: (lt n d)).(let TMP_53 \def (\forall (w: T).(let 
TMP_52 \def (\lambda (v: T).(let TMP_49 \def (TLRef n) in (let TMP_50 \def (S 
O) in (let TMP_51 \def (lift TMP_50 d v) in (subst0 d w TMP_49 TMP_51))))) in 
(ex T TMP_52))) in (let TMP_57 \def (\lambda (v: T).(let TMP_54 \def (TLRef 
n) in (let TMP_55 \def (S O) in (let TMP_56 \def (lift TMP_55 d v) in (eq T 
TMP_54 TMP_56))))) in (let TMP_58 \def (ex T TMP_57) in (let TMP_62 \def 
(\lambda (v: T).(let TMP_59 \def (TLRef n) in (let TMP_60 \def (S O) in (let 
TMP_61 \def (lift TMP_60 d v) in (eq T TMP_59 TMP_61))))) in (let TMP_63 \def 
(TLRef n) in (let TMP_64 \def (TLRef n) in (let TMP_66 \def (\lambda (t0: 
T).(let TMP_65 \def (TLRef n) in (eq T TMP_65 t0))) in (let TMP_67 \def 
(TLRef n) in (let TMP_68 \def (refl_equal T TMP_67) in (let TMP_69 \def (S O) 
in (let TMP_70 \def (TLRef n) in (let TMP_71 \def (lift TMP_69 d TMP_70) in 
(let TMP_72 \def (S O) in (let TMP_73 \def (lift_lref_lt n TMP_72 d H) in 
(let TMP_74 \def (eq_ind_r T TMP_64 TMP_66 TMP_68 TMP_71 TMP_73) in (let 
TMP_75 \def (ex_intro T TMP_62 TMP_63 TMP_74) in (or_intror TMP_53 TMP_58 
TMP_75)))))))))))))))))) in (let TMP_119 \def (\lambda (H: (eq nat n d)).(let 
TMP_87 \def (\lambda (n0: nat).(let TMP_81 \def (\forall (w: T).(let TMP_80 
\def (\lambda (v: T).(let TMP_77 \def (TLRef n) in (let TMP_78 \def (S O) in 
(let TMP_79 \def (lift TMP_78 n0 v) in (subst0 n0 w TMP_77 TMP_79))))) in (ex 
T TMP_80))) in (let TMP_85 \def (\lambda (v: T).(let TMP_82 \def (TLRef n) in 
(let TMP_83 \def (S O) in (let TMP_84 \def (lift TMP_83 n0 v) in (eq T TMP_82 
TMP_84))))) in (let TMP_86 \def (ex T TMP_85) in (or TMP_81 TMP_86))))) in 
(let TMP_92 \def (\forall (w: T).(let TMP_91 \def (\lambda (v: T).(let TMP_88 
\def (TLRef n) in (let TMP_89 \def (S O) in (let TMP_90 \def (lift TMP_89 n 
v) in (subst0 n w TMP_88 TMP_90))))) in (ex T TMP_91))) in (let TMP_96 \def 
(\lambda (v: T).(let TMP_93 \def (TLRef n) in (let TMP_94 \def (S O) in (let 
TMP_95 \def (lift TMP_94 n v) in (eq T TMP_93 TMP_95))))) in (let TMP_97 \def 
(ex T TMP_96) in (let TMP_117 \def (\lambda (w: T).(let TMP_101 \def (\lambda 
(v: T).(let TMP_98 \def (TLRef n) in (let TMP_99 \def (S O) in (let TMP_100 
\def (lift TMP_99 n v) in (subst0 n w TMP_98 TMP_100))))) in (let TMP_102 
\def (lift n O w) in (let TMP_103 \def (S O) in (let TMP_104 \def (plus 
TMP_103 n) in (let TMP_105 \def (lift TMP_104 O w) in (let TMP_107 \def 
(\lambda (t0: T).(let TMP_106 \def (TLRef n) in (subst0 n w TMP_106 t0))) in 
(let TMP_108 \def (subst0_lref w n) in (let TMP_109 \def (S O) in (let 
TMP_110 \def (lift n O w) in (let TMP_111 \def (lift TMP_109 n TMP_110) in 
(let TMP_112 \def (S O) in (let TMP_113 \def (le_plus_r O n) in (let TMP_114 
\def (le_O_n n) in (let TMP_115 \def (lift_free w n TMP_112 O n TMP_113 
TMP_114) in (let TMP_116 \def (eq_ind_r T TMP_105 TMP_107 TMP_108 TMP_111 
TMP_115) in (ex_intro T TMP_101 TMP_102 TMP_116))))))))))))))))) in (let 
TMP_118 \def (or_introl TMP_92 TMP_97 TMP_117) in (eq_ind nat n TMP_87 
TMP_118 d H)))))))) in (let TMP_148 \def (\lambda (H: (lt d n)).(let TMP_124 
\def (\forall (w: T).(let TMP_123 \def (\lambda (v: T).(let TMP_120 \def 
(TLRef n) in (let TMP_121 \def (S O) in (let TMP_122 \def (lift TMP_121 d v) 
in (subst0 d w TMP_120 TMP_122))))) in (ex T TMP_123))) in (let TMP_128 \def 
(\lambda (v: T).(let TMP_125 \def (TLRef n) in (let TMP_126 \def (S O) in 
(let TMP_127 \def (lift TMP_126 d v) in (eq T TMP_125 TMP_127))))) in (let 
TMP_129 \def (ex T TMP_128) in (let TMP_133 \def (\lambda (v: T).(let TMP_130 
\def (TLRef n) in (let TMP_131 \def (S O) in (let TMP_132 \def (lift TMP_131 
d v) in (eq T TMP_130 TMP_132))))) in (let TMP_134 \def (pred n) in (let 
TMP_135 \def (TLRef TMP_134) in (let TMP_136 \def (TLRef n) in (let TMP_138 
\def (\lambda (t0: T).(let TMP_137 \def (TLRef n) in (eq T TMP_137 t0))) in 
(let TMP_139 \def (TLRef n) in (let TMP_140 \def (refl_equal T TMP_139) in 
(let TMP_141 \def (S O) in (let TMP_142 \def (pred n) in (let TMP_143 \def 
(TLRef TMP_142) in (let TMP_144 \def (lift TMP_141 d TMP_143) in (let TMP_145 
\def (lift_lref_gt d n H) in (let TMP_146 \def (eq_ind_r T TMP_136 TMP_138 
TMP_140 TMP_144 TMP_145) in (let TMP_147 \def (ex_intro T TMP_133 TMP_135 
TMP_146) in (or_intror TMP_124 TMP_129 TMP_147))))))))))))))))))) in 
(lt_eq_gt_e n d TMP_48 TMP_76 TMP_119 TMP_148)))))))))) in (let TMP_562 \def 
(\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (d: nat).(or (\forall 
(w: T).(ex T (\lambda (v: T).(subst0 d w t0 (lift (S O) d v))))) (ex T 
(\lambda (v: T).(eq T t0 (lift (S O) d v)))))))).(\lambda (t1: T).(\lambda 
(H0: ((\forall (d: nat).(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w 
t1 (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t1 (lift (S O) d 
v)))))))).(\lambda (d: nat).(let H_x \def (H d) in (let H1 \def H_x in (let 
TMP_153 \def (\forall (w: T).(let TMP_152 \def (\lambda (v: T).(let TMP_150 
\def (S O) in (let TMP_151 \def (lift TMP_150 d v) in (subst0 d w t0 
TMP_151)))) in (ex T TMP_152))) in (let TMP_156 \def (\lambda (v: T).(let 
TMP_154 \def (S O) in (let TMP_155 \def (lift TMP_154 d v) in (eq T t0 
TMP_155)))) in (let TMP_157 \def (ex T TMP_156) in (let TMP_162 \def (\forall 
(w: T).(let TMP_161 \def (\lambda (v: T).(let TMP_158 \def (THead k t0 t1) in 
(let TMP_159 \def (S O) in (let TMP_160 \def (lift TMP_159 d v) in (subst0 d 
w TMP_158 TMP_160))))) in (ex T TMP_161))) in (let TMP_166 \def (\lambda (v: 
T).(let TMP_163 \def (THead k t0 t1) in (let TMP_164 \def (S O) in (let 
TMP_165 \def (lift TMP_164 d v) in (eq T TMP_163 TMP_165))))) in (let TMP_167 
\def (ex T TMP_166) in (let TMP_168 \def (or TMP_162 TMP_167) in (let TMP_341 
\def (\lambda (H2: ((\forall (w: T).(ex T (\lambda (v: T).(subst0 d w t0 
(lift (S O) d v))))))).(let TMP_169 \def (s k d) in (let H_x0 \def (H0 
TMP_169) in (let H3 \def H_x0 in (let TMP_175 \def (\forall (w: T).(let 
TMP_174 \def (\lambda (v: T).(let TMP_170 \def (s k d) in (let TMP_171 \def 
(S O) in (let TMP_172 \def (s k d) in (let TMP_173 \def (lift TMP_171 TMP_172 
v) in (subst0 TMP_170 w t1 TMP_173)))))) in (ex T TMP_174))) in (let TMP_179 
\def (\lambda (v: T).(let TMP_176 \def (S O) in (let TMP_177 \def (s k d) in 
(let TMP_178 \def (lift TMP_176 TMP_177 v) in (eq T t1 TMP_178))))) in (let 
TMP_180 \def (ex T TMP_179) in (let TMP_185 \def (\forall (w: T).(let TMP_184 
\def (\lambda (v: T).(let TMP_181 \def (THead k t0 t1) in (let TMP_182 \def 
(S O) in (let TMP_183 \def (lift TMP_182 d v) in (subst0 d w TMP_181 
TMP_183))))) in (ex T TMP_184))) in (let TMP_189 \def (\lambda (v: T).(let 
TMP_186 \def (THead k t0 t1) in (let TMP_187 \def (S O) in (let TMP_188 \def 
(lift TMP_187 d v) in (eq T TMP_186 TMP_188))))) in (let TMP_190 \def (ex T 
TMP_189) in (let TMP_191 \def (or TMP_185 TMP_190) in (let TMP_248 \def 
(\lambda (H4: ((\forall (w: T).(ex T (\lambda (v: T).(subst0 (s k d) w t1 
(lift (S O) (s k d) v))))))).(let TMP_196 \def (\forall (w: T).(let TMP_195 
\def (\lambda (v: T).(let TMP_192 \def (THead k t0 t1) in (let TMP_193 \def 
(S O) in (let TMP_194 \def (lift TMP_193 d v) in (subst0 d w TMP_192 
TMP_194))))) in (ex T TMP_195))) in (let TMP_200 \def (\lambda (v: T).(let 
TMP_197 \def (THead k t0 t1) in (let TMP_198 \def (S O) in (let TMP_199 \def 
(lift TMP_198 d v) in (eq T TMP_197 TMP_199))))) in (let TMP_201 \def (ex T 
TMP_200) in (let TMP_247 \def (\lambda (w: T).(let H_x1 \def (H4 w) in (let 
H5 \def H_x1 in (let TMP_206 \def (\lambda (v: T).(let TMP_202 \def (s k d) 
in (let TMP_203 \def (S O) in (let TMP_204 \def (s k d) in (let TMP_205 \def 
(lift TMP_203 TMP_204 v) in (subst0 TMP_202 w t1 TMP_205)))))) in (let 
TMP_210 \def (\lambda (v: T).(let TMP_207 \def (THead k t0 t1) in (let 
TMP_208 \def (S O) in (let TMP_209 \def (lift TMP_208 d v) in (subst0 d w 
TMP_207 TMP_209))))) in (let TMP_211 \def (ex T TMP_210) in (let TMP_246 \def 
(\lambda (x: T).(\lambda (H6: (subst0 (s k d) w t1 (lift (S O) (s k d) 
x))).(let H_x2 \def (H2 w) in (let H7 \def H_x2 in (let TMP_214 \def (\lambda 
(v: T).(let TMP_212 \def (S O) in (let TMP_213 \def (lift TMP_212 d v) in 
(subst0 d w t0 TMP_213)))) in (let TMP_218 \def (\lambda (v: T).(let TMP_215 
\def (THead k t0 t1) in (let TMP_216 \def (S O) in (let TMP_217 \def (lift 
TMP_216 d v) in (subst0 d w TMP_215 TMP_217))))) in (let TMP_219 \def (ex T 
TMP_218) in (let TMP_245 \def (\lambda (x0: T).(\lambda (H8: (subst0 d w t0 
(lift (S O) d x0))).(let TMP_223 \def (\lambda (v: T).(let TMP_220 \def 
(THead k t0 t1) in (let TMP_221 \def (S O) in (let TMP_222 \def (lift TMP_221 
d v) in (subst0 d w TMP_220 TMP_222))))) in (let TMP_224 \def (THead k x0 x) 
in (let TMP_225 \def (S O) in (let TMP_226 \def (lift TMP_225 d x0) in (let 
TMP_227 \def (S O) in (let TMP_228 \def (s k d) in (let TMP_229 \def (lift 
TMP_227 TMP_228 x) in (let TMP_230 \def (THead k TMP_226 TMP_229) in (let 
TMP_232 \def (\lambda (t2: T).(let TMP_231 \def (THead k t0 t1) in (subst0 d 
w TMP_231 t2))) in (let TMP_233 \def (S O) in (let TMP_234 \def (lift TMP_233 
d x0) in (let TMP_235 \def (S O) in (let TMP_236 \def (s k d) in (let TMP_237 
\def (lift TMP_235 TMP_236 x) in (let TMP_238 \def (subst0_both w t0 TMP_234 
d H8 k t1 TMP_237 H6) in (let TMP_239 \def (S O) in (let TMP_240 \def (THead 
k x0 x) in (let TMP_241 \def (lift TMP_239 d TMP_240) in (let TMP_242 \def (S 
O) in (let TMP_243 \def (lift_head k x0 x TMP_242 d) in (let TMP_244 \def 
(eq_ind_r T TMP_230 TMP_232 TMP_238 TMP_241 TMP_243) in (ex_intro T TMP_223 
TMP_224 TMP_244)))))))))))))))))))))))) in (ex_ind T TMP_214 TMP_219 TMP_245 
H7))))))))) in (ex_ind T TMP_206 TMP_211 TMP_246 H5)))))))) in (or_introl 
TMP_196 TMP_201 TMP_247)))))) in (let TMP_340 \def (\lambda (H4: (ex T 
(\lambda (v: T).(eq T t1 (lift (S O) (s k d) v))))).(let TMP_252 \def 
(\lambda (v: T).(let TMP_249 \def (S O) in (let TMP_250 \def (s k d) in (let 
TMP_251 \def (lift TMP_249 TMP_250 v) in (eq T t1 TMP_251))))) in (let 
TMP_257 \def (\forall (w: T).(let TMP_256 \def (\lambda (v: T).(let TMP_253 
\def (THead k t0 t1) in (let TMP_254 \def (S O) in (let TMP_255 \def (lift 
TMP_254 d v) in (subst0 d w TMP_253 TMP_255))))) in (ex T TMP_256))) in (let 
TMP_261 \def (\lambda (v: T).(let TMP_258 \def (THead k t0 t1) in (let 
TMP_259 \def (S O) in (let TMP_260 \def (lift TMP_259 d v) in (eq T TMP_258 
TMP_260))))) in (let TMP_262 \def (ex T TMP_261) in (let TMP_263 \def (or 
TMP_257 TMP_262) in (let TMP_339 \def (\lambda (x: T).(\lambda (H5: (eq T t1 
(lift (S O) (s k d) x))).(let TMP_264 \def (S O) in (let TMP_265 \def (s k d) 
in (let TMP_266 \def (lift TMP_264 TMP_265 x) in (let TMP_277 \def (\lambda 
(t2: T).(let TMP_271 \def (\forall (w: T).(let TMP_270 \def (\lambda (v: 
T).(let TMP_267 \def (THead k t0 t2) in (let TMP_268 \def (S O) in (let 
TMP_269 \def (lift TMP_268 d v) in (subst0 d w TMP_267 TMP_269))))) in (ex T 
TMP_270))) in (let TMP_275 \def (\lambda (v: T).(let TMP_272 \def (THead k t0 
t2) in (let TMP_273 \def (S O) in (let TMP_274 \def (lift TMP_273 d v) in (eq 
T TMP_272 TMP_274))))) in (let TMP_276 \def (ex T TMP_275) in (or TMP_271 
TMP_276))))) in (let TMP_285 \def (\forall (w: T).(let TMP_284 \def (\lambda 
(v: T).(let TMP_278 \def (S O) in (let TMP_279 \def (s k d) in (let TMP_280 
\def (lift TMP_278 TMP_279 x) in (let TMP_281 \def (THead k t0 TMP_280) in 
(let TMP_282 \def (S O) in (let TMP_283 \def (lift TMP_282 d v) in (subst0 d 
w TMP_281 TMP_283)))))))) in (ex T TMP_284))) in (let TMP_292 \def (\lambda 
(v: T).(let TMP_286 \def (S O) in (let TMP_287 \def (s k d) in (let TMP_288 
\def (lift TMP_286 TMP_287 x) in (let TMP_289 \def (THead k t0 TMP_288) in 
(let TMP_290 \def (S O) in (let TMP_291 \def (lift TMP_290 d v) in (eq T 
TMP_289 TMP_291)))))))) in (let TMP_293 \def (ex T TMP_292) in (let TMP_337 
\def (\lambda (w: T).(let H_x1 \def (H2 w) in (let H6 \def H_x1 in (let 
TMP_296 \def (\lambda (v: T).(let TMP_294 \def (S O) in (let TMP_295 \def 
(lift TMP_294 d v) in (subst0 d w t0 TMP_295)))) in (let TMP_303 \def 
(\lambda (v: T).(let TMP_297 \def (S O) in (let TMP_298 \def (s k d) in (let 
TMP_299 \def (lift TMP_297 TMP_298 x) in (let TMP_300 \def (THead k t0 
TMP_299) in (let TMP_301 \def (S O) in (let TMP_302 \def (lift TMP_301 d v) 
in (subst0 d w TMP_300 TMP_302)))))))) in (let TMP_304 \def (ex T TMP_303) in 
(let TMP_336 \def (\lambda (x0: T).(\lambda (H7: (subst0 d w t0 (lift (S O) d 
x0))).(let TMP_311 \def (\lambda (v: T).(let TMP_305 \def (S O) in (let 
TMP_306 \def (s k d) in (let TMP_307 \def (lift TMP_305 TMP_306 x) in (let 
TMP_308 \def (THead k t0 TMP_307) in (let TMP_309 \def (S O) in (let TMP_310 
\def (lift TMP_309 d v) in (subst0 d w TMP_308 TMP_310)))))))) in (let 
TMP_312 \def (THead k x0 x) in (let TMP_313 \def (S O) in (let TMP_314 \def 
(lift TMP_313 d x0) in (let TMP_315 \def (S O) in (let TMP_316 \def (s k d) 
in (let TMP_317 \def (lift TMP_315 TMP_316 x) in (let TMP_318 \def (THead k 
TMP_314 TMP_317) in (let TMP_323 \def (\lambda (t2: T).(let TMP_319 \def (S 
O) in (let TMP_320 \def (s k d) in (let TMP_321 \def (lift TMP_319 TMP_320 x) 
in (let TMP_322 \def (THead k t0 TMP_321) in (subst0 d w TMP_322 t2)))))) in 
(let TMP_324 \def (S O) in (let TMP_325 \def (lift TMP_324 d x0) in (let 
TMP_326 \def (S O) in (let TMP_327 \def (s k d) in (let TMP_328 \def (lift 
TMP_326 TMP_327 x) in (let TMP_329 \def (subst0_fst w TMP_325 t0 d H7 TMP_328 
k) in (let TMP_330 \def (S O) in (let TMP_331 \def (THead k x0 x) in (let 
TMP_332 \def (lift TMP_330 d TMP_331) in (let TMP_333 \def (S O) in (let 
TMP_334 \def (lift_head k x0 x TMP_333 d) in (let TMP_335 \def (eq_ind_r T 
TMP_318 TMP_323 TMP_329 TMP_332 TMP_334) in (ex_intro T TMP_311 TMP_312 
TMP_335)))))))))))))))))))))))) in (ex_ind T TMP_296 TMP_304 TMP_336 
H6)))))))) in (let TMP_338 \def (or_introl TMP_285 TMP_293 TMP_337) in 
(eq_ind_r T TMP_266 TMP_277 TMP_338 t1 H5)))))))))))) in (ex_ind T TMP_252 
TMP_263 TMP_339 H4)))))))) in (or_ind TMP_175 TMP_180 TMP_191 TMP_248 TMP_340 
H3)))))))))))))) in (let TMP_561 \def (\lambda (H2: (ex T (\lambda (v: T).(eq 
T t0 (lift (S O) d v))))).(let TMP_344 \def (\lambda (v: T).(let TMP_342 \def 
(S O) in (let TMP_343 \def (lift TMP_342 d v) in (eq T t0 TMP_343)))) in (let 
TMP_349 \def (\forall (w: T).(let TMP_348 \def (\lambda (v: T).(let TMP_345 
\def (THead k t0 t1) in (let TMP_346 \def (S O) in (let TMP_347 \def (lift 
TMP_346 d v) in (subst0 d w TMP_345 TMP_347))))) in (ex T TMP_348))) in (let 
TMP_353 \def (\lambda (v: T).(let TMP_350 \def (THead k t0 t1) in (let 
TMP_351 \def (S O) in (let TMP_352 \def (lift TMP_351 d v) in (eq T TMP_350 
TMP_352))))) in (let TMP_354 \def (ex T TMP_353) in (let TMP_355 \def (or 
TMP_349 TMP_354) in (let TMP_560 \def (\lambda (x: T).(\lambda (H3: (eq T t0 
(lift (S O) d x))).(let TMP_356 \def (s k d) in (let H_x0 \def (H0 TMP_356) 
in (let H4 \def H_x0 in (let TMP_362 \def (\forall (w: T).(let TMP_361 \def 
(\lambda (v: T).(let TMP_357 \def (s k d) in (let TMP_358 \def (S O) in (let 
TMP_359 \def (s k d) in (let TMP_360 \def (lift TMP_358 TMP_359 v) in (subst0 
TMP_357 w t1 TMP_360)))))) in (ex T TMP_361))) in (let TMP_366 \def (\lambda 
(v: T).(let TMP_363 \def (S O) in (let TMP_364 \def (s k d) in (let TMP_365 
\def (lift TMP_363 TMP_364 v) in (eq T t1 TMP_365))))) in (let TMP_367 \def 
(ex T TMP_366) in (let TMP_372 \def (\forall (w: T).(let TMP_371 \def 
(\lambda (v: T).(let TMP_368 \def (THead k t0 t1) in (let TMP_369 \def (S O) 
in (let TMP_370 \def (lift TMP_369 d v) in (subst0 d w TMP_368 TMP_370))))) 
in (ex T TMP_371))) in (let TMP_376 \def (\lambda (v: T).(let TMP_373 \def 
(THead k t0 t1) in (let TMP_374 \def (S O) in (let TMP_375 \def (lift TMP_374 
d v) in (eq T TMP_373 TMP_375))))) in (let TMP_377 \def (ex T TMP_376) in 
(let TMP_378 \def (or TMP_372 TMP_377) in (let TMP_450 \def (\lambda (H5: 
((\forall (w: T).(ex T (\lambda (v: T).(subst0 (s k d) w t1 (lift (S O) (s k 
d) v))))))).(let TMP_379 \def (S O) in (let TMP_380 \def (lift TMP_379 d x) 
in (let TMP_391 \def (\lambda (t2: T).(let TMP_385 \def (\forall (w: T).(let 
TMP_384 \def (\lambda (v: T).(let TMP_381 \def (THead k t2 t1) in (let 
TMP_382 \def (S O) in (let TMP_383 \def (lift TMP_382 d v) in (subst0 d w 
TMP_381 TMP_383))))) in (ex T TMP_384))) in (let TMP_389 \def (\lambda (v: 
T).(let TMP_386 \def (THead k t2 t1) in (let TMP_387 \def (S O) in (let 
TMP_388 \def (lift TMP_387 d v) in (eq T TMP_386 TMP_388))))) in (let TMP_390 
\def (ex T TMP_389) in (or TMP_385 TMP_390))))) in (let TMP_398 \def (\forall 
(w: T).(let TMP_397 \def (\lambda (v: T).(let TMP_392 \def (S O) in (let 
TMP_393 \def (lift TMP_392 d x) in (let TMP_394 \def (THead k TMP_393 t1) in 
(let TMP_395 \def (S O) in (let TMP_396 \def (lift TMP_395 d v) in (subst0 d 
w TMP_394 TMP_396))))))) in (ex T TMP_397))) in (let TMP_404 \def (\lambda 
(v: T).(let TMP_399 \def (S O) in (let TMP_400 \def (lift TMP_399 d x) in 
(let TMP_401 \def (THead k TMP_400 t1) in (let TMP_402 \def (S O) in (let 
TMP_403 \def (lift TMP_402 d v) in (eq T TMP_401 TMP_403))))))) in (let 
TMP_405 \def (ex T TMP_404) in (let TMP_448 \def (\lambda (w: T).(let H_x1 
\def (H5 w) in (let H6 \def H_x1 in (let TMP_410 \def (\lambda (v: T).(let 
TMP_406 \def (s k d) in (let TMP_407 \def (S O) in (let TMP_408 \def (s k d) 
in (let TMP_409 \def (lift TMP_407 TMP_408 v) in (subst0 TMP_406 w t1 
TMP_409)))))) in (let TMP_416 \def (\lambda (v: T).(let TMP_411 \def (S O) in 
(let TMP_412 \def (lift TMP_411 d x) in (let TMP_413 \def (THead k TMP_412 
t1) in (let TMP_414 \def (S O) in (let TMP_415 \def (lift TMP_414 d v) in 
(subst0 d w TMP_413 TMP_415))))))) in (let TMP_417 \def (ex T TMP_416) in 
(let TMP_447 \def (\lambda (x0: T).(\lambda (H7: (subst0 (s k d) w t1 (lift 
(S O) (s k d) x0))).(let TMP_423 \def (\lambda (v: T).(let TMP_418 \def (S O) 
in (let TMP_419 \def (lift TMP_418 d x) in (let TMP_420 \def (THead k TMP_419 
t1) in (let TMP_421 \def (S O) in (let TMP_422 \def (lift TMP_421 d v) in 
(subst0 d w TMP_420 TMP_422))))))) in (let TMP_424 \def (THead k x x0) in 
(let TMP_425 \def (S O) in (let TMP_426 \def (lift TMP_425 d x) in (let 
TMP_427 \def (S O) in (let TMP_428 \def (s k d) in (let TMP_429 \def (lift 
TMP_427 TMP_428 x0) in (let TMP_430 \def (THead k TMP_426 TMP_429) in (let 
TMP_434 \def (\lambda (t2: T).(let TMP_431 \def (S O) in (let TMP_432 \def 
(lift TMP_431 d x) in (let TMP_433 \def (THead k TMP_432 t1) in (subst0 d w 
TMP_433 t2))))) in (let TMP_435 \def (S O) in (let TMP_436 \def (s k d) in 
(let TMP_437 \def (lift TMP_435 TMP_436 x0) in (let TMP_438 \def (S O) in 
(let TMP_439 \def (lift TMP_438 d x) in (let TMP_440 \def (subst0_snd k w 
TMP_437 t1 d H7 TMP_439) in (let TMP_441 \def (S O) in (let TMP_442 \def 
(THead k x x0) in (let TMP_443 \def (lift TMP_441 d TMP_442) in (let TMP_444 
\def (S O) in (let TMP_445 \def (lift_head k x x0 TMP_444 d) in (let TMP_446 
\def (eq_ind_r T TMP_430 TMP_434 TMP_440 TMP_443 TMP_445) in (ex_intro T 
TMP_423 TMP_424 TMP_446)))))))))))))))))))))))) in (ex_ind T TMP_410 TMP_417 
TMP_447 H6)))))))) in (let TMP_449 \def (or_introl TMP_398 TMP_405 TMP_448) 
in (eq_ind_r T TMP_380 TMP_391 TMP_449 t0 H3)))))))))) in (let TMP_559 \def 
(\lambda (H5: (ex T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) v))))).(let 
TMP_454 \def (\lambda (v: T).(let TMP_451 \def (S O) in (let TMP_452 \def (s 
k d) in (let TMP_453 \def (lift TMP_451 TMP_452 v) in (eq T t1 TMP_453))))) 
in (let TMP_459 \def (\forall (w: T).(let TMP_458 \def (\lambda (v: T).(let 
TMP_455 \def (THead k t0 t1) in (let TMP_456 \def (S O) in (let TMP_457 \def 
(lift TMP_456 d v) in (subst0 d w TMP_455 TMP_457))))) in (ex T TMP_458))) in 
(let TMP_463 \def (\lambda (v: T).(let TMP_460 \def (THead k t0 t1) in (let 
TMP_461 \def (S O) in (let TMP_462 \def (lift TMP_461 d v) in (eq T TMP_460 
TMP_462))))) in (let TMP_464 \def (ex T TMP_463) in (let TMP_465 \def (or 
TMP_459 TMP_464) in (let TMP_558 \def (\lambda (x0: T).(\lambda (H6: (eq T t1 
(lift (S O) (s k d) x0))).(let TMP_466 \def (S O) in (let TMP_467 \def (s k 
d) in (let TMP_468 \def (lift TMP_466 TMP_467 x0) in (let TMP_479 \def 
(\lambda (t2: T).(let TMP_473 \def (\forall (w: T).(let TMP_472 \def (\lambda 
(v: T).(let TMP_469 \def (THead k t0 t2) in (let TMP_470 \def (S O) in (let 
TMP_471 \def (lift TMP_470 d v) in (subst0 d w TMP_469 TMP_471))))) in (ex T 
TMP_472))) in (let TMP_477 \def (\lambda (v: T).(let TMP_474 \def (THead k t0 
t2) in (let TMP_475 \def (S O) in (let TMP_476 \def (lift TMP_475 d v) in (eq 
T TMP_474 TMP_476))))) in (let TMP_478 \def (ex T TMP_477) in (or TMP_473 
TMP_478))))) in (let TMP_480 \def (S O) in (let TMP_481 \def (lift TMP_480 d 
x) in (let TMP_498 \def (\lambda (t2: T).(let TMP_489 \def (\forall (w: 
T).(let TMP_488 \def (\lambda (v: T).(let TMP_482 \def (S O) in (let TMP_483 
\def (s k d) in (let TMP_484 \def (lift TMP_482 TMP_483 x0) in (let TMP_485 
\def (THead k t2 TMP_484) in (let TMP_486 \def (S O) in (let TMP_487 \def 
(lift TMP_486 d v) in (subst0 d w TMP_485 TMP_487)))))))) in (ex T TMP_488))) 
in (let TMP_496 \def (\lambda (v: T).(let TMP_490 \def (S O) in (let TMP_491 
\def (s k d) in (let TMP_492 \def (lift TMP_490 TMP_491 x0) in (let TMP_493 
\def (THead k t2 TMP_492) in (let TMP_494 \def (S O) in (let TMP_495 \def 
(lift TMP_494 d v) in (eq T TMP_493 TMP_495)))))))) in (let TMP_497 \def (ex 
T TMP_496) in (or TMP_489 TMP_497))))) in (let TMP_508 \def (\forall (w: 
T).(let TMP_507 \def (\lambda (v: T).(let TMP_499 \def (S O) in (let TMP_500 
\def (lift TMP_499 d x) in (let TMP_501 \def (S O) in (let TMP_502 \def (s k 
d) in (let TMP_503 \def (lift TMP_501 TMP_502 x0) in (let TMP_504 \def (THead 
k TMP_500 TMP_503) in (let TMP_505 \def (S O) in (let TMP_506 \def (lift 
TMP_505 d v) in (subst0 d w TMP_504 TMP_506)))))))))) in (ex T TMP_507))) in 
(let TMP_517 \def (\lambda (v: T).(let TMP_509 \def (S O) in (let TMP_510 
\def (lift TMP_509 d x) in (let TMP_511 \def (S O) in (let TMP_512 \def (s k 
d) in (let TMP_513 \def (lift TMP_511 TMP_512 x0) in (let TMP_514 \def (THead 
k TMP_510 TMP_513) in (let TMP_515 \def (S O) in (let TMP_516 \def (lift 
TMP_515 d v) in (eq T TMP_514 TMP_516)))))))))) in (let TMP_518 \def (ex T 
TMP_517) in (let TMP_527 \def (\lambda (v: T).(let TMP_519 \def (S O) in (let 
TMP_520 \def (lift TMP_519 d x) in (let TMP_521 \def (S O) in (let TMP_522 
\def (s k d) in (let TMP_523 \def (lift TMP_521 TMP_522 x0) in (let TMP_524 
\def (THead k TMP_520 TMP_523) in (let TMP_525 \def (S O) in (let TMP_526 
\def (lift TMP_525 d v) in (eq T TMP_524 TMP_526)))))))))) in (let TMP_528 
\def (THead k x x0) in (let TMP_529 \def (S O) in (let TMP_530 \def (lift 
TMP_529 d x) in (let TMP_531 \def (S O) in (let TMP_532 \def (s k d) in (let 
TMP_533 \def (lift TMP_531 TMP_532 x0) in (let TMP_534 \def (THead k TMP_530 
TMP_533) in (let TMP_541 \def (\lambda (t2: T).(let TMP_535 \def (S O) in 
(let TMP_536 \def (lift TMP_535 d x) in (let TMP_537 \def (S O) in (let 
TMP_538 \def (s k d) in (let TMP_539 \def (lift TMP_537 TMP_538 x0) in (let 
TMP_540 \def (THead k TMP_536 TMP_539) in (eq T TMP_540 t2)))))))) in (let 
TMP_542 \def (S O) in (let TMP_543 \def (lift TMP_542 d x) in (let TMP_544 
\def (S O) in (let TMP_545 \def (s k d) in (let TMP_546 \def (lift TMP_544 
TMP_545 x0) in (let TMP_547 \def (THead k TMP_543 TMP_546) in (let TMP_548 
\def (refl_equal T TMP_547) in (let TMP_549 \def (S O) in (let TMP_550 \def 
(THead k x x0) in (let TMP_551 \def (lift TMP_549 d TMP_550) in (let TMP_552 
\def (S O) in (let TMP_553 \def (lift_head k x x0 TMP_552 d) in (let TMP_554 
\def (eq_ind_r T TMP_534 TMP_541 TMP_548 TMP_551 TMP_553) in (let TMP_555 
\def (ex_intro T TMP_527 TMP_528 TMP_554) in (let TMP_556 \def (or_intror 
TMP_508 TMP_518 TMP_555) in (let TMP_557 \def (eq_ind_r T TMP_481 TMP_498 
TMP_556 t0 H3) in (eq_ind_r T TMP_468 TMP_479 TMP_557 t1 
H6)))))))))))))))))))))))))))))))))))))) in (ex_ind T TMP_454 TMP_465 TMP_558 
H5)))))))) in (or_ind TMP_362 TMP_367 TMP_378 TMP_450 TMP_559 
H4))))))))))))))) in (ex_ind T TMP_344 TMP_355 TMP_560 H2)))))))) in (or_ind 
TMP_153 TMP_157 TMP_168 TMP_341 TMP_561 H1)))))))))))))))))) in (T_ind TMP_9 
TMP_37 TMP_149 TMP_562 t))))).

theorem dnf_dec:
 \forall (w: T).(\forall (t: T).(\forall (d: nat).(ex T (\lambda (v: T).(or 
(subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d v)))))))
\def
 \lambda (w: T).(\lambda (t: T).(\lambda (d: nat).(let H_x \def (dnf_dec2 t 
d) in (let H \def H_x in (let TMP_4 \def (\forall (w0: T).(let TMP_3 \def 
(\lambda (v: T).(let TMP_1 \def (S O) in (let TMP_2 \def (lift TMP_1 d v) in 
(subst0 d w0 t TMP_2)))) in (ex T TMP_3))) in (let TMP_7 \def (\lambda (v: 
T).(let TMP_5 \def (S O) in (let TMP_6 \def (lift TMP_5 d v) in (eq T t 
TMP_6)))) in (let TMP_8 \def (ex T TMP_7) in (let TMP_15 \def (\lambda (v: 
T).(let TMP_9 \def (S O) in (let TMP_10 \def (lift TMP_9 d v) in (let TMP_11 
\def (subst0 d w t TMP_10) in (let TMP_12 \def (S O) in (let TMP_13 \def 
(lift TMP_12 d v) in (let TMP_14 \def (eq T t TMP_13) in (or TMP_11 
TMP_14)))))))) in (let TMP_16 \def (ex T TMP_15) in (let TMP_43 \def (\lambda 
(H0: ((\forall (w0: T).(ex T (\lambda (v: T).(subst0 d w0 t (lift (S O) d 
v))))))).(let H_x0 \def (H0 w) in (let H1 \def H_x0 in (let TMP_19 \def 
(\lambda (v: T).(let TMP_17 \def (S O) in (let TMP_18 \def (lift TMP_17 d v) 
in (subst0 d w t TMP_18)))) in (let TMP_26 \def (\lambda (v: T).(let TMP_20 
\def (S O) in (let TMP_21 \def (lift TMP_20 d v) in (let TMP_22 \def (subst0 
d w t TMP_21) in (let TMP_23 \def (S O) in (let TMP_24 \def (lift TMP_23 d v) 
in (let TMP_25 \def (eq T t TMP_24) in (or TMP_22 TMP_25)))))))) in (let 
TMP_27 \def (ex T TMP_26) in (let TMP_42 \def (\lambda (x: T).(\lambda (H2: 
(subst0 d w t (lift (S O) d x))).(let TMP_34 \def (\lambda (v: T).(let TMP_28 
\def (S O) in (let TMP_29 \def (lift TMP_28 d v) in (let TMP_30 \def (subst0 
d w t TMP_29) in (let TMP_31 \def (S O) in (let TMP_32 \def (lift TMP_31 d v) 
in (let TMP_33 \def (eq T t TMP_32) in (or TMP_30 TMP_33)))))))) in (let 
TMP_35 \def (S O) in (let TMP_36 \def (lift TMP_35 d x) in (let TMP_37 \def 
(subst0 d w t TMP_36) in (let TMP_38 \def (S O) in (let TMP_39 \def (lift 
TMP_38 d x) in (let TMP_40 \def (eq T t TMP_39) in (let TMP_41 \def 
(or_introl TMP_37 TMP_40 H2) in (ex_intro T TMP_34 x TMP_41))))))))))) in 
(ex_ind T TMP_19 TMP_27 TMP_42 H1)))))))) in (let TMP_92 \def (\lambda (H0: 
(ex T (\lambda (v: T).(eq T t (lift (S O) d v))))).(let TMP_46 \def (\lambda 
(v: T).(let TMP_44 \def (S O) in (let TMP_45 \def (lift TMP_44 d v) in (eq T 
t TMP_45)))) in (let TMP_53 \def (\lambda (v: T).(let TMP_47 \def (S O) in 
(let TMP_48 \def (lift TMP_47 d v) in (let TMP_49 \def (subst0 d w t TMP_48) 
in (let TMP_50 \def (S O) in (let TMP_51 \def (lift TMP_50 d v) in (let 
TMP_52 \def (eq T t TMP_51) in (or TMP_49 TMP_52)))))))) in (let TMP_54 \def 
(ex T TMP_53) in (let TMP_91 \def (\lambda (x: T).(\lambda (H1: (eq T t (lift 
(S O) d x))).(let TMP_55 \def (S O) in (let TMP_56 \def (lift TMP_55 d x) in 
(let TMP_64 \def (\lambda (t0: T).(let TMP_63 \def (\lambda (v: T).(let 
TMP_57 \def (S O) in (let TMP_58 \def (lift TMP_57 d v) in (let TMP_59 \def 
(subst0 d w t0 TMP_58) in (let TMP_60 \def (S O) in (let TMP_61 \def (lift 
TMP_60 d v) in (let TMP_62 \def (eq T t0 TMP_61) in (or TMP_59 TMP_62)))))))) 
in (ex T TMP_63))) in (let TMP_75 \def (\lambda (v: T).(let TMP_65 \def (S O) 
in (let TMP_66 \def (lift TMP_65 d x) in (let TMP_67 \def (S O) in (let 
TMP_68 \def (lift TMP_67 d v) in (let TMP_69 \def (subst0 d w TMP_66 TMP_68) 
in (let TMP_70 \def (S O) in (let TMP_71 \def (lift TMP_70 d x) in (let 
TMP_72 \def (S O) in (let TMP_73 \def (lift TMP_72 d v) in (let TMP_74 \def 
(eq T TMP_71 TMP_73) in (or TMP_69 TMP_74)))))))))))) in (let TMP_76 \def (S 
O) in (let TMP_77 \def (lift TMP_76 d x) in (let TMP_78 \def (S O) in (let 
TMP_79 \def (lift TMP_78 d x) in (let TMP_80 \def (subst0 d w TMP_77 TMP_79) 
in (let TMP_81 \def (S O) in (let TMP_82 \def (lift TMP_81 d x) in (let 
TMP_83 \def (S O) in (let TMP_84 \def (lift TMP_83 d x) in (let TMP_85 \def 
(eq T TMP_82 TMP_84) in (let TMP_86 \def (S O) in (let TMP_87 \def (lift 
TMP_86 d x) in (let TMP_88 \def (refl_equal T TMP_87) in (let TMP_89 \def 
(or_intror TMP_80 TMP_85 TMP_88) in (let TMP_90 \def (ex_intro T TMP_75 x 
TMP_89) in (eq_ind_r T TMP_56 TMP_64 TMP_90 t H1)))))))))))))))))))))) in 
(ex_ind T TMP_46 TMP_54 TMP_91 H0)))))) in (or_ind TMP_4 TMP_8 TMP_16 TMP_43 
TMP_92 H)))))))))))).

