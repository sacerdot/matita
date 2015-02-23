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

include "basic_1/pr0/fwd.ma".

include "basic_1/subst0/props.ma".

theorem pr0_lift:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (h: nat).(\forall 
(d: nat).(pr0 (lift h d t1) (lift h d t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(let TMP_3 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).(let 
TMP_1 \def (lift h d t) in (let TMP_2 \def (lift h d t0) in (pr0 TMP_1 
TMP_2))))))) in (let TMP_5 \def (\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(let TMP_4 \def (lift h d t) in (pr0_refl TMP_4))))) in (let TMP_39 
\def (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d u1) (lift h d 
u2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda 
(H3: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) (lift h d 
t4)))))).(\lambda (k: K).(\lambda (h: nat).(\lambda (d: nat).(let TMP_6 \def 
(lift h d u1) in (let TMP_7 \def (s k d) in (let TMP_8 \def (lift h TMP_7 t3) 
in (let TMP_9 \def (THead k TMP_6 TMP_8) in (let TMP_12 \def (\lambda (t: 
T).(let TMP_10 \def (THead k u2 t4) in (let TMP_11 \def (lift h d TMP_10) in 
(pr0 t TMP_11)))) in (let TMP_13 \def (lift h d u2) in (let TMP_14 \def (s k 
d) in (let TMP_15 \def (lift h TMP_14 t4) in (let TMP_16 \def (THead k TMP_13 
TMP_15) in (let TMP_21 \def (\lambda (t: T).(let TMP_17 \def (lift h d u1) in 
(let TMP_18 \def (s k d) in (let TMP_19 \def (lift h TMP_18 t3) in (let 
TMP_20 \def (THead k TMP_17 TMP_19) in (pr0 TMP_20 t)))))) in (let TMP_22 
\def (lift h d u1) in (let TMP_23 \def (lift h d u2) in (let TMP_24 \def (H1 
h d) in (let TMP_25 \def (s k d) in (let TMP_26 \def (lift h TMP_25 t3) in 
(let TMP_27 \def (s k d) in (let TMP_28 \def (lift h TMP_27 t4) in (let 
TMP_29 \def (s k d) in (let TMP_30 \def (H3 h TMP_29) in (let TMP_31 \def 
(pr0_comp TMP_22 TMP_23 TMP_24 TMP_26 TMP_28 TMP_30 k) in (let TMP_32 \def 
(THead k u2 t4) in (let TMP_33 \def (lift h d TMP_32) in (let TMP_34 \def 
(lift_head k u2 t4 h d) in (let TMP_35 \def (eq_ind_r T TMP_16 TMP_21 TMP_31 
TMP_33 TMP_34) in (let TMP_36 \def (THead k u1 t3) in (let TMP_37 \def (lift 
h d TMP_36) in (let TMP_38 \def (lift_head k u1 t3 h d) in (eq_ind_r T TMP_9 
TMP_12 TMP_35 TMP_37 TMP_38))))))))))))))))))))))))))))))))))))))) in (let 
TMP_132 \def (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: 
(pr0 v1 v2)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h 
d v1) (lift h d v2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 
t3 t4)).(\lambda (H3: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) 
(lift h d t4)))))).(\lambda (h: nat).(\lambda (d: nat).(let TMP_40 \def (Flat 
Appl) in (let TMP_41 \def (lift h d v1) in (let TMP_42 \def (Flat Appl) in 
(let TMP_43 \def (s TMP_42 d) in (let TMP_44 \def (Bind Abst) in (let TMP_45 
\def (THead TMP_44 u t3) in (let TMP_46 \def (lift h TMP_43 TMP_45) in (let 
TMP_47 \def (THead TMP_40 TMP_41 TMP_46) in (let TMP_51 \def (\lambda (t: 
T).(let TMP_48 \def (Bind Abbr) in (let TMP_49 \def (THead TMP_48 v2 t4) in 
(let TMP_50 \def (lift h d TMP_49) in (pr0 t TMP_50))))) in (let TMP_52 \def 
(Bind Abst) in (let TMP_53 \def (Flat Appl) in (let TMP_54 \def (s TMP_53 d) 
in (let TMP_55 \def (lift h TMP_54 u) in (let TMP_56 \def (Bind Abst) in (let 
TMP_57 \def (Flat Appl) in (let TMP_58 \def (s TMP_57 d) in (let TMP_59 \def 
(s TMP_56 TMP_58) in (let TMP_60 \def (lift h TMP_59 t3) in (let TMP_61 \def 
(THead TMP_52 TMP_55 TMP_60) in (let TMP_68 \def (\lambda (t: T).(let TMP_62 
\def (Flat Appl) in (let TMP_63 \def (lift h d v1) in (let TMP_64 \def (THead 
TMP_62 TMP_63 t) in (let TMP_65 \def (Bind Abbr) in (let TMP_66 \def (THead 
TMP_65 v2 t4) in (let TMP_67 \def (lift h d TMP_66) in (pr0 TMP_64 
TMP_67)))))))) in (let TMP_69 \def (Bind Abbr) in (let TMP_70 \def (lift h d 
v2) in (let TMP_71 \def (Bind Abbr) in (let TMP_72 \def (s TMP_71 d) in (let 
TMP_73 \def (lift h TMP_72 t4) in (let TMP_74 \def (THead TMP_69 TMP_70 
TMP_73) in (let TMP_88 \def (\lambda (t: T).(let TMP_75 \def (Flat Appl) in 
(let TMP_76 \def (lift h d v1) in (let TMP_77 \def (Bind Abst) in (let TMP_78 
\def (Flat Appl) in (let TMP_79 \def (s TMP_78 d) in (let TMP_80 \def (lift h 
TMP_79 u) in (let TMP_81 \def (Bind Abst) in (let TMP_82 \def (Flat Appl) in 
(let TMP_83 \def (s TMP_82 d) in (let TMP_84 \def (s TMP_81 TMP_83) in (let 
TMP_85 \def (lift h TMP_84 t3) in (let TMP_86 \def (THead TMP_77 TMP_80 
TMP_85) in (let TMP_87 \def (THead TMP_75 TMP_76 TMP_86) in (pr0 TMP_87 
t))))))))))))))) in (let TMP_89 \def (Flat Appl) in (let TMP_90 \def (s 
TMP_89 d) in (let TMP_91 \def (lift h TMP_90 u) in (let TMP_92 \def (lift h d 
v1) in (let TMP_93 \def (lift h d v2) in (let TMP_94 \def (H1 h d) in (let 
TMP_95 \def (Bind Abst) in (let TMP_96 \def (Flat Appl) in (let TMP_97 \def 
(s TMP_96 d) in (let TMP_98 \def (s TMP_95 TMP_97) in (let TMP_99 \def (lift 
h TMP_98 t3) in (let TMP_100 \def (Bind Abbr) in (let TMP_101 \def (s TMP_100 
d) in (let TMP_102 \def (lift h TMP_101 t4) in (let TMP_103 \def (Bind Abbr) 
in (let TMP_104 \def (s TMP_103 d) in (let TMP_105 \def (H3 h TMP_104) in 
(let TMP_106 \def (pr0_beta TMP_91 TMP_92 TMP_93 TMP_94 TMP_99 TMP_102 
TMP_105) in (let TMP_107 \def (Bind Abbr) in (let TMP_108 \def (THead TMP_107 
v2 t4) in (let TMP_109 \def (lift h d TMP_108) in (let TMP_110 \def (Bind 
Abbr) in (let TMP_111 \def (lift_head TMP_110 v2 t4 h d) in (let TMP_112 \def 
(eq_ind_r T TMP_74 TMP_88 TMP_106 TMP_109 TMP_111) in (let TMP_113 \def (Flat 
Appl) in (let TMP_114 \def (s TMP_113 d) in (let TMP_115 \def (Bind Abst) in 
(let TMP_116 \def (THead TMP_115 u t3) in (let TMP_117 \def (lift h TMP_114 
TMP_116) in (let TMP_118 \def (Bind Abst) in (let TMP_119 \def (Flat Appl) in 
(let TMP_120 \def (s TMP_119 d) in (let TMP_121 \def (lift_head TMP_118 u t3 
h TMP_120) in (let TMP_122 \def (eq_ind_r T TMP_61 TMP_68 TMP_112 TMP_117 
TMP_121) in (let TMP_123 \def (Flat Appl) in (let TMP_124 \def (Bind Abst) in 
(let TMP_125 \def (THead TMP_124 u t3) in (let TMP_126 \def (THead TMP_123 v1 
TMP_125) in (let TMP_127 \def (lift h d TMP_126) in (let TMP_128 \def (Flat 
Appl) in (let TMP_129 \def (Bind Abst) in (let TMP_130 \def (THead TMP_129 u 
t3) in (let TMP_131 \def (lift_head TMP_128 v1 TMP_130 h d) in (eq_ind_r T 
TMP_47 TMP_51 TMP_122 TMP_127 
TMP_131)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))) in (let TMP_339 \def (\lambda (b: B).(\lambda (H0: (not (eq B b 
Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda 
(H2: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d v1) (lift h d 
v2)))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(H4: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d u1) (lift h d 
u2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda 
(H6: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) (lift h d 
t4)))))).(\lambda (h: nat).(\lambda (d: nat).(let TMP_133 \def (Flat Appl) in 
(let TMP_134 \def (lift h d v1) in (let TMP_135 \def (Flat Appl) in (let 
TMP_136 \def (s TMP_135 d) in (let TMP_137 \def (Bind b) in (let TMP_138 \def 
(THead TMP_137 u1 t3) in (let TMP_139 \def (lift h TMP_136 TMP_138) in (let 
TMP_140 \def (THead TMP_133 TMP_134 TMP_139) in (let TMP_148 \def (\lambda 
(t: T).(let TMP_141 \def (Bind b) in (let TMP_142 \def (Flat Appl) in (let 
TMP_143 \def (S O) in (let TMP_144 \def (lift TMP_143 O v2) in (let TMP_145 
\def (THead TMP_142 TMP_144 t4) in (let TMP_146 \def (THead TMP_141 u2 
TMP_145) in (let TMP_147 \def (lift h d TMP_146) in (pr0 t TMP_147))))))))) 
in (let TMP_149 \def (Bind b) in (let TMP_150 \def (Flat Appl) in (let 
TMP_151 \def (s TMP_150 d) in (let TMP_152 \def (lift h TMP_151 u1) in (let 
TMP_153 \def (Bind b) in (let TMP_154 \def (Flat Appl) in (let TMP_155 \def 
(s TMP_154 d) in (let TMP_156 \def (s TMP_153 TMP_155) in (let TMP_157 \def 
(lift h TMP_156 t3) in (let TMP_158 \def (THead TMP_149 TMP_152 TMP_157) in 
(let TMP_169 \def (\lambda (t: T).(let TMP_159 \def (Flat Appl) in (let 
TMP_160 \def (lift h d v1) in (let TMP_161 \def (THead TMP_159 TMP_160 t) in 
(let TMP_162 \def (Bind b) in (let TMP_163 \def (Flat Appl) in (let TMP_164 
\def (S O) in (let TMP_165 \def (lift TMP_164 O v2) in (let TMP_166 \def 
(THead TMP_163 TMP_165 t4) in (let TMP_167 \def (THead TMP_162 u2 TMP_166) in 
(let TMP_168 \def (lift h d TMP_167) in (pr0 TMP_161 TMP_168)))))))))))) in 
(let TMP_170 \def (Bind b) in (let TMP_171 \def (lift h d u2) in (let TMP_172 
\def (Bind b) in (let TMP_173 \def (s TMP_172 d) in (let TMP_174 \def (Flat 
Appl) in (let TMP_175 \def (S O) in (let TMP_176 \def (lift TMP_175 O v2) in 
(let TMP_177 \def (THead TMP_174 TMP_176 t4) in (let TMP_178 \def (lift h 
TMP_173 TMP_177) in (let TMP_179 \def (THead TMP_170 TMP_171 TMP_178) in (let 
TMP_193 \def (\lambda (t: T).(let TMP_180 \def (Flat Appl) in (let TMP_181 
\def (lift h d v1) in (let TMP_182 \def (Bind b) in (let TMP_183 \def (Flat 
Appl) in (let TMP_184 \def (s TMP_183 d) in (let TMP_185 \def (lift h TMP_184 
u1) in (let TMP_186 \def (Bind b) in (let TMP_187 \def (Flat Appl) in (let 
TMP_188 \def (s TMP_187 d) in (let TMP_189 \def (s TMP_186 TMP_188) in (let 
TMP_190 \def (lift h TMP_189 t3) in (let TMP_191 \def (THead TMP_182 TMP_185 
TMP_190) in (let TMP_192 \def (THead TMP_180 TMP_181 TMP_191) in (pr0 TMP_192 
t))))))))))))))) in (let TMP_194 \def (Flat Appl) in (let TMP_195 \def (Bind 
b) in (let TMP_196 \def (s TMP_195 d) in (let TMP_197 \def (S O) in (let 
TMP_198 \def (lift TMP_197 O v2) in (let TMP_199 \def (lift h TMP_196 
TMP_198) in (let TMP_200 \def (Flat Appl) in (let TMP_201 \def (Bind b) in 
(let TMP_202 \def (s TMP_201 d) in (let TMP_203 \def (s TMP_200 TMP_202) in 
(let TMP_204 \def (lift h TMP_203 t4) in (let TMP_205 \def (THead TMP_194 
TMP_199 TMP_204) in (let TMP_222 \def (\lambda (t: T).(let TMP_206 \def (Flat 
Appl) in (let TMP_207 \def (lift h d v1) in (let TMP_208 \def (Bind b) in 
(let TMP_209 \def (Flat Appl) in (let TMP_210 \def (s TMP_209 d) in (let 
TMP_211 \def (lift h TMP_210 u1) in (let TMP_212 \def (Bind b) in (let 
TMP_213 \def (Flat Appl) in (let TMP_214 \def (s TMP_213 d) in (let TMP_215 
\def (s TMP_212 TMP_214) in (let TMP_216 \def (lift h TMP_215 t3) in (let 
TMP_217 \def (THead TMP_208 TMP_211 TMP_216) in (let TMP_218 \def (THead 
TMP_206 TMP_207 TMP_217) in (let TMP_219 \def (Bind b) in (let TMP_220 \def 
(lift h d u2) in (let TMP_221 \def (THead TMP_219 TMP_220 t) in (pr0 TMP_218 
TMP_221)))))))))))))))))) in (let TMP_223 \def (S O) in (let TMP_224 \def 
(plus TMP_223 d) in (let TMP_241 \def (\lambda (n: nat).(let TMP_225 \def 
(Flat Appl) in (let TMP_226 \def (lift h d v1) in (let TMP_227 \def (Bind b) 
in (let TMP_228 \def (lift h d u1) in (let TMP_229 \def (lift h n t3) in (let 
TMP_230 \def (THead TMP_227 TMP_228 TMP_229) in (let TMP_231 \def (THead 
TMP_225 TMP_226 TMP_230) in (let TMP_232 \def (Bind b) in (let TMP_233 \def 
(lift h d u2) in (let TMP_234 \def (Flat Appl) in (let TMP_235 \def (S O) in 
(let TMP_236 \def (lift TMP_235 O v2) in (let TMP_237 \def (lift h n TMP_236) 
in (let TMP_238 \def (lift h n t4) in (let TMP_239 \def (THead TMP_234 
TMP_237 TMP_238) in (let TMP_240 \def (THead TMP_232 TMP_233 TMP_239) in (pr0 
TMP_231 TMP_240)))))))))))))))))) in (let TMP_242 \def (S O) in (let TMP_243 
\def (lift h d v2) in (let TMP_244 \def (lift TMP_242 O TMP_243) in (let 
TMP_262 \def (\lambda (t: T).(let TMP_245 \def (Flat Appl) in (let TMP_246 
\def (lift h d v1) in (let TMP_247 \def (Bind b) in (let TMP_248 \def (lift h 
d u1) in (let TMP_249 \def (S O) in (let TMP_250 \def (plus TMP_249 d) in 
(let TMP_251 \def (lift h TMP_250 t3) in (let TMP_252 \def (THead TMP_247 
TMP_248 TMP_251) in (let TMP_253 \def (THead TMP_245 TMP_246 TMP_252) in (let 
TMP_254 \def (Bind b) in (let TMP_255 \def (lift h d u2) in (let TMP_256 \def 
(Flat Appl) in (let TMP_257 \def (S O) in (let TMP_258 \def (plus TMP_257 d) 
in (let TMP_259 \def (lift h TMP_258 t4) in (let TMP_260 \def (THead TMP_256 
t TMP_259) in (let TMP_261 \def (THead TMP_254 TMP_255 TMP_260) in (pr0 
TMP_253 TMP_261))))))))))))))))))) in (let TMP_263 \def (lift h d v1) in (let 
TMP_264 \def (lift h d v2) in (let TMP_265 \def (H2 h d) in (let TMP_266 \def 
(lift h d u1) in (let TMP_267 \def (lift h d u2) in (let TMP_268 \def (H4 h 
d) in (let TMP_269 \def (S O) in (let TMP_270 \def (plus TMP_269 d) in (let 
TMP_271 \def (lift h TMP_270 t3) in (let TMP_272 \def (S O) in (let TMP_273 
\def (plus TMP_272 d) in (let TMP_274 \def (lift h TMP_273 t4) in (let 
TMP_275 \def (S O) in (let TMP_276 \def (plus TMP_275 d) in (let TMP_277 \def 
(H6 h TMP_276) in (let TMP_278 \def (pr0_upsilon b H0 TMP_263 TMP_264 TMP_265 
TMP_266 TMP_267 TMP_268 TMP_271 TMP_274 TMP_277) in (let TMP_279 \def (S O) 
in (let TMP_280 \def (plus TMP_279 d) in (let TMP_281 \def (S O) in (let 
TMP_282 \def (lift TMP_281 O v2) in (let TMP_283 \def (lift h TMP_280 
TMP_282) in (let TMP_284 \def (S O) in (let TMP_285 \def (le_O_n d) in (let 
TMP_286 \def (lift_d v2 h TMP_284 d O TMP_285) in (let TMP_287 \def (eq_ind_r 
T TMP_244 TMP_262 TMP_278 TMP_283 TMP_286) in (let TMP_288 \def (S d) in (let 
TMP_289 \def (S d) in (let TMP_290 \def (refl_equal nat TMP_289) in (let 
TMP_291 \def (eq_ind nat TMP_224 TMP_241 TMP_287 TMP_288 TMP_290) in (let 
TMP_292 \def (Bind b) in (let TMP_293 \def (s TMP_292 d) in (let TMP_294 \def 
(Flat Appl) in (let TMP_295 \def (S O) in (let TMP_296 \def (lift TMP_295 O 
v2) in (let TMP_297 \def (THead TMP_294 TMP_296 t4) in (let TMP_298 \def 
(lift h TMP_293 TMP_297) in (let TMP_299 \def (Flat Appl) in (let TMP_300 
\def (S O) in (let TMP_301 \def (lift TMP_300 O v2) in (let TMP_302 \def 
(Bind b) in (let TMP_303 \def (s TMP_302 d) in (let TMP_304 \def (lift_head 
TMP_299 TMP_301 t4 h TMP_303) in (let TMP_305 \def (eq_ind_r T TMP_205 
TMP_222 TMP_291 TMP_298 TMP_304) in (let TMP_306 \def (Bind b) in (let 
TMP_307 \def (Flat Appl) in (let TMP_308 \def (S O) in (let TMP_309 \def 
(lift TMP_308 O v2) in (let TMP_310 \def (THead TMP_307 TMP_309 t4) in (let 
TMP_311 \def (THead TMP_306 u2 TMP_310) in (let TMP_312 \def (lift h d 
TMP_311) in (let TMP_313 \def (Bind b) in (let TMP_314 \def (Flat Appl) in 
(let TMP_315 \def (S O) in (let TMP_316 \def (lift TMP_315 O v2) in (let 
TMP_317 \def (THead TMP_314 TMP_316 t4) in (let TMP_318 \def (lift_head 
TMP_313 u2 TMP_317 h d) in (let TMP_319 \def (eq_ind_r T TMP_179 TMP_193 
TMP_305 TMP_312 TMP_318) in (let TMP_320 \def (Flat Appl) in (let TMP_321 
\def (s TMP_320 d) in (let TMP_322 \def (Bind b) in (let TMP_323 \def (THead 
TMP_322 u1 t3) in (let TMP_324 \def (lift h TMP_321 TMP_323) in (let TMP_325 
\def (Bind b) in (let TMP_326 \def (Flat Appl) in (let TMP_327 \def (s 
TMP_326 d) in (let TMP_328 \def (lift_head TMP_325 u1 t3 h TMP_327) in (let 
TMP_329 \def (eq_ind_r T TMP_158 TMP_169 TMP_319 TMP_324 TMP_328) in (let 
TMP_330 \def (Flat Appl) in (let TMP_331 \def (Bind b) in (let TMP_332 \def 
(THead TMP_331 u1 t3) in (let TMP_333 \def (THead TMP_330 v1 TMP_332) in (let 
TMP_334 \def (lift h d TMP_333) in (let TMP_335 \def (Flat Appl) in (let 
TMP_336 \def (Bind b) in (let TMP_337 \def (THead TMP_336 u1 t3) in (let 
TMP_338 \def (lift_head TMP_335 v1 TMP_337 h d) in (eq_ind_r T TMP_140 
TMP_148 TMP_329 TMP_334 
TMP_338)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(let TMP_405 \def (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 
u2)).(\lambda (H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d u1) 
(lift h d u2)))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 
t4)).(\lambda (H3: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) 
(lift h d t4)))))).(\lambda (w: T).(\lambda (H4: (subst0 O u2 t4 w)).(\lambda 
(h: nat).(\lambda (d: nat).(let TMP_340 \def (Bind Abbr) in (let TMP_341 \def 
(lift h d u1) in (let TMP_342 \def (Bind Abbr) in (let TMP_343 \def (s 
TMP_342 d) in (let TMP_344 \def (lift h TMP_343 t3) in (let TMP_345 \def 
(THead TMP_340 TMP_341 TMP_344) in (let TMP_349 \def (\lambda (t: T).(let 
TMP_346 \def (Bind Abbr) in (let TMP_347 \def (THead TMP_346 u2 w) in (let 
TMP_348 \def (lift h d TMP_347) in (pr0 t TMP_348))))) in (let TMP_350 \def 
(Bind Abbr) in (let TMP_351 \def (lift h d u2) in (let TMP_352 \def (Bind 
Abbr) in (let TMP_353 \def (s TMP_352 d) in (let TMP_354 \def (lift h TMP_353 
w) in (let TMP_355 \def (THead TMP_350 TMP_351 TMP_354) in (let TMP_362 \def 
(\lambda (t: T).(let TMP_356 \def (Bind Abbr) in (let TMP_357 \def (lift h d 
u1) in (let TMP_358 \def (Bind Abbr) in (let TMP_359 \def (s TMP_358 d) in 
(let TMP_360 \def (lift h TMP_359 t3) in (let TMP_361 \def (THead TMP_356 
TMP_357 TMP_360) in (pr0 TMP_361 t)))))))) in (let TMP_363 \def (lift h d u1) 
in (let TMP_364 \def (lift h d u2) in (let TMP_365 \def (H1 h d) in (let 
TMP_366 \def (S d) in (let TMP_367 \def (lift h TMP_366 t3) in (let TMP_368 
\def (S d) in (let TMP_369 \def (lift h TMP_368 t4) in (let TMP_370 \def (S 
d) in (let TMP_371 \def (H3 h TMP_370) in (let TMP_372 \def (S d) in (let 
TMP_373 \def (lift h TMP_372 w) in (let d' \def (S d) in (let TMP_374 \def (S 
d) in (let TMP_375 \def (S O) in (let TMP_376 \def (minus TMP_374 TMP_375) in 
(let TMP_380 \def (\lambda (n: nat).(let TMP_377 \def (lift h n u2) in (let 
TMP_378 \def (lift h d' t4) in (let TMP_379 \def (lift h d' w) in (subst0 O 
TMP_377 TMP_378 TMP_379))))) in (let TMP_381 \def (S d) in (let TMP_382 \def 
(le_O_n d) in (let TMP_383 \def (le_n_S O d TMP_382) in (let TMP_384 \def 
(subst0_lift_lt t4 w u2 O H4 TMP_381 TMP_383 h) in (let TMP_385 \def (\lambda 
(n: nat).(eq nat n d)) in (let TMP_386 \def (le_n d) in (let TMP_387 \def 
(le_n d) in (let TMP_388 \def (le_antisym d d TMP_386 TMP_387) in (let 
TMP_389 \def (minus d O) in (let TMP_390 \def (minus_n_O d) in (let TMP_391 
\def (eq_ind nat d TMP_385 TMP_388 TMP_389 TMP_390) in (let TMP_392 \def 
(eq_ind nat TMP_376 TMP_380 TMP_384 d TMP_391) in (let TMP_393 \def 
(pr0_delta TMP_363 TMP_364 TMP_365 TMP_367 TMP_369 TMP_371 TMP_373 TMP_392) 
in (let TMP_394 \def (Bind Abbr) in (let TMP_395 \def (THead TMP_394 u2 w) in 
(let TMP_396 \def (lift h d TMP_395) in (let TMP_397 \def (Bind Abbr) in (let 
TMP_398 \def (lift_head TMP_397 u2 w h d) in (let TMP_399 \def (eq_ind_r T 
TMP_355 TMP_362 TMP_393 TMP_396 TMP_398) in (let TMP_400 \def (Bind Abbr) in 
(let TMP_401 \def (THead TMP_400 u1 t3) in (let TMP_402 \def (lift h d 
TMP_401) in (let TMP_403 \def (Bind Abbr) in (let TMP_404 \def (lift_head 
TMP_403 u1 t3 h d) in (eq_ind_r T TMP_345 TMP_349 TMP_399 TMP_402 
TMP_404))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(let TMP_461 \def (\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (H2: ((\forall 
(h: nat).(\forall (d: nat).(pr0 (lift h d t3) (lift h d t4)))))).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (d: nat).(let TMP_406 \def (Bind b) in (let 
TMP_407 \def (lift h d u) in (let TMP_408 \def (Bind b) in (let TMP_409 \def 
(s TMP_408 d) in (let TMP_410 \def (S O) in (let TMP_411 \def (lift TMP_410 O 
t3) in (let TMP_412 \def (lift h TMP_409 TMP_411) in (let TMP_413 \def (THead 
TMP_406 TMP_407 TMP_412) in (let TMP_415 \def (\lambda (t: T).(let TMP_414 
\def (lift h d t4) in (pr0 t TMP_414))) in (let TMP_416 \def (S O) in (let 
TMP_417 \def (plus TMP_416 d) in (let TMP_425 \def (\lambda (n: nat).(let 
TMP_418 \def (Bind b) in (let TMP_419 \def (lift h d u) in (let TMP_420 \def 
(S O) in (let TMP_421 \def (lift TMP_420 O t3) in (let TMP_422 \def (lift h n 
TMP_421) in (let TMP_423 \def (THead TMP_418 TMP_419 TMP_422) in (let TMP_424 
\def (lift h d t4) in (pr0 TMP_423 TMP_424))))))))) in (let TMP_426 \def (S 
O) in (let TMP_427 \def (lift h d t3) in (let TMP_428 \def (lift TMP_426 O 
TMP_427) in (let TMP_433 \def (\lambda (t: T).(let TMP_429 \def (Bind b) in 
(let TMP_430 \def (lift h d u) in (let TMP_431 \def (THead TMP_429 TMP_430 t) 
in (let TMP_432 \def (lift h d t4) in (pr0 TMP_431 TMP_432)))))) in (let 
TMP_434 \def (lift h d t3) in (let TMP_435 \def (lift h d t4) in (let TMP_436 
\def (H2 h d) in (let TMP_437 \def (lift h d u) in (let TMP_438 \def 
(pr0_zeta b H0 TMP_434 TMP_435 TMP_436 TMP_437) in (let TMP_439 \def (S O) in 
(let TMP_440 \def (plus TMP_439 d) in (let TMP_441 \def (S O) in (let TMP_442 
\def (lift TMP_441 O t3) in (let TMP_443 \def (lift h TMP_440 TMP_442) in 
(let TMP_444 \def (S O) in (let TMP_445 \def (le_O_n d) in (let TMP_446 \def 
(lift_d t3 h TMP_444 d O TMP_445) in (let TMP_447 \def (eq_ind_r T TMP_428 
TMP_433 TMP_438 TMP_443 TMP_446) in (let TMP_448 \def (S d) in (let TMP_449 
\def (S d) in (let TMP_450 \def (refl_equal nat TMP_449) in (let TMP_451 \def 
(eq_ind nat TMP_417 TMP_425 TMP_447 TMP_448 TMP_450) in (let TMP_452 \def 
(Bind b) in (let TMP_453 \def (S O) in (let TMP_454 \def (lift TMP_453 O t3) 
in (let TMP_455 \def (THead TMP_452 u TMP_454) in (let TMP_456 \def (lift h d 
TMP_455) in (let TMP_457 \def (Bind b) in (let TMP_458 \def (S O) in (let 
TMP_459 \def (lift TMP_458 O t3) in (let TMP_460 \def (lift_head TMP_457 u 
TMP_459 h d) in (eq_ind_r T TMP_413 TMP_415 TMP_451 TMP_456 
TMP_460))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_482 
\def (\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda 
(H1: ((\forall (h: nat).(\forall (d: nat).(pr0 (lift h d t3) (lift h d 
t4)))))).(\lambda (u: T).(\lambda (h: nat).(\lambda (d: nat).(let TMP_462 
\def (Flat Cast) in (let TMP_463 \def (lift h d u) in (let TMP_464 \def (Flat 
Cast) in (let TMP_465 \def (s TMP_464 d) in (let TMP_466 \def (lift h TMP_465 
t3) in (let TMP_467 \def (THead TMP_462 TMP_463 TMP_466) in (let TMP_469 \def 
(\lambda (t: T).(let TMP_468 \def (lift h d t4) in (pr0 t TMP_468))) in (let 
TMP_470 \def (Flat Cast) in (let TMP_471 \def (s TMP_470 d) in (let TMP_472 
\def (lift h TMP_471 t3) in (let TMP_473 \def (lift h d t4) in (let TMP_474 
\def (H1 h d) in (let TMP_475 \def (lift h d u) in (let TMP_476 \def (pr0_tau 
TMP_472 TMP_473 TMP_474 TMP_475) in (let TMP_477 \def (Flat Cast) in (let 
TMP_478 \def (THead TMP_477 u t3) in (let TMP_479 \def (lift h d TMP_478) in 
(let TMP_480 \def (Flat Cast) in (let TMP_481 \def (lift_head TMP_480 u t3 h 
d) in (eq_ind_r T TMP_467 TMP_469 TMP_476 TMP_479 
TMP_481))))))))))))))))))))))))))) in (pr0_ind TMP_3 TMP_5 TMP_39 TMP_132 
TMP_339 TMP_405 TMP_461 TMP_482 t1 t2 H))))))))))).

theorem pr0_gen_abbr:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abbr) u1 t1) x)).(let TMP_1 \def (Bind Abbr) in (let TMP_2 \def (THead 
TMP_1 u1 t1) in (let TMP_3 \def (\lambda (t: T).(pr0 t x)) in (let TMP_17 
\def (\lambda (_: T).(let TMP_6 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_4 \def (Bind Abbr) in (let TMP_5 \def (THead TMP_4 u2 t2) in (eq T x 
TMP_5))))) in (let TMP_7 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
in (let TMP_12 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_8 \def (pr0 t1 
t2) in (let TMP_9 \def (\lambda (y: T).(pr0 t1 y)) in (let TMP_10 \def 
(\lambda (y: T).(subst0 O u2 y t2)) in (let TMP_11 \def (ex2 T TMP_9 TMP_10) 
in (or TMP_8 TMP_11))))))) in (let TMP_13 \def (ex3_2 T T TMP_6 TMP_7 TMP_12) 
in (let TMP_14 \def (S O) in (let TMP_15 \def (lift TMP_14 O x) in (let 
TMP_16 \def (pr0 t1 TMP_15) in (or TMP_13 TMP_16))))))))) in (let TMP_448 
\def (\lambda (y: T).(\lambda (H0: (pr0 y x)).(let TMP_31 \def (\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (let TMP_20 \def 
(\lambda (u2: T).(\lambda (t2: T).(let TMP_18 \def (Bind Abbr) in (let TMP_19 
\def (THead TMP_18 u2 t2) in (eq T t0 TMP_19))))) in (let TMP_21 \def 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_26 \def (\lambda 
(u2: T).(\lambda (t2: T).(let TMP_22 \def (pr0 t1 t2) in (let TMP_23 \def 
(\lambda (y0: T).(pr0 t1 y0)) in (let TMP_24 \def (\lambda (y0: T).(subst0 O 
u2 y0 t2)) in (let TMP_25 \def (ex2 T TMP_23 TMP_24) in (or TMP_22 
TMP_25))))))) in (let TMP_27 \def (ex3_2 T T TMP_20 TMP_21 TMP_26) in (let 
TMP_28 \def (S O) in (let TMP_29 \def (lift TMP_28 O t0) in (let TMP_30 \def 
(pr0 t1 TMP_29) in (or TMP_27 TMP_30))))))))))) in (let TMP_91 \def (\lambda 
(t: T).(\lambda (H1: (eq T t (THead (Bind Abbr) u1 t1))).(let TMP_32 \def 
(\lambda (e: T).e) in (let TMP_33 \def (Bind Abbr) in (let TMP_34 \def (THead 
TMP_33 u1 t1) in (let H2 \def (f_equal T T TMP_32 t TMP_34 H1) in (let TMP_35 
\def (Bind Abbr) in (let TMP_36 \def (THead TMP_35 u1 t1) in (let TMP_50 \def 
(\lambda (t0: T).(let TMP_39 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_37 \def (Bind Abbr) in (let TMP_38 \def (THead TMP_37 u2 t2) in (eq T t0 
TMP_38))))) in (let TMP_40 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_45 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_41 \def 
(pr0 t1 t2) in (let TMP_42 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_43 
\def (\lambda (y0: T).(subst0 O u2 y0 t2)) in (let TMP_44 \def (ex2 T TMP_42 
TMP_43) in (or TMP_41 TMP_44))))))) in (let TMP_46 \def (ex3_2 T T TMP_39 
TMP_40 TMP_45) in (let TMP_47 \def (S O) in (let TMP_48 \def (lift TMP_47 O 
t0) in (let TMP_49 \def (pr0 t1 TMP_48) in (or TMP_46 TMP_49))))))))) in (let 
TMP_55 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_51 \def (Bind Abbr) in 
(let TMP_52 \def (THead TMP_51 u1 t1) in (let TMP_53 \def (Bind Abbr) in (let 
TMP_54 \def (THead TMP_53 u2 t2) in (eq T TMP_52 TMP_54))))))) in (let TMP_56 
\def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_61 \def 
(\lambda (u2: T).(\lambda (t2: T).(let TMP_57 \def (pr0 t1 t2) in (let TMP_58 
\def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_59 \def (\lambda (y0: 
T).(subst0 O u2 y0 t2)) in (let TMP_60 \def (ex2 T TMP_58 TMP_59) in (or 
TMP_57 TMP_60))))))) in (let TMP_62 \def (ex3_2 T T TMP_55 TMP_56 TMP_61) in 
(let TMP_63 \def (S O) in (let TMP_64 \def (Bind Abbr) in (let TMP_65 \def 
(THead TMP_64 u1 t1) in (let TMP_66 \def (lift TMP_63 O TMP_65) in (let 
TMP_67 \def (pr0 t1 TMP_66) in (let TMP_72 \def (\lambda (u2: T).(\lambda 
(t2: T).(let TMP_68 \def (Bind Abbr) in (let TMP_69 \def (THead TMP_68 u1 t1) 
in (let TMP_70 \def (Bind Abbr) in (let TMP_71 \def (THead TMP_70 u2 t2) in 
(eq T TMP_69 TMP_71))))))) in (let TMP_73 \def (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) in (let TMP_78 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_74 \def (pr0 t1 t2) in (let TMP_75 \def (\lambda (y0: T).(pr0 t1 y0)) in 
(let TMP_76 \def (\lambda (y0: T).(subst0 O u2 y0 t2)) in (let TMP_77 \def 
(ex2 T TMP_75 TMP_76) in (or TMP_74 TMP_77))))))) in (let TMP_79 \def (Bind 
Abbr) in (let TMP_80 \def (THead TMP_79 u1 t1) in (let TMP_81 \def 
(refl_equal T TMP_80) in (let TMP_82 \def (pr0_refl u1) in (let TMP_83 \def 
(pr0 t1 t1) in (let TMP_84 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_85 
\def (\lambda (y0: T).(subst0 O u1 y0 t1)) in (let TMP_86 \def (ex2 T TMP_84 
TMP_85) in (let TMP_87 \def (pr0_refl t1) in (let TMP_88 \def (or_introl 
TMP_83 TMP_86 TMP_87) in (let TMP_89 \def (ex3_2_intro T T TMP_72 TMP_73 
TMP_78 u1 t1 TMP_81 TMP_82 TMP_88) in (let TMP_90 \def (or_introl TMP_62 
TMP_67 TMP_89) in (eq_ind_r T TMP_36 TMP_50 TMP_90 t 
H2)))))))))))))))))))))))))))))))))) in (let TMP_191 \def (\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 
(THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 
t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: 
(pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u0 t0) (THead (Bind 
Abbr) u1 t1))).(let TMP_92 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) in 
(let TMP_93 \def (THead k u0 t0) in (let TMP_94 \def (Bind Abbr) in (let 
TMP_95 \def (THead TMP_94 u1 t1) in (let H6 \def (f_equal T K TMP_92 TMP_93 
TMP_95 H5) in (let TMP_96 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) in 
(let TMP_97 \def (THead k u0 t0) in (let TMP_98 \def (Bind Abbr) in (let 
TMP_99 \def (THead TMP_98 u1 t1) in (let H7 \def (f_equal T T TMP_96 TMP_97 
TMP_99 H5) in (let TMP_100 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) in 
(let TMP_101 \def (THead k u0 t0) in (let TMP_102 \def (Bind Abbr) in (let 
TMP_103 \def (THead TMP_102 u1 t1) in (let H8 \def (f_equal T T TMP_100 
TMP_101 TMP_103 H5) in (let TMP_189 \def (\lambda (H9: (eq T u0 u1)).(\lambda 
(H10: (eq K k (Bind Abbr))).(let TMP_104 \def (Bind Abbr) in (let TMP_120 
\def (\lambda (k0: K).(let TMP_108 \def (\lambda (u3: T).(\lambda (t3: 
T).(let TMP_105 \def (THead k0 u2 t2) in (let TMP_106 \def (Bind Abbr) in 
(let TMP_107 \def (THead TMP_106 u3 t3) in (eq T TMP_105 TMP_107)))))) in 
(let TMP_109 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_114 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_110 \def (pr0 t1 t3) 
in (let TMP_111 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_112 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_113 \def (ex2 T TMP_111 
TMP_112) in (or TMP_110 TMP_113))))))) in (let TMP_115 \def (ex3_2 T T 
TMP_108 TMP_109 TMP_114) in (let TMP_116 \def (S O) in (let TMP_117 \def 
(THead k0 u2 t2) in (let TMP_118 \def (lift TMP_116 O TMP_117) in (let 
TMP_119 \def (pr0 t1 TMP_118) in (or TMP_115 TMP_119)))))))))) in (let 
TMP_134 \def (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (let 
TMP_123 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_121 \def (Bind Abbr) 
in (let TMP_122 \def (THead TMP_121 u3 t3) in (eq T t2 TMP_122))))) in (let 
TMP_124 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_129 
\def (\lambda (u3: T).(\lambda (t3: T).(let TMP_125 \def (pr0 t1 t3) in (let 
TMP_126 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_127 \def (\lambda (y0: 
T).(subst0 O u3 y0 t3)) in (let TMP_128 \def (ex2 T TMP_126 TMP_127) in (or 
TMP_125 TMP_128))))))) in (let TMP_130 \def (ex3_2 T T TMP_123 TMP_124 
TMP_129) in (let TMP_131 \def (S O) in (let TMP_132 \def (lift TMP_131 O t2) 
in (let TMP_133 \def (pr0 t1 TMP_132) in (or TMP_130 TMP_133)))))))))) in 
(let H11 \def (eq_ind T t0 TMP_134 H4 t1 H8) in (let TMP_135 \def (\lambda 
(t: T).(pr0 t t2)) in (let H12 \def (eq_ind T t0 TMP_135 H3 t1 H8) in (let 
TMP_149 \def (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (let 
TMP_138 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_136 \def (Bind Abbr) 
in (let TMP_137 \def (THead TMP_136 u3 t3) in (eq T u2 TMP_137))))) in (let 
TMP_139 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_144 
\def (\lambda (u3: T).(\lambda (t3: T).(let TMP_140 \def (pr0 t1 t3) in (let 
TMP_141 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_142 \def (\lambda (y0: 
T).(subst0 O u3 y0 t3)) in (let TMP_143 \def (ex2 T TMP_141 TMP_142) in (or 
TMP_140 TMP_143))))))) in (let TMP_145 \def (ex3_2 T T TMP_138 TMP_139 
TMP_144) in (let TMP_146 \def (S O) in (let TMP_147 \def (lift TMP_146 O u2) 
in (let TMP_148 \def (pr0 t1 TMP_147) in (or TMP_145 TMP_148)))))))))) in 
(let H13 \def (eq_ind T u0 TMP_149 H2 u1 H9) in (let TMP_150 \def (\lambda 
(t: T).(pr0 t u2)) in (let H14 \def (eq_ind T u0 TMP_150 H1 u1 H9) in (let 
TMP_155 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_151 \def (Bind Abbr) 
in (let TMP_152 \def (THead TMP_151 u2 t2) in (let TMP_153 \def (Bind Abbr) 
in (let TMP_154 \def (THead TMP_153 u3 t3) in (eq T TMP_152 TMP_154))))))) in 
(let TMP_156 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_161 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_157 \def (pr0 t1 t3) 
in (let TMP_158 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_159 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_160 \def (ex2 T TMP_158 
TMP_159) in (or TMP_157 TMP_160))))))) in (let TMP_162 \def (ex3_2 T T 
TMP_155 TMP_156 TMP_161) in (let TMP_163 \def (S O) in (let TMP_164 \def 
(Bind Abbr) in (let TMP_165 \def (THead TMP_164 u2 t2) in (let TMP_166 \def 
(lift TMP_163 O TMP_165) in (let TMP_167 \def (pr0 t1 TMP_166) in (let 
TMP_172 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_168 \def (Bind Abbr) 
in (let TMP_169 \def (THead TMP_168 u2 t2) in (let TMP_170 \def (Bind Abbr) 
in (let TMP_171 \def (THead TMP_170 u3 t3) in (eq T TMP_169 TMP_171))))))) in 
(let TMP_173 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_178 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_174 \def (pr0 t1 t3) 
in (let TMP_175 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_176 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_177 \def (ex2 T TMP_175 
TMP_176) in (or TMP_174 TMP_177))))))) in (let TMP_179 \def (Bind Abbr) in 
(let TMP_180 \def (THead TMP_179 u2 t2) in (let TMP_181 \def (refl_equal T 
TMP_180) in (let TMP_182 \def (pr0 t1 t2) in (let TMP_183 \def (\lambda (y0: 
T).(pr0 t1 y0)) in (let TMP_184 \def (\lambda (y0: T).(subst0 O u2 y0 t2)) in 
(let TMP_185 \def (ex2 T TMP_183 TMP_184) in (let TMP_186 \def (or_introl 
TMP_182 TMP_185 H12) in (let TMP_187 \def (ex3_2_intro T T TMP_172 TMP_173 
TMP_178 u2 t2 TMP_181 H14 TMP_186) in (let TMP_188 \def (or_introl TMP_162 
TMP_167 TMP_187) in (eq_ind_r K TMP_104 TMP_120 TMP_188 k 
H10))))))))))))))))))))))))))))))))))) in (let TMP_190 \def (TMP_189 H7) in 
(TMP_190 H6)))))))))))))))))))))))))))) in (let TMP_217 \def (\lambda (u: 
T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: 
(((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t2))))))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 
t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) 
(THead (Bind Abbr) u1 t1))).(let TMP_192 \def (Flat Appl) in (let TMP_193 
\def (Bind Abst) in (let TMP_194 \def (THead TMP_193 u t0) in (let TMP_195 
\def (THead TMP_192 v1 TMP_194) in (let TMP_196 \def (\lambda (ee: T).(match 
ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k 
_ _) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) in (let TMP_197 \def (Bind Abbr) in (let TMP_198 \def 
(THead TMP_197 u1 t1) in (let H6 \def (eq_ind T TMP_195 TMP_196 I TMP_198 H5) 
in (let TMP_203 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_199 \def 
(Bind Abbr) in (let TMP_200 \def (THead TMP_199 v2 t2) in (let TMP_201 \def 
(Bind Abbr) in (let TMP_202 \def (THead TMP_201 u2 t3) in (eq T TMP_200 
TMP_202))))))) in (let TMP_204 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_209 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_205 
\def (pr0 t1 t3) in (let TMP_206 \def (\lambda (y0: T).(pr0 t1 y0)) in (let 
TMP_207 \def (\lambda (y0: T).(subst0 O u2 y0 t3)) in (let TMP_208 \def (ex2 
T TMP_206 TMP_207) in (or TMP_205 TMP_208))))))) in (let TMP_210 \def (ex3_2 
T T TMP_203 TMP_204 TMP_209) in (let TMP_211 \def (S O) in (let TMP_212 \def 
(Bind Abbr) in (let TMP_213 \def (THead TMP_212 v2 t2) in (let TMP_214 \def 
(lift TMP_211 O TMP_213) in (let TMP_215 \def (pr0 t1 TMP_214) in (let 
TMP_216 \def (or TMP_210 TMP_215) in (False_ind TMP_216 
H6))))))))))))))))))))))))))))) in (let TMP_251 \def (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead 
(Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 t1 (lift (S 
O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq 
T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Bind Abbr) u1 
t1))).(let TMP_218 \def (Flat Appl) in (let TMP_219 \def (Bind b) in (let 
TMP_220 \def (THead TMP_219 u0 t0) in (let TMP_221 \def (THead TMP_218 v1 
TMP_220) in (let TMP_222 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) in 
(let TMP_223 \def (Bind Abbr) in (let TMP_224 \def (THead TMP_223 u1 t1) in 
(let H9 \def (eq_ind T TMP_221 TMP_222 I TMP_224 H8) in (let TMP_233 \def 
(\lambda (u3: T).(\lambda (t3: T).(let TMP_225 \def (Bind b) in (let TMP_226 
\def (Flat Appl) in (let TMP_227 \def (S O) in (let TMP_228 \def (lift 
TMP_227 O v2) in (let TMP_229 \def (THead TMP_226 TMP_228 t2) in (let TMP_230 
\def (THead TMP_225 u2 TMP_229) in (let TMP_231 \def (Bind Abbr) in (let 
TMP_232 \def (THead TMP_231 u3 t3) in (eq T TMP_230 TMP_232))))))))))) in 
(let TMP_234 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_239 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_235 \def (pr0 t1 t3) 
in (let TMP_236 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_237 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_238 \def (ex2 T TMP_236 
TMP_237) in (or TMP_235 TMP_238))))))) in (let TMP_240 \def (ex3_2 T T 
TMP_233 TMP_234 TMP_239) in (let TMP_241 \def (S O) in (let TMP_242 \def 
(Bind b) in (let TMP_243 \def (Flat Appl) in (let TMP_244 \def (S O) in (let 
TMP_245 \def (lift TMP_244 O v2) in (let TMP_246 \def (THead TMP_243 TMP_245 
t2) in (let TMP_247 \def (THead TMP_242 u2 TMP_246) in (let TMP_248 \def 
(lift TMP_241 O TMP_247) in (let TMP_249 \def (pr0 t1 TMP_248) in (let 
TMP_250 \def (or TMP_240 TMP_249) in (False_ind TMP_250 
H9)))))))))))))))))))))))))))))))))))))) in (let TMP_333 \def (\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 
(THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 
t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: 
(pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (w: T).(\lambda (H5: (subst0 O u2 t2 w)).(\lambda (H6: (eq 
T (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1))).(let TMP_252 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) in (let TMP_253 \def (Bind 
Abbr) in (let TMP_254 \def (THead TMP_253 u0 t0) in (let TMP_255 \def (Bind 
Abbr) in (let TMP_256 \def (THead TMP_255 u1 t1) in (let H7 \def (f_equal T T 
TMP_252 TMP_254 TMP_256 H6) in (let TMP_257 \def (\lambda (e: T).(match e 
with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) in (let TMP_258 \def (Bind Abbr) in (let TMP_259 \def (THead 
TMP_258 u0 t0) in (let TMP_260 \def (Bind Abbr) in (let TMP_261 \def (THead 
TMP_260 u1 t1) in (let H8 \def (f_equal T T TMP_257 TMP_259 TMP_261 H6) in 
(let TMP_332 \def (\lambda (H9: (eq T u0 u1)).(let TMP_275 \def (\lambda (t: 
T).((eq T t (THead (Bind Abbr) u1 t1)) \to (let TMP_264 \def (\lambda (u3: 
T).(\lambda (t3: T).(let TMP_262 \def (Bind Abbr) in (let TMP_263 \def (THead 
TMP_262 u3 t3) in (eq T t2 TMP_263))))) in (let TMP_265 \def (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_270 \def (\lambda (u3: 
T).(\lambda (t3: T).(let TMP_266 \def (pr0 t1 t3) in (let TMP_267 \def 
(\lambda (y0: T).(pr0 t1 y0)) in (let TMP_268 \def (\lambda (y0: T).(subst0 O 
u3 y0 t3)) in (let TMP_269 \def (ex2 T TMP_267 TMP_268) in (or TMP_266 
TMP_269))))))) in (let TMP_271 \def (ex3_2 T T TMP_264 TMP_265 TMP_270) in 
(let TMP_272 \def (S O) in (let TMP_273 \def (lift TMP_272 O t2) in (let 
TMP_274 \def (pr0 t1 TMP_273) in (or TMP_271 TMP_274)))))))))) in (let H10 
\def (eq_ind T t0 TMP_275 H4 t1 H8) in (let TMP_276 \def (\lambda (t: T).(pr0 
t t2)) in (let H11 \def (eq_ind T t0 TMP_276 H3 t1 H8) in (let TMP_290 \def 
(\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (let TMP_279 \def 
(\lambda (u3: T).(\lambda (t3: T).(let TMP_277 \def (Bind Abbr) in (let 
TMP_278 \def (THead TMP_277 u3 t3) in (eq T u2 TMP_278))))) in (let TMP_280 
\def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_285 \def 
(\lambda (u3: T).(\lambda (t3: T).(let TMP_281 \def (pr0 t1 t3) in (let 
TMP_282 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_283 \def (\lambda (y0: 
T).(subst0 O u3 y0 t3)) in (let TMP_284 \def (ex2 T TMP_282 TMP_283) in (or 
TMP_281 TMP_284))))))) in (let TMP_286 \def (ex3_2 T T TMP_279 TMP_280 
TMP_285) in (let TMP_287 \def (S O) in (let TMP_288 \def (lift TMP_287 O u2) 
in (let TMP_289 \def (pr0 t1 TMP_288) in (or TMP_286 TMP_289)))))))))) in 
(let H12 \def (eq_ind T u0 TMP_290 H2 u1 H9) in (let TMP_291 \def (\lambda 
(t: T).(pr0 t u2)) in (let H13 \def (eq_ind T u0 TMP_291 H1 u1 H9) in (let 
TMP_296 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_292 \def (Bind Abbr) 
in (let TMP_293 \def (THead TMP_292 u2 w) in (let TMP_294 \def (Bind Abbr) in 
(let TMP_295 \def (THead TMP_294 u3 t3) in (eq T TMP_293 TMP_295))))))) in 
(let TMP_297 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_302 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_298 \def (pr0 t1 t3) 
in (let TMP_299 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_300 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_301 \def (ex2 T TMP_299 
TMP_300) in (or TMP_298 TMP_301))))))) in (let TMP_303 \def (ex3_2 T T 
TMP_296 TMP_297 TMP_302) in (let TMP_304 \def (S O) in (let TMP_305 \def 
(Bind Abbr) in (let TMP_306 \def (THead TMP_305 u2 w) in (let TMP_307 \def 
(lift TMP_304 O TMP_306) in (let TMP_308 \def (pr0 t1 TMP_307) in (let 
TMP_313 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_309 \def (Bind Abbr) 
in (let TMP_310 \def (THead TMP_309 u2 w) in (let TMP_311 \def (Bind Abbr) in 
(let TMP_312 \def (THead TMP_311 u3 t3) in (eq T TMP_310 TMP_312))))))) in 
(let TMP_314 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_319 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_315 \def (pr0 t1 t3) 
in (let TMP_316 \def (\lambda (y0: T).(pr0 t1 y0)) in (let TMP_317 \def 
(\lambda (y0: T).(subst0 O u3 y0 t3)) in (let TMP_318 \def (ex2 T TMP_316 
TMP_317) in (or TMP_315 TMP_318))))))) in (let TMP_320 \def (Bind Abbr) in 
(let TMP_321 \def (THead TMP_320 u2 w) in (let TMP_322 \def (refl_equal T 
TMP_321) in (let TMP_323 \def (pr0 t1 w) in (let TMP_324 \def (\lambda (y0: 
T).(pr0 t1 y0)) in (let TMP_325 \def (\lambda (y0: T).(subst0 O u2 y0 w)) in 
(let TMP_326 \def (ex2 T TMP_324 TMP_325) in (let TMP_327 \def (\lambda (y0: 
T).(pr0 t1 y0)) in (let TMP_328 \def (\lambda (y0: T).(subst0 O u2 y0 w)) in 
(let TMP_329 \def (ex_intro2 T TMP_327 TMP_328 t2 H11 H5) in (let TMP_330 
\def (or_intror TMP_323 TMP_326 TMP_329) in (let TMP_331 \def (ex3_2_intro T 
T TMP_313 TMP_314 TMP_319 u2 w TMP_322 H13 TMP_330) in (or_introl TMP_303 
TMP_308 TMP_331)))))))))))))))))))))))))))))))))) in (TMP_332 
H7))))))))))))))))))))))))) in (let TMP_427 \def (\lambda (b: B).(\lambda 
(H1: (not (eq B b Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: 
(pr0 t0 t2)).(\lambda (H3: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (u: T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O 
t0)) (THead (Bind Abbr) u1 t1))).(let TMP_334 \def (\lambda (e: T).(match e 
with [(TSort _) \Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) 
\Rightarrow (match k with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) in (let TMP_335 \def (Bind b) in (let TMP_336 \def (S O) in (let 
TMP_337 \def (lift TMP_336 O t0) in (let TMP_338 \def (THead TMP_335 u 
TMP_337) in (let TMP_339 \def (Bind Abbr) in (let TMP_340 \def (THead TMP_339 
u1 t1) in (let H5 \def (f_equal T B TMP_334 TMP_338 TMP_340 H4) in (let 
TMP_341 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow u | (TLRef 
_) \Rightarrow u | (THead _ t _) \Rightarrow t])) in (let TMP_342 \def (Bind 
b) in (let TMP_343 \def (S O) in (let TMP_344 \def (lift TMP_343 O t0) in 
(let TMP_345 \def (THead TMP_342 u TMP_344) in (let TMP_346 \def (Bind Abbr) 
in (let TMP_347 \def (THead TMP_346 u1 t1) in (let H6 \def (f_equal T T 
TMP_341 TMP_345 TMP_347 H4) in (let TMP_362 \def (\lambda (e: T).(match e 
with [(TSort _) \Rightarrow (let TMP_361 \def (\lambda (x0: nat).(let TMP_360 
\def (S O) in (plus x0 TMP_360))) in (lref_map TMP_361 O t0)) | (TLRef _) 
\Rightarrow (let TMP_354 \def (\lambda (x0: nat).(let TMP_353 \def (S O) in 
(plus x0 TMP_353))) in (lref_map TMP_354 O t0)) | (THead _ _ t) \Rightarrow 
t])) in (let TMP_363 \def (Bind b) in (let TMP_364 \def (S O) in (let TMP_365 
\def (lift TMP_364 O t0) in (let TMP_366 \def (THead TMP_363 u TMP_365) in 
(let TMP_367 \def (Bind Abbr) in (let TMP_368 \def (THead TMP_367 u1 t1) in 
(let H7 \def (f_equal T T TMP_362 TMP_366 TMP_368 H4) in (let TMP_425 \def 
(\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b Abbr)).(let TMP_370 \def 
(\lambda (b0: B).(let TMP_369 \def (eq B b0 Abst) in (not TMP_369))) in (let 
H10 \def (eq_ind B b TMP_370 H1 Abbr H9) in (let TMP_384 \def (\lambda (t: 
T).((eq T t0 (THead (Bind Abbr) u1 t)) \to (let TMP_373 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_371 \def (Bind Abbr) in (let TMP_372 \def (THead 
TMP_371 u2 t3) in (eq T t2 TMP_372))))) in (let TMP_374 \def (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_379 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_375 \def (pr0 t t3) in (let TMP_376 \def 
(\lambda (y0: T).(pr0 t y0)) in (let TMP_377 \def (\lambda (y0: T).(subst0 O 
u2 y0 t3)) in (let TMP_378 \def (ex2 T TMP_376 TMP_377) in (or TMP_375 
TMP_378))))))) in (let TMP_380 \def (ex3_2 T T TMP_373 TMP_374 TMP_379) in 
(let TMP_381 \def (S O) in (let TMP_382 \def (lift TMP_381 O t2) in (let 
TMP_383 \def (pr0 t TMP_382) in (or TMP_380 TMP_383)))))))))) in (let TMP_385 
\def (S O) in (let TMP_386 \def (lift TMP_385 O t0) in (let H11 \def 
(eq_ind_r T t1 TMP_384 H3 TMP_386 H7) in (let TMP_387 \def (S O) in (let 
TMP_388 \def (lift TMP_387 O t0) in (let TMP_402 \def (\lambda (t: T).(let 
TMP_391 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_389 \def (Bind Abbr) 
in (let TMP_390 \def (THead TMP_389 u2 t3) in (eq T t2 TMP_390))))) in (let 
TMP_392 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_397 
\def (\lambda (u2: T).(\lambda (t3: T).(let TMP_393 \def (pr0 t t3) in (let 
TMP_394 \def (\lambda (y0: T).(pr0 t y0)) in (let TMP_395 \def (\lambda (y0: 
T).(subst0 O u2 y0 t3)) in (let TMP_396 \def (ex2 T TMP_394 TMP_395) in (or 
TMP_393 TMP_396))))))) in (let TMP_398 \def (ex3_2 T T TMP_391 TMP_392 
TMP_397) in (let TMP_399 \def (S O) in (let TMP_400 \def (lift TMP_399 O t2) 
in (let TMP_401 \def (pr0 t TMP_400) in (or TMP_398 TMP_401))))))))) in (let 
TMP_405 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_403 \def (Bind Abbr) 
in (let TMP_404 \def (THead TMP_403 u2 t3) in (eq T t2 TMP_404))))) in (let 
TMP_406 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_415 
\def (\lambda (u2: T).(\lambda (t3: T).(let TMP_407 \def (S O) in (let 
TMP_408 \def (lift TMP_407 O t0) in (let TMP_409 \def (pr0 TMP_408 t3) in 
(let TMP_412 \def (\lambda (y0: T).(let TMP_410 \def (S O) in (let TMP_411 
\def (lift TMP_410 O t0) in (pr0 TMP_411 y0)))) in (let TMP_413 \def (\lambda 
(y0: T).(subst0 O u2 y0 t3)) in (let TMP_414 \def (ex2 T TMP_412 TMP_413) in 
(or TMP_409 TMP_414))))))))) in (let TMP_416 \def (ex3_2 T T TMP_405 TMP_406 
TMP_415) in (let TMP_417 \def (S O) in (let TMP_418 \def (lift TMP_417 O t0) 
in (let TMP_419 \def (S O) in (let TMP_420 \def (lift TMP_419 O t2) in (let 
TMP_421 \def (pr0 TMP_418 TMP_420) in (let TMP_422 \def (S O) in (let TMP_423 
\def (pr0_lift t0 t2 H2 TMP_422 O) in (let TMP_424 \def (or_intror TMP_416 
TMP_421 TMP_423) in (eq_ind T TMP_388 TMP_402 TMP_424 t1 
H7)))))))))))))))))))))))) in (let TMP_426 \def (TMP_425 H6) in (TMP_426 
H5))))))))))))))))))))))))))))))))))) in (let TMP_447 \def (\lambda (t0: 
T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead 
(Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S 
O) O t2)))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t0) 
(THead (Bind Abbr) u1 t1))).(let TMP_428 \def (Flat Cast) in (let TMP_429 
\def (THead TMP_428 u t0) in (let TMP_430 \def (\lambda (ee: T).(match ee 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ 
_) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) in (let TMP_431 \def (Bind Abbr) in (let TMP_432 \def 
(THead TMP_431 u1 t1) in (let H4 \def (eq_ind T TMP_429 TMP_430 I TMP_432 H3) 
in (let TMP_435 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_433 \def 
(Bind Abbr) in (let TMP_434 \def (THead TMP_433 u2 t3) in (eq T t2 
TMP_434))))) in (let TMP_436 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_441 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_437 
\def (pr0 t1 t3) in (let TMP_438 \def (\lambda (y0: T).(pr0 t1 y0)) in (let 
TMP_439 \def (\lambda (y0: T).(subst0 O u2 y0 t3)) in (let TMP_440 \def (ex2 
T TMP_438 TMP_439) in (or TMP_437 TMP_440))))))) in (let TMP_442 \def (ex3_2 
T T TMP_435 TMP_436 TMP_441) in (let TMP_443 \def (S O) in (let TMP_444 \def 
(lift TMP_443 O t2) in (let TMP_445 \def (pr0 t1 TMP_444) in (let TMP_446 
\def (or TMP_442 TMP_445) in (False_ind TMP_446 H4))))))))))))))))))))) in 
(pr0_ind TMP_31 TMP_91 TMP_191 TMP_217 TMP_251 TMP_333 TMP_427 TMP_447 y x 
H0))))))))))) in (insert_eq T TMP_2 TMP_3 TMP_17 TMP_448 H))))))))).

theorem pr0_gen_void:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Void) u1 t1) x)).(let TMP_1 \def (Bind Void) in (let TMP_2 \def (THead 
TMP_1 u1 t1) in (let TMP_3 \def (\lambda (t: T).(pr0 t x)) in (let TMP_13 
\def (\lambda (_: T).(let TMP_6 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_4 \def (Bind Void) in (let TMP_5 \def (THead TMP_4 u2 t2) in (eq T x 
TMP_5))))) in (let TMP_7 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
in (let TMP_8 \def (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) in (let 
TMP_9 \def (ex3_2 T T TMP_6 TMP_7 TMP_8) in (let TMP_10 \def (S O) in (let 
TMP_11 \def (lift TMP_10 O x) in (let TMP_12 \def (pr0 t1 TMP_11) in (or 
TMP_9 TMP_12))))))))) in (let TMP_310 \def (\lambda (y: T).(\lambda (H0: (pr0 
y x)).(let TMP_23 \def (\lambda (t: T).(\lambda (t0: T).((eq T t (THead (Bind 
Void) u1 t1)) \to (let TMP_16 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_14 \def (Bind Void) in (let TMP_15 \def (THead TMP_14 u2 t2) in (eq T t0 
TMP_15))))) in (let TMP_17 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_18 \def (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) in 
(let TMP_19 \def (ex3_2 T T TMP_16 TMP_17 TMP_18) in (let TMP_20 \def (S O) 
in (let TMP_21 \def (lift TMP_20 O t0) in (let TMP_22 \def (pr0 t1 TMP_21) in 
(or TMP_19 TMP_22))))))))))) in (let TMP_66 \def (\lambda (t: T).(\lambda 
(H1: (eq T t (THead (Bind Void) u1 t1))).(let TMP_24 \def (\lambda (e: T).e) 
in (let TMP_25 \def (Bind Void) in (let TMP_26 \def (THead TMP_25 u1 t1) in 
(let H2 \def (f_equal T T TMP_24 t TMP_26 H1) in (let TMP_27 \def (Bind Void) 
in (let TMP_28 \def (THead TMP_27 u1 t1) in (let TMP_38 \def (\lambda (t0: 
T).(let TMP_31 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_29 \def (Bind 
Void) in (let TMP_30 \def (THead TMP_29 u2 t2) in (eq T t0 TMP_30))))) in 
(let TMP_32 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let 
TMP_33 \def (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) in (let TMP_34 
\def (ex3_2 T T TMP_31 TMP_32 TMP_33) in (let TMP_35 \def (S O) in (let 
TMP_36 \def (lift TMP_35 O t0) in (let TMP_37 \def (pr0 t1 TMP_36) in (or 
TMP_34 TMP_37))))))))) in (let TMP_43 \def (\lambda (u2: T).(\lambda (t2: 
T).(let TMP_39 \def (Bind Void) in (let TMP_40 \def (THead TMP_39 u1 t1) in 
(let TMP_41 \def (Bind Void) in (let TMP_42 \def (THead TMP_41 u2 t2) in (eq 
T TMP_40 TMP_42))))))) in (let TMP_44 \def (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) in (let TMP_45 \def (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2))) in (let TMP_46 \def (ex3_2 T T TMP_43 TMP_44 TMP_45) in (let TMP_47 
\def (S O) in (let TMP_48 \def (Bind Void) in (let TMP_49 \def (THead TMP_48 
u1 t1) in (let TMP_50 \def (lift TMP_47 O TMP_49) in (let TMP_51 \def (pr0 t1 
TMP_50) in (let TMP_56 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_52 
\def (Bind Void) in (let TMP_53 \def (THead TMP_52 u1 t1) in (let TMP_54 \def 
(Bind Void) in (let TMP_55 \def (THead TMP_54 u2 t2) in (eq T TMP_53 
TMP_55))))))) in (let TMP_57 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_58 \def (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) in 
(let TMP_59 \def (Bind Void) in (let TMP_60 \def (THead TMP_59 u1 t1) in (let 
TMP_61 \def (refl_equal T TMP_60) in (let TMP_62 \def (pr0_refl u1) in (let 
TMP_63 \def (pr0_refl t1) in (let TMP_64 \def (ex3_2_intro T T TMP_56 TMP_57 
TMP_58 u1 t1 TMP_61 TMP_62 TMP_63) in (let TMP_65 \def (or_introl TMP_46 
TMP_51 TMP_64) in (eq_ind_r T TMP_28 TMP_38 TMP_65 t 
H2))))))))))))))))))))))))))))) in (let TMP_141 \def (\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 
(THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: (pr0 
t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T 
T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (k: K).(\lambda 
(H5: (eq T (THead k u0 t0) (THead (Bind Void) u1 t1))).(let TMP_67 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) in (let TMP_68 \def (THead k 
u0 t0) in (let TMP_69 \def (Bind Void) in (let TMP_70 \def (THead TMP_69 u1 
t1) in (let H6 \def (f_equal T K TMP_67 TMP_68 TMP_70 H5) in (let TMP_71 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) in (let TMP_72 \def (THead k 
u0 t0) in (let TMP_73 \def (Bind Void) in (let TMP_74 \def (THead TMP_73 u1 
t1) in (let H7 \def (f_equal T T TMP_71 TMP_72 TMP_74 H5) in (let TMP_75 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) in (let TMP_76 \def (THead k 
u0 t0) in (let TMP_77 \def (Bind Void) in (let TMP_78 \def (THead TMP_77 u1 
t1) in (let H8 \def (f_equal T T TMP_75 TMP_76 TMP_78 H5) in (let TMP_139 
\def (\lambda (H9: (eq T u0 u1)).(\lambda (H10: (eq K k (Bind Void))).(let 
TMP_79 \def (Bind Void) in (let TMP_91 \def (\lambda (k0: K).(let TMP_83 \def 
(\lambda (u3: T).(\lambda (t3: T).(let TMP_80 \def (THead k0 u2 t2) in (let 
TMP_81 \def (Bind Void) in (let TMP_82 \def (THead TMP_81 u3 t3) in (eq T 
TMP_80 TMP_82)))))) in (let TMP_84 \def (\lambda (u3: T).(\lambda (_: T).(pr0 
u1 u3))) in (let TMP_85 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) 
in (let TMP_86 \def (ex3_2 T T TMP_83 TMP_84 TMP_85) in (let TMP_87 \def (S 
O) in (let TMP_88 \def (THead k0 u2 t2) in (let TMP_89 \def (lift TMP_87 O 
TMP_88) in (let TMP_90 \def (pr0 t1 TMP_89) in (or TMP_86 TMP_90)))))))))) in 
(let TMP_101 \def (\lambda (t: T).((eq T t (THead (Bind Void) u1 t1)) \to 
(let TMP_94 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_92 \def (Bind 
Void) in (let TMP_93 \def (THead TMP_92 u3 t3) in (eq T t2 TMP_93))))) in 
(let TMP_95 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let 
TMP_96 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) in (let TMP_97 
\def (ex3_2 T T TMP_94 TMP_95 TMP_96) in (let TMP_98 \def (S O) in (let 
TMP_99 \def (lift TMP_98 O t2) in (let TMP_100 \def (pr0 t1 TMP_99) in (or 
TMP_97 TMP_100)))))))))) in (let H11 \def (eq_ind T t0 TMP_101 H4 t1 H8) in 
(let TMP_102 \def (\lambda (t: T).(pr0 t t2)) in (let H12 \def (eq_ind T t0 
TMP_102 H3 t1 H8) in (let TMP_112 \def (\lambda (t: T).((eq T t (THead (Bind 
Void) u1 t1)) \to (let TMP_105 \def (\lambda (u3: T).(\lambda (t3: T).(let 
TMP_103 \def (Bind Void) in (let TMP_104 \def (THead TMP_103 u3 t3) in (eq T 
u2 TMP_104))))) in (let TMP_106 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) in (let TMP_107 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) in 
(let TMP_108 \def (ex3_2 T T TMP_105 TMP_106 TMP_107) in (let TMP_109 \def (S 
O) in (let TMP_110 \def (lift TMP_109 O u2) in (let TMP_111 \def (pr0 t1 
TMP_110) in (or TMP_108 TMP_111)))))))))) in (let H13 \def (eq_ind T u0 
TMP_112 H2 u1 H9) in (let TMP_113 \def (\lambda (t: T).(pr0 t u2)) in (let 
H14 \def (eq_ind T u0 TMP_113 H1 u1 H9) in (let TMP_118 \def (\lambda (u3: 
T).(\lambda (t3: T).(let TMP_114 \def (Bind Void) in (let TMP_115 \def (THead 
TMP_114 u2 t2) in (let TMP_116 \def (Bind Void) in (let TMP_117 \def (THead 
TMP_116 u3 t3) in (eq T TMP_115 TMP_117))))))) in (let TMP_119 \def (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_120 \def (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) in (let TMP_121 \def (ex3_2 T T TMP_118 
TMP_119 TMP_120) in (let TMP_122 \def (S O) in (let TMP_123 \def (Bind Void) 
in (let TMP_124 \def (THead TMP_123 u2 t2) in (let TMP_125 \def (lift TMP_122 
O TMP_124) in (let TMP_126 \def (pr0 t1 TMP_125) in (let TMP_131 \def 
(\lambda (u3: T).(\lambda (t3: T).(let TMP_127 \def (Bind Void) in (let 
TMP_128 \def (THead TMP_127 u2 t2) in (let TMP_129 \def (Bind Void) in (let 
TMP_130 \def (THead TMP_129 u3 t3) in (eq T TMP_128 TMP_130))))))) in (let 
TMP_132 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_133 
\def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) in (let TMP_134 \def 
(Bind Void) in (let TMP_135 \def (THead TMP_134 u2 t2) in (let TMP_136 \def 
(refl_equal T TMP_135) in (let TMP_137 \def (ex3_2_intro T T TMP_131 TMP_132 
TMP_133 u2 t2 TMP_136 H14 H12) in (let TMP_138 \def (or_introl TMP_121 
TMP_126 TMP_137) in (eq_ind_r K TMP_79 TMP_91 TMP_138 k 
H10)))))))))))))))))))))))))))))) in (let TMP_140 \def (TMP_139 H7) in 
(TMP_140 H6)))))))))))))))))))))))))))) in (let TMP_163 \def (\lambda (u: 
T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: 
(((eq T v1 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v2 (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2)))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) 
(THead (Bind Void) u1 t1))).(let TMP_142 \def (Flat Appl) in (let TMP_143 
\def (Bind Abst) in (let TMP_144 \def (THead TMP_143 u t0) in (let TMP_145 
\def (THead TMP_142 v1 TMP_144) in (let TMP_146 \def (\lambda (ee: T).(match 
ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k 
_ _) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) in (let TMP_147 \def (Bind Void) in (let TMP_148 \def 
(THead TMP_147 u1 t1) in (let H6 \def (eq_ind T TMP_145 TMP_146 I TMP_148 H5) 
in (let TMP_153 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_149 \def 
(Bind Abbr) in (let TMP_150 \def (THead TMP_149 v2 t2) in (let TMP_151 \def 
(Bind Void) in (let TMP_152 \def (THead TMP_151 u2 t3) in (eq T TMP_150 
TMP_152))))))) in (let TMP_154 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_155 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) in 
(let TMP_156 \def (ex3_2 T T TMP_153 TMP_154 TMP_155) in (let TMP_157 \def (S 
O) in (let TMP_158 \def (Bind Abbr) in (let TMP_159 \def (THead TMP_158 v2 
t2) in (let TMP_160 \def (lift TMP_157 O TMP_159) in (let TMP_161 \def (pr0 
t1 TMP_160) in (let TMP_162 \def (or TMP_156 TMP_161) in (False_ind TMP_162 
H6))))))))))))))))))))))))))))) in (let TMP_193 \def (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: T).(\lambda 
(u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead (Bind Void) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq T (THead (Flat Appl) 
v1 (THead (Bind b) u0 t0)) (THead (Bind Void) u1 t1))).(let TMP_164 \def 
(Flat Appl) in (let TMP_165 \def (Bind b) in (let TMP_166 \def (THead TMP_165 
u0 t0) in (let TMP_167 \def (THead TMP_164 v1 TMP_166) in (let TMP_168 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_169 \def (Bind 
Void) in (let TMP_170 \def (THead TMP_169 u1 t1) in (let H9 \def (eq_ind T 
TMP_167 TMP_168 I TMP_170 H8) in (let TMP_179 \def (\lambda (u3: T).(\lambda 
(t3: T).(let TMP_171 \def (Bind b) in (let TMP_172 \def (Flat Appl) in (let 
TMP_173 \def (S O) in (let TMP_174 \def (lift TMP_173 O v2) in (let TMP_175 
\def (THead TMP_172 TMP_174 t2) in (let TMP_176 \def (THead TMP_171 u2 
TMP_175) in (let TMP_177 \def (Bind Void) in (let TMP_178 \def (THead TMP_177 
u3 t3) in (eq T TMP_176 TMP_178))))))))))) in (let TMP_180 \def (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) in (let TMP_181 \def (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) in (let TMP_182 \def (ex3_2 T T TMP_179 
TMP_180 TMP_181) in (let TMP_183 \def (S O) in (let TMP_184 \def (Bind b) in 
(let TMP_185 \def (Flat Appl) in (let TMP_186 \def (S O) in (let TMP_187 \def 
(lift TMP_186 O v2) in (let TMP_188 \def (THead TMP_185 TMP_187 t2) in (let 
TMP_189 \def (THead TMP_184 u2 TMP_188) in (let TMP_190 \def (lift TMP_183 O 
TMP_189) in (let TMP_191 \def (pr0 t1 TMP_190) in (let TMP_192 \def (or 
TMP_182 TMP_191) in (False_ind TMP_192 
H9)))))))))))))))))))))))))))))))))))))) in (let TMP_213 \def (\lambda (u0: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead 
(Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (w: T).(\lambda (_: (subst0 O 
u2 t2 w)).(\lambda (H6: (eq T (THead (Bind Abbr) u0 t0) (THead (Bind Void) u1 
t1))).(let TMP_194 \def (Bind Abbr) in (let TMP_195 \def (THead TMP_194 u0 
t0) in (let TMP_196 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k with [(Bind b) \Rightarrow (match b with [Abbr \Rightarrow True | 
Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])])) in (let TMP_197 \def (Bind Void) in (let TMP_198 \def (THead 
TMP_197 u1 t1) in (let H7 \def (eq_ind T TMP_195 TMP_196 I TMP_198 H6) in 
(let TMP_203 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_199 \def (Bind 
Abbr) in (let TMP_200 \def (THead TMP_199 u2 w) in (let TMP_201 \def (Bind 
Void) in (let TMP_202 \def (THead TMP_201 u3 t3) in (eq T TMP_200 
TMP_202))))))) in (let TMP_204 \def (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) in (let TMP_205 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) in 
(let TMP_206 \def (ex3_2 T T TMP_203 TMP_204 TMP_205) in (let TMP_207 \def (S 
O) in (let TMP_208 \def (Bind Abbr) in (let TMP_209 \def (THead TMP_208 u2 w) 
in (let TMP_210 \def (lift TMP_207 O TMP_209) in (let TMP_211 \def (pr0 t1 
TMP_210) in (let TMP_212 \def (or TMP_206 TMP_211) in (False_ind TMP_212 
H7)))))))))))))))))))))))))))) in (let TMP_293 \def (\lambda (b: B).(\lambda 
(H1: (not (eq B b Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: 
(pr0 t0 t2)).(\lambda (H3: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda 
(u: T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead (Bind 
Void) u1 t1))).(let TMP_214 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k 
with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) in (let TMP_215 
\def (Bind b) in (let TMP_216 \def (S O) in (let TMP_217 \def (lift TMP_216 O 
t0) in (let TMP_218 \def (THead TMP_215 u TMP_217) in (let TMP_219 \def (Bind 
Void) in (let TMP_220 \def (THead TMP_219 u1 t1) in (let H5 \def (f_equal T B 
TMP_214 TMP_218 TMP_220 H4) in (let TMP_221 \def (\lambda (e: T).(match e 
with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t _) 
\Rightarrow t])) in (let TMP_222 \def (Bind b) in (let TMP_223 \def (S O) in 
(let TMP_224 \def (lift TMP_223 O t0) in (let TMP_225 \def (THead TMP_222 u 
TMP_224) in (let TMP_226 \def (Bind Void) in (let TMP_227 \def (THead TMP_226 
u1 t1) in (let H6 \def (f_equal T T TMP_221 TMP_225 TMP_227 H4) in (let 
TMP_242 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow (let 
TMP_241 \def (\lambda (x0: nat).(let TMP_240 \def (S O) in (plus x0 
TMP_240))) in (lref_map TMP_241 O t0)) | (TLRef _) \Rightarrow (let TMP_234 
\def (\lambda (x0: nat).(let TMP_233 \def (S O) in (plus x0 TMP_233))) in 
(lref_map TMP_234 O t0)) | (THead _ _ t) \Rightarrow t])) in (let TMP_243 
\def (Bind b) in (let TMP_244 \def (S O) in (let TMP_245 \def (lift TMP_244 O 
t0) in (let TMP_246 \def (THead TMP_243 u TMP_245) in (let TMP_247 \def (Bind 
Void) in (let TMP_248 \def (THead TMP_247 u1 t1) in (let H7 \def (f_equal T T 
TMP_242 TMP_246 TMP_248 H4) in (let TMP_291 \def (\lambda (_: (eq T u 
u1)).(\lambda (H9: (eq B b Void)).(let TMP_250 \def (\lambda (b0: B).(let 
TMP_249 \def (eq B b0 Abst) in (not TMP_249))) in (let H10 \def (eq_ind B b 
TMP_250 H1 Void H9) in (let TMP_260 \def (\lambda (t: T).((eq T t0 (THead 
(Bind Void) u1 t)) \to (let TMP_253 \def (\lambda (u2: T).(\lambda (t3: 
T).(let TMP_251 \def (Bind Void) in (let TMP_252 \def (THead TMP_251 u2 t3) 
in (eq T t2 TMP_252))))) in (let TMP_254 \def (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) in (let TMP_255 \def (\lambda (_: T).(\lambda (t3: T).(pr0 t 
t3))) in (let TMP_256 \def (ex3_2 T T TMP_253 TMP_254 TMP_255) in (let 
TMP_257 \def (S O) in (let TMP_258 \def (lift TMP_257 O t2) in (let TMP_259 
\def (pr0 t TMP_258) in (or TMP_256 TMP_259)))))))))) in (let TMP_261 \def (S 
O) in (let TMP_262 \def (lift TMP_261 O t0) in (let H11 \def (eq_ind_r T t1 
TMP_260 H3 TMP_262 H7) in (let TMP_263 \def (S O) in (let TMP_264 \def (lift 
TMP_263 O t0) in (let TMP_274 \def (\lambda (t: T).(let TMP_267 \def (\lambda 
(u2: T).(\lambda (t3: T).(let TMP_265 \def (Bind Void) in (let TMP_266 \def 
(THead TMP_265 u2 t3) in (eq T t2 TMP_266))))) in (let TMP_268 \def (\lambda 
(u2: T).(\lambda (_: T).(pr0 u1 u2))) in (let TMP_269 \def (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3))) in (let TMP_270 \def (ex3_2 T T TMP_267 
TMP_268 TMP_269) in (let TMP_271 \def (S O) in (let TMP_272 \def (lift 
TMP_271 O t2) in (let TMP_273 \def (pr0 t TMP_272) in (or TMP_270 
TMP_273))))))))) in (let TMP_277 \def (\lambda (u2: T).(\lambda (t3: T).(let 
TMP_275 \def (Bind Void) in (let TMP_276 \def (THead TMP_275 u2 t3) in (eq T 
t2 TMP_276))))) in (let TMP_278 \def (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) in (let TMP_281 \def (\lambda (_: T).(\lambda (t3: T).(let TMP_279 \def 
(S O) in (let TMP_280 \def (lift TMP_279 O t0) in (pr0 TMP_280 t3))))) in 
(let TMP_282 \def (ex3_2 T T TMP_277 TMP_278 TMP_281) in (let TMP_283 \def (S 
O) in (let TMP_284 \def (lift TMP_283 O t0) in (let TMP_285 \def (S O) in 
(let TMP_286 \def (lift TMP_285 O t2) in (let TMP_287 \def (pr0 TMP_284 
TMP_286) in (let TMP_288 \def (S O) in (let TMP_289 \def (pr0_lift t0 t2 H2 
TMP_288 O) in (let TMP_290 \def (or_intror TMP_282 TMP_287 TMP_289) in 
(eq_ind T TMP_264 TMP_274 TMP_290 t1 H7)))))))))))))))))))))))) in (let 
TMP_292 \def (TMP_291 H6) in (TMP_292 H5))))))))))))))))))))))))))))))))))) 
in (let TMP_309 \def (\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (u: T).(\lambda 
(H3: (eq T (THead (Flat Cast) u t0) (THead (Bind Void) u1 t1))).(let TMP_294 
\def (Flat Cast) in (let TMP_295 \def (THead TMP_294 u t0) in (let TMP_296 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_297 \def (Bind 
Void) in (let TMP_298 \def (THead TMP_297 u1 t1) in (let H4 \def (eq_ind T 
TMP_295 TMP_296 I TMP_298 H3) in (let TMP_301 \def (\lambda (u2: T).(\lambda 
(t3: T).(let TMP_299 \def (Bind Void) in (let TMP_300 \def (THead TMP_299 u2 
t3) in (eq T t2 TMP_300))))) in (let TMP_302 \def (\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))) in (let TMP_303 \def (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) in (let TMP_304 \def (ex3_2 T T TMP_301 TMP_302 TMP_303) in 
(let TMP_305 \def (S O) in (let TMP_306 \def (lift TMP_305 O t2) in (let 
TMP_307 \def (pr0 t1 TMP_306) in (let TMP_308 \def (or TMP_304 TMP_307) in 
(False_ind TMP_308 H4))))))))))))))))))))) in (pr0_ind TMP_23 TMP_66 TMP_141 
TMP_163 TMP_193 TMP_213 TMP_293 TMP_309 y x H0))))))))))) in (insert_eq T 
TMP_2 TMP_3 TMP_13 TMP_310 H))))))))).

