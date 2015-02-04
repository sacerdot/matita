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

include "basic_1/lift/fwd.ma".

include "basic_1/tlt/props.ma".

theorem lift_weight_map:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(\forall (f: ((nat \to 
nat))).(((\forall (m: nat).((le d m) \to (eq nat (f m) O)))) \to (eq nat 
(weight_map f (lift h d t)) (weight_map f t))))))
\def
 \lambda (t: T).(let TMP_4 \def (\lambda (t0: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq 
nat (f m) O)))) \to (let TMP_1 \def (lift h d t0) in (let TMP_2 \def 
(weight_map f TMP_1) in (let TMP_3 \def (weight_map f t0) in (eq nat TMP_2 
TMP_3))))))))) in (let TMP_7 \def (\lambda (n: nat).(\lambda (_: 
nat).(\lambda (d: nat).(\lambda (f: ((nat \to nat))).(\lambda (_: ((\forall 
(m: nat).((le d m) \to (eq nat (f m) O))))).(let TMP_5 \def (TSort n) in (let 
TMP_6 \def (weight_map f TMP_5) in (refl_equal nat TMP_6)))))))) in (let 
TMP_45 \def (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(f: ((nat \to nat))).(\lambda (H: ((\forall (m: nat).((le d m) \to (eq nat (f 
m) O))))).(let TMP_8 \def (TLRef n) in (let TMP_9 \def (lift h d TMP_8) in 
(let TMP_10 \def (weight_map f TMP_9) in (let TMP_11 \def (TLRef n) in (let 
TMP_12 \def (weight_map f TMP_11) in (let TMP_13 \def (eq nat TMP_10 TMP_12) 
in (let TMP_25 \def (\lambda (H0: (lt n d)).(let TMP_14 \def (TLRef n) in 
(let TMP_18 \def (\lambda (t0: T).(let TMP_15 \def (weight_map f t0) in (let 
TMP_16 \def (TLRef n) in (let TMP_17 \def (weight_map f TMP_16) in (eq nat 
TMP_15 TMP_17))))) in (let TMP_19 \def (TLRef n) in (let TMP_20 \def 
(weight_map f TMP_19) in (let TMP_21 \def (refl_equal nat TMP_20) in (let 
TMP_22 \def (TLRef n) in (let TMP_23 \def (lift h d TMP_22) in (let TMP_24 
\def (lift_lref_lt n h d H0) in (eq_ind_r T TMP_14 TMP_18 TMP_21 TMP_23 
TMP_24)))))))))) in (let TMP_44 \def (\lambda (H0: (le d n)).(let TMP_26 \def 
(plus n h) in (let TMP_27 \def (TLRef TMP_26) in (let TMP_31 \def (\lambda 
(t0: T).(let TMP_28 \def (weight_map f t0) in (let TMP_29 \def (TLRef n) in 
(let TMP_30 \def (weight_map f TMP_29) in (eq nat TMP_28 TMP_30))))) in (let 
TMP_34 \def (\lambda (n0: nat).(let TMP_32 \def (plus n h) in (let TMP_33 
\def (f TMP_32) in (eq nat TMP_33 n0)))) in (let TMP_35 \def (plus n h) in 
(let TMP_36 \def (le_plus_trans d n h H0) in (let TMP_37 \def (H TMP_35 
TMP_36) in (let TMP_38 \def (f n) in (let TMP_39 \def (H n H0) in (let TMP_40 
\def (eq_ind_r nat O TMP_34 TMP_37 TMP_38 TMP_39) in (let TMP_41 \def (TLRef 
n) in (let TMP_42 \def (lift h d TMP_41) in (let TMP_43 \def (lift_lref_ge n 
h d H0) in (eq_ind_r T TMP_27 TMP_31 TMP_40 TMP_42 TMP_43))))))))))))))) in 
(lt_le_e n d TMP_13 TMP_25 TMP_44)))))))))))))) in (let TMP_325 \def (\lambda 
(k: K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat 
(f m) O)))) \to (eq nat (weight_map f (lift h d t0)) (weight_map f 
t0)))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(((\forall (m: nat).((le d m) \to (eq nat 
(f m) O)))) \to (eq nat (weight_map f (lift h d t1)) (weight_map f 
t1)))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (H1: ((\forall (m: nat).((le d m) \to (eq nat (f m) 
O))))).(let TMP_51 \def (\lambda (k0: K).(let TMP_46 \def (THead k0 t0 t1) in 
(let TMP_47 \def (lift h d TMP_46) in (let TMP_48 \def (weight_map f TMP_47) 
in (let TMP_49 \def (THead k0 t0 t1) in (let TMP_50 \def (weight_map f 
TMP_49) in (eq nat TMP_48 TMP_50))))))) in (let TMP_289 \def (\lambda (b: 
B).(let TMP_52 \def (Bind b) in (let TMP_53 \def (lift h d t0) in (let TMP_54 
\def (Bind b) in (let TMP_55 \def (s TMP_54 d) in (let TMP_56 \def (lift h 
TMP_55 t1) in (let TMP_57 \def (THead TMP_52 TMP_53 TMP_56) in (let TMP_62 
\def (\lambda (t2: T).(let TMP_58 \def (weight_map f t2) in (let TMP_59 \def 
(Bind b) in (let TMP_60 \def (THead TMP_59 t0 t1) in (let TMP_61 \def 
(weight_map f TMP_60) in (eq nat TMP_58 TMP_61)))))) in (let TMP_103 \def 
(\lambda (b0: B).(let TMP_87 \def (match b0 with [Abbr \Rightarrow (let 
TMP_77 \def (lift h d t0) in (let TMP_78 \def (weight_map f TMP_77) in (let 
TMP_79 \def (lift h d t0) in (let TMP_80 \def (weight_map f TMP_79) in (let 
TMP_81 \def (S TMP_80) in (let TMP_82 \def (wadd f TMP_81) in (let TMP_83 
\def (S d) in (let TMP_84 \def (lift h TMP_83 t1) in (let TMP_85 \def 
(weight_map TMP_82 TMP_84) in (let TMP_86 \def (plus TMP_78 TMP_85) in (S 
TMP_86))))))))))) | Abst \Rightarrow (let TMP_70 \def (lift h d t0) in (let 
TMP_71 \def (weight_map f TMP_70) in (let TMP_72 \def (wadd f O) in (let 
TMP_73 \def (S d) in (let TMP_74 \def (lift h TMP_73 t1) in (let TMP_75 \def 
(weight_map TMP_72 TMP_74) in (let TMP_76 \def (plus TMP_71 TMP_75) in (S 
TMP_76)))))))) | Void \Rightarrow (let TMP_63 \def (lift h d t0) in (let 
TMP_64 \def (weight_map f TMP_63) in (let TMP_65 \def (wadd f O) in (let 
TMP_66 \def (S d) in (let TMP_67 \def (lift h TMP_66 t1) in (let TMP_68 \def 
(weight_map TMP_65 TMP_67) in (let TMP_69 \def (plus TMP_64 TMP_68) in (S 
TMP_69))))))))]) in (let TMP_102 \def (match b0 with [Abbr \Rightarrow (let 
TMP_96 \def (weight_map f t0) in (let TMP_97 \def (weight_map f t0) in (let 
TMP_98 \def (S TMP_97) in (let TMP_99 \def (wadd f TMP_98) in (let TMP_100 
\def (weight_map TMP_99 t1) in (let TMP_101 \def (plus TMP_96 TMP_100) in (S 
TMP_101))))))) | Abst \Rightarrow (let TMP_92 \def (weight_map f t0) in (let 
TMP_93 \def (wadd f O) in (let TMP_94 \def (weight_map TMP_93 t1) in (let 
TMP_95 \def (plus TMP_92 TMP_94) in (S TMP_95))))) | Void \Rightarrow (let 
TMP_88 \def (weight_map f t0) in (let TMP_89 \def (wadd f O) in (let TMP_90 
\def (weight_map TMP_89 t1) in (let TMP_91 \def (plus TMP_88 TMP_90) in (S 
TMP_91)))))]) in (eq nat TMP_87 TMP_102)))) in (let TMP_104 \def (weight_map 
f t0) in (let TMP_119 \def (\lambda (n: nat).(let TMP_105 \def (S n) in (let 
TMP_106 \def (wadd f TMP_105) in (let TMP_107 \def (S d) in (let TMP_108 \def 
(lift h TMP_107 t1) in (let TMP_109 \def (weight_map TMP_106 TMP_108) in (let 
TMP_110 \def (plus n TMP_109) in (let TMP_111 \def (S TMP_110) in (let 
TMP_112 \def (weight_map f t0) in (let TMP_113 \def (weight_map f t0) in (let 
TMP_114 \def (S TMP_113) in (let TMP_115 \def (wadd f TMP_114) in (let 
TMP_116 \def (weight_map TMP_115 t1) in (let TMP_117 \def (plus TMP_112 
TMP_116) in (let TMP_118 \def (S TMP_117) in (eq nat TMP_111 
TMP_118)))))))))))))))) in (let TMP_120 \def (weight_map f t0) in (let 
TMP_121 \def (S TMP_120) in (let TMP_122 \def (wadd f TMP_121) in (let 
TMP_123 \def (weight_map TMP_122 t1) in (let TMP_134 \def (\lambda (n: 
nat).(let TMP_124 \def (weight_map f t0) in (let TMP_125 \def (plus TMP_124 
n) in (let TMP_126 \def (S TMP_125) in (let TMP_127 \def (weight_map f t0) in 
(let TMP_128 \def (weight_map f t0) in (let TMP_129 \def (S TMP_128) in (let 
TMP_130 \def (wadd f TMP_129) in (let TMP_131 \def (weight_map TMP_130 t1) in 
(let TMP_132 \def (plus TMP_127 TMP_131) in (let TMP_133 \def (S TMP_132) in 
(eq nat TMP_126 TMP_133)))))))))))) in (let TMP_135 \def (weight_map f t0) in 
(let TMP_136 \def (weight_map f t0) in (let TMP_137 \def (S TMP_136) in (let 
TMP_138 \def (wadd f TMP_137) in (let TMP_139 \def (weight_map TMP_138 t1) in 
(let TMP_140 \def (plus TMP_135 TMP_139) in (let TMP_141 \def (S TMP_140) in 
(let TMP_142 \def (refl_equal nat TMP_141) in (let TMP_143 \def (weight_map f 
t0) in (let TMP_144 \def (S TMP_143) in (let TMP_145 \def (wadd f TMP_144) in 
(let TMP_146 \def (S d) in (let TMP_147 \def (lift h TMP_146 t1) in (let 
TMP_148 \def (weight_map TMP_145 TMP_147) in (let TMP_149 \def (S d) in (let 
TMP_150 \def (weight_map f t0) in (let TMP_151 \def (S TMP_150) in (let 
TMP_152 \def (wadd f TMP_151) in (let TMP_168 \def (\lambda (m: nat).(\lambda 
(H2: (le (S d) m)).(let TMP_154 \def (\lambda (n: nat).(let TMP_153 \def (S 
n) in (eq nat m TMP_153))) in (let TMP_155 \def (\lambda (n: nat).(le d n)) 
in (let TMP_156 \def (weight_map f t0) in (let TMP_157 \def (S TMP_156) in 
(let TMP_158 \def (wadd f TMP_157 m) in (let TMP_159 \def (eq nat TMP_158 O) 
in (let TMP_166 \def (\lambda (x: nat).(\lambda (H3: (eq nat m (S 
x))).(\lambda (H4: (le d x)).(let TMP_160 \def (S x) in (let TMP_164 \def 
(\lambda (n: nat).(let TMP_161 \def (weight_map f t0) in (let TMP_162 \def (S 
TMP_161) in (let TMP_163 \def (wadd f TMP_162 n) in (eq nat TMP_163 O))))) in 
(let TMP_165 \def (H1 x H4) in (eq_ind_r nat TMP_160 TMP_164 TMP_165 m 
H3))))))) in (let TMP_167 \def (le_gen_S d m H2) in (ex2_ind nat TMP_154 
TMP_155 TMP_159 TMP_166 TMP_167))))))))))) in (let TMP_169 \def (H0 h TMP_149 
TMP_152 TMP_168) in (let TMP_170 \def (eq_ind_r nat TMP_123 TMP_134 TMP_142 
TMP_148 TMP_169) in (let TMP_171 \def (lift h d t0) in (let TMP_172 \def 
(weight_map f TMP_171) in (let TMP_173 \def (H h d f H1) in (let TMP_174 \def 
(eq_ind_r nat TMP_104 TMP_119 TMP_170 TMP_172 TMP_173) in (let TMP_175 \def 
(wadd f O) in (let TMP_176 \def (weight_map TMP_175 t1) in (let TMP_186 \def 
(\lambda (n: nat).(let TMP_177 \def (lift h d t0) in (let TMP_178 \def 
(weight_map f TMP_177) in (let TMP_179 \def (plus TMP_178 n) in (let TMP_180 
\def (S TMP_179) in (let TMP_181 \def (weight_map f t0) in (let TMP_182 \def 
(wadd f O) in (let TMP_183 \def (weight_map TMP_182 t1) in (let TMP_184 \def 
(plus TMP_181 TMP_183) in (let TMP_185 \def (S TMP_184) in (eq nat TMP_180 
TMP_185))))))))))) in (let TMP_187 \def (lift h d t0) in (let TMP_188 \def 
(weight_map f TMP_187) in (let TMP_189 \def (wadd f O) in (let TMP_190 \def 
(weight_map TMP_189 t1) in (let TMP_191 \def (plus TMP_188 TMP_190) in (let 
TMP_192 \def (weight_map f t0) in (let TMP_193 \def (wadd f O) in (let 
TMP_194 \def (weight_map TMP_193 t1) in (let TMP_195 \def (plus TMP_192 
TMP_194) in (let TMP_196 \def (lift h d t0) in (let TMP_197 \def (weight_map 
f TMP_196) in (let TMP_198 \def (weight_map f t0) in (let TMP_199 \def (wadd 
f O) in (let TMP_200 \def (weight_map TMP_199 t1) in (let TMP_201 \def (wadd 
f O) in (let TMP_202 \def (weight_map TMP_201 t1) in (let TMP_203 \def (H h d 
f H1) in (let TMP_204 \def (wadd f O) in (let TMP_205 \def (weight_map 
TMP_204 t1) in (let TMP_206 \def (refl_equal nat TMP_205) in (let TMP_207 
\def (f_equal2 nat nat nat plus TMP_197 TMP_198 TMP_200 TMP_202 TMP_203 
TMP_206) in (let TMP_208 \def (f_equal nat nat S TMP_191 TMP_195 TMP_207) in 
(let TMP_209 \def (wadd f O) in (let TMP_210 \def (S d) in (let TMP_211 \def 
(lift h TMP_210 t1) in (let TMP_212 \def (weight_map TMP_209 TMP_211) in (let 
TMP_213 \def (S d) in (let TMP_214 \def (wadd f O) in (let TMP_226 \def 
(\lambda (m: nat).(\lambda (H2: (le (S d) m)).(let TMP_216 \def (\lambda (n: 
nat).(let TMP_215 \def (S n) in (eq nat m TMP_215))) in (let TMP_217 \def 
(\lambda (n: nat).(le d n)) in (let TMP_218 \def (wadd f O m) in (let TMP_219 
\def (eq nat TMP_218 O) in (let TMP_224 \def (\lambda (x: nat).(\lambda (H3: 
(eq nat m (S x))).(\lambda (H4: (le d x)).(let TMP_220 \def (S x) in (let 
TMP_222 \def (\lambda (n: nat).(let TMP_221 \def (wadd f O n) in (eq nat 
TMP_221 O))) in (let TMP_223 \def (H1 x H4) in (eq_ind_r nat TMP_220 TMP_222 
TMP_223 m H3))))))) in (let TMP_225 \def (le_gen_S d m H2) in (ex2_ind nat 
TMP_216 TMP_217 TMP_219 TMP_224 TMP_225))))))))) in (let TMP_227 \def (H0 h 
TMP_213 TMP_214 TMP_226) in (let TMP_228 \def (eq_ind_r nat TMP_176 TMP_186 
TMP_208 TMP_212 TMP_227) in (let TMP_229 \def (wadd f O) in (let TMP_230 \def 
(weight_map TMP_229 t1) in (let TMP_240 \def (\lambda (n: nat).(let TMP_231 
\def (lift h d t0) in (let TMP_232 \def (weight_map f TMP_231) in (let 
TMP_233 \def (plus TMP_232 n) in (let TMP_234 \def (S TMP_233) in (let 
TMP_235 \def (weight_map f t0) in (let TMP_236 \def (wadd f O) in (let 
TMP_237 \def (weight_map TMP_236 t1) in (let TMP_238 \def (plus TMP_235 
TMP_237) in (let TMP_239 \def (S TMP_238) in (eq nat TMP_234 
TMP_239))))))))))) in (let TMP_241 \def (lift h d t0) in (let TMP_242 \def 
(weight_map f TMP_241) in (let TMP_243 \def (wadd f O) in (let TMP_244 \def 
(weight_map TMP_243 t1) in (let TMP_245 \def (plus TMP_242 TMP_244) in (let 
TMP_246 \def (weight_map f t0) in (let TMP_247 \def (wadd f O) in (let 
TMP_248 \def (weight_map TMP_247 t1) in (let TMP_249 \def (plus TMP_246 
TMP_248) in (let TMP_250 \def (lift h d t0) in (let TMP_251 \def (weight_map 
f TMP_250) in (let TMP_252 \def (weight_map f t0) in (let TMP_253 \def (wadd 
f O) in (let TMP_254 \def (weight_map TMP_253 t1) in (let TMP_255 \def (wadd 
f O) in (let TMP_256 \def (weight_map TMP_255 t1) in (let TMP_257 \def (H h d 
f H1) in (let TMP_258 \def (wadd f O) in (let TMP_259 \def (weight_map 
TMP_258 t1) in (let TMP_260 \def (refl_equal nat TMP_259) in (let TMP_261 
\def (f_equal2 nat nat nat plus TMP_251 TMP_252 TMP_254 TMP_256 TMP_257 
TMP_260) in (let TMP_262 \def (f_equal nat nat S TMP_245 TMP_249 TMP_261) in 
(let TMP_263 \def (wadd f O) in (let TMP_264 \def (S d) in (let TMP_265 \def 
(lift h TMP_264 t1) in (let TMP_266 \def (weight_map TMP_263 TMP_265) in (let 
TMP_267 \def (S d) in (let TMP_268 \def (wadd f O) in (let TMP_280 \def 
(\lambda (m: nat).(\lambda (H2: (le (S d) m)).(let TMP_270 \def (\lambda (n: 
nat).(let TMP_269 \def (S n) in (eq nat m TMP_269))) in (let TMP_271 \def 
(\lambda (n: nat).(le d n)) in (let TMP_272 \def (wadd f O m) in (let TMP_273 
\def (eq nat TMP_272 O) in (let TMP_278 \def (\lambda (x: nat).(\lambda (H3: 
(eq nat m (S x))).(\lambda (H4: (le d x)).(let TMP_274 \def (S x) in (let 
TMP_276 \def (\lambda (n: nat).(let TMP_275 \def (wadd f O n) in (eq nat 
TMP_275 O))) in (let TMP_277 \def (H1 x H4) in (eq_ind_r nat TMP_274 TMP_276 
TMP_277 m H3))))))) in (let TMP_279 \def (le_gen_S d m H2) in (ex2_ind nat 
TMP_270 TMP_271 TMP_273 TMP_278 TMP_279))))))))) in (let TMP_281 \def (H0 h 
TMP_267 TMP_268 TMP_280) in (let TMP_282 \def (eq_ind_r nat TMP_230 TMP_240 
TMP_262 TMP_266 TMP_281) in (let TMP_283 \def (B_ind TMP_103 TMP_174 TMP_228 
TMP_282 b) in (let TMP_284 \def (Bind b) in (let TMP_285 \def (THead TMP_284 
t0 t1) in (let TMP_286 \def (lift h d TMP_285) in (let TMP_287 \def (Bind b) 
in (let TMP_288 \def (lift_head TMP_287 t0 t1 h d) in (eq_ind_r T TMP_57 
TMP_62 TMP_283 TMP_286 
TMP_288)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_324 \def (\lambda 
(f0: F).(let TMP_290 \def (Flat f0) in (let TMP_291 \def (lift h d t0) in 
(let TMP_292 \def (Flat f0) in (let TMP_293 \def (s TMP_292 d) in (let 
TMP_294 \def (lift h TMP_293 t1) in (let TMP_295 \def (THead TMP_290 TMP_291 
TMP_294) in (let TMP_300 \def (\lambda (t2: T).(let TMP_296 \def (weight_map 
f t2) in (let TMP_297 \def (Flat f0) in (let TMP_298 \def (THead TMP_297 t0 
t1) in (let TMP_299 \def (weight_map f TMP_298) in (eq nat TMP_296 
TMP_299)))))) in (let TMP_301 \def (lift h d t0) in (let TMP_302 \def 
(weight_map f TMP_301) in (let TMP_303 \def (lift h d t1) in (let TMP_304 
\def (weight_map f TMP_303) in (let TMP_305 \def (plus TMP_302 TMP_304) in 
(let TMP_306 \def (weight_map f t0) in (let TMP_307 \def (weight_map f t1) in 
(let TMP_308 \def (plus TMP_306 TMP_307) in (let TMP_309 \def (lift h d t0) 
in (let TMP_310 \def (weight_map f TMP_309) in (let TMP_311 \def (weight_map 
f t0) in (let TMP_312 \def (lift h d t1) in (let TMP_313 \def (weight_map f 
TMP_312) in (let TMP_314 \def (weight_map f t1) in (let TMP_315 \def (H h d f 
H1) in (let TMP_316 \def (H0 h d f H1) in (let TMP_317 \def (f_equal2 nat nat 
nat plus TMP_310 TMP_311 TMP_313 TMP_314 TMP_315 TMP_316) in (let TMP_318 
\def (f_equal nat nat S TMP_305 TMP_308 TMP_317) in (let TMP_319 \def (Flat 
f0) in (let TMP_320 \def (THead TMP_319 t0 t1) in (let TMP_321 \def (lift h d 
TMP_320) in (let TMP_322 \def (Flat f0) in (let TMP_323 \def (lift_head 
TMP_322 t0 t1 h d) in (eq_ind_r T TMP_295 TMP_300 TMP_318 TMP_321 
TMP_323)))))))))))))))))))))))))))))))) in (K_ind TMP_51 TMP_289 TMP_324 
k))))))))))))) in (T_ind TMP_4 TMP_7 TMP_45 TMP_325 t))))).

theorem lift_weight:
 \forall (t: T).(\forall (h: nat).(\forall (d: nat).(eq nat (weight (lift h d 
t)) (weight t))))
\def
 \lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(let TMP_1 \def (\lambda 
(_: nat).O) in (let TMP_2 \def (\lambda (m: nat).(\lambda (_: (le d 
m)).(refl_equal nat O))) in (lift_weight_map t h d TMP_1 TMP_2))))).

theorem lift_weight_add:
 \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to 
(((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) \to (eq nat 
(weight_map f (lift h d t)) (weight_map g (lift (S h) d t)))))))))))
\def
 \lambda (w: nat).(\lambda (t: T).(let TMP_6 \def (\lambda (t0: T).(\forall 
(h: nat).(\forall (d: nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq 
nat (g d) w) \to (((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f 
m))))) \to (let TMP_1 \def (lift h d t0) in (let TMP_2 \def (weight_map f 
TMP_1) in (let TMP_3 \def (S h) in (let TMP_4 \def (lift TMP_3 d t0) in (let 
TMP_5 \def (weight_map g TMP_4) in (eq nat TMP_2 TMP_5)))))))))))))) in (let 
TMP_11 \def (\lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (m: 
nat).((lt m d) \to (eq nat (g m) (f m)))))).(\lambda (_: (eq nat (g d) 
w)).(\lambda (_: ((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f 
m)))))).(let TMP_7 \def (S h) in (let TMP_8 \def (TSort n) in (let TMP_9 \def 
(lift TMP_7 d TMP_8) in (let TMP_10 \def (weight_map g TMP_9) in (refl_equal 
nat TMP_10))))))))))))) in (let TMP_91 \def (\lambda (n: nat).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H: ((\forall (m: nat).((lt m d) \to (eq nat (g m) (f 
m)))))).(\lambda (_: (eq nat (g d) w)).(\lambda (H1: ((\forall (m: nat).((le 
d m) \to (eq nat (g (S m)) (f m)))))).(let TMP_12 \def (TLRef n) in (let 
TMP_13 \def (lift h d TMP_12) in (let TMP_14 \def (weight_map f TMP_13) in 
(let TMP_15 \def (S h) in (let TMP_16 \def (TLRef n) in (let TMP_17 \def 
(lift TMP_15 d TMP_16) in (let TMP_18 \def (weight_map g TMP_17) in (let 
TMP_19 \def (eq nat TMP_14 TMP_18) in (let TMP_45 \def (\lambda (H2: (lt n 
d)).(let TMP_20 \def (TLRef n) in (let TMP_26 \def (\lambda (t0: T).(let 
TMP_21 \def (weight_map f t0) in (let TMP_22 \def (S h) in (let TMP_23 \def 
(TLRef n) in (let TMP_24 \def (lift TMP_22 d TMP_23) in (let TMP_25 \def 
(weight_map g TMP_24) in (eq nat TMP_21 TMP_25))))))) in (let TMP_27 \def 
(TLRef n) in (let TMP_31 \def (\lambda (t0: T).(let TMP_28 \def (TLRef n) in 
(let TMP_29 \def (weight_map f TMP_28) in (let TMP_30 \def (weight_map g t0) 
in (eq nat TMP_29 TMP_30))))) in (let TMP_32 \def (g n) in (let TMP_33 \def 
(f n) in (let TMP_34 \def (H n H2) in (let TMP_35 \def (sym_eq nat TMP_32 
TMP_33 TMP_34) in (let TMP_36 \def (S h) in (let TMP_37 \def (TLRef n) in 
(let TMP_38 \def (lift TMP_36 d TMP_37) in (let TMP_39 \def (S h) in (let 
TMP_40 \def (lift_lref_lt n TMP_39 d H2) in (let TMP_41 \def (eq_ind_r T 
TMP_27 TMP_31 TMP_35 TMP_38 TMP_40) in (let TMP_42 \def (TLRef n) in (let 
TMP_43 \def (lift h d TMP_42) in (let TMP_44 \def (lift_lref_lt n h d H2) in 
(eq_ind_r T TMP_20 TMP_26 TMP_41 TMP_43 TMP_44))))))))))))))))))) in (let 
TMP_90 \def (\lambda (H2: (le d n)).(let TMP_46 \def (plus n h) in (let 
TMP_47 \def (TLRef TMP_46) in (let TMP_53 \def (\lambda (t0: T).(let TMP_48 
\def (weight_map f t0) in (let TMP_49 \def (S h) in (let TMP_50 \def (TLRef 
n) in (let TMP_51 \def (lift TMP_49 d TMP_50) in (let TMP_52 \def (weight_map 
g TMP_51) in (eq nat TMP_48 TMP_52))))))) in (let TMP_54 \def (S h) in (let 
TMP_55 \def (plus n TMP_54) in (let TMP_56 \def (TLRef TMP_55) in (let TMP_61 
\def (\lambda (t0: T).(let TMP_57 \def (plus n h) in (let TMP_58 \def (TLRef 
TMP_57) in (let TMP_59 \def (weight_map f TMP_58) in (let TMP_60 \def 
(weight_map g t0) in (eq nat TMP_59 TMP_60)))))) in (let TMP_62 \def (plus n 
h) in (let TMP_63 \def (S TMP_62) in (let TMP_67 \def (\lambda (n0: nat).(let 
TMP_64 \def (plus n h) in (let TMP_65 \def (f TMP_64) in (let TMP_66 \def (g 
n0) in (eq nat TMP_65 TMP_66))))) in (let TMP_68 \def (plus n h) in (let 
TMP_69 \def (S TMP_68) in (let TMP_70 \def (g TMP_69) in (let TMP_71 \def 
(plus n h) in (let TMP_72 \def (f TMP_71) in (let TMP_73 \def (plus n h) in 
(let TMP_74 \def (le_plus_trans d n h H2) in (let TMP_75 \def (H1 TMP_73 
TMP_74) in (let TMP_76 \def (sym_eq nat TMP_70 TMP_72 TMP_75) in (let TMP_77 
\def (S h) in (let TMP_78 \def (plus n TMP_77) in (let TMP_79 \def (plus_n_Sm 
n h) in (let TMP_80 \def (eq_ind nat TMP_63 TMP_67 TMP_76 TMP_78 TMP_79) in 
(let TMP_81 \def (S h) in (let TMP_82 \def (TLRef n) in (let TMP_83 \def 
(lift TMP_81 d TMP_82) in (let TMP_84 \def (S h) in (let TMP_85 \def 
(lift_lref_ge n TMP_84 d H2) in (let TMP_86 \def (eq_ind_r T TMP_56 TMP_61 
TMP_80 TMP_83 TMP_85) in (let TMP_87 \def (TLRef n) in (let TMP_88 \def (lift 
h d TMP_87) in (let TMP_89 \def (lift_lref_ge n h d H2) in (eq_ind_r T TMP_47 
TMP_53 TMP_86 TMP_88 TMP_89)))))))))))))))))))))))))))))))))) in (lt_le_e n d 
TMP_19 TMP_45 TMP_90))))))))))))))))))) in (let TMP_577 \def (\lambda (k: 
K).(\lambda (t0: T).(\lambda (H: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to 
(((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) \to (eq nat 
(weight_map f (lift h d t0)) (weight_map g (lift (S h) d 
t0)))))))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (h: nat).(\forall (d: 
nat).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).((lt m d) \to (eq nat (g m) (f m))))) \to ((eq nat (g d) w) \to 
(((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m))))) \to (eq nat 
(weight_map f (lift h d t1)) (weight_map g (lift (S h) d 
t1)))))))))))).(\lambda (h: nat).(\lambda (d: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (m: nat).((lt m 
d) \to (eq nat (g m) (f m)))))).(\lambda (H2: (eq nat (g d) w)).(\lambda (H3: 
((\forall (m: nat).((le d m) \to (eq nat (g (S m)) (f m)))))).(let TMP_99 
\def (\lambda (k0: K).(let TMP_92 \def (THead k0 t0 t1) in (let TMP_93 \def 
(lift h d TMP_92) in (let TMP_94 \def (weight_map f TMP_93) in (let TMP_95 
\def (S h) in (let TMP_96 \def (THead k0 t0 t1) in (let TMP_97 \def (lift 
TMP_95 d TMP_96) in (let TMP_98 \def (weight_map g TMP_97) in (eq nat TMP_94 
TMP_98))))))))) in (let TMP_506 \def (\lambda (b: B).(let TMP_100 \def (Bind 
b) in (let TMP_101 \def (lift h d t0) in (let TMP_102 \def (Bind b) in (let 
TMP_103 \def (s TMP_102 d) in (let TMP_104 \def (lift h TMP_103 t1) in (let 
TMP_105 \def (THead TMP_100 TMP_101 TMP_104) in (let TMP_112 \def (\lambda 
(t2: T).(let TMP_106 \def (weight_map f t2) in (let TMP_107 \def (S h) in 
(let TMP_108 \def (Bind b) in (let TMP_109 \def (THead TMP_108 t0 t1) in (let 
TMP_110 \def (lift TMP_107 d TMP_109) in (let TMP_111 \def (weight_map g 
TMP_110) in (eq nat TMP_106 TMP_111)))))))) in (let TMP_113 \def (Bind b) in 
(let TMP_114 \def (S h) in (let TMP_115 \def (lift TMP_114 d t0) in (let 
TMP_116 \def (S h) in (let TMP_117 \def (Bind b) in (let TMP_118 \def (s 
TMP_117 d) in (let TMP_119 \def (lift TMP_116 TMP_118 t1) in (let TMP_120 
\def (THead TMP_113 TMP_115 TMP_119) in (let TMP_129 \def (\lambda (t2: 
T).(let TMP_121 \def (Bind b) in (let TMP_122 \def (lift h d t0) in (let 
TMP_123 \def (Bind b) in (let TMP_124 \def (s TMP_123 d) in (let TMP_125 \def 
(lift h TMP_124 t1) in (let TMP_126 \def (THead TMP_121 TMP_122 TMP_125) in 
(let TMP_127 \def (weight_map f TMP_126) in (let TMP_128 \def (weight_map g 
t2) in (eq nat TMP_127 TMP_128)))))))))) in (let TMP_187 \def (\lambda (b0: 
B).(let TMP_154 \def (match b0 with [Abbr \Rightarrow (let TMP_144 \def (lift 
h d t0) in (let TMP_145 \def (weight_map f TMP_144) in (let TMP_146 \def 
(lift h d t0) in (let TMP_147 \def (weight_map f TMP_146) in (let TMP_148 
\def (S TMP_147) in (let TMP_149 \def (wadd f TMP_148) in (let TMP_150 \def 
(S d) in (let TMP_151 \def (lift h TMP_150 t1) in (let TMP_152 \def 
(weight_map TMP_149 TMP_151) in (let TMP_153 \def (plus TMP_145 TMP_152) in 
(S TMP_153))))))))))) | Abst \Rightarrow (let TMP_137 \def (lift h d t0) in 
(let TMP_138 \def (weight_map f TMP_137) in (let TMP_139 \def (wadd f O) in 
(let TMP_140 \def (S d) in (let TMP_141 \def (lift h TMP_140 t1) in (let 
TMP_142 \def (weight_map TMP_139 TMP_141) in (let TMP_143 \def (plus TMP_138 
TMP_142) in (S TMP_143)))))))) | Void \Rightarrow (let TMP_130 \def (lift h d 
t0) in (let TMP_131 \def (weight_map f TMP_130) in (let TMP_132 \def (wadd f 
O) in (let TMP_133 \def (S d) in (let TMP_134 \def (lift h TMP_133 t1) in 
(let TMP_135 \def (weight_map TMP_132 TMP_134) in (let TMP_136 \def (plus 
TMP_131 TMP_135) in (S TMP_136))))))))]) in (let TMP_186 \def (match b0 with 
[Abbr \Rightarrow (let TMP_173 \def (S h) in (let TMP_174 \def (lift TMP_173 
d t0) in (let TMP_175 \def (weight_map g TMP_174) in (let TMP_176 \def (S h) 
in (let TMP_177 \def (lift TMP_176 d t0) in (let TMP_178 \def (weight_map g 
TMP_177) in (let TMP_179 \def (S TMP_178) in (let TMP_180 \def (wadd g 
TMP_179) in (let TMP_181 \def (S h) in (let TMP_182 \def (S d) in (let 
TMP_183 \def (lift TMP_181 TMP_182 t1) in (let TMP_184 \def (weight_map 
TMP_180 TMP_183) in (let TMP_185 \def (plus TMP_175 TMP_184) in (S 
TMP_185)))))))))))))) | Abst \Rightarrow (let TMP_164 \def (S h) in (let 
TMP_165 \def (lift TMP_164 d t0) in (let TMP_166 \def (weight_map g TMP_165) 
in (let TMP_167 \def (wadd g O) in (let TMP_168 \def (S h) in (let TMP_169 
\def (S d) in (let TMP_170 \def (lift TMP_168 TMP_169 t1) in (let TMP_171 
\def (weight_map TMP_167 TMP_170) in (let TMP_172 \def (plus TMP_166 TMP_171) 
in (S TMP_172)))))))))) | Void \Rightarrow (let TMP_155 \def (S h) in (let 
TMP_156 \def (lift TMP_155 d t0) in (let TMP_157 \def (weight_map g TMP_156) 
in (let TMP_158 \def (wadd g O) in (let TMP_159 \def (S h) in (let TMP_160 
\def (S d) in (let TMP_161 \def (lift TMP_159 TMP_160 t1) in (let TMP_162 
\def (weight_map TMP_158 TMP_161) in (let TMP_163 \def (plus TMP_157 TMP_162) 
in (S TMP_163))))))))))]) in (eq nat TMP_154 TMP_186)))) in (let TMP_188 \def 
(lift h d t0) in (let TMP_189 \def (weight_map f TMP_188) in (let TMP_190 
\def (lift h d t0) in (let TMP_191 \def (weight_map f TMP_190) in (let 
TMP_192 \def (S TMP_191) in (let TMP_193 \def (wadd f TMP_192) in (let 
TMP_194 \def (S d) in (let TMP_195 \def (lift h TMP_194 t1) in (let TMP_196 
\def (weight_map TMP_193 TMP_195) in (let TMP_197 \def (plus TMP_189 TMP_196) 
in (let TMP_198 \def (S h) in (let TMP_199 \def (lift TMP_198 d t0) in (let 
TMP_200 \def (weight_map g TMP_199) in (let TMP_201 \def (S h) in (let 
TMP_202 \def (lift TMP_201 d t0) in (let TMP_203 \def (weight_map g TMP_202) 
in (let TMP_204 \def (S TMP_203) in (let TMP_205 \def (wadd g TMP_204) in 
(let TMP_206 \def (S h) in (let TMP_207 \def (S d) in (let TMP_208 \def (lift 
TMP_206 TMP_207 t1) in (let TMP_209 \def (weight_map TMP_205 TMP_208) in (let 
TMP_210 \def (plus TMP_200 TMP_209) in (let TMP_211 \def (lift h d t0) in 
(let TMP_212 \def (weight_map f TMP_211) in (let TMP_213 \def (S h) in (let 
TMP_214 \def (lift TMP_213 d t0) in (let TMP_215 \def (weight_map g TMP_214) 
in (let TMP_216 \def (lift h d t0) in (let TMP_217 \def (weight_map f 
TMP_216) in (let TMP_218 \def (S TMP_217) in (let TMP_219 \def (wadd f 
TMP_218) in (let TMP_220 \def (S d) in (let TMP_221 \def (lift h TMP_220 t1) 
in (let TMP_222 \def (weight_map TMP_219 TMP_221) in (let TMP_223 \def (S h) 
in (let TMP_224 \def (lift TMP_223 d t0) in (let TMP_225 \def (weight_map g 
TMP_224) in (let TMP_226 \def (S TMP_225) in (let TMP_227 \def (wadd g 
TMP_226) in (let TMP_228 \def (S h) in (let TMP_229 \def (S d) in (let 
TMP_230 \def (lift TMP_228 TMP_229 t1) in (let TMP_231 \def (weight_map 
TMP_227 TMP_230) in (let TMP_232 \def (H h d f g H1 H2 H3) in (let TMP_233 
\def (S d) in (let TMP_234 \def (lift h d t0) in (let TMP_235 \def 
(weight_map f TMP_234) in (let TMP_236 \def (S TMP_235) in (let TMP_237 \def 
(wadd f TMP_236) in (let TMP_238 \def (S h) in (let TMP_239 \def (lift 
TMP_238 d t0) in (let TMP_240 \def (weight_map g TMP_239) in (let TMP_241 
\def (S TMP_240) in (let TMP_242 \def (wadd g TMP_241) in (let TMP_310 \def 
(\lambda (m: nat).(\lambda (H4: (lt m (S d))).(let TMP_243 \def (eq nat m O) 
in (let TMP_245 \def (\lambda (m0: nat).(let TMP_244 \def (S m0) in (eq nat m 
TMP_244))) in (let TMP_246 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_247 
\def (ex2 nat TMP_245 TMP_246) in (let TMP_248 \def (S h) in (let TMP_249 
\def (lift TMP_248 d t0) in (let TMP_250 \def (weight_map g TMP_249) in (let 
TMP_251 \def (S TMP_250) in (let TMP_252 \def (wadd g TMP_251 m) in (let 
TMP_253 \def (lift h d t0) in (let TMP_254 \def (weight_map f TMP_253) in 
(let TMP_255 \def (S TMP_254) in (let TMP_256 \def (wadd f TMP_255 m) in (let 
TMP_257 \def (eq nat TMP_252 TMP_256) in (let TMP_281 \def (\lambda (H5: (eq 
nat m O)).(let TMP_267 \def (\lambda (n: nat).(let TMP_258 \def (S h) in (let 
TMP_259 \def (lift TMP_258 d t0) in (let TMP_260 \def (weight_map g TMP_259) 
in (let TMP_261 \def (S TMP_260) in (let TMP_262 \def (wadd g TMP_261 n) in 
(let TMP_263 \def (lift h d t0) in (let TMP_264 \def (weight_map f TMP_263) 
in (let TMP_265 \def (S TMP_264) in (let TMP_266 \def (wadd f TMP_265 n) in 
(eq nat TMP_262 TMP_266))))))))))) in (let TMP_268 \def (S h) in (let TMP_269 
\def (lift TMP_268 d t0) in (let TMP_270 \def (weight_map g TMP_269) in (let 
TMP_271 \def (lift h d t0) in (let TMP_272 \def (weight_map f TMP_271) in 
(let TMP_273 \def (lift h d t0) in (let TMP_274 \def (weight_map f TMP_273) 
in (let TMP_275 \def (S h) in (let TMP_276 \def (lift TMP_275 d t0) in (let 
TMP_277 \def (weight_map g TMP_276) in (let TMP_278 \def (H h d f g H1 H2 H3) 
in (let TMP_279 \def (sym_eq nat TMP_274 TMP_277 TMP_278) in (let TMP_280 
\def (f_equal nat nat S TMP_270 TMP_272 TMP_279) in (eq_ind_r nat O TMP_267 
TMP_280 m H5)))))))))))))))) in (let TMP_308 \def (\lambda (H5: (ex2 nat 
(\lambda (m0: nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d)))).(let 
TMP_283 \def (\lambda (m0: nat).(let TMP_282 \def (S m0) in (eq nat m 
TMP_282))) in (let TMP_284 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_285 
\def (S h) in (let TMP_286 \def (lift TMP_285 d t0) in (let TMP_287 \def 
(weight_map g TMP_286) in (let TMP_288 \def (S TMP_287) in (let TMP_289 \def 
(wadd g TMP_288 m) in (let TMP_290 \def (lift h d t0) in (let TMP_291 \def 
(weight_map f TMP_290) in (let TMP_292 \def (S TMP_291) in (let TMP_293 \def 
(wadd f TMP_292 m) in (let TMP_294 \def (eq nat TMP_289 TMP_293) in (let 
TMP_307 \def (\lambda (x: nat).(\lambda (H6: (eq nat m (S x))).(\lambda (H7: 
(lt x d)).(let TMP_295 \def (S x) in (let TMP_305 \def (\lambda (n: nat).(let 
TMP_296 \def (S h) in (let TMP_297 \def (lift TMP_296 d t0) in (let TMP_298 
\def (weight_map g TMP_297) in (let TMP_299 \def (S TMP_298) in (let TMP_300 
\def (wadd g TMP_299 n) in (let TMP_301 \def (lift h d t0) in (let TMP_302 
\def (weight_map f TMP_301) in (let TMP_303 \def (S TMP_302) in (let TMP_304 
\def (wadd f TMP_303 n) in (eq nat TMP_300 TMP_304))))))))))) in (let TMP_306 
\def (H1 x H7) in (eq_ind_r nat TMP_295 TMP_305 TMP_306 m H6))))))) in 
(ex2_ind nat TMP_283 TMP_284 TMP_294 TMP_307 H5))))))))))))))) in (let 
TMP_309 \def (lt_gen_xS m d H4) in (or_ind TMP_243 TMP_247 TMP_257 TMP_281 
TMP_308 TMP_309)))))))))))))))))))) in (let TMP_330 \def (\lambda (m: 
nat).(\lambda (H4: (le (S d) m)).(let TMP_312 \def (\lambda (n: nat).(let 
TMP_311 \def (S n) in (eq nat m TMP_311))) in (let TMP_313 \def (\lambda (n: 
nat).(le d n)) in (let TMP_314 \def (g m) in (let TMP_315 \def (lift h d t0) 
in (let TMP_316 \def (weight_map f TMP_315) in (let TMP_317 \def (S TMP_316) 
in (let TMP_318 \def (wadd f TMP_317 m) in (let TMP_319 \def (eq nat TMP_314 
TMP_318) in (let TMP_328 \def (\lambda (x: nat).(\lambda (H5: (eq nat m (S 
x))).(\lambda (H6: (le d x)).(let TMP_320 \def (S x) in (let TMP_326 \def 
(\lambda (n: nat).(let TMP_321 \def (g n) in (let TMP_322 \def (lift h d t0) 
in (let TMP_323 \def (weight_map f TMP_322) in (let TMP_324 \def (S TMP_323) 
in (let TMP_325 \def (wadd f TMP_324 n) in (eq nat TMP_321 TMP_325))))))) in 
(let TMP_327 \def (H3 x H6) in (eq_ind_r nat TMP_320 TMP_326 TMP_327 m 
H5))))))) in (let TMP_329 \def (le_gen_S d m H4) in (ex2_ind nat TMP_312 
TMP_313 TMP_319 TMP_328 TMP_329))))))))))))) in (let TMP_331 \def (H0 h 
TMP_233 TMP_237 TMP_242 TMP_310 H2 TMP_330) in (let TMP_332 \def (f_equal2 
nat nat nat plus TMP_212 TMP_215 TMP_222 TMP_231 TMP_232 TMP_331) in (let 
TMP_333 \def (f_equal nat nat S TMP_197 TMP_210 TMP_332) in (let TMP_334 \def 
(lift h d t0) in (let TMP_335 \def (weight_map f TMP_334) in (let TMP_336 
\def (wadd f O) in (let TMP_337 \def (S d) in (let TMP_338 \def (lift h 
TMP_337 t1) in (let TMP_339 \def (weight_map TMP_336 TMP_338) in (let TMP_340 
\def (plus TMP_335 TMP_339) in (let TMP_341 \def (S h) in (let TMP_342 \def 
(lift TMP_341 d t0) in (let TMP_343 \def (weight_map g TMP_342) in (let 
TMP_344 \def (wadd g O) in (let TMP_345 \def (S h) in (let TMP_346 \def (S d) 
in (let TMP_347 \def (lift TMP_345 TMP_346 t1) in (let TMP_348 \def 
(weight_map TMP_344 TMP_347) in (let TMP_349 \def (plus TMP_343 TMP_348) in 
(let TMP_350 \def (lift h d t0) in (let TMP_351 \def (weight_map f TMP_350) 
in (let TMP_352 \def (S h) in (let TMP_353 \def (lift TMP_352 d t0) in (let 
TMP_354 \def (weight_map g TMP_353) in (let TMP_355 \def (wadd f O) in (let 
TMP_356 \def (S d) in (let TMP_357 \def (lift h TMP_356 t1) in (let TMP_358 
\def (weight_map TMP_355 TMP_357) in (let TMP_359 \def (wadd g O) in (let 
TMP_360 \def (S h) in (let TMP_361 \def (S d) in (let TMP_362 \def (lift 
TMP_360 TMP_361 t1) in (let TMP_363 \def (weight_map TMP_359 TMP_362) in (let 
TMP_364 \def (H h d f g H1 H2 H3) in (let TMP_365 \def (S d) in (let TMP_366 
\def (wadd f O) in (let TMP_367 \def (wadd g O) in (let TMP_395 \def (\lambda 
(m: nat).(\lambda (H4: (lt m (S d))).(let TMP_368 \def (eq nat m O) in (let 
TMP_370 \def (\lambda (m0: nat).(let TMP_369 \def (S m0) in (eq nat m 
TMP_369))) in (let TMP_371 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_372 
\def (ex2 nat TMP_370 TMP_371) in (let TMP_373 \def (wadd g O m) in (let 
TMP_374 \def (wadd f O m) in (let TMP_375 \def (eq nat TMP_373 TMP_374) in 
(let TMP_380 \def (\lambda (H5: (eq nat m O)).(let TMP_378 \def (\lambda (n: 
nat).(let TMP_376 \def (wadd g O n) in (let TMP_377 \def (wadd f O n) in (eq 
nat TMP_376 TMP_377)))) in (let TMP_379 \def (refl_equal nat O) in (eq_ind_r 
nat O TMP_378 TMP_379 m H5)))) in (let TMP_393 \def (\lambda (H5: (ex2 nat 
(\lambda (m0: nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d)))).(let 
TMP_382 \def (\lambda (m0: nat).(let TMP_381 \def (S m0) in (eq nat m 
TMP_381))) in (let TMP_383 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_384 
\def (wadd g O m) in (let TMP_385 \def (wadd f O m) in (let TMP_386 \def (eq 
nat TMP_384 TMP_385) in (let TMP_392 \def (\lambda (x: nat).(\lambda (H6: (eq 
nat m (S x))).(\lambda (H7: (lt x d)).(let TMP_387 \def (S x) in (let TMP_390 
\def (\lambda (n: nat).(let TMP_388 \def (wadd g O n) in (let TMP_389 \def 
(wadd f O n) in (eq nat TMP_388 TMP_389)))) in (let TMP_391 \def (H1 x H7) in 
(eq_ind_r nat TMP_387 TMP_390 TMP_391 m H6))))))) in (ex2_ind nat TMP_382 
TMP_383 TMP_386 TMP_392 H5)))))))) in (let TMP_394 \def (lt_gen_xS m d H4) in 
(or_ind TMP_368 TMP_372 TMP_375 TMP_380 TMP_393 TMP_394))))))))))))) in (let 
TMP_409 \def (\lambda (m: nat).(\lambda (H4: (le (S d) m)).(let TMP_397 \def 
(\lambda (n: nat).(let TMP_396 \def (S n) in (eq nat m TMP_396))) in (let 
TMP_398 \def (\lambda (n: nat).(le d n)) in (let TMP_399 \def (g m) in (let 
TMP_400 \def (wadd f O m) in (let TMP_401 \def (eq nat TMP_399 TMP_400) in 
(let TMP_407 \def (\lambda (x: nat).(\lambda (H5: (eq nat m (S x))).(\lambda 
(H6: (le d x)).(let TMP_402 \def (S x) in (let TMP_405 \def (\lambda (n: 
nat).(let TMP_403 \def (g n) in (let TMP_404 \def (wadd f O n) in (eq nat 
TMP_403 TMP_404)))) in (let TMP_406 \def (H3 x H6) in (eq_ind_r nat TMP_402 
TMP_405 TMP_406 m H5))))))) in (let TMP_408 \def (le_gen_S d m H4) in 
(ex2_ind nat TMP_397 TMP_398 TMP_401 TMP_407 TMP_408)))))))))) in (let 
TMP_410 \def (H0 h TMP_365 TMP_366 TMP_367 TMP_395 H2 TMP_409) in (let 
TMP_411 \def (f_equal2 nat nat nat plus TMP_351 TMP_354 TMP_358 TMP_363 
TMP_364 TMP_410) in (let TMP_412 \def (f_equal nat nat S TMP_340 TMP_349 
TMP_411) in (let TMP_413 \def (lift h d t0) in (let TMP_414 \def (weight_map 
f TMP_413) in (let TMP_415 \def (wadd f O) in (let TMP_416 \def (S d) in (let 
TMP_417 \def (lift h TMP_416 t1) in (let TMP_418 \def (weight_map TMP_415 
TMP_417) in (let TMP_419 \def (plus TMP_414 TMP_418) in (let TMP_420 \def (S 
h) in (let TMP_421 \def (lift TMP_420 d t0) in (let TMP_422 \def (weight_map 
g TMP_421) in (let TMP_423 \def (wadd g O) in (let TMP_424 \def (S h) in (let 
TMP_425 \def (S d) in (let TMP_426 \def (lift TMP_424 TMP_425 t1) in (let 
TMP_427 \def (weight_map TMP_423 TMP_426) in (let TMP_428 \def (plus TMP_422 
TMP_427) in (let TMP_429 \def (lift h d t0) in (let TMP_430 \def (weight_map 
f TMP_429) in (let TMP_431 \def (S h) in (let TMP_432 \def (lift TMP_431 d 
t0) in (let TMP_433 \def (weight_map g TMP_432) in (let TMP_434 \def (wadd f 
O) in (let TMP_435 \def (S d) in (let TMP_436 \def (lift h TMP_435 t1) in 
(let TMP_437 \def (weight_map TMP_434 TMP_436) in (let TMP_438 \def (wadd g 
O) in (let TMP_439 \def (S h) in (let TMP_440 \def (S d) in (let TMP_441 \def 
(lift TMP_439 TMP_440 t1) in (let TMP_442 \def (weight_map TMP_438 TMP_441) 
in (let TMP_443 \def (H h d f g H1 H2 H3) in (let TMP_444 \def (S d) in (let 
TMP_445 \def (wadd f O) in (let TMP_446 \def (wadd g O) in (let TMP_474 \def 
(\lambda (m: nat).(\lambda (H4: (lt m (S d))).(let TMP_447 \def (eq nat m O) 
in (let TMP_449 \def (\lambda (m0: nat).(let TMP_448 \def (S m0) in (eq nat m 
TMP_448))) in (let TMP_450 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_451 
\def (ex2 nat TMP_449 TMP_450) in (let TMP_452 \def (wadd g O m) in (let 
TMP_453 \def (wadd f O m) in (let TMP_454 \def (eq nat TMP_452 TMP_453) in 
(let TMP_459 \def (\lambda (H5: (eq nat m O)).(let TMP_457 \def (\lambda (n: 
nat).(let TMP_455 \def (wadd g O n) in (let TMP_456 \def (wadd f O n) in (eq 
nat TMP_455 TMP_456)))) in (let TMP_458 \def (refl_equal nat O) in (eq_ind_r 
nat O TMP_457 TMP_458 m H5)))) in (let TMP_472 \def (\lambda (H5: (ex2 nat 
(\lambda (m0: nat).(eq nat m (S m0))) (\lambda (m0: nat).(lt m0 d)))).(let 
TMP_461 \def (\lambda (m0: nat).(let TMP_460 \def (S m0) in (eq nat m 
TMP_460))) in (let TMP_462 \def (\lambda (m0: nat).(lt m0 d)) in (let TMP_463 
\def (wadd g O m) in (let TMP_464 \def (wadd f O m) in (let TMP_465 \def (eq 
nat TMP_463 TMP_464) in (let TMP_471 \def (\lambda (x: nat).(\lambda (H6: (eq 
nat m (S x))).(\lambda (H7: (lt x d)).(let TMP_466 \def (S x) in (let TMP_469 
\def (\lambda (n: nat).(let TMP_467 \def (wadd g O n) in (let TMP_468 \def 
(wadd f O n) in (eq nat TMP_467 TMP_468)))) in (let TMP_470 \def (H1 x H7) in 
(eq_ind_r nat TMP_466 TMP_469 TMP_470 m H6))))))) in (ex2_ind nat TMP_461 
TMP_462 TMP_465 TMP_471 H5)))))))) in (let TMP_473 \def (lt_gen_xS m d H4) in 
(or_ind TMP_447 TMP_451 TMP_454 TMP_459 TMP_472 TMP_473))))))))))))) in (let 
TMP_488 \def (\lambda (m: nat).(\lambda (H4: (le (S d) m)).(let TMP_476 \def 
(\lambda (n: nat).(let TMP_475 \def (S n) in (eq nat m TMP_475))) in (let 
TMP_477 \def (\lambda (n: nat).(le d n)) in (let TMP_478 \def (g m) in (let 
TMP_479 \def (wadd f O m) in (let TMP_480 \def (eq nat TMP_478 TMP_479) in 
(let TMP_486 \def (\lambda (x: nat).(\lambda (H5: (eq nat m (S x))).(\lambda 
(H6: (le d x)).(let TMP_481 \def (S x) in (let TMP_484 \def (\lambda (n: 
nat).(let TMP_482 \def (g n) in (let TMP_483 \def (wadd f O n) in (eq nat 
TMP_482 TMP_483)))) in (let TMP_485 \def (H3 x H6) in (eq_ind_r nat TMP_481 
TMP_484 TMP_485 m H5))))))) in (let TMP_487 \def (le_gen_S d m H4) in 
(ex2_ind nat TMP_476 TMP_477 TMP_480 TMP_486 TMP_487)))))))))) in (let 
TMP_489 \def (H0 h TMP_444 TMP_445 TMP_446 TMP_474 H2 TMP_488) in (let 
TMP_490 \def (f_equal2 nat nat nat plus TMP_430 TMP_433 TMP_437 TMP_442 
TMP_443 TMP_489) in (let TMP_491 \def (f_equal nat nat S TMP_419 TMP_428 
TMP_490) in (let TMP_492 \def (B_ind TMP_187 TMP_333 TMP_412 TMP_491 b) in 
(let TMP_493 \def (S h) in (let TMP_494 \def (Bind b) in (let TMP_495 \def 
(THead TMP_494 t0 t1) in (let TMP_496 \def (lift TMP_493 d TMP_495) in (let 
TMP_497 \def (Bind b) in (let TMP_498 \def (S h) in (let TMP_499 \def 
(lift_head TMP_497 t0 t1 TMP_498 d) in (let TMP_500 \def (eq_ind_r T TMP_120 
TMP_129 TMP_492 TMP_496 TMP_499) in (let TMP_501 \def (Bind b) in (let 
TMP_502 \def (THead TMP_501 t0 t1) in (let TMP_503 \def (lift h d TMP_502) in 
(let TMP_504 \def (Bind b) in (let TMP_505 \def (lift_head TMP_504 t0 t1 h d) 
in (eq_ind_r T TMP_105 TMP_112 TMP_500 TMP_503 
TMP_505)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))))))))))) in (let TMP_576 \def (\lambda (f0: F).(let TMP_507 
\def (Flat f0) in (let TMP_508 \def (lift h d t0) in (let TMP_509 \def (Flat 
f0) in (let TMP_510 \def (s TMP_509 d) in (let TMP_511 \def (lift h TMP_510 
t1) in (let TMP_512 \def (THead TMP_507 TMP_508 TMP_511) in (let TMP_519 \def 
(\lambda (t2: T).(let TMP_513 \def (weight_map f t2) in (let TMP_514 \def (S 
h) in (let TMP_515 \def (Flat f0) in (let TMP_516 \def (THead TMP_515 t0 t1) 
in (let TMP_517 \def (lift TMP_514 d TMP_516) in (let TMP_518 \def 
(weight_map g TMP_517) in (eq nat TMP_513 TMP_518)))))))) in (let TMP_520 
\def (Flat f0) in (let TMP_521 \def (S h) in (let TMP_522 \def (lift TMP_521 
d t0) in (let TMP_523 \def (S h) in (let TMP_524 \def (Flat f0) in (let 
TMP_525 \def (s TMP_524 d) in (let TMP_526 \def (lift TMP_523 TMP_525 t1) in 
(let TMP_527 \def (THead TMP_520 TMP_522 TMP_526) in (let TMP_536 \def 
(\lambda (t2: T).(let TMP_528 \def (Flat f0) in (let TMP_529 \def (lift h d 
t0) in (let TMP_530 \def (Flat f0) in (let TMP_531 \def (s TMP_530 d) in (let 
TMP_532 \def (lift h TMP_531 t1) in (let TMP_533 \def (THead TMP_528 TMP_529 
TMP_532) in (let TMP_534 \def (weight_map f TMP_533) in (let TMP_535 \def 
(weight_map g t2) in (eq nat TMP_534 TMP_535)))))))))) in (let TMP_537 \def 
(lift h d t0) in (let TMP_538 \def (weight_map f TMP_537) in (let TMP_539 
\def (lift h d t1) in (let TMP_540 \def (weight_map f TMP_539) in (let 
TMP_541 \def (plus TMP_538 TMP_540) in (let TMP_542 \def (S h) in (let 
TMP_543 \def (lift TMP_542 d t0) in (let TMP_544 \def (weight_map g TMP_543) 
in (let TMP_545 \def (S h) in (let TMP_546 \def (lift TMP_545 d t1) in (let 
TMP_547 \def (weight_map g TMP_546) in (let TMP_548 \def (plus TMP_544 
TMP_547) in (let TMP_549 \def (lift h d t0) in (let TMP_550 \def (weight_map 
f TMP_549) in (let TMP_551 \def (S h) in (let TMP_552 \def (lift TMP_551 d 
t0) in (let TMP_553 \def (weight_map g TMP_552) in (let TMP_554 \def (lift h 
d t1) in (let TMP_555 \def (weight_map f TMP_554) in (let TMP_556 \def (S h) 
in (let TMP_557 \def (lift TMP_556 d t1) in (let TMP_558 \def (weight_map g 
TMP_557) in (let TMP_559 \def (H h d f g H1 H2 H3) in (let TMP_560 \def (H0 h 
d f g H1 H2 H3) in (let TMP_561 \def (f_equal2 nat nat nat plus TMP_550 
TMP_553 TMP_555 TMP_558 TMP_559 TMP_560) in (let TMP_562 \def (f_equal nat 
nat S TMP_541 TMP_548 TMP_561) in (let TMP_563 \def (S h) in (let TMP_564 
\def (Flat f0) in (let TMP_565 \def (THead TMP_564 t0 t1) in (let TMP_566 
\def (lift TMP_563 d TMP_565) in (let TMP_567 \def (Flat f0) in (let TMP_568 
\def (S h) in (let TMP_569 \def (lift_head TMP_567 t0 t1 TMP_568 d) in (let 
TMP_570 \def (eq_ind_r T TMP_527 TMP_536 TMP_562 TMP_566 TMP_569) in (let 
TMP_571 \def (Flat f0) in (let TMP_572 \def (THead TMP_571 t0 t1) in (let 
TMP_573 \def (lift h d TMP_572) in (let TMP_574 \def (Flat f0) in (let 
TMP_575 \def (lift_head TMP_574 t0 t1 h d) in (eq_ind_r T TMP_512 TMP_519 
TMP_570 TMP_573 
TMP_575))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (K_ind 
TMP_99 TMP_506 TMP_576 k)))))))))))))))) in (T_ind TMP_6 TMP_11 TMP_91 
TMP_577 t)))))).

theorem lift_weight_add_O:
 \forall (w: nat).(\forall (t: T).(\forall (h: nat).(\forall (f: ((nat \to 
nat))).(eq nat (weight_map f (lift h O t)) (weight_map (wadd f w) (lift (S h) 
O t))))))
\def
 \lambda (w: nat).(\lambda (t: T).(\lambda (h: nat).(\lambda (f: ((nat \to 
nat))).(let TMP_1 \def (wadd f w O) in (let TMP_2 \def (minus TMP_1 O) in 
(let TMP_3 \def (wadd f w) in (let TMP_7 \def (\lambda (m: nat).(\lambda (H: 
(lt m O)).(let TMP_4 \def (wadd f w m) in (let TMP_5 \def (f m) in (let TMP_6 
\def (eq nat TMP_4 TMP_5) in (lt_x_O m H TMP_6)))))) in (let TMP_8 \def (wadd 
f w O) in (let TMP_9 \def (minus_n_O TMP_8) in (let TMP_11 \def (\lambda (m: 
nat).(\lambda (_: (le O m)).(let TMP_10 \def (f m) in (refl_equal nat 
TMP_10)))) in (lift_weight_add TMP_2 t h O f TMP_3 TMP_7 TMP_9 
TMP_11))))))))))).

theorem lift_tlt_dx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (h: nat).(\forall 
(d: nat).(tlt t (THead k u (lift h d t)))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (h: nat).(\lambda 
(d: nat).(let TMP_1 \def (lift h d t) in (let TMP_2 \def (weight TMP_1) in 
(let TMP_6 \def (\lambda (n: nat).(let TMP_3 \def (lift h d t) in (let TMP_4 
\def (THead k u TMP_3) in (let TMP_5 \def (weight TMP_4) in (lt n TMP_5))))) 
in (let TMP_7 \def (lift h d t) in (let TMP_8 \def (tlt_head_dx k u TMP_7) in 
(let TMP_9 \def (weight t) in (let TMP_10 \def (lift_weight t h d) in (eq_ind 
nat TMP_2 TMP_6 TMP_8 TMP_9 TMP_10)))))))))))).

