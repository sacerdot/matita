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

include "basic_1/subst0/fwd.ma".

include "basic_1/lift/tlt.ma".

theorem subst0_weight_le:
 \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d 
u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
d) O u)) (g d)) \to (le (weight_map f z) (weight_map g t))))))))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d u t z)).(let TMP_3 \def (\lambda (n: nat).(\lambda (t0: 
T).(\lambda (t1: T).(\lambda (t2: T).(\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S n) O t0)) (g n)) \to (let TMP_1 \def (weight_map f t2) 
in (let TMP_2 \def (weight_map g t1) in (le TMP_1 TMP_2))))))))))) in (let 
TMP_33 \def (\lambda (v: T).(\lambda (i: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H1: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_4 \def (S i) in (let TMP_5 \def (lift TMP_4 O v) in (let TMP_6 \def 
(weight_map f TMP_5) in (let TMP_7 \def (TLRef i) in (let TMP_8 \def 
(weight_map g TMP_7) in (let TMP_9 \def (S i) in (let TMP_10 \def (lift TMP_9 
O v) in (let TMP_11 \def (weight_map f TMP_10) in (let TMP_12 \def (S TMP_11) 
in (let TMP_13 \def (TLRef i) in (let TMP_14 \def (weight_map g TMP_13) in 
(let TMP_15 \def (S TMP_14) in (let TMP_16 \def (S i) in (let TMP_17 \def 
(lift TMP_16 O v) in (let TMP_18 \def (weight_map f TMP_17) in (let TMP_19 
\def (S TMP_18) in (let TMP_20 \def (S TMP_19) in (let TMP_21 \def (TLRef i) 
in (let TMP_22 \def (weight_map g TMP_21) in (let TMP_23 \def (S TMP_22) in 
(let TMP_24 \def (S i) in (let TMP_25 \def (lift TMP_24 O v) in (let TMP_26 
\def (weight_map f TMP_25) in (let TMP_27 \def (S TMP_26) in (let TMP_28 \def 
(TLRef i) in (let TMP_29 \def (weight_map g TMP_28) in (let TMP_30 \def 
(le_n_S TMP_27 TMP_29 H1) in (let TMP_31 \def (le_S TMP_20 TMP_23 TMP_30) in 
(let TMP_32 \def (le_S_n TMP_12 TMP_15 TMP_31) in (le_S_n TMP_6 TMP_8 
TMP_32)))))))))))))))))))))))))))))))))))) in (let TMP_146 \def (\lambda (v: 
T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v u1 u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (le (weight_map f u2) (weight_map g u1)))))))).(\lambda 
(t0: T).(\lambda (k: K).(let TMP_38 \def (\lambda (k0: K).(\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g 
m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (let TMP_34 \def 
(THead k0 u2 t0) in (let TMP_35 \def (weight_map f TMP_34) in (let TMP_36 
\def (THead k0 u1 t0) in (let TMP_37 \def (weight_map g TMP_36) in (le TMP_35 
TMP_37)))))))))) in (let TMP_131 \def (\lambda (b: B).(let TMP_45 \def 
(\lambda (b0: B).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (let TMP_39 \def (Bind b0) in (let TMP_40 \def (THead 
TMP_39 u2 t0) in (let TMP_41 \def (weight_map f TMP_40) in (let TMP_42 \def 
(Bind b0) in (let TMP_43 \def (THead TMP_42 u1 t0) in (let TMP_44 \def 
(weight_map g TMP_43) in (le TMP_41 TMP_44)))))))))))) in (let TMP_86 \def 
(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: 
((\forall (m: nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift 
(S i) O v)) (g i))).(let TMP_46 \def (weight_map f u2) in (let TMP_47 \def 
(weight_map f u2) in (let TMP_48 \def (S TMP_47) in (let TMP_49 \def (wadd f 
TMP_48) in (let TMP_50 \def (weight_map TMP_49 t0) in (let TMP_51 \def (plus 
TMP_46 TMP_50) in (let TMP_52 \def (weight_map g u1) in (let TMP_53 \def 
(weight_map g u1) in (let TMP_54 \def (S TMP_53) in (let TMP_55 \def (wadd g 
TMP_54) in (let TMP_56 \def (weight_map TMP_55 t0) in (let TMP_57 \def (plus 
TMP_52 TMP_56) in (let TMP_58 \def (weight_map f u2) in (let TMP_59 \def 
(weight_map g u1) in (let TMP_60 \def (weight_map f u2) in (let TMP_61 \def 
(S TMP_60) in (let TMP_62 \def (wadd f TMP_61) in (let TMP_63 \def 
(weight_map TMP_62 t0) in (let TMP_64 \def (weight_map g u1) in (let TMP_65 
\def (S TMP_64) in (let TMP_66 \def (wadd g TMP_65) in (let TMP_67 \def 
(weight_map TMP_66 t0) in (let TMP_68 \def (H1 f g H2 H3) in (let TMP_69 \def 
(weight_map f u2) in (let TMP_70 \def (S TMP_69) in (let TMP_71 \def (wadd f 
TMP_70) in (let TMP_72 \def (weight_map g u1) in (let TMP_73 \def (S TMP_72) 
in (let TMP_74 \def (wadd g TMP_73) in (let TMP_83 \def (\lambda (n: 
nat).(let TMP_75 \def (weight_map f u2) in (let TMP_76 \def (S TMP_75) in 
(let TMP_77 \def (weight_map g u1) in (let TMP_78 \def (S TMP_77) in (let 
TMP_79 \def (weight_map f u2) in (let TMP_80 \def (weight_map g u1) in (let 
TMP_81 \def (H1 f g H2 H3) in (let TMP_82 \def (le_n_S TMP_79 TMP_80 TMP_81) 
in (wadd_le f g H2 TMP_76 TMP_78 TMP_82 n)))))))))) in (let TMP_84 \def 
(weight_le t0 TMP_71 TMP_74 TMP_83) in (let TMP_85 \def (le_plus_plus TMP_58 
TMP_59 TMP_63 TMP_67 TMP_68 TMP_84) in (le_n_S TMP_51 TMP_57 
TMP_85))))))))))))))))))))))))))))))))))))) in (let TMP_108 \def (\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_87 \def (weight_map f u2) in (let TMP_88 \def (wadd f O) in 
(let TMP_89 \def (weight_map TMP_88 t0) in (let TMP_90 \def (plus TMP_87 
TMP_89) in (let TMP_91 \def (weight_map g u1) in (let TMP_92 \def (wadd g O) 
in (let TMP_93 \def (weight_map TMP_92 t0) in (let TMP_94 \def (plus TMP_91 
TMP_93) in (let TMP_95 \def (weight_map f u2) in (let TMP_96 \def (weight_map 
g u1) in (let TMP_97 \def (wadd f O) in (let TMP_98 \def (weight_map TMP_97 
t0) in (let TMP_99 \def (wadd g O) in (let TMP_100 \def (weight_map TMP_99 
t0) in (let TMP_101 \def (H1 f g H2 H3) in (let TMP_102 \def (wadd f O) in 
(let TMP_103 \def (wadd g O) in (let TMP_105 \def (\lambda (n: nat).(let 
TMP_104 \def (le_O_n O) in (wadd_le f g H2 O O TMP_104 n))) in (let TMP_106 
\def (weight_le t0 TMP_102 TMP_103 TMP_105) in (let TMP_107 \def 
(le_plus_plus TMP_95 TMP_96 TMP_98 TMP_100 TMP_101 TMP_106) in (le_n_S TMP_90 
TMP_94 TMP_107))))))))))))))))))))))))) in (let TMP_130 \def (\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_109 \def (weight_map f u2) in (let TMP_110 \def (wadd f O) in 
(let TMP_111 \def (weight_map TMP_110 t0) in (let TMP_112 \def (plus TMP_109 
TMP_111) in (let TMP_113 \def (weight_map g u1) in (let TMP_114 \def (wadd g 
O) in (let TMP_115 \def (weight_map TMP_114 t0) in (let TMP_116 \def (plus 
TMP_113 TMP_115) in (let TMP_117 \def (weight_map f u2) in (let TMP_118 \def 
(weight_map g u1) in (let TMP_119 \def (wadd f O) in (let TMP_120 \def 
(weight_map TMP_119 t0) in (let TMP_121 \def (wadd g O) in (let TMP_122 \def 
(weight_map TMP_121 t0) in (let TMP_123 \def (H1 f g H2 H3) in (let TMP_124 
\def (wadd f O) in (let TMP_125 \def (wadd g O) in (let TMP_127 \def (\lambda 
(n: nat).(let TMP_126 \def (le_O_n O) in (wadd_le f g H2 O O TMP_126 n))) in 
(let TMP_128 \def (weight_le t0 TMP_124 TMP_125 TMP_127) in (let TMP_129 \def 
(le_plus_plus TMP_117 TMP_118 TMP_120 TMP_122 TMP_123 TMP_128) in (le_n_S 
TMP_112 TMP_116 TMP_129))))))))))))))))))))))))) in (B_ind TMP_45 TMP_86 
TMP_108 TMP_130 b)))))) in (let TMP_145 \def (\lambda (_: F).(\lambda (f0: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f0 m) (g m))))).(\lambda (H3: (lt (weight_map f0 (lift (S i) O v)) 
(g i))).(let TMP_132 \def (weight_map f0 u2) in (let TMP_133 \def (weight_map 
f0 t0) in (let TMP_134 \def (plus TMP_132 TMP_133) in (let TMP_135 \def 
(weight_map g u1) in (let TMP_136 \def (weight_map g t0) in (let TMP_137 \def 
(plus TMP_135 TMP_136) in (let TMP_138 \def (weight_map f0 u2) in (let 
TMP_139 \def (weight_map g u1) in (let TMP_140 \def (weight_map f0 t0) in 
(let TMP_141 \def (weight_map g t0) in (let TMP_142 \def (H1 f0 g H2 H3) in 
(let TMP_143 \def (weight_le t0 f0 g H2) in (let TMP_144 \def (le_plus_plus 
TMP_138 TMP_139 TMP_140 TMP_141 TMP_142 TMP_143) in (le_n_S TMP_134 TMP_137 
TMP_144))))))))))))))))))) in (K_ind TMP_38 TMP_131 TMP_145 k)))))))))))) in 
(let TMP_302 \def (\lambda (k: K).(let TMP_151 \def (\lambda (k0: K).(\forall 
(v: T).(\forall (t2: T).(\forall (t1: T).(\forall (i: nat).((subst0 (s k0 i) 
v t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(s k0 i)) O v)) (g (s k0 i))) \to (le (weight_map f t2) (weight_map g 
t1))))))) \to (\forall (u0: T).(\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (let TMP_147 \def (THead k0 u0 t2) in (let 
TMP_148 \def (weight_map f TMP_147) in (let TMP_149 \def (THead k0 u0 t1) in 
(let TMP_150 \def (weight_map g TMP_149) in (le TMP_148 
TMP_150))))))))))))))))) in (let TMP_287 \def (\lambda (b: B).(let TMP_158 
\def (\lambda (b0: B).(\forall (v: T).(\forall (t2: T).(\forall (t1: 
T).(\forall (i: nat).((subst0 (s (Bind b0) i) v t1 t2) \to (((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (s (Bind b0) i)) O v)) (g (s (Bind 
b0) i))) \to (le (weight_map f t2) (weight_map g t1))))))) \to (\forall (u0: 
T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to 
(let TMP_152 \def (Bind b0) in (let TMP_153 \def (THead TMP_152 u0 t2) in 
(let TMP_154 \def (weight_map f TMP_153) in (let TMP_155 \def (Bind b0) in 
(let TMP_156 \def (THead TMP_155 u0 t1) in (let TMP_157 \def (weight_map g 
TMP_156) in (le TMP_154 TMP_157))))))))))))))))))) in (let TMP_216 \def 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_159 \def (weight_map f u0) in (let TMP_160 \def (weight_map f u0) in (let 
TMP_161 \def (S TMP_160) in (let TMP_162 \def (wadd f TMP_161) in (let 
TMP_163 \def (weight_map TMP_162 t2) in (let TMP_164 \def (plus TMP_159 
TMP_163) in (let TMP_165 \def (weight_map g u0) in (let TMP_166 \def 
(weight_map g u0) in (let TMP_167 \def (S TMP_166) in (let TMP_168 \def (wadd 
g TMP_167) in (let TMP_169 \def (weight_map TMP_168 t1) in (let TMP_170 \def 
(plus TMP_165 TMP_169) in (let TMP_171 \def (weight_map f u0) in (let TMP_172 
\def (weight_map g u0) in (let TMP_173 \def (weight_map f u0) in (let TMP_174 
\def (S TMP_173) in (let TMP_175 \def (wadd f TMP_174) in (let TMP_176 \def 
(weight_map TMP_175 t2) in (let TMP_177 \def (weight_map g u0) in (let 
TMP_178 \def (S TMP_177) in (let TMP_179 \def (wadd g TMP_178) in (let 
TMP_180 \def (weight_map TMP_179 t1) in (let TMP_181 \def (weight_le u0 f g 
H2) in (let TMP_182 \def (weight_map f u0) in (let TMP_183 \def (S TMP_182) 
in (let TMP_184 \def (wadd f TMP_183) in (let TMP_185 \def (weight_map g u0) 
in (let TMP_186 \def (S TMP_185) in (let TMP_187 \def (wadd g TMP_186) in 
(let TMP_196 \def (\lambda (m: nat).(let TMP_188 \def (weight_map f u0) in 
(let TMP_189 \def (S TMP_188) in (let TMP_190 \def (weight_map g u0) in (let 
TMP_191 \def (S TMP_190) in (let TMP_192 \def (weight_map f u0) in (let 
TMP_193 \def (weight_map g u0) in (let TMP_194 \def (weight_le u0 f g H2) in 
(let TMP_195 \def (le_n_S TMP_192 TMP_193 TMP_194) in (wadd_le f g H2 TMP_189 
TMP_191 TMP_195 m)))))))))) in (let TMP_197 \def (S i) in (let TMP_198 \def 
(lift TMP_197 O v) in (let TMP_199 \def (weight_map f TMP_198) in (let 
TMP_201 \def (\lambda (n: nat).(let TMP_200 \def (g i) in (lt n TMP_200))) in 
(let TMP_202 \def (weight_map f u0) in (let TMP_203 \def (S TMP_202) in (let 
TMP_204 \def (wadd f TMP_203) in (let TMP_205 \def (S i) in (let TMP_206 \def 
(S TMP_205) in (let TMP_207 \def (lift TMP_206 O v) in (let TMP_208 \def 
(weight_map TMP_204 TMP_207) in (let TMP_209 \def (weight_map f u0) in (let 
TMP_210 \def (S TMP_209) in (let TMP_211 \def (S i) in (let TMP_212 \def 
(lift_weight_add_O TMP_210 v TMP_211 f) in (let TMP_213 \def (eq_ind nat 
TMP_199 TMP_201 H3 TMP_208 TMP_212) in (let TMP_214 \def (H1 TMP_184 TMP_187 
TMP_196 TMP_213) in (let TMP_215 \def (le_plus_plus TMP_171 TMP_172 TMP_176 
TMP_180 TMP_181 TMP_214) in (le_n_S TMP_164 TMP_170 
TMP_215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_251 \def (\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: 
nat).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g 
m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_217 \def (weight_map f u0) in (let TMP_218 \def (wadd f O) in 
(let TMP_219 \def (weight_map TMP_218 t2) in (let TMP_220 \def (plus TMP_217 
TMP_219) in (let TMP_221 \def (weight_map g u0) in (let TMP_222 \def (wadd g 
O) in (let TMP_223 \def (weight_map TMP_222 t1) in (let TMP_224 \def (plus 
TMP_221 TMP_223) in (let TMP_225 \def (weight_map f u0) in (let TMP_226 \def 
(weight_map g u0) in (let TMP_227 \def (wadd f O) in (let TMP_228 \def 
(weight_map TMP_227 t2) in (let TMP_229 \def (wadd g O) in (let TMP_230 \def 
(weight_map TMP_229 t1) in (let TMP_231 \def (weight_le u0 f g H2) in (let 
TMP_232 \def (wadd f O) in (let TMP_233 \def (wadd g O) in (let TMP_235 \def 
(\lambda (m: nat).(let TMP_234 \def (le_O_n O) in (wadd_le f g H2 O O TMP_234 
m))) in (let TMP_236 \def (S i) in (let TMP_237 \def (lift TMP_236 O v) in 
(let TMP_238 \def (weight_map f TMP_237) in (let TMP_240 \def (\lambda (n: 
nat).(let TMP_239 \def (g i) in (lt n TMP_239))) in (let TMP_241 \def (wadd f 
O) in (let TMP_242 \def (S i) in (let TMP_243 \def (S TMP_242) in (let 
TMP_244 \def (lift TMP_243 O v) in (let TMP_245 \def (weight_map TMP_241 
TMP_244) in (let TMP_246 \def (S i) in (let TMP_247 \def (lift_weight_add_O O 
v TMP_246 f) in (let TMP_248 \def (eq_ind nat TMP_238 TMP_240 H3 TMP_245 
TMP_247) in (let TMP_249 \def (H1 TMP_232 TMP_233 TMP_235 TMP_248) in (let 
TMP_250 \def (le_plus_plus TMP_225 TMP_226 TMP_228 TMP_230 TMP_231 TMP_249) 
in (le_n_S TMP_220 TMP_224 
TMP_250)))))))))))))))))))))))))))))))))))))))))))) in (let TMP_286 \def 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (le (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_252 \def (weight_map f u0) in (let TMP_253 \def (wadd f O) in (let 
TMP_254 \def (weight_map TMP_253 t2) in (let TMP_255 \def (plus TMP_252 
TMP_254) in (let TMP_256 \def (weight_map g u0) in (let TMP_257 \def (wadd g 
O) in (let TMP_258 \def (weight_map TMP_257 t1) in (let TMP_259 \def (plus 
TMP_256 TMP_258) in (let TMP_260 \def (weight_map f u0) in (let TMP_261 \def 
(weight_map g u0) in (let TMP_262 \def (wadd f O) in (let TMP_263 \def 
(weight_map TMP_262 t2) in (let TMP_264 \def (wadd g O) in (let TMP_265 \def 
(weight_map TMP_264 t1) in (let TMP_266 \def (weight_le u0 f g H2) in (let 
TMP_267 \def (wadd f O) in (let TMP_268 \def (wadd g O) in (let TMP_270 \def 
(\lambda (m: nat).(let TMP_269 \def (le_O_n O) in (wadd_le f g H2 O O TMP_269 
m))) in (let TMP_271 \def (S i) in (let TMP_272 \def (lift TMP_271 O v) in 
(let TMP_273 \def (weight_map f TMP_272) in (let TMP_275 \def (\lambda (n: 
nat).(let TMP_274 \def (g i) in (lt n TMP_274))) in (let TMP_276 \def (wadd f 
O) in (let TMP_277 \def (S i) in (let TMP_278 \def (S TMP_277) in (let 
TMP_279 \def (lift TMP_278 O v) in (let TMP_280 \def (weight_map TMP_276 
TMP_279) in (let TMP_281 \def (S i) in (let TMP_282 \def (lift_weight_add_O O 
v TMP_281 f) in (let TMP_283 \def (eq_ind nat TMP_273 TMP_275 H3 TMP_280 
TMP_282) in (let TMP_284 \def (H1 TMP_267 TMP_268 TMP_270 TMP_283) in (let 
TMP_285 \def (le_plus_plus TMP_260 TMP_261 TMP_263 TMP_265 TMP_266 TMP_284) 
in (le_n_S TMP_255 TMP_259 
TMP_285)))))))))))))))))))))))))))))))))))))))))))) in (B_ind TMP_158 TMP_216 
TMP_251 TMP_286 b)))))) in (let TMP_301 \def (\lambda (_: F).(\lambda (v: 
T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v t1 t2)).(\lambda (H1: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (m: nat).(le (f0 m) (g m)))) \to ((lt (weight_map f0 
(lift (S i) O v)) (g i)) \to (le (weight_map f0 t2) (weight_map g 
t1)))))))).(\lambda (u0: T).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda 
(H3: (lt (weight_map f0 (lift (S i) O v)) (g i))).(let TMP_288 \def 
(weight_map f0 u0) in (let TMP_289 \def (weight_map f0 t2) in (let TMP_290 
\def (plus TMP_288 TMP_289) in (let TMP_291 \def (weight_map g u0) in (let 
TMP_292 \def (weight_map g t1) in (let TMP_293 \def (plus TMP_291 TMP_292) in 
(let TMP_294 \def (weight_map f0 u0) in (let TMP_295 \def (weight_map g u0) 
in (let TMP_296 \def (weight_map f0 t2) in (let TMP_297 \def (weight_map g 
t1) in (let TMP_298 \def (weight_le u0 f0 g H2) in (let TMP_299 \def (H1 f0 g 
H2 H3) in (let TMP_300 \def (le_plus_plus TMP_294 TMP_295 TMP_296 TMP_297 
TMP_298 TMP_299) in (le_n_S TMP_290 TMP_293 TMP_300)))))))))))))))))))))))))) 
in (K_ind TMP_151 TMP_287 TMP_301 k))))) in (let TMP_458 \def (\lambda (v: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v u1 u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (le (weight_map f u2) (weight_map g u1)))))))).(\lambda 
(k: K).(let TMP_307 \def (\lambda (k0: K).(\forall (t1: T).(\forall (t2: 
T).((subst0 (s k0 i) v t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S (s k0 i)) O v)) (g (s k0 i))) \to (le (weight_map f 
t2) (weight_map g t1))))))) \to (\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (let TMP_303 \def (THead k0 u2 t2) in (let 
TMP_304 \def (weight_map f TMP_303) in (let TMP_305 \def (THead k0 u1 t1) in 
(let TMP_306 \def (weight_map g TMP_305) in (le TMP_304 TMP_306)))))))))))))) 
in (let TMP_443 \def (\lambda (b: B).(let TMP_314 \def (\lambda (b0: 
B).(\forall (t1: T).(\forall (t2: T).((subst0 (s (Bind b0) i) v t1 t2) \to 
(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (s (Bind b0) i)) O 
v)) (g (s (Bind b0) i))) \to (le (weight_map f t2) (weight_map g t1))))))) 
\to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) 
\to (let TMP_308 \def (Bind b0) in (let TMP_309 \def (THead TMP_308 u2 t2) in 
(let TMP_310 \def (weight_map f TMP_309) in (let TMP_311 \def (Bind b0) in 
(let TMP_312 \def (THead TMP_311 u1 t1) in (let TMP_313 \def (weight_map g 
TMP_312) in (le TMP_310 TMP_313)))))))))))))))) in (let TMP_372 \def (\lambda 
(t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H3: 
((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S 
i))) \to (le (weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le 
(f m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_315 \def (weight_map f u2) in (let TMP_316 \def (weight_map f 
u2) in (let TMP_317 \def (S TMP_316) in (let TMP_318 \def (wadd f TMP_317) in 
(let TMP_319 \def (weight_map TMP_318 t2) in (let TMP_320 \def (plus TMP_315 
TMP_319) in (let TMP_321 \def (weight_map g u1) in (let TMP_322 \def 
(weight_map g u1) in (let TMP_323 \def (S TMP_322) in (let TMP_324 \def (wadd 
g TMP_323) in (let TMP_325 \def (weight_map TMP_324 t1) in (let TMP_326 \def 
(plus TMP_321 TMP_325) in (let TMP_327 \def (weight_map f u2) in (let TMP_328 
\def (weight_map g u1) in (let TMP_329 \def (weight_map f u2) in (let TMP_330 
\def (S TMP_329) in (let TMP_331 \def (wadd f TMP_330) in (let TMP_332 \def 
(weight_map TMP_331 t2) in (let TMP_333 \def (weight_map g u1) in (let 
TMP_334 \def (S TMP_333) in (let TMP_335 \def (wadd g TMP_334) in (let 
TMP_336 \def (weight_map TMP_335 t1) in (let TMP_337 \def (H1 f g H4 H5) in 
(let TMP_338 \def (weight_map f u2) in (let TMP_339 \def (S TMP_338) in (let 
TMP_340 \def (wadd f TMP_339) in (let TMP_341 \def (weight_map g u1) in (let 
TMP_342 \def (S TMP_341) in (let TMP_343 \def (wadd g TMP_342) in (let 
TMP_352 \def (\lambda (m: nat).(let TMP_344 \def (weight_map f u2) in (let 
TMP_345 \def (S TMP_344) in (let TMP_346 \def (weight_map g u1) in (let 
TMP_347 \def (S TMP_346) in (let TMP_348 \def (weight_map f u2) in (let 
TMP_349 \def (weight_map g u1) in (let TMP_350 \def (H1 f g H4 H5) in (let 
TMP_351 \def (le_n_S TMP_348 TMP_349 TMP_350) in (wadd_le f g H4 TMP_345 
TMP_347 TMP_351 m)))))))))) in (let TMP_353 \def (S i) in (let TMP_354 \def 
(lift TMP_353 O v) in (let TMP_355 \def (weight_map f TMP_354) in (let 
TMP_357 \def (\lambda (n: nat).(let TMP_356 \def (g i) in (lt n TMP_356))) in 
(let TMP_358 \def (weight_map f u2) in (let TMP_359 \def (S TMP_358) in (let 
TMP_360 \def (wadd f TMP_359) in (let TMP_361 \def (S i) in (let TMP_362 \def 
(S TMP_361) in (let TMP_363 \def (lift TMP_362 O v) in (let TMP_364 \def 
(weight_map TMP_360 TMP_363) in (let TMP_365 \def (weight_map f u2) in (let 
TMP_366 \def (S TMP_365) in (let TMP_367 \def (S i) in (let TMP_368 \def 
(lift_weight_add_O TMP_366 v TMP_367 f) in (let TMP_369 \def (eq_ind nat 
TMP_355 TMP_357 H5 TMP_364 TMP_368) in (let TMP_370 \def (H3 TMP_340 TMP_343 
TMP_352 TMP_369) in (let TMP_371 \def (le_plus_plus TMP_327 TMP_328 TMP_332 
TMP_336 TMP_337 TMP_370) in (le_n_S TMP_320 TMP_326 
TMP_371))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_407 \def (\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v 
t1 t2)).(\lambda (H3: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (le (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: (lt 
(weight_map f (lift (S i) O v)) (g i))).(let TMP_373 \def (weight_map f u2) 
in (let TMP_374 \def (wadd f O) in (let TMP_375 \def (weight_map TMP_374 t2) 
in (let TMP_376 \def (plus TMP_373 TMP_375) in (let TMP_377 \def (weight_map 
g u1) in (let TMP_378 \def (wadd g O) in (let TMP_379 \def (weight_map 
TMP_378 t1) in (let TMP_380 \def (plus TMP_377 TMP_379) in (let TMP_381 \def 
(weight_map f u2) in (let TMP_382 \def (weight_map g u1) in (let TMP_383 \def 
(wadd f O) in (let TMP_384 \def (weight_map TMP_383 t2) in (let TMP_385 \def 
(wadd g O) in (let TMP_386 \def (weight_map TMP_385 t1) in (let TMP_387 \def 
(H1 f g H4 H5) in (let TMP_388 \def (wadd f O) in (let TMP_389 \def (wadd g 
O) in (let TMP_391 \def (\lambda (m: nat).(let TMP_390 \def (le_O_n O) in 
(wadd_le f g H4 O O TMP_390 m))) in (let TMP_392 \def (S i) in (let TMP_393 
\def (lift TMP_392 O v) in (let TMP_394 \def (weight_map f TMP_393) in (let 
TMP_396 \def (\lambda (n: nat).(let TMP_395 \def (g i) in (lt n TMP_395))) in 
(let TMP_397 \def (wadd f O) in (let TMP_398 \def (S i) in (let TMP_399 \def 
(S TMP_398) in (let TMP_400 \def (lift TMP_399 O v) in (let TMP_401 \def 
(weight_map TMP_397 TMP_400) in (let TMP_402 \def (S i) in (let TMP_403 \def 
(lift_weight_add_O O v TMP_402 f) in (let TMP_404 \def (eq_ind nat TMP_394 
TMP_396 H5 TMP_401 TMP_403) in (let TMP_405 \def (H3 TMP_388 TMP_389 TMP_391 
TMP_404) in (let TMP_406 \def (le_plus_plus TMP_381 TMP_382 TMP_384 TMP_386 
TMP_387 TMP_405) in (le_n_S TMP_376 TMP_380 
TMP_406))))))))))))))))))))))))))))))))))))))))) in (let TMP_442 \def 
(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v t1 
t2)).(\lambda (H3: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (le (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: (lt 
(weight_map f (lift (S i) O v)) (g i))).(let TMP_408 \def (weight_map f u2) 
in (let TMP_409 \def (wadd f O) in (let TMP_410 \def (weight_map TMP_409 t2) 
in (let TMP_411 \def (plus TMP_408 TMP_410) in (let TMP_412 \def (weight_map 
g u1) in (let TMP_413 \def (wadd g O) in (let TMP_414 \def (weight_map 
TMP_413 t1) in (let TMP_415 \def (plus TMP_412 TMP_414) in (let TMP_416 \def 
(weight_map f u2) in (let TMP_417 \def (weight_map g u1) in (let TMP_418 \def 
(wadd f O) in (let TMP_419 \def (weight_map TMP_418 t2) in (let TMP_420 \def 
(wadd g O) in (let TMP_421 \def (weight_map TMP_420 t1) in (let TMP_422 \def 
(H1 f g H4 H5) in (let TMP_423 \def (wadd f O) in (let TMP_424 \def (wadd g 
O) in (let TMP_426 \def (\lambda (m: nat).(let TMP_425 \def (le_O_n O) in 
(wadd_le f g H4 O O TMP_425 m))) in (let TMP_427 \def (S i) in (let TMP_428 
\def (lift TMP_427 O v) in (let TMP_429 \def (weight_map f TMP_428) in (let 
TMP_431 \def (\lambda (n: nat).(let TMP_430 \def (g i) in (lt n TMP_430))) in 
(let TMP_432 \def (wadd f O) in (let TMP_433 \def (S i) in (let TMP_434 \def 
(S TMP_433) in (let TMP_435 \def (lift TMP_434 O v) in (let TMP_436 \def 
(weight_map TMP_432 TMP_435) in (let TMP_437 \def (S i) in (let TMP_438 \def 
(lift_weight_add_O O v TMP_437 f) in (let TMP_439 \def (eq_ind nat TMP_429 
TMP_431 H5 TMP_436 TMP_438) in (let TMP_440 \def (H3 TMP_423 TMP_424 TMP_426 
TMP_439) in (let TMP_441 \def (le_plus_plus TMP_416 TMP_417 TMP_419 TMP_421 
TMP_422 TMP_440) in (le_n_S TMP_411 TMP_415 
TMP_441))))))))))))))))))))))))))))))))))))))))) in (B_ind TMP_314 TMP_372 
TMP_407 TMP_442 b)))))) in (let TMP_457 \def (\lambda (_: F).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (subst0 i v t1 t2)).(\lambda (H3: ((\forall 
(f0: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le 
(f0 m) (g m)))) \to ((lt (weight_map f0 (lift (S i) O v)) (g i)) \to (le 
(weight_map f0 t2) (weight_map g t1)))))))).(\lambda (f0: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le (f0 
m) (g m))))).(\lambda (H5: (lt (weight_map f0 (lift (S i) O v)) (g i))).(let 
TMP_444 \def (weight_map f0 u2) in (let TMP_445 \def (weight_map f0 t2) in 
(let TMP_446 \def (plus TMP_444 TMP_445) in (let TMP_447 \def (weight_map g 
u1) in (let TMP_448 \def (weight_map g t1) in (let TMP_449 \def (plus TMP_447 
TMP_448) in (let TMP_450 \def (weight_map f0 u2) in (let TMP_451 \def 
(weight_map g u1) in (let TMP_452 \def (weight_map f0 t2) in (let TMP_453 
\def (weight_map g t1) in (let TMP_454 \def (H1 f0 g H4 H5) in (let TMP_455 
\def (H3 f0 g H4 H5) in (let TMP_456 \def (le_plus_plus TMP_450 TMP_451 
TMP_452 TMP_453 TMP_454 TMP_455) in (le_n_S TMP_446 TMP_449 
TMP_456))))))))))))))))))))))) in (K_ind TMP_307 TMP_443 TMP_457 k))))))))))) 
in (subst0_ind TMP_3 TMP_33 TMP_146 TMP_302 TMP_458 d u t z H)))))))))).

theorem subst0_weight_lt:
 \forall (u: T).(\forall (t: T).(\forall (z: T).(\forall (d: nat).((subst0 d 
u t z) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
d) O u)) (g d)) \to (lt (weight_map f z) (weight_map g t))))))))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d u t z)).(let TMP_3 \def (\lambda (n: nat).(\lambda (t0: 
T).(\lambda (t1: T).(\lambda (t2: T).(\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S n) O t0)) (g n)) \to (let TMP_1 \def (weight_map f t2) 
in (let TMP_2 \def (weight_map g t1) in (lt TMP_1 TMP_2))))))))))) in (let 
TMP_4 \def (\lambda (v: T).(\lambda (i: nat).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H1: (lt (weight_map f (lift (S i) O v)) (g 
i))).H1)))))) in (let TMP_129 \def (\lambda (v: T).(\lambda (u2: T).(\lambda 
(u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 u2)).(\lambda (H1: 
((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to 
(lt (weight_map f u2) (weight_map g u1)))))))).(\lambda (t0: T).(\lambda (k: 
K).(let TMP_9 \def (\lambda (k0: K).(\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S i) O v)) (g i)) \to (let TMP_5 \def (THead k0 u2 t0) 
in (let TMP_6 \def (weight_map f TMP_5) in (let TMP_7 \def (THead k0 u1 t0) 
in (let TMP_8 \def (weight_map g TMP_7) in (lt TMP_6 TMP_8)))))))))) in (let 
TMP_114 \def (\lambda (b: B).(let TMP_16 \def (\lambda (b0: B).(\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to (let TMP_10 \def 
(Bind b0) in (let TMP_11 \def (THead TMP_10 u2 t0) in (let TMP_12 \def 
(weight_map f TMP_11) in (let TMP_13 \def (Bind b0) in (let TMP_14 \def 
(THead TMP_13 u1 t0) in (let TMP_15 \def (weight_map g TMP_14) in (lt TMP_12 
TMP_15)))))))))))) in (let TMP_57 \def (\lambda (f: ((nat \to nat))).(\lambda 
(g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f m) (g 
m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let TMP_17 
\def (weight_map f u2) in (let TMP_18 \def (weight_map f u2) in (let TMP_19 
\def (S TMP_18) in (let TMP_20 \def (wadd f TMP_19) in (let TMP_21 \def 
(weight_map TMP_20 t0) in (let TMP_22 \def (plus TMP_17 TMP_21) in (let 
TMP_23 \def (weight_map g u1) in (let TMP_24 \def (weight_map g u1) in (let 
TMP_25 \def (S TMP_24) in (let TMP_26 \def (wadd g TMP_25) in (let TMP_27 
\def (weight_map TMP_26 t0) in (let TMP_28 \def (plus TMP_23 TMP_27) in (let 
TMP_29 \def (weight_map f u2) in (let TMP_30 \def (weight_map g u1) in (let 
TMP_31 \def (weight_map f u2) in (let TMP_32 \def (S TMP_31) in (let TMP_33 
\def (wadd f TMP_32) in (let TMP_34 \def (weight_map TMP_33 t0) in (let 
TMP_35 \def (weight_map g u1) in (let TMP_36 \def (S TMP_35) in (let TMP_37 
\def (wadd g TMP_36) in (let TMP_38 \def (weight_map TMP_37 t0) in (let 
TMP_39 \def (H1 f g H2 H3) in (let TMP_40 \def (weight_map f u2) in (let 
TMP_41 \def (S TMP_40) in (let TMP_42 \def (wadd f TMP_41) in (let TMP_43 
\def (weight_map g u1) in (let TMP_44 \def (S TMP_43) in (let TMP_45 \def 
(wadd g TMP_44) in (let TMP_54 \def (\lambda (n: nat).(let TMP_46 \def 
(weight_map f u2) in (let TMP_47 \def (S TMP_46) in (let TMP_48 \def 
(weight_map g u1) in (let TMP_49 \def (S TMP_48) in (let TMP_50 \def 
(weight_map f u2) in (let TMP_51 \def (weight_map g u1) in (let TMP_52 \def 
(H1 f g H2 H3) in (let TMP_53 \def (lt_n_S TMP_50 TMP_51 TMP_52) in (wadd_lt 
f g H2 TMP_47 TMP_49 TMP_53 n)))))))))) in (let TMP_55 \def (weight_le t0 
TMP_42 TMP_45 TMP_54) in (let TMP_56 \def (lt_le_plus_plus TMP_29 TMP_30 
TMP_34 TMP_38 TMP_39 TMP_55) in (lt_n_S TMP_22 TMP_28 
TMP_56))))))))))))))))))))))))))))))))))))) in (let TMP_85 \def (\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_58 \def (weight_map f u2) in (let TMP_59 \def (wadd f O) in 
(let TMP_60 \def (weight_map TMP_59 t0) in (let TMP_61 \def (plus TMP_58 
TMP_60) in (let TMP_62 \def (weight_map g u1) in (let TMP_63 \def (wadd g O) 
in (let TMP_64 \def (weight_map TMP_63 t0) in (let TMP_65 \def (plus TMP_62 
TMP_64) in (let TMP_66 \def (weight_map f u2) in (let TMP_67 \def (weight_map 
g u1) in (let TMP_68 \def (wadd f O) in (let TMP_69 \def (weight_map TMP_68 
t0) in (let TMP_70 \def (wadd g O) in (let TMP_71 \def (weight_map TMP_70 t0) 
in (let TMP_72 \def (H1 f g H2 H3) in (let TMP_73 \def (wadd f O) in (let 
TMP_74 \def (wadd g O) in (let TMP_82 \def (\lambda (n: nat).(let TMP_75 \def 
(wadd f O n) in (let TMP_76 \def (wadd g O n) in (let TMP_77 \def (wadd f O 
n) in (let TMP_78 \def (wadd g O n) in (let TMP_79 \def (le_O_n O) in (let 
TMP_80 \def (wadd_le f g H2 O O TMP_79 n) in (let TMP_81 \def (le_n_S TMP_77 
TMP_78 TMP_80) in (le_S_n TMP_75 TMP_76 TMP_81))))))))) in (let TMP_83 \def 
(weight_le t0 TMP_73 TMP_74 TMP_82) in (let TMP_84 \def (lt_le_plus_plus 
TMP_66 TMP_67 TMP_69 TMP_71 TMP_72 TMP_83) in (lt_n_S TMP_61 TMP_65 
TMP_84))))))))))))))))))))))))) in (let TMP_113 \def (\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_86 \def (weight_map f u2) in (let TMP_87 \def (wadd f O) in (let TMP_88 
\def (weight_map TMP_87 t0) in (let TMP_89 \def (plus TMP_86 TMP_88) in (let 
TMP_90 \def (weight_map g u1) in (let TMP_91 \def (wadd g O) in (let TMP_92 
\def (weight_map TMP_91 t0) in (let TMP_93 \def (plus TMP_90 TMP_92) in (let 
TMP_94 \def (weight_map f u2) in (let TMP_95 \def (weight_map g u1) in (let 
TMP_96 \def (wadd f O) in (let TMP_97 \def (weight_map TMP_96 t0) in (let 
TMP_98 \def (wadd g O) in (let TMP_99 \def (weight_map TMP_98 t0) in (let 
TMP_100 \def (H1 f g H2 H3) in (let TMP_101 \def (wadd f O) in (let TMP_102 
\def (wadd g O) in (let TMP_110 \def (\lambda (n: nat).(let TMP_103 \def 
(wadd f O n) in (let TMP_104 \def (wadd g O n) in (let TMP_105 \def (wadd f O 
n) in (let TMP_106 \def (wadd g O n) in (let TMP_107 \def (le_O_n O) in (let 
TMP_108 \def (wadd_le f g H2 O O TMP_107 n) in (let TMP_109 \def (le_n_S 
TMP_105 TMP_106 TMP_108) in (le_S_n TMP_103 TMP_104 TMP_109))))))))) in (let 
TMP_111 \def (weight_le t0 TMP_101 TMP_102 TMP_110) in (let TMP_112 \def 
(lt_le_plus_plus TMP_94 TMP_95 TMP_97 TMP_99 TMP_100 TMP_111) in (lt_n_S 
TMP_89 TMP_93 TMP_112))))))))))))))))))))))))) in (B_ind TMP_16 TMP_57 TMP_85 
TMP_113 b)))))) in (let TMP_128 \def (\lambda (_: F).(\lambda (f0: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 
m) (g m))))).(\lambda (H3: (lt (weight_map f0 (lift (S i) O v)) (g i))).(let 
TMP_115 \def (weight_map f0 u2) in (let TMP_116 \def (weight_map f0 t0) in 
(let TMP_117 \def (plus TMP_115 TMP_116) in (let TMP_118 \def (weight_map g 
u1) in (let TMP_119 \def (weight_map g t0) in (let TMP_120 \def (plus TMP_118 
TMP_119) in (let TMP_121 \def (weight_map f0 u2) in (let TMP_122 \def 
(weight_map g u1) in (let TMP_123 \def (weight_map f0 t0) in (let TMP_124 
\def (weight_map g t0) in (let TMP_125 \def (H1 f0 g H2 H3) in (let TMP_126 
\def (weight_le t0 f0 g H2) in (let TMP_127 \def (lt_le_plus_plus TMP_121 
TMP_122 TMP_123 TMP_124 TMP_125 TMP_126) in (lt_n_S TMP_117 TMP_120 
TMP_127))))))))))))))))))) in (K_ind TMP_9 TMP_114 TMP_128 k)))))))))))) in 
(let TMP_285 \def (\lambda (k: K).(let TMP_134 \def (\lambda (k0: K).(\forall 
(v: T).(\forall (t2: T).(\forall (t1: T).(\forall (i: nat).((subst0 (s k0 i) 
v t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(s k0 i)) O v)) (g (s k0 i))) \to (lt (weight_map f t2) (weight_map g 
t1))))))) \to (\forall (u0: T).(\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (let TMP_130 \def (THead k0 u0 t2) in (let 
TMP_131 \def (weight_map f TMP_130) in (let TMP_132 \def (THead k0 u0 t1) in 
(let TMP_133 \def (weight_map g TMP_132) in (lt TMP_131 
TMP_133))))))))))))))))) in (let TMP_270 \def (\lambda (b: B).(let TMP_141 
\def (\lambda (b0: B).(\forall (v: T).(\forall (t2: T).(\forall (t1: 
T).(\forall (i: nat).((subst0 (s (Bind b0) i) v t1 t2) \to (((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) 
(g m)))) \to ((lt (weight_map f (lift (S (s (Bind b0) i)) O v)) (g (s (Bind 
b0) i))) \to (lt (weight_map f t2) (weight_map g t1))))))) \to (\forall (u0: 
T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) \to 
(let TMP_135 \def (Bind b0) in (let TMP_136 \def (THead TMP_135 u0 t2) in 
(let TMP_137 \def (weight_map f TMP_136) in (let TMP_138 \def (Bind b0) in 
(let TMP_139 \def (THead TMP_138 u0 t1) in (let TMP_140 \def (weight_map g 
TMP_139) in (lt TMP_137 TMP_140))))))))))))))))))) in (let TMP_199 \def 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_142 \def (weight_map f u0) in (let TMP_143 \def (weight_map f u0) in (let 
TMP_144 \def (S TMP_143) in (let TMP_145 \def (wadd f TMP_144) in (let 
TMP_146 \def (weight_map TMP_145 t2) in (let TMP_147 \def (plus TMP_142 
TMP_146) in (let TMP_148 \def (weight_map g u0) in (let TMP_149 \def 
(weight_map g u0) in (let TMP_150 \def (S TMP_149) in (let TMP_151 \def (wadd 
g TMP_150) in (let TMP_152 \def (weight_map TMP_151 t1) in (let TMP_153 \def 
(plus TMP_148 TMP_152) in (let TMP_154 \def (weight_map f u0) in (let TMP_155 
\def (weight_map g u0) in (let TMP_156 \def (weight_map f u0) in (let TMP_157 
\def (S TMP_156) in (let TMP_158 \def (wadd f TMP_157) in (let TMP_159 \def 
(weight_map TMP_158 t2) in (let TMP_160 \def (weight_map g u0) in (let 
TMP_161 \def (S TMP_160) in (let TMP_162 \def (wadd g TMP_161) in (let 
TMP_163 \def (weight_map TMP_162 t1) in (let TMP_164 \def (weight_le u0 f g 
H2) in (let TMP_165 \def (weight_map f u0) in (let TMP_166 \def (S TMP_165) 
in (let TMP_167 \def (wadd f TMP_166) in (let TMP_168 \def (weight_map g u0) 
in (let TMP_169 \def (S TMP_168) in (let TMP_170 \def (wadd g TMP_169) in 
(let TMP_179 \def (\lambda (m: nat).(let TMP_171 \def (weight_map f u0) in 
(let TMP_172 \def (S TMP_171) in (let TMP_173 \def (weight_map g u0) in (let 
TMP_174 \def (S TMP_173) in (let TMP_175 \def (weight_map f u0) in (let 
TMP_176 \def (weight_map g u0) in (let TMP_177 \def (weight_le u0 f g H2) in 
(let TMP_178 \def (le_n_S TMP_175 TMP_176 TMP_177) in (wadd_le f g H2 TMP_172 
TMP_174 TMP_178 m)))))))))) in (let TMP_180 \def (S i) in (let TMP_181 \def 
(lift TMP_180 O v) in (let TMP_182 \def (weight_map f TMP_181) in (let 
TMP_184 \def (\lambda (n: nat).(let TMP_183 \def (g i) in (lt n TMP_183))) in 
(let TMP_185 \def (weight_map f u0) in (let TMP_186 \def (S TMP_185) in (let 
TMP_187 \def (wadd f TMP_186) in (let TMP_188 \def (S i) in (let TMP_189 \def 
(S TMP_188) in (let TMP_190 \def (lift TMP_189 O v) in (let TMP_191 \def 
(weight_map TMP_187 TMP_190) in (let TMP_192 \def (weight_map f u0) in (let 
TMP_193 \def (S TMP_192) in (let TMP_194 \def (S i) in (let TMP_195 \def 
(lift_weight_add_O TMP_193 v TMP_194 f) in (let TMP_196 \def (eq_ind nat 
TMP_182 TMP_184 H3 TMP_191 TMP_195) in (let TMP_197 \def (H1 TMP_167 TMP_170 
TMP_179 TMP_196) in (let TMP_198 \def (le_lt_plus_plus TMP_154 TMP_155 
TMP_159 TMP_163 TMP_164 TMP_197) in (lt_n_S TMP_147 TMP_153 
TMP_198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_234 \def (\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: 
nat).(\lambda (_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g 
m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt 
(weight_map f t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: 
nat).(le (f m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_200 \def (weight_map f u0) in (let TMP_201 \def (wadd f O) in 
(let TMP_202 \def (weight_map TMP_201 t2) in (let TMP_203 \def (plus TMP_200 
TMP_202) in (let TMP_204 \def (weight_map g u0) in (let TMP_205 \def (wadd g 
O) in (let TMP_206 \def (weight_map TMP_205 t1) in (let TMP_207 \def (plus 
TMP_204 TMP_206) in (let TMP_208 \def (weight_map f u0) in (let TMP_209 \def 
(weight_map g u0) in (let TMP_210 \def (wadd f O) in (let TMP_211 \def 
(weight_map TMP_210 t2) in (let TMP_212 \def (wadd g O) in (let TMP_213 \def 
(weight_map TMP_212 t1) in (let TMP_214 \def (weight_le u0 f g H2) in (let 
TMP_215 \def (wadd f O) in (let TMP_216 \def (wadd g O) in (let TMP_218 \def 
(\lambda (m: nat).(let TMP_217 \def (le_O_n O) in (wadd_le f g H2 O O TMP_217 
m))) in (let TMP_219 \def (S i) in (let TMP_220 \def (lift TMP_219 O v) in 
(let TMP_221 \def (weight_map f TMP_220) in (let TMP_223 \def (\lambda (n: 
nat).(let TMP_222 \def (g i) in (lt n TMP_222))) in (let TMP_224 \def (wadd f 
O) in (let TMP_225 \def (S i) in (let TMP_226 \def (S TMP_225) in (let 
TMP_227 \def (lift TMP_226 O v) in (let TMP_228 \def (weight_map TMP_224 
TMP_227) in (let TMP_229 \def (S i) in (let TMP_230 \def (lift_weight_add_O O 
v TMP_229 f) in (let TMP_231 \def (eq_ind nat TMP_221 TMP_223 H3 TMP_228 
TMP_230) in (let TMP_232 \def (H1 TMP_215 TMP_216 TMP_218 TMP_231) in (let 
TMP_233 \def (le_lt_plus_plus TMP_208 TMP_209 TMP_211 TMP_213 TMP_214 
TMP_232) in (lt_n_S TMP_203 TMP_207 
TMP_233)))))))))))))))))))))))))))))))))))))))))))) in (let TMP_269 \def 
(\lambda (v: T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(_: (subst0 (S i) v t1 t2)).(\lambda (H1: ((\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) 
\to ((lt (weight_map f (lift (S (S i)) O v)) (g (S i))) \to (lt (weight_map f 
t2) (weight_map g t1)))))))).(\lambda (u0: T).(\lambda (f: ((nat \to 
nat))).(\lambda (g: ((nat \to nat))).(\lambda (H2: ((\forall (m: nat).(le (f 
m) (g m))))).(\lambda (H3: (lt (weight_map f (lift (S i) O v)) (g i))).(let 
TMP_235 \def (weight_map f u0) in (let TMP_236 \def (wadd f O) in (let 
TMP_237 \def (weight_map TMP_236 t2) in (let TMP_238 \def (plus TMP_235 
TMP_237) in (let TMP_239 \def (weight_map g u0) in (let TMP_240 \def (wadd g 
O) in (let TMP_241 \def (weight_map TMP_240 t1) in (let TMP_242 \def (plus 
TMP_239 TMP_241) in (let TMP_243 \def (weight_map f u0) in (let TMP_244 \def 
(weight_map g u0) in (let TMP_245 \def (wadd f O) in (let TMP_246 \def 
(weight_map TMP_245 t2) in (let TMP_247 \def (wadd g O) in (let TMP_248 \def 
(weight_map TMP_247 t1) in (let TMP_249 \def (weight_le u0 f g H2) in (let 
TMP_250 \def (wadd f O) in (let TMP_251 \def (wadd g O) in (let TMP_253 \def 
(\lambda (m: nat).(let TMP_252 \def (le_O_n O) in (wadd_le f g H2 O O TMP_252 
m))) in (let TMP_254 \def (S i) in (let TMP_255 \def (lift TMP_254 O v) in 
(let TMP_256 \def (weight_map f TMP_255) in (let TMP_258 \def (\lambda (n: 
nat).(let TMP_257 \def (g i) in (lt n TMP_257))) in (let TMP_259 \def (wadd f 
O) in (let TMP_260 \def (S i) in (let TMP_261 \def (S TMP_260) in (let 
TMP_262 \def (lift TMP_261 O v) in (let TMP_263 \def (weight_map TMP_259 
TMP_262) in (let TMP_264 \def (S i) in (let TMP_265 \def (lift_weight_add_O O 
v TMP_264 f) in (let TMP_266 \def (eq_ind nat TMP_256 TMP_258 H3 TMP_263 
TMP_265) in (let TMP_267 \def (H1 TMP_250 TMP_251 TMP_253 TMP_266) in (let 
TMP_268 \def (le_lt_plus_plus TMP_243 TMP_244 TMP_246 TMP_248 TMP_249 
TMP_267) in (lt_n_S TMP_238 TMP_242 
TMP_268)))))))))))))))))))))))))))))))))))))))))))) in (B_ind TMP_141 TMP_199 
TMP_234 TMP_269 b)))))) in (let TMP_284 \def (\lambda (_: F).(\lambda (v: 
T).(\lambda (t2: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v t1 t2)).(\lambda (H1: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (m: nat).(le (f0 m) (g m)))) \to ((lt (weight_map f0 
(lift (S i) O v)) (g i)) \to (lt (weight_map f0 t2) (weight_map g 
t1)))))))).(\lambda (u0: T).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat 
\to nat))).(\lambda (H2: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda 
(H3: (lt (weight_map f0 (lift (S i) O v)) (g i))).(let TMP_271 \def 
(weight_map f0 u0) in (let TMP_272 \def (weight_map f0 t2) in (let TMP_273 
\def (plus TMP_271 TMP_272) in (let TMP_274 \def (weight_map g u0) in (let 
TMP_275 \def (weight_map g t1) in (let TMP_276 \def (plus TMP_274 TMP_275) in 
(let TMP_277 \def (weight_map f0 u0) in (let TMP_278 \def (weight_map g u0) 
in (let TMP_279 \def (weight_map f0 t2) in (let TMP_280 \def (weight_map g 
t1) in (let TMP_281 \def (weight_le u0 f0 g H2) in (let TMP_282 \def (H1 f0 g 
H2 H3) in (let TMP_283 \def (le_lt_plus_plus TMP_277 TMP_278 TMP_279 TMP_280 
TMP_281 TMP_282) in (lt_n_S TMP_273 TMP_276 TMP_283)))))))))))))))))))))))))) 
in (K_ind TMP_134 TMP_270 TMP_284 k))))) in (let TMP_454 \def (\lambda (v: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda (_: (subst0 i 
v u1 u2)).(\lambda (H1: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
i) O v)) (g i)) \to (lt (weight_map f u2) (weight_map g u1)))))))).(\lambda 
(k: K).(let TMP_290 \def (\lambda (k0: K).(\forall (t1: T).(\forall (t2: 
T).((subst0 (s k0 i) v t1 t2) \to (((\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt 
(weight_map f (lift (S (s k0 i)) O v)) (g (s k0 i))) \to (lt (weight_map f 
t2) (weight_map g t1))))))) \to (\forall (f: ((nat \to nat))).(\forall (g: 
((nat \to nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map 
f (lift (S i) O v)) (g i)) \to (let TMP_286 \def (THead k0 u2 t2) in (let 
TMP_287 \def (weight_map f TMP_286) in (let TMP_288 \def (THead k0 u1 t1) in 
(let TMP_289 \def (weight_map g TMP_288) in (lt TMP_287 TMP_289)))))))))))))) 
in (let TMP_439 \def (\lambda (b: B).(let TMP_297 \def (\lambda (b0: 
B).(\forall (t1: T).(\forall (t2: T).((subst0 (s (Bind b0) i) v t1 t2) \to 
(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (s (Bind b0) i)) O 
v)) (g (s (Bind b0) i))) \to (lt (weight_map f t2) (weight_map g t1))))))) 
\to (\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall 
(m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S i) O v)) (g i)) 
\to (let TMP_291 \def (Bind b0) in (let TMP_292 \def (THead TMP_291 u2 t2) in 
(let TMP_293 \def (weight_map f TMP_292) in (let TMP_294 \def (Bind b0) in 
(let TMP_295 \def (THead TMP_294 u1 t1) in (let TMP_296 \def (weight_map g 
TMP_295) in (lt TMP_293 TMP_296)))))))))))))))) in (let TMP_356 \def (\lambda 
(t1: T).(\lambda (t2: T).(\lambda (H2: (subst0 (S i) v t1 t2)).(\lambda (_: 
((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (m: 
nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S (S i)) O v)) (g (S 
i))) \to (lt (weight_map f t2) (weight_map g t1)))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H4: ((\forall (m: nat).(le 
(f m) (g m))))).(\lambda (H5: (lt (weight_map f (lift (S i) O v)) (g 
i))).(let TMP_298 \def (weight_map f u2) in (let TMP_299 \def (weight_map f 
u2) in (let TMP_300 \def (S TMP_299) in (let TMP_301 \def (wadd f TMP_300) in 
(let TMP_302 \def (weight_map TMP_301 t2) in (let TMP_303 \def (plus TMP_298 
TMP_302) in (let TMP_304 \def (weight_map g u1) in (let TMP_305 \def 
(weight_map g u1) in (let TMP_306 \def (S TMP_305) in (let TMP_307 \def (wadd 
g TMP_306) in (let TMP_308 \def (weight_map TMP_307 t1) in (let TMP_309 \def 
(plus TMP_304 TMP_308) in (let TMP_310 \def (weight_map f u2) in (let TMP_311 
\def (weight_map g u1) in (let TMP_312 \def (weight_map f u2) in (let TMP_313 
\def (S TMP_312) in (let TMP_314 \def (wadd f TMP_313) in (let TMP_315 \def 
(weight_map TMP_314 t2) in (let TMP_316 \def (weight_map g u1) in (let 
TMP_317 \def (S TMP_316) in (let TMP_318 \def (wadd g TMP_317) in (let 
TMP_319 \def (weight_map TMP_318 t1) in (let TMP_320 \def (H1 f g H4 H5) in 
(let TMP_321 \def (S i) in (let TMP_322 \def (weight_map f u2) in (let 
TMP_323 \def (S TMP_322) in (let TMP_324 \def (wadd f TMP_323) in (let 
TMP_325 \def (weight_map g u1) in (let TMP_326 \def (S TMP_325) in (let 
TMP_327 \def (wadd g TMP_326) in (let TMP_336 \def (\lambda (m: nat).(let 
TMP_328 \def (weight_map f u2) in (let TMP_329 \def (S TMP_328) in (let 
TMP_330 \def (weight_map g u1) in (let TMP_331 \def (S TMP_330) in (let 
TMP_332 \def (weight_map f u2) in (let TMP_333 \def (weight_map g u1) in (let 
TMP_334 \def (H1 f g H4 H5) in (let TMP_335 \def (lt_n_S TMP_332 TMP_333 
TMP_334) in (wadd_lt f g H4 TMP_329 TMP_331 TMP_335 m)))))))))) in (let 
TMP_337 \def (S i) in (let TMP_338 \def (lift TMP_337 O v) in (let TMP_339 
\def (weight_map f TMP_338) in (let TMP_341 \def (\lambda (n: nat).(let 
TMP_340 \def (g i) in (lt n TMP_340))) in (let TMP_342 \def (weight_map f u2) 
in (let TMP_343 \def (S TMP_342) in (let TMP_344 \def (wadd f TMP_343) in 
(let TMP_345 \def (S i) in (let TMP_346 \def (S TMP_345) in (let TMP_347 \def 
(lift TMP_346 O v) in (let TMP_348 \def (weight_map TMP_344 TMP_347) in (let 
TMP_349 \def (weight_map f u2) in (let TMP_350 \def (S TMP_349) in (let 
TMP_351 \def (S i) in (let TMP_352 \def (lift_weight_add_O TMP_350 v TMP_351 
f) in (let TMP_353 \def (eq_ind nat TMP_339 TMP_341 H5 TMP_348 TMP_352) in 
(let TMP_354 \def (subst0_weight_le v t1 t2 TMP_321 H2 TMP_324 TMP_327 
TMP_336 TMP_353) in (let TMP_355 \def (lt_le_plus_plus TMP_310 TMP_311 
TMP_315 TMP_319 TMP_320 TMP_354) in (lt_n_S TMP_303 TMP_309 
TMP_355)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_397 \def (\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v 
t1 t2)).(\lambda (H3: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (lt (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: (lt 
(weight_map f (lift (S i) O v)) (g i))).(let TMP_357 \def (weight_map f u2) 
in (let TMP_358 \def (wadd f O) in (let TMP_359 \def (weight_map TMP_358 t2) 
in (let TMP_360 \def (plus TMP_357 TMP_359) in (let TMP_361 \def (weight_map 
g u1) in (let TMP_362 \def (wadd g O) in (let TMP_363 \def (weight_map 
TMP_362 t1) in (let TMP_364 \def (plus TMP_361 TMP_363) in (let TMP_365 \def 
(weight_map f u2) in (let TMP_366 \def (weight_map g u1) in (let TMP_367 \def 
(wadd f O) in (let TMP_368 \def (weight_map TMP_367 t2) in (let TMP_369 \def 
(wadd g O) in (let TMP_370 \def (weight_map TMP_369 t1) in (let TMP_371 \def 
(H1 f g H4 H5) in (let TMP_372 \def (wadd f O) in (let TMP_373 \def (wadd g 
O) in (let TMP_381 \def (\lambda (m: nat).(let TMP_374 \def (wadd f O m) in 
(let TMP_375 \def (wadd g O m) in (let TMP_376 \def (wadd f O m) in (let 
TMP_377 \def (wadd g O m) in (let TMP_378 \def (le_O_n O) in (let TMP_379 
\def (wadd_le f g H4 O O TMP_378 m) in (let TMP_380 \def (le_n_S TMP_376 
TMP_377 TMP_379) in (le_S_n TMP_374 TMP_375 TMP_380))))))))) in (let TMP_382 
\def (S i) in (let TMP_383 \def (lift TMP_382 O v) in (let TMP_384 \def 
(weight_map f TMP_383) in (let TMP_386 \def (\lambda (n: nat).(let TMP_385 
\def (g i) in (lt n TMP_385))) in (let TMP_387 \def (wadd f O) in (let 
TMP_388 \def (S i) in (let TMP_389 \def (S TMP_388) in (let TMP_390 \def 
(lift TMP_389 O v) in (let TMP_391 \def (weight_map TMP_387 TMP_390) in (let 
TMP_392 \def (S i) in (let TMP_393 \def (lift_weight_add_O O v TMP_392 f) in 
(let TMP_394 \def (eq_ind nat TMP_384 TMP_386 H5 TMP_391 TMP_393) in (let 
TMP_395 \def (H3 TMP_372 TMP_373 TMP_381 TMP_394) in (let TMP_396 \def 
(lt_plus_plus TMP_365 TMP_366 TMP_368 TMP_370 TMP_371 TMP_395) in (lt_n_S 
TMP_360 TMP_364 TMP_396))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_438 \def (\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 (S i) v 
t1 t2)).(\lambda (H3: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f m) (g m)))) \to ((lt (weight_map f (lift (S 
(S i)) O v)) (g (S i))) \to (lt (weight_map f t2) (weight_map g 
t1)))))))).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f m) (g m))))).(\lambda (H5: (lt 
(weight_map f (lift (S i) O v)) (g i))).(let TMP_398 \def (weight_map f u2) 
in (let TMP_399 \def (wadd f O) in (let TMP_400 \def (weight_map TMP_399 t2) 
in (let TMP_401 \def (plus TMP_398 TMP_400) in (let TMP_402 \def (weight_map 
g u1) in (let TMP_403 \def (wadd g O) in (let TMP_404 \def (weight_map 
TMP_403 t1) in (let TMP_405 \def (plus TMP_402 TMP_404) in (let TMP_406 \def 
(weight_map f u2) in (let TMP_407 \def (weight_map g u1) in (let TMP_408 \def 
(wadd f O) in (let TMP_409 \def (weight_map TMP_408 t2) in (let TMP_410 \def 
(wadd g O) in (let TMP_411 \def (weight_map TMP_410 t1) in (let TMP_412 \def 
(H1 f g H4 H5) in (let TMP_413 \def (wadd f O) in (let TMP_414 \def (wadd g 
O) in (let TMP_422 \def (\lambda (m: nat).(let TMP_415 \def (wadd f O m) in 
(let TMP_416 \def (wadd g O m) in (let TMP_417 \def (wadd f O m) in (let 
TMP_418 \def (wadd g O m) in (let TMP_419 \def (le_O_n O) in (let TMP_420 
\def (wadd_le f g H4 O O TMP_419 m) in (let TMP_421 \def (le_n_S TMP_417 
TMP_418 TMP_420) in (le_S_n TMP_415 TMP_416 TMP_421))))))))) in (let TMP_423 
\def (S i) in (let TMP_424 \def (lift TMP_423 O v) in (let TMP_425 \def 
(weight_map f TMP_424) in (let TMP_427 \def (\lambda (n: nat).(let TMP_426 
\def (g i) in (lt n TMP_426))) in (let TMP_428 \def (wadd f O) in (let 
TMP_429 \def (S i) in (let TMP_430 \def (S TMP_429) in (let TMP_431 \def 
(lift TMP_430 O v) in (let TMP_432 \def (weight_map TMP_428 TMP_431) in (let 
TMP_433 \def (S i) in (let TMP_434 \def (lift_weight_add_O O v TMP_433 f) in 
(let TMP_435 \def (eq_ind nat TMP_425 TMP_427 H5 TMP_432 TMP_434) in (let 
TMP_436 \def (H3 TMP_413 TMP_414 TMP_422 TMP_435) in (let TMP_437 \def 
(lt_plus_plus TMP_406 TMP_407 TMP_409 TMP_411 TMP_412 TMP_436) in (lt_n_S 
TMP_401 TMP_405 TMP_437))))))))))))))))))))))))))))))))))))))))) in (B_ind 
TMP_297 TMP_356 TMP_397 TMP_438 b)))))) in (let TMP_453 \def (\lambda (_: 
F).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (subst0 i v t1 
t2)).(\lambda (H3: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (m: nat).(le (f0 m) (g m)))) \to ((lt (weight_map f0 (lift 
(S i) O v)) (g i)) \to (lt (weight_map f0 t2) (weight_map g 
t1)))))))).(\lambda (f0: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H4: ((\forall (m: nat).(le (f0 m) (g m))))).(\lambda (H5: 
(lt (weight_map f0 (lift (S i) O v)) (g i))).(let TMP_440 \def (weight_map f0 
u2) in (let TMP_441 \def (weight_map f0 t2) in (let TMP_442 \def (plus 
TMP_440 TMP_441) in (let TMP_443 \def (weight_map g u1) in (let TMP_444 \def 
(weight_map g t1) in (let TMP_445 \def (plus TMP_443 TMP_444) in (let TMP_446 
\def (weight_map f0 u2) in (let TMP_447 \def (weight_map g u1) in (let 
TMP_448 \def (weight_map f0 t2) in (let TMP_449 \def (weight_map g t1) in 
(let TMP_450 \def (H1 f0 g H4 H5) in (let TMP_451 \def (H3 f0 g H4 H5) in 
(let TMP_452 \def (lt_plus_plus TMP_446 TMP_447 TMP_448 TMP_449 TMP_450 
TMP_451) in (lt_n_S TMP_442 TMP_445 TMP_452))))))))))))))))))))))) in (K_ind 
TMP_290 TMP_439 TMP_453 k))))))))))) in (subst0_ind TMP_3 TMP_4 TMP_129 
TMP_285 TMP_454 d u t z H)))))))))).

theorem subst0_tlt_head:
 \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt 
(THead (Bind Abbr) u z) (THead (Bind Abbr) u t)))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (H: (subst0 O u t 
z)).(let TMP_1 \def (\lambda (_: nat).O) in (let TMP_2 \def (weight_map TMP_1 
u) in (let TMP_3 \def (\lambda (_: nat).O) in (let TMP_4 \def (\lambda (_: 
nat).O) in (let TMP_5 \def (weight_map TMP_4 u) in (let TMP_6 \def (S TMP_5) 
in (let TMP_7 \def (wadd TMP_3 TMP_6) in (let TMP_8 \def (weight_map TMP_7 z) 
in (let TMP_9 \def (plus TMP_2 TMP_8) in (let TMP_10 \def (\lambda (_: 
nat).O) in (let TMP_11 \def (weight_map TMP_10 u) in (let TMP_12 \def 
(\lambda (_: nat).O) in (let TMP_13 \def (\lambda (_: nat).O) in (let TMP_14 
\def (weight_map TMP_13 u) in (let TMP_15 \def (S TMP_14) in (let TMP_16 \def 
(wadd TMP_12 TMP_15) in (let TMP_17 \def (weight_map TMP_16 t) in (let TMP_18 
\def (plus TMP_11 TMP_17) in (let TMP_19 \def (\lambda (_: nat).O) in (let 
TMP_20 \def (weight_map TMP_19 u) in (let TMP_21 \def (\lambda (_: nat).O) in 
(let TMP_22 \def (weight_map TMP_21 u) in (let TMP_23 \def (\lambda (_: 
nat).O) in (let TMP_24 \def (\lambda (_: nat).O) in (let TMP_25 \def 
(weight_map TMP_24 u) in (let TMP_26 \def (S TMP_25) in (let TMP_27 \def 
(wadd TMP_23 TMP_26) in (let TMP_28 \def (weight_map TMP_27 z) in (let TMP_29 
\def (\lambda (_: nat).O) in (let TMP_30 \def (\lambda (_: nat).O) in (let 
TMP_31 \def (weight_map TMP_30 u) in (let TMP_32 \def (S TMP_31) in (let 
TMP_33 \def (wadd TMP_29 TMP_32) in (let TMP_34 \def (weight_map TMP_33 t) in 
(let TMP_35 \def (\lambda (_: nat).O) in (let TMP_36 \def (weight_map TMP_35 
u) in (let TMP_37 \def (le_n TMP_36) in (let TMP_38 \def (\lambda (_: nat).O) 
in (let TMP_39 \def (\lambda (_: nat).O) in (let TMP_40 \def (weight_map 
TMP_39 u) in (let TMP_41 \def (S TMP_40) in (let TMP_42 \def (wadd TMP_38 
TMP_41) in (let TMP_43 \def (\lambda (_: nat).O) in (let TMP_44 \def (\lambda 
(_: nat).O) in (let TMP_45 \def (weight_map TMP_44 u) in (let TMP_46 \def (S 
TMP_45) in (let TMP_47 \def (wadd TMP_43 TMP_46) in (let TMP_53 \def (\lambda 
(m: nat).(let TMP_48 \def (\lambda (_: nat).O) in (let TMP_49 \def (\lambda 
(_: nat).O) in (let TMP_50 \def (weight_map TMP_49 u) in (let TMP_51 \def (S 
TMP_50) in (let TMP_52 \def (wadd TMP_48 TMP_51 m) in (le_n TMP_52))))))) in 
(let TMP_54 \def (\lambda (_: nat).O) in (let TMP_55 \def (lift O O u) in 
(let TMP_56 \def (weight_map TMP_54 TMP_55) in (let TMP_60 \def (\lambda (n: 
nat).(let TMP_57 \def (\lambda (_: nat).O) in (let TMP_58 \def (weight_map 
TMP_57 u) in (let TMP_59 \def (S TMP_58) in (lt n TMP_59))))) in (let TMP_66 
\def (\lambda (t0: T).(let TMP_61 \def (\lambda (_: nat).O) in (let TMP_62 
\def (weight_map TMP_61 t0) in (let TMP_63 \def (\lambda (_: nat).O) in (let 
TMP_64 \def (weight_map TMP_63 u) in (let TMP_65 \def (S TMP_64) in (lt 
TMP_62 TMP_65))))))) in (let TMP_67 \def (\lambda (_: nat).O) in (let TMP_68 
\def (weight_map TMP_67 u) in (let TMP_69 \def (S TMP_68) in (let TMP_70 \def 
(le_n TMP_69) in (let TMP_71 \def (lift O O u) in (let TMP_72 \def (lift_r u 
O) in (let TMP_73 \def (eq_ind_r T u TMP_66 TMP_70 TMP_71 TMP_72) in (let 
TMP_74 \def (\lambda (_: nat).O) in (let TMP_75 \def (\lambda (_: nat).O) in 
(let TMP_76 \def (weight_map TMP_75 u) in (let TMP_77 \def (S TMP_76) in (let 
TMP_78 \def (wadd TMP_74 TMP_77) in (let TMP_79 \def (S O) in (let TMP_80 
\def (lift TMP_79 O u) in (let TMP_81 \def (weight_map TMP_78 TMP_80) in (let 
TMP_82 \def (\lambda (_: nat).O) in (let TMP_83 \def (weight_map TMP_82 u) in 
(let TMP_84 \def (S TMP_83) in (let TMP_85 \def (\lambda (_: nat).O) in (let 
TMP_86 \def (lift_weight_add_O TMP_84 u O TMP_85) in (let TMP_87 \def (eq_ind 
nat TMP_56 TMP_60 TMP_73 TMP_81 TMP_86) in (let TMP_88 \def (subst0_weight_lt 
u t z O H TMP_42 TMP_47 TMP_53 TMP_87) in (let TMP_89 \def (le_lt_plus_plus 
TMP_20 TMP_22 TMP_28 TMP_34 TMP_37 TMP_88) in (lt_n_S TMP_9 TMP_18 
TMP_89))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))).

theorem subst0_tlt:
 \forall (u: T).(\forall (t: T).(\forall (z: T).((subst0 O u t z) \to (tlt z 
(THead (Bind Abbr) u t)))))
\def
 \lambda (u: T).(\lambda (t: T).(\lambda (z: T).(\lambda (H: (subst0 O u t 
z)).(let TMP_1 \def (Bind Abbr) in (let TMP_2 \def (THead TMP_1 u z) in (let 
TMP_3 \def (Bind Abbr) in (let TMP_4 \def (THead TMP_3 u t) in (let TMP_5 
\def (Bind Abbr) in (let TMP_6 \def (tlt_head_dx TMP_5 u z) in (let TMP_7 
\def (subst0_tlt_head u t z H) in (tlt_trans TMP_2 z TMP_4 TMP_6 
TMP_7))))))))))).

