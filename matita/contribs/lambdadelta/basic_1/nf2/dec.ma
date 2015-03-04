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

include "basic_1/nf2/defs.ma".

include "basic_1/pr2/clen.ma".

include "basic_1/pr0/dec.ma".

include "basic_1/C/props.ma".

theorem nf2_dec:
 \forall (c: C).(\forall (t1: T).(or (nf2 c t1) (ex2 T (\lambda (t2: T).((eq 
T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c t1 t2)))))
\def
 \lambda (c: C).(let TMP_5 \def (\lambda (c0: C).(\forall (t1: T).(let TMP_1 
\def (\forall (t2: T).((pr2 c0 t1 t2) \to (eq T t1 t2))) in (let TMP_2 \def 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_3 \def 
(\lambda (t2: T).(pr2 c0 t1 t2)) in (let TMP_4 \def (ex2 T TMP_2 TMP_3) in 
(or TMP_1 TMP_4))))))) in (let TMP_44 \def (\lambda (n: nat).(\lambda (t1: 
T).(let H_x \def (nf0_dec t1) in (let H \def H_x in (let TMP_6 \def (\forall 
(t2: T).((pr0 t1 t2) \to (eq T t1 t2))) in (let TMP_7 \def (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_8 \def (\lambda (t2: 
T).(pr0 t1 t2)) in (let TMP_9 \def (ex2 T TMP_7 TMP_8) in (let TMP_10 \def 
(\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) in (let TMP_11 
\def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let 
TMP_13 \def (\lambda (t2: T).(let TMP_12 \def (CSort n) in (pr2 TMP_12 t1 
t2))) in (let TMP_14 \def (ex2 T TMP_11 TMP_13) in (let TMP_15 \def (or 
TMP_10 TMP_14) in (let TMP_22 \def (\lambda (H0: ((\forall (t2: T).((pr0 t1 
t2) \to (eq T t1 t2))))).(let TMP_16 \def (\forall (t2: T).((pr2 (CSort n) t1 
t2) \to (eq T t1 t2))) in (let TMP_17 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_19 \def (\lambda (t2: T).(let TMP_18 \def 
(CSort n) in (pr2 TMP_18 t1 t2))) in (let TMP_20 \def (ex2 T TMP_17 TMP_19) 
in (let TMP_21 \def (\lambda (t2: T).(\lambda (H1: (pr2 (CSort n) t1 
t2)).(let H_y \def (pr2_gen_csort t1 t2 n H1) in (H0 t2 H_y)))) in (or_introl 
TMP_16 TMP_20 TMP_21))))))) in (let TMP_43 \def (\lambda (H0: (ex2 T (\lambda 
(t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t1 
t2)))).(let TMP_23 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) in (let TMP_24 \def (\lambda (t2: T).(pr0 t1 t2)) in (let TMP_25 
\def (\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) in (let 
TMP_26 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in 
(let TMP_28 \def (\lambda (t2: T).(let TMP_27 \def (CSort n) in (pr2 TMP_27 
t1 t2))) in (let TMP_29 \def (ex2 T TMP_26 TMP_28) in (let TMP_30 \def (or 
TMP_25 TMP_29) in (let TMP_42 \def (\lambda (x: T).(\lambda (H1: (((eq T t1 
x) \to (\forall (P: Prop).P)))).(\lambda (H2: (pr0 t1 x)).(let TMP_31 \def 
(\forall (t2: T).((pr2 (CSort n) t1 t2) \to (eq T t1 t2))) in (let TMP_32 
\def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let 
TMP_34 \def (\lambda (t2: T).(let TMP_33 \def (CSort n) in (pr2 TMP_33 t1 
t2))) in (let TMP_35 \def (ex2 T TMP_32 TMP_34) in (let TMP_36 \def (\lambda 
(t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_38 \def 
(\lambda (t2: T).(let TMP_37 \def (CSort n) in (pr2 TMP_37 t1 t2))) in (let 
TMP_39 \def (CSort n) in (let TMP_40 \def (pr2_free TMP_39 t1 x H2) in (let 
TMP_41 \def (ex_intro2 T TMP_36 TMP_38 x H1 TMP_40) in (or_intror TMP_31 
TMP_35 TMP_41))))))))))))) in (ex2_ind T TMP_23 TMP_24 TMP_30 TMP_42 
H0)))))))))) in (or_ind TMP_6 TMP_9 TMP_15 TMP_22 TMP_43 H)))))))))))))))) in 
(let TMP_404 \def (\lambda (c0: C).(\lambda (H: ((\forall (t1: T).(or 
(\forall (t2: T).((pr2 c0 t1 t2) \to (eq T t1 t2))) (ex2 T (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c0 t1 
t2))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (t1: T).(let H_x \def (H 
t1) in (let H0 \def H_x in (let TMP_45 \def (\forall (t2: T).((pr2 c0 t1 t2) 
\to (eq T t1 t2))) in (let TMP_46 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_47 \def (\lambda (t2: T).(pr2 c0 t1 t2)) 
in (let TMP_48 \def (ex2 T TMP_46 TMP_47) in (let TMP_49 \def (\forall (t2: 
T).((pr2 (CTail k t c0) t1 t2) \to (eq T t1 t2))) in (let TMP_50 \def 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_52 
\def (\lambda (t2: T).(let TMP_51 \def (CTail k t c0) in (pr2 TMP_51 t1 t2))) 
in (let TMP_53 \def (ex2 T TMP_50 TMP_52) in (let TMP_54 \def (or TMP_49 
TMP_53) in (let TMP_383 \def (\lambda (H1: ((\forall (t2: T).((pr2 c0 t1 t2) 
\to (eq T t1 t2))))).(let TMP_60 \def (\lambda (k0: K).(let TMP_55 \def 
(\forall (t2: T).((pr2 (CTail k0 t c0) t1 t2) \to (eq T t1 t2))) in (let 
TMP_56 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in 
(let TMP_58 \def (\lambda (t2: T).(let TMP_57 \def (CTail k0 t c0) in (pr2 
TMP_57 t1 t2))) in (let TMP_59 \def (ex2 T TMP_56 TMP_58) in (or TMP_55 
TMP_59)))))) in (let TMP_350 \def (\lambda (b: B).(let TMP_67 \def (\lambda 
(b0: B).(let TMP_61 \def (\forall (t2: T).((pr2 (CTail (Bind b0) t c0) t1 t2) 
\to (eq T t1 t2))) in (let TMP_62 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_65 \def (\lambda (t2: T).(let TMP_63 \def 
(Bind b0) in (let TMP_64 \def (CTail TMP_63 t c0) in (pr2 TMP_64 t1 t2)))) in 
(let TMP_66 \def (ex2 T TMP_62 TMP_65) in (or TMP_61 TMP_66)))))) in (let 
TMP_68 \def (clen c0) in (let H_x0 \def (dnf_dec t t1 TMP_68) in (let H2 \def 
H_x0 in (let TMP_78 \def (\lambda (v: T).(let TMP_69 \def (clen c0) in (let 
TMP_70 \def (S O) in (let TMP_71 \def (clen c0) in (let TMP_72 \def (lift 
TMP_70 TMP_71 v) in (let TMP_73 \def (subst0 TMP_69 t t1 TMP_72) in (let 
TMP_74 \def (S O) in (let TMP_75 \def (clen c0) in (let TMP_76 \def (lift 
TMP_74 TMP_75 v) in (let TMP_77 \def (eq T t1 TMP_76) in (or TMP_73 
TMP_77))))))))))) in (let TMP_79 \def (\forall (t2: T).((pr2 (CTail (Bind 
Abbr) t c0) t1 t2) \to (eq T t1 t2))) in (let TMP_80 \def (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_83 \def (\lambda 
(t2: T).(let TMP_81 \def (Bind Abbr) in (let TMP_82 \def (CTail TMP_81 t c0) 
in (pr2 TMP_82 t1 t2)))) in (let TMP_84 \def (ex2 T TMP_80 TMP_83) in (let 
TMP_85 \def (or TMP_79 TMP_84) in (let TMP_284 \def (\lambda (x: T).(\lambda 
(H3: (or (subst0 (clen c0) t t1 (lift (S O) (clen c0) x)) (eq T t1 (lift (S 
O) (clen c0) x)))).(let TMP_86 \def (clen c0) in (let TMP_87 \def (S O) in 
(let TMP_88 \def (clen c0) in (let TMP_89 \def (lift TMP_87 TMP_88 x) in (let 
TMP_90 \def (subst0 TMP_86 t t1 TMP_89) in (let TMP_91 \def (S O) in (let 
TMP_92 \def (clen c0) in (let TMP_93 \def (lift TMP_91 TMP_92 x) in (let 
TMP_94 \def (eq T t1 TMP_93) in (let TMP_95 \def (\forall (t2: T).((pr2 
(CTail (Bind Abbr) t c0) t1 t2) \to (eq T t1 t2))) in (let TMP_96 \def 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_99 
\def (\lambda (t2: T).(let TMP_97 \def (Bind Abbr) in (let TMP_98 \def (CTail 
TMP_97 t c0) in (pr2 TMP_98 t1 t2)))) in (let TMP_100 \def (ex2 T TMP_96 
TMP_99) in (let TMP_101 \def (or TMP_95 TMP_100) in (let TMP_173 \def 
(\lambda (H4: (subst0 (clen c0) t t1 (lift (S O) (clen c0) x))).(let H_x1 
\def (getl_ctail_clen Abbr t c0) in (let H5 \def H_x1 in (let TMP_108 \def 
(\lambda (n: nat).(let TMP_102 \def (clen c0) in (let TMP_103 \def (Bind 
Abbr) in (let TMP_104 \def (CTail TMP_103 t c0) in (let TMP_105 \def (CSort 
n) in (let TMP_106 \def (Bind Abbr) in (let TMP_107 \def (CHead TMP_105 
TMP_106 t) in (getl TMP_102 TMP_104 TMP_107)))))))) in (let TMP_109 \def 
(\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) t1 t2) \to (eq T t1 t2))) in 
(let TMP_110 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
in (let TMP_113 \def (\lambda (t2: T).(let TMP_111 \def (Bind Abbr) in (let 
TMP_112 \def (CTail TMP_111 t c0) in (pr2 TMP_112 t1 t2)))) in (let TMP_114 
\def (ex2 T TMP_110 TMP_113) in (let TMP_115 \def (or TMP_109 TMP_114) in 
(let TMP_172 \def (\lambda (x0: nat).(\lambda (H6: (getl (clen c0) (CTail 
(Bind Abbr) t c0) (CHead (CSort x0) (Bind Abbr) t))).(let TMP_116 \def 
(\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) t1 t2) \to (eq T t1 t2))) in 
(let TMP_117 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
in (let TMP_120 \def (\lambda (t2: T).(let TMP_118 \def (Bind Abbr) in (let 
TMP_119 \def (CTail TMP_118 t c0) in (pr2 TMP_119 t1 t2)))) in (let TMP_121 
\def (ex2 T TMP_117 TMP_120) in (let TMP_122 \def (\lambda (t2: T).((eq T t1 
t2) \to (\forall (P: Prop).P))) in (let TMP_125 \def (\lambda (t2: T).(let 
TMP_123 \def (Bind Abbr) in (let TMP_124 \def (CTail TMP_123 t c0) in (pr2 
TMP_124 t1 t2)))) in (let TMP_126 \def (S O) in (let TMP_127 \def (clen c0) 
in (let TMP_128 \def (lift TMP_126 TMP_127 x) in (let TMP_161 \def (\lambda 
(H7: (eq T t1 (lift (S O) (clen c0) x))).(\lambda (P: Prop).(let TMP_133 \def 
(\lambda (t0: T).(let TMP_129 \def (clen c0) in (let TMP_130 \def (S O) in 
(let TMP_131 \def (clen c0) in (let TMP_132 \def (lift TMP_130 TMP_131 x) in 
(subst0 TMP_129 t t0 TMP_132)))))) in (let TMP_134 \def (S O) in (let TMP_135 
\def (clen c0) in (let TMP_136 \def (lift TMP_134 TMP_135 x) in (let H8 \def 
(eq_ind T t1 TMP_133 H4 TMP_136 H7) in (let TMP_137 \def (S O) in (let 
TMP_138 \def (clen c0) in (let TMP_139 \def (lift TMP_137 TMP_138 x) in (let 
TMP_140 \def (S O) in (let TMP_141 \def (clen c0) in (let TMP_142 \def (clen 
c0) in (let TMP_143 \def (clen c0) in (let TMP_144 \def (le_n TMP_143) in 
(let TMP_145 \def (S O) in (let TMP_146 \def (clen c0) in (let TMP_147 \def 
(plus TMP_145 TMP_146) in (let TMP_149 \def (\lambda (n: nat).(let TMP_148 
\def (clen c0) in (lt TMP_148 n))) in (let TMP_150 \def (S O) in (let TMP_151 
\def (clen c0) in (let TMP_152 \def (plus TMP_150 TMP_151) in (let TMP_153 
\def (le_n TMP_152) in (let TMP_154 \def (clen c0) in (let TMP_155 \def (S O) 
in (let TMP_156 \def (plus TMP_154 TMP_155) in (let TMP_157 \def (clen c0) in 
(let TMP_158 \def (S O) in (let TMP_159 \def (plus_sym TMP_157 TMP_158) in 
(let TMP_160 \def (eq_ind_r nat TMP_147 TMP_149 TMP_153 TMP_156 TMP_159) in 
(subst0_gen_lift_false x t TMP_139 TMP_140 TMP_141 TMP_142 TMP_144 TMP_160 H8 
P))))))))))))))))))))))))))))))) in (let TMP_162 \def (Bind Abbr) in (let 
TMP_163 \def (CTail TMP_162 t c0) in (let TMP_164 \def (CSort x0) in (let 
TMP_165 \def (clen c0) in (let TMP_166 \def (pr0_refl t1) in (let TMP_167 
\def (S O) in (let TMP_168 \def (clen c0) in (let TMP_169 \def (lift TMP_167 
TMP_168 x) in (let TMP_170 \def (pr2_delta TMP_163 TMP_164 t TMP_165 H6 t1 t1 
TMP_166 TMP_169 H4) in (let TMP_171 \def (ex_intro2 T TMP_122 TMP_125 TMP_128 
TMP_161 TMP_170) in (or_intror TMP_116 TMP_121 TMP_171))))))))))))))))))))))) 
in (ex_ind nat TMP_108 TMP_115 TMP_172 H5))))))))))) in (let TMP_283 \def 
(\lambda (H4: (eq T t1 (lift (S O) (clen c0) x))).(let TMP_174 \def (\lambda 
(t0: T).(\forall (t2: T).((pr2 c0 t0 t2) \to (eq T t0 t2)))) in (let TMP_175 
\def (S O) in (let TMP_176 \def (clen c0) in (let TMP_177 \def (lift TMP_175 
TMP_176 x) in (let H5 \def (eq_ind T t1 TMP_174 H1 TMP_177 H4) in (let 
TMP_178 \def (S O) in (let TMP_179 \def (clen c0) in (let TMP_180 \def (lift 
TMP_178 TMP_179 x) in (let TMP_187 \def (\lambda (t0: T).(let TMP_181 \def 
(\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) t0 t2) \to (eq T t0 t2))) in 
(let TMP_182 \def (\lambda (t2: T).((eq T t0 t2) \to (\forall (P: Prop).P))) 
in (let TMP_185 \def (\lambda (t2: T).(let TMP_183 \def (Bind Abbr) in (let 
TMP_184 \def (CTail TMP_183 t c0) in (pr2 TMP_184 t0 t2)))) in (let TMP_186 
\def (ex2 T TMP_182 TMP_185) in (or TMP_181 TMP_186)))))) in (let TMP_191 
\def (\forall (t2: T).((pr2 (CTail (Bind Abbr) t c0) (lift (S O) (clen c0) x) 
t2) \to (let TMP_188 \def (S O) in (let TMP_189 \def (clen c0) in (let 
TMP_190 \def (lift TMP_188 TMP_189 x) in (eq T TMP_190 t2)))))) in (let 
TMP_192 \def (\lambda (t2: T).((eq T (lift (S O) (clen c0) x) t2) \to 
(\forall (P: Prop).P))) in (let TMP_198 \def (\lambda (t2: T).(let TMP_193 
\def (Bind Abbr) in (let TMP_194 \def (CTail TMP_193 t c0) in (let TMP_195 
\def (S O) in (let TMP_196 \def (clen c0) in (let TMP_197 \def (lift TMP_195 
TMP_196 x) in (pr2 TMP_194 TMP_197 t2))))))) in (let TMP_199 \def (ex2 T 
TMP_192 TMP_198) in (let TMP_281 \def (\lambda (t2: T).(\lambda (H6: (pr2 
(CTail (Bind Abbr) t c0) (lift (S O) (clen c0) x) t2)).(let TMP_200 \def 
(Bind Abbr) in (let TMP_201 \def (S O) in (let TMP_202 \def (clen c0) in (let 
TMP_203 \def (lift TMP_201 TMP_202 x) in (let H_x1 \def (pr2_gen_ctail 
TMP_200 c0 t TMP_203 t2 H6) in (let H7 \def H_x1 in (let TMP_204 \def (S O) 
in (let TMP_205 \def (clen c0) in (let TMP_206 \def (lift TMP_204 TMP_205 x) 
in (let TMP_207 \def (pr2 c0 TMP_206 t2) in (let TMP_210 \def (\lambda (_: 
T).(let TMP_208 \def (Bind Abbr) in (let TMP_209 \def (Bind Abbr) in (eq K 
TMP_208 TMP_209)))) in (let TMP_214 \def (\lambda (t0: T).(let TMP_211 \def 
(S O) in (let TMP_212 \def (clen c0) in (let TMP_213 \def (lift TMP_211 
TMP_212 x) in (pr0 TMP_213 t0))))) in (let TMP_216 \def (\lambda (t0: T).(let 
TMP_215 \def (clen c0) in (subst0 TMP_215 t t0 t2))) in (let TMP_217 \def 
(ex3 T TMP_210 TMP_214 TMP_216) in (let TMP_218 \def (S O) in (let TMP_219 
\def (clen c0) in (let TMP_220 \def (lift TMP_218 TMP_219 x) in (let TMP_221 
\def (eq T TMP_220 t2) in (let TMP_222 \def (\lambda (H8: (pr2 c0 (lift (S O) 
(clen c0) x) t2)).(H5 t2 H8)) in (let TMP_280 \def (\lambda (H8: (ex3 T 
(\lambda (_: T).(eq K (Bind Abbr) (Bind Abbr))) (\lambda (t0: T).(pr0 (lift 
(S O) (clen c0) x) t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2)))).(let 
TMP_225 \def (\lambda (_: T).(let TMP_223 \def (Bind Abbr) in (let TMP_224 
\def (Bind Abbr) in (eq K TMP_223 TMP_224)))) in (let TMP_229 \def (\lambda 
(t0: T).(let TMP_226 \def (S O) in (let TMP_227 \def (clen c0) in (let 
TMP_228 \def (lift TMP_226 TMP_227 x) in (pr0 TMP_228 t0))))) in (let TMP_231 
\def (\lambda (t0: T).(let TMP_230 \def (clen c0) in (subst0 TMP_230 t t0 
t2))) in (let TMP_232 \def (S O) in (let TMP_233 \def (clen c0) in (let 
TMP_234 \def (lift TMP_232 TMP_233 x) in (let TMP_235 \def (eq T TMP_234 t2) 
in (let TMP_279 \def (\lambda (x0: T).(\lambda (_: (eq K (Bind Abbr) (Bind 
Abbr))).(\lambda (H10: (pr0 (lift (S O) (clen c0) x) x0)).(\lambda (H11: 
(subst0 (clen c0) t x0 t2)).(let TMP_239 \def (\lambda (t3: T).(let TMP_236 
\def (S O) in (let TMP_237 \def (clen c0) in (let TMP_238 \def (lift TMP_236 
TMP_237 t3) in (eq T x0 TMP_238))))) in (let TMP_240 \def (\lambda (t3: 
T).(pr0 x t3)) in (let TMP_241 \def (S O) in (let TMP_242 \def (clen c0) in 
(let TMP_243 \def (lift TMP_241 TMP_242 x) in (let TMP_244 \def (eq T TMP_243 
t2) in (let TMP_275 \def (\lambda (x1: T).(\lambda (H12: (eq T x0 (lift (S O) 
(clen c0) x1))).(\lambda (_: (pr0 x x1)).(let TMP_246 \def (\lambda (t0: 
T).(let TMP_245 \def (clen c0) in (subst0 TMP_245 t t0 t2))) in (let TMP_247 
\def (S O) in (let TMP_248 \def (clen c0) in (let TMP_249 \def (lift TMP_247 
TMP_248 x1) in (let H14 \def (eq_ind T x0 TMP_246 H11 TMP_249 H12) in (let 
TMP_250 \def (S O) in (let TMP_251 \def (clen c0) in (let TMP_252 \def (clen 
c0) in (let TMP_253 \def (clen c0) in (let TMP_254 \def (le_n TMP_253) in 
(let TMP_255 \def (S O) in (let TMP_256 \def (clen c0) in (let TMP_257 \def 
(plus TMP_255 TMP_256) in (let TMP_259 \def (\lambda (n: nat).(let TMP_258 
\def (clen c0) in (lt TMP_258 n))) in (let TMP_260 \def (S O) in (let TMP_261 
\def (clen c0) in (let TMP_262 \def (plus TMP_260 TMP_261) in (let TMP_263 
\def (le_n TMP_262) in (let TMP_264 \def (clen c0) in (let TMP_265 \def (S O) 
in (let TMP_266 \def (plus TMP_264 TMP_265) in (let TMP_267 \def (clen c0) in 
(let TMP_268 \def (S O) in (let TMP_269 \def (plus_sym TMP_267 TMP_268) in 
(let TMP_270 \def (eq_ind_r nat TMP_257 TMP_259 TMP_263 TMP_266 TMP_269) in 
(let TMP_271 \def (S O) in (let TMP_272 \def (clen c0) in (let TMP_273 \def 
(lift TMP_271 TMP_272 x) in (let TMP_274 \def (eq T TMP_273 t2) in 
(subst0_gen_lift_false x1 t t2 TMP_250 TMP_251 TMP_252 TMP_254 TMP_270 H14 
TMP_274))))))))))))))))))))))))))))))))) in (let TMP_276 \def (S O) in (let 
TMP_277 \def (clen c0) in (let TMP_278 \def (pr0_gen_lift x x0 TMP_276 
TMP_277 H10) in (ex2_ind T TMP_239 TMP_240 TMP_244 TMP_275 
TMP_278))))))))))))))) in (ex3_ind T TMP_225 TMP_229 TMP_231 TMP_235 TMP_279 
H8)))))))))) in (or_ind TMP_207 TMP_217 TMP_221 TMP_222 TMP_280 
H7))))))))))))))))))))))) in (let TMP_282 \def (or_introl TMP_191 TMP_199 
TMP_281) in (eq_ind_r T TMP_180 TMP_187 TMP_282 t1 H4))))))))))))))))) in 
(or_ind TMP_90 TMP_94 TMP_101 TMP_173 TMP_283 H3))))))))))))))))))) in (let 
TMP_285 \def (ex_ind T TMP_78 TMP_85 TMP_284 H2) in (let TMP_286 \def 
(\forall (t2: T).((pr2 (CTail (Bind Abst) t c0) t1 t2) \to (eq T t1 t2))) in 
(let TMP_287 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) 
in (let TMP_290 \def (\lambda (t2: T).(let TMP_288 \def (Bind Abst) in (let 
TMP_289 \def (CTail TMP_288 t c0) in (pr2 TMP_289 t1 t2)))) in (let TMP_291 
\def (ex2 T TMP_287 TMP_290) in (let TMP_316 \def (\lambda (t2: T).(\lambda 
(H2: (pr2 (CTail (Bind Abst) t c0) t1 t2)).(let TMP_292 \def (Bind Abst) in 
(let H_x0 \def (pr2_gen_ctail TMP_292 c0 t t1 t2 H2) in (let H3 \def H_x0 in 
(let TMP_293 \def (pr2 c0 t1 t2) in (let TMP_296 \def (\lambda (_: T).(let 
TMP_294 \def (Bind Abst) in (let TMP_295 \def (Bind Abbr) in (eq K TMP_294 
TMP_295)))) in (let TMP_297 \def (\lambda (t0: T).(pr0 t1 t0)) in (let 
TMP_299 \def (\lambda (t0: T).(let TMP_298 \def (clen c0) in (subst0 TMP_298 
t t0 t2))) in (let TMP_300 \def (ex3 T TMP_296 TMP_297 TMP_299) in (let 
TMP_301 \def (eq T t1 t2) in (let TMP_302 \def (\lambda (H4: (pr2 c0 t1 
t2)).(H1 t2 H4)) in (let TMP_315 \def (\lambda (H4: (ex3 T (\lambda (_: 
T).(eq K (Bind Abst) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda 
(t0: T).(subst0 (clen c0) t t0 t2)))).(let TMP_305 \def (\lambda (_: T).(let 
TMP_303 \def (Bind Abst) in (let TMP_304 \def (Bind Abbr) in (eq K TMP_303 
TMP_304)))) in (let TMP_306 \def (\lambda (t0: T).(pr0 t1 t0)) in (let 
TMP_308 \def (\lambda (t0: T).(let TMP_307 \def (clen c0) in (subst0 TMP_307 
t t0 t2))) in (let TMP_309 \def (eq T t1 t2) in (let TMP_314 \def (\lambda 
(x0: T).(\lambda (H5: (eq K (Bind Abst) (Bind Abbr))).(\lambda (_: (pr0 t1 
x0)).(\lambda (_: (subst0 (clen c0) t x0 t2)).(let TMP_310 \def (Bind Abst) 
in (let TMP_311 \def (\lambda (ee: K).(match ee with [(Bind b0) \Rightarrow 
(match b0 with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])) in (let TMP_312 \def 
(Bind Abbr) in (let H8 \def (eq_ind K TMP_310 TMP_311 I TMP_312 H5) in (let 
TMP_313 \def (eq T t1 t2) in (False_ind TMP_313 H8)))))))))) in (ex3_ind T 
TMP_305 TMP_306 TMP_308 TMP_309 TMP_314 H4))))))) in (or_ind TMP_293 TMP_300 
TMP_301 TMP_302 TMP_315 H3)))))))))))))) in (let TMP_317 \def (or_introl 
TMP_286 TMP_291 TMP_316) in (let TMP_318 \def (\forall (t2: T).((pr2 (CTail 
(Bind Void) t c0) t1 t2) \to (eq T t1 t2))) in (let TMP_319 \def (\lambda 
(t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_322 \def 
(\lambda (t2: T).(let TMP_320 \def (Bind Void) in (let TMP_321 \def (CTail 
TMP_320 t c0) in (pr2 TMP_321 t1 t2)))) in (let TMP_323 \def (ex2 T TMP_319 
TMP_322) in (let TMP_348 \def (\lambda (t2: T).(\lambda (H2: (pr2 (CTail 
(Bind Void) t c0) t1 t2)).(let TMP_324 \def (Bind Void) in (let H_x0 \def 
(pr2_gen_ctail TMP_324 c0 t t1 t2 H2) in (let H3 \def H_x0 in (let TMP_325 
\def (pr2 c0 t1 t2) in (let TMP_328 \def (\lambda (_: T).(let TMP_326 \def 
(Bind Void) in (let TMP_327 \def (Bind Abbr) in (eq K TMP_326 TMP_327)))) in 
(let TMP_329 \def (\lambda (t0: T).(pr0 t1 t0)) in (let TMP_331 \def (\lambda 
(t0: T).(let TMP_330 \def (clen c0) in (subst0 TMP_330 t t0 t2))) in (let 
TMP_332 \def (ex3 T TMP_328 TMP_329 TMP_331) in (let TMP_333 \def (eq T t1 
t2) in (let TMP_334 \def (\lambda (H4: (pr2 c0 t1 t2)).(H1 t2 H4)) in (let 
TMP_347 \def (\lambda (H4: (ex3 T (\lambda (_: T).(eq K (Bind Void) (Bind 
Abbr))) (\lambda (t0: T).(pr0 t1 t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 
t2)))).(let TMP_337 \def (\lambda (_: T).(let TMP_335 \def (Bind Void) in 
(let TMP_336 \def (Bind Abbr) in (eq K TMP_335 TMP_336)))) in (let TMP_338 
\def (\lambda (t0: T).(pr0 t1 t0)) in (let TMP_340 \def (\lambda (t0: T).(let 
TMP_339 \def (clen c0) in (subst0 TMP_339 t t0 t2))) in (let TMP_341 \def (eq 
T t1 t2) in (let TMP_346 \def (\lambda (x0: T).(\lambda (H5: (eq K (Bind 
Void) (Bind Abbr))).(\lambda (_: (pr0 t1 x0)).(\lambda (_: (subst0 (clen c0) 
t x0 t2)).(let TMP_342 \def (Bind Void) in (let TMP_343 \def (\lambda (ee: 
K).(match ee with [(Bind b0) \Rightarrow (match b0 with [Abbr \Rightarrow 
False | Abst \Rightarrow False | Void \Rightarrow True]) | (Flat _) 
\Rightarrow False])) in (let TMP_344 \def (Bind Abbr) in (let H8 \def (eq_ind 
K TMP_342 TMP_343 I TMP_344 H5) in (let TMP_345 \def (eq T t1 t2) in 
(False_ind TMP_345 H8)))))))))) in (ex3_ind T TMP_337 TMP_338 TMP_340 TMP_341 
TMP_346 H4))))))) in (or_ind TMP_325 TMP_332 TMP_333 TMP_334 TMP_347 
H3)))))))))))))) in (let TMP_349 \def (or_introl TMP_318 TMP_323 TMP_348) in 
(B_ind TMP_67 TMP_285 TMP_317 TMP_349 b)))))))))))))))))))))))))) in (let 
TMP_382 \def (\lambda (f: F).(let TMP_351 \def (\forall (t2: T).((pr2 (CTail 
(Flat f) t c0) t1 t2) \to (eq T t1 t2))) in (let TMP_352 \def (\lambda (t2: 
T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_355 \def (\lambda 
(t2: T).(let TMP_353 \def (Flat f) in (let TMP_354 \def (CTail TMP_353 t c0) 
in (pr2 TMP_354 t1 t2)))) in (let TMP_356 \def (ex2 T TMP_352 TMP_355) in 
(let TMP_381 \def (\lambda (t2: T).(\lambda (H2: (pr2 (CTail (Flat f) t c0) 
t1 t2)).(let TMP_357 \def (Flat f) in (let H_x0 \def (pr2_gen_ctail TMP_357 
c0 t t1 t2 H2) in (let H3 \def H_x0 in (let TMP_358 \def (pr2 c0 t1 t2) in 
(let TMP_361 \def (\lambda (_: T).(let TMP_359 \def (Flat f) in (let TMP_360 
\def (Bind Abbr) in (eq K TMP_359 TMP_360)))) in (let TMP_362 \def (\lambda 
(t0: T).(pr0 t1 t0)) in (let TMP_364 \def (\lambda (t0: T).(let TMP_363 \def 
(clen c0) in (subst0 TMP_363 t t0 t2))) in (let TMP_365 \def (ex3 T TMP_361 
TMP_362 TMP_364) in (let TMP_366 \def (eq T t1 t2) in (let TMP_367 \def 
(\lambda (H4: (pr2 c0 t1 t2)).(H1 t2 H4)) in (let TMP_380 \def (\lambda (H4: 
(ex3 T (\lambda (_: T).(eq K (Flat f) (Bind Abbr))) (\lambda (t0: T).(pr0 t1 
t0)) (\lambda (t0: T).(subst0 (clen c0) t t0 t2)))).(let TMP_370 \def 
(\lambda (_: T).(let TMP_368 \def (Flat f) in (let TMP_369 \def (Bind Abbr) 
in (eq K TMP_368 TMP_369)))) in (let TMP_371 \def (\lambda (t0: T).(pr0 t1 
t0)) in (let TMP_373 \def (\lambda (t0: T).(let TMP_372 \def (clen c0) in 
(subst0 TMP_372 t t0 t2))) in (let TMP_374 \def (eq T t1 t2) in (let TMP_379 
\def (\lambda (x0: T).(\lambda (H5: (eq K (Flat f) (Bind Abbr))).(\lambda (_: 
(pr0 t1 x0)).(\lambda (_: (subst0 (clen c0) t x0 t2)).(let TMP_375 \def (Flat 
f) in (let TMP_376 \def (\lambda (ee: K).(match ee with [(Bind _) \Rightarrow 
False | (Flat _) \Rightarrow True])) in (let TMP_377 \def (Bind Abbr) in (let 
H8 \def (eq_ind K TMP_375 TMP_376 I TMP_377 H5) in (let TMP_378 \def (eq T t1 
t2) in (False_ind TMP_378 H8)))))))))) in (ex3_ind T TMP_370 TMP_371 TMP_373 
TMP_374 TMP_379 H4))))))) in (or_ind TMP_358 TMP_365 TMP_366 TMP_367 TMP_380 
H3)))))))))))))) in (or_introl TMP_351 TMP_356 TMP_381))))))) in (K_ind 
TMP_60 TMP_350 TMP_382 k))))) in (let TMP_403 \def (\lambda (H1: (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 c0 t1 t2)))).(let TMP_384 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_385 \def (\lambda (t2: T).(pr2 c0 t1 t2)) 
in (let TMP_386 \def (\forall (t2: T).((pr2 (CTail k t c0) t1 t2) \to (eq T 
t1 t2))) in (let TMP_387 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: 
Prop).P))) in (let TMP_389 \def (\lambda (t2: T).(let TMP_388 \def (CTail k t 
c0) in (pr2 TMP_388 t1 t2))) in (let TMP_390 \def (ex2 T TMP_387 TMP_389) in 
(let TMP_391 \def (or TMP_386 TMP_390) in (let TMP_402 \def (\lambda (x: 
T).(\lambda (H2: (((eq T t1 x) \to (\forall (P: Prop).P)))).(\lambda (H3: 
(pr2 c0 t1 x)).(let TMP_392 \def (\forall (t2: T).((pr2 (CTail k t c0) t1 t2) 
\to (eq T t1 t2))) in (let TMP_393 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_395 \def (\lambda (t2: T).(let TMP_394 
\def (CTail k t c0) in (pr2 TMP_394 t1 t2))) in (let TMP_396 \def (ex2 T 
TMP_393 TMP_395) in (let TMP_397 \def (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) in (let TMP_399 \def (\lambda (t2: T).(let TMP_398 
\def (CTail k t c0) in (pr2 TMP_398 t1 t2))) in (let TMP_400 \def (pr2_ctail 
c0 t1 x H3 k t) in (let TMP_401 \def (ex_intro2 T TMP_397 TMP_399 x H2 
TMP_400) in (or_intror TMP_392 TMP_396 TMP_401)))))))))))) in (ex2_ind T 
TMP_384 TMP_385 TMP_391 TMP_402 H1)))))))))) in (or_ind TMP_45 TMP_48 TMP_54 
TMP_383 TMP_403 H0))))))))))))))))))) in (c_tail_ind TMP_5 TMP_44 TMP_404 
c)))).

