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

include "basic_1/csubc/arity.ma".

include "basic_1/csubc/getl.ma".

include "basic_1/csubc/drop1.ma".

include "basic_1/csubc/props.ma".

theorem sc3_arity_csubc:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (a: A).((arity g c1 
t a) \to (\forall (d1: C).(\forall (is: PList).((drop1 is d1 c1) \to (\forall 
(c2: C).((csubc g d1 c2) \to (sc3 g a c2 (lift1 is t)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c1 t a)).(let TMP_2 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a0: A).(\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall 
(c2: C).((csubc g d1 c2) \to (let TMP_1 \def (lift1 is t0) in (sc3 g a0 c2 
TMP_1)))))))))) in (let TMP_21 \def (\lambda (c: C).(\lambda (n: 
nat).(\lambda (d1: C).(\lambda (is: PList).(\lambda (_: (drop1 is d1 
c)).(\lambda (c2: C).(\lambda (_: (csubc g d1 c2)).(let TMP_3 \def (TSort n) 
in (let TMP_7 \def (\lambda (t0: T).(let TMP_4 \def (ASort O n) in (let TMP_5 
\def (arity g c2 t0 TMP_4) in (let TMP_6 \def (sn3 c2 t0) in (land TMP_5 
TMP_6))))) in (let TMP_8 \def (TSort n) in (let TMP_9 \def (ASort O n) in 
(let TMP_10 \def (arity g c2 TMP_8 TMP_9) in (let TMP_11 \def (TSort n) in 
(let TMP_12 \def (sn3 c2 TMP_11) in (let TMP_13 \def (arity_sort g c2 n) in 
(let TMP_14 \def (TSort n) in (let TMP_15 \def (nf2_sort c2 n) in (let TMP_16 
\def (sn3_nf2 c2 TMP_14 TMP_15) in (let TMP_17 \def (conj TMP_10 TMP_12 
TMP_13 TMP_16) in (let TMP_18 \def (TSort n) in (let TMP_19 \def (lift1 is 
TMP_18) in (let TMP_20 \def (lift1_sort n is) in (eq_ind_r T TMP_3 TMP_7 
TMP_17 TMP_19 TMP_20))))))))))))))))))))))) in (let TMP_191 \def (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u 
a0)).(\lambda (H2: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 d) 
\to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a0 c2 (lift1 is 
u))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H3: (drop1 is d1 
c)).(\lambda (c2: C).(\lambda (H4: (csubc g d1 c2)).(let H_x \def 
(drop1_getl_trans is c d1 H3 Abbr d u i H0) in (let H5 \def H_x in (let 
TMP_23 \def (\lambda (e2: C).(let TMP_22 \def (ptrans is i) in (drop1 TMP_22 
e2 d))) in (let TMP_29 \def (\lambda (e2: C).(let TMP_24 \def (trans is i) in 
(let TMP_25 \def (Bind Abbr) in (let TMP_26 \def (ptrans is i) in (let TMP_27 
\def (lift1 TMP_26 u) in (let TMP_28 \def (CHead e2 TMP_25 TMP_27) in (getl 
TMP_24 d1 TMP_28))))))) in (let TMP_30 \def (TLRef i) in (let TMP_31 \def 
(lift1 is TMP_30) in (let TMP_32 \def (sc3 g a0 c2 TMP_31) in (let TMP_190 
\def (\lambda (x: C).(\lambda (_: (drop1 (ptrans is i) x d)).(\lambda (H7: 
(getl (trans is i) d1 (CHead x (Bind Abbr) (lift1 (ptrans is i) u)))).(let 
TMP_33 \def (Bind Abbr) in (let TMP_34 \def (ptrans is i) in (let TMP_35 \def 
(lift1 TMP_34 u) in (let TMP_36 \def (CHead x TMP_33 TMP_35) in (let TMP_37 
\def (trans is i) in (let H_x0 \def (csubc_getl_conf g d1 TMP_36 TMP_37 H7 c2 
H4) in (let H8 \def H_x0 in (let TMP_39 \def (\lambda (e2: C).(let TMP_38 
\def (trans is i) in (getl TMP_38 c2 e2))) in (let TMP_44 \def (\lambda (e2: 
C).(let TMP_40 \def (Bind Abbr) in (let TMP_41 \def (ptrans is i) in (let 
TMP_42 \def (lift1 TMP_41 u) in (let TMP_43 \def (CHead x TMP_40 TMP_42) in 
(csubc g TMP_43 e2)))))) in (let TMP_45 \def (TLRef i) in (let TMP_46 \def 
(lift1 is TMP_45) in (let TMP_47 \def (sc3 g a0 c2 TMP_46) in (let TMP_189 
\def (\lambda (x0: C).(\lambda (H9: (getl (trans is i) c2 x0)).(\lambda (H10: 
(csubc g (CHead x (Bind Abbr) (lift1 (ptrans is i) u)) x0)).(let TMP_48 \def 
(ptrans is i) in (let TMP_49 \def (lift1 TMP_48 u) in (let TMP_50 \def (Bind 
Abbr) in (let H_x1 \def (csubc_gen_head_l g x x0 TMP_49 TMP_50 H10) in (let 
H11 \def H_x1 in (let TMP_55 \def (\lambda (c3: C).(let TMP_51 \def (Bind 
Abbr) in (let TMP_52 \def (ptrans is i) in (let TMP_53 \def (lift1 TMP_52 u) 
in (let TMP_54 \def (CHead c3 TMP_51 TMP_53) in (eq C x0 TMP_54)))))) in (let 
TMP_56 \def (\lambda (c3: C).(csubc g x c3)) in (let TMP_57 \def (ex2 C 
TMP_55 TMP_56) in (let TMP_60 \def (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(let TMP_58 \def (Bind Abbr) in (let TMP_59 \def (Bind Abst) in (eq K 
TMP_58 TMP_59)))))) in (let TMP_63 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (_: A).(let TMP_61 \def (Bind Abbr) in (let TMP_62 \def (CHead c3 
TMP_61 w) in (eq C x0 TMP_62)))))) in (let TMP_64 \def (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) in (let TMP_68 \def 
(\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(let TMP_65 \def (asucc g 
a1) in (let TMP_66 \def (ptrans is i) in (let TMP_67 \def (lift1 TMP_66 u) in 
(sc3 g TMP_65 x TMP_67))))))) in (let TMP_69 \def (\lambda (c3: C).(\lambda 
(w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))) in (let TMP_70 \def (ex5_3 C T A 
TMP_60 TMP_63 TMP_64 TMP_68 TMP_69) in (let TMP_73 \def (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_71 \def (Bind b) in (let TMP_72 
\def (CHead c3 TMP_71 v2) in (eq C x0 TMP_72)))))) in (let TMP_76 \def 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_74 \def (Bind Abbr) 
in (let TMP_75 \def (Bind Void) in (eq K TMP_74 TMP_75)))))) in (let TMP_78 
\def (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(let TMP_77 \def (eq B b 
Void) in (not TMP_77))))) in (let TMP_79 \def (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g x c3)))) in (let TMP_80 \def (ex4_3 B C T TMP_73 
TMP_76 TMP_78 TMP_79) in (let TMP_81 \def (TLRef i) in (let TMP_82 \def 
(lift1 is TMP_81) in (let TMP_83 \def (sc3 g a0 c2 TMP_82) in (let TMP_137 
\def (\lambda (H12: (ex2 C (\lambda (c3: C).(eq C x0 (CHead c3 (Bind Abbr) 
(lift1 (ptrans is i) u)))) (\lambda (c3: C).(csubc g x c3)))).(let TMP_88 
\def (\lambda (c3: C).(let TMP_84 \def (Bind Abbr) in (let TMP_85 \def 
(ptrans is i) in (let TMP_86 \def (lift1 TMP_85 u) in (let TMP_87 \def (CHead 
c3 TMP_84 TMP_86) in (eq C x0 TMP_87)))))) in (let TMP_89 \def (\lambda (c3: 
C).(csubc g x c3)) in (let TMP_90 \def (TLRef i) in (let TMP_91 \def (lift1 
is TMP_90) in (let TMP_92 \def (sc3 g a0 c2 TMP_91) in (let TMP_136 \def 
(\lambda (x1: C).(\lambda (H13: (eq C x0 (CHead x1 (Bind Abbr) (lift1 (ptrans 
is i) u)))).(\lambda (_: (csubc g x x1)).(let TMP_94 \def (\lambda (c0: 
C).(let TMP_93 \def (trans is i) in (getl TMP_93 c2 c0))) in (let TMP_95 \def 
(Bind Abbr) in (let TMP_96 \def (ptrans is i) in (let TMP_97 \def (lift1 
TMP_96 u) in (let TMP_98 \def (CHead x1 TMP_95 TMP_97) in (let H15 \def 
(eq_ind C x0 TMP_94 H9 TMP_98 H13) in (let H_y \def (sc3_abbr g a0 TNil) in 
(let TMP_99 \def (trans is i) in (let TMP_100 \def (TLRef TMP_99) in (let 
TMP_101 \def (\lambda (t0: T).(sc3 g a0 c2 t0)) in (let TMP_102 \def (trans 
is i) in (let TMP_103 \def (ptrans is i) in (let TMP_104 \def (lift1 TMP_103 
u) in (let TMP_105 \def (S i) in (let TMP_106 \def (lift TMP_105 O u) in (let 
TMP_107 \def (lift1 is TMP_106) in (let TMP_108 \def (\lambda (t0: T).(sc3 g 
a0 c2 t0)) in (let TMP_109 \def (S i) in (let TMP_110 \def (PConsTail is 
TMP_109 O) in (let TMP_111 \def (lift1 TMP_110 u) in (let TMP_112 \def 
(\lambda (t0: T).(sc3 g a0 c2 t0)) in (let TMP_113 \def (S i) in (let TMP_114 
\def (PConsTail is TMP_113 O) in (let TMP_115 \def (S i) in (let TMP_116 \def 
(getl_drop Abbr c d u i H0) in (let TMP_117 \def (drop1_cons_tail c d TMP_115 
O TMP_116 is d1 H3) in (let TMP_118 \def (H2 d1 TMP_114 TMP_117 c2 H4) in 
(let TMP_119 \def (S i) in (let TMP_120 \def (lift TMP_119 O u) in (let 
TMP_121 \def (lift1 is TMP_120) in (let TMP_122 \def (S i) in (let TMP_123 
\def (lift1_cons_tail u TMP_122 O is) in (let TMP_124 \def (eq_ind T TMP_111 
TMP_112 TMP_118 TMP_121 TMP_123) in (let TMP_125 \def (trans is i) in (let 
TMP_126 \def (S TMP_125) in (let TMP_127 \def (ptrans is i) in (let TMP_128 
\def (lift1 TMP_127 u) in (let TMP_129 \def (lift TMP_126 O TMP_128) in (let 
TMP_130 \def (lift1_free is i u) in (let TMP_131 \def (eq_ind T TMP_107 
TMP_108 TMP_124 TMP_129 TMP_130) in (let TMP_132 \def (H_y TMP_102 x1 TMP_104 
c2 TMP_131 H15) in (let TMP_133 \def (TLRef i) in (let TMP_134 \def (lift1 is 
TMP_133) in (let TMP_135 \def (lift1_lref is i) in (eq_ind_r T TMP_100 
TMP_101 TMP_132 TMP_134 
TMP_135)))))))))))))))))))))))))))))))))))))))))))))))) in (ex2_ind C TMP_88 
TMP_89 TMP_92 TMP_136 H12)))))))) in (let TMP_164 \def (\lambda (H12: (ex5_3 
C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind Abbr) (Bind 
Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C x0 (CHead c3 
(Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g 
x c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(sc3 g (asucc g a1) 
x (lift1 (ptrans is i) u))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: 
A).(sc3 g a1 c3 w)))))).(let TMP_140 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(let TMP_138 \def (Bind Abbr) in (let TMP_139 \def (Bind 
Abst) in (eq K TMP_138 TMP_139)))))) in (let TMP_143 \def (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(let TMP_141 \def (Bind Abbr) in (let 
TMP_142 \def (CHead c3 TMP_141 w) in (eq C x0 TMP_142)))))) in (let TMP_144 
\def (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) in 
(let TMP_148 \def (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(let 
TMP_145 \def (asucc g a1) in (let TMP_146 \def (ptrans is i) in (let TMP_147 
\def (lift1 TMP_146 u) in (sc3 g TMP_145 x TMP_147))))))) in (let TMP_149 
\def (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))) in 
(let TMP_150 \def (TLRef i) in (let TMP_151 \def (lift1 is TMP_150) in (let 
TMP_152 \def (sc3 g a0 c2 TMP_151) in (let TMP_163 \def (\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: A).(\lambda (H13: (eq K (Bind Abbr) (Bind 
Abst))).(\lambda (H14: (eq C x0 (CHead x1 (Bind Abbr) x2))).(\lambda (_: 
(csubc g x x1)).(\lambda (_: (sc3 g (asucc g x3) x (lift1 (ptrans is i) 
u))).(\lambda (_: (sc3 g x3 x1 x2)).(let TMP_154 \def (\lambda (c0: C).(let 
TMP_153 \def (trans is i) in (getl TMP_153 c2 c0))) in (let TMP_155 \def 
(Bind Abbr) in (let TMP_156 \def (CHead x1 TMP_155 x2) in (let H18 \def 
(eq_ind C x0 TMP_154 H9 TMP_156 H14) in (let TMP_157 \def (Bind Abbr) in (let 
TMP_158 \def (\lambda (ee: K).(match ee with [(Bind b) \Rightarrow (match b 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False]) | (Flat _) \Rightarrow False])) in (let TMP_159 \def (Bind Abst) in 
(let H19 \def (eq_ind K TMP_157 TMP_158 I TMP_159 H13) in (let TMP_160 \def 
(TLRef i) in (let TMP_161 \def (lift1 is TMP_160) in (let TMP_162 \def (sc3 g 
a0 c2 TMP_161) in (False_ind TMP_162 H19)))))))))))))))))))) in (ex5_3_ind C 
T A TMP_140 TMP_143 TMP_144 TMP_148 TMP_149 TMP_152 TMP_163 H12))))))))))) in 
(let TMP_188 \def (\lambda (H12: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C x0 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Abbr) (Bind Void))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))))).(let TMP_167 \def 
(\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_165 \def (Bind b) 
in (let TMP_166 \def (CHead c3 TMP_165 v2) in (eq C x0 TMP_166)))))) in (let 
TMP_170 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_168 
\def (Bind Abbr) in (let TMP_169 \def (Bind Void) in (eq K TMP_168 
TMP_169)))))) in (let TMP_172 \def (\lambda (b: B).(\lambda (_: C).(\lambda 
(_: T).(let TMP_171 \def (eq B b Void) in (not TMP_171))))) in (let TMP_173 
\def (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))) in 
(let TMP_174 \def (TLRef i) in (let TMP_175 \def (lift1 is TMP_174) in (let 
TMP_176 \def (sc3 g a0 c2 TMP_175) in (let TMP_187 \def (\lambda (x1: 
B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H13: (eq C x0 (CHead x2 (Bind 
x1) x3))).(\lambda (H14: (eq K (Bind Abbr) (Bind Void))).(\lambda (_: (not 
(eq B x1 Void))).(\lambda (_: (csubc g x x2)).(let TMP_178 \def (\lambda (c0: 
C).(let TMP_177 \def (trans is i) in (getl TMP_177 c2 c0))) in (let TMP_179 
\def (Bind x1) in (let TMP_180 \def (CHead x2 TMP_179 x3) in (let H17 \def 
(eq_ind C x0 TMP_178 H9 TMP_180 H13) in (let TMP_181 \def (Bind Abbr) in (let 
TMP_182 \def (\lambda (ee: K).(match ee with [(Bind b) \Rightarrow (match b 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False]) | (Flat _) \Rightarrow False])) in (let TMP_183 \def (Bind Void) in 
(let H18 \def (eq_ind K TMP_181 TMP_182 I TMP_183 H14) in (let TMP_184 \def 
(TLRef i) in (let TMP_185 \def (lift1 is TMP_184) in (let TMP_186 \def (sc3 g 
a0 c2 TMP_185) in (False_ind TMP_186 H18))))))))))))))))))) in (ex4_3_ind B C 
T TMP_167 TMP_170 TMP_172 TMP_173 TMP_176 TMP_187 H12)))))))))) in (or3_ind 
TMP_57 TMP_70 TMP_80 TMP_83 TMP_137 TMP_164 TMP_188 
H11))))))))))))))))))))))))))))) in (ex2_ind C TMP_39 TMP_44 TMP_47 TMP_189 
H8))))))))))))))))) in (ex2_ind C TMP_23 TMP_29 TMP_32 TMP_190 
H5)))))))))))))))))))))) in (let TMP_371 \def (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abst) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u (asucc g 
a0))).(\lambda (_: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 d) 
\to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g (asucc g a0) c2 (lift1 is 
u))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H3: (drop1 is d1 
c)).(\lambda (c2: C).(\lambda (H4: (csubc g d1 c2)).(let H5 \def H0 in (let 
H_x \def (drop1_getl_trans is c d1 H3 Abst d u i H5) in (let H6 \def H_x in 
(let TMP_193 \def (\lambda (e2: C).(let TMP_192 \def (ptrans is i) in (drop1 
TMP_192 e2 d))) in (let TMP_199 \def (\lambda (e2: C).(let TMP_194 \def 
(trans is i) in (let TMP_195 \def (Bind Abst) in (let TMP_196 \def (ptrans is 
i) in (let TMP_197 \def (lift1 TMP_196 u) in (let TMP_198 \def (CHead e2 
TMP_195 TMP_197) in (getl TMP_194 d1 TMP_198))))))) in (let TMP_200 \def 
(TLRef i) in (let TMP_201 \def (lift1 is TMP_200) in (let TMP_202 \def (sc3 g 
a0 c2 TMP_201) in (let TMP_370 \def (\lambda (x: C).(\lambda (H7: (drop1 
(ptrans is i) x d)).(\lambda (H8: (getl (trans is i) d1 (CHead x (Bind Abst) 
(lift1 (ptrans is i) u)))).(let TMP_203 \def (Bind Abst) in (let TMP_204 \def 
(ptrans is i) in (let TMP_205 \def (lift1 TMP_204 u) in (let TMP_206 \def 
(CHead x TMP_203 TMP_205) in (let TMP_207 \def (trans is i) in (let H_x0 \def 
(csubc_getl_conf g d1 TMP_206 TMP_207 H8 c2 H4) in (let H9 \def H_x0 in (let 
TMP_209 \def (\lambda (e2: C).(let TMP_208 \def (trans is i) in (getl TMP_208 
c2 e2))) in (let TMP_214 \def (\lambda (e2: C).(let TMP_210 \def (Bind Abst) 
in (let TMP_211 \def (ptrans is i) in (let TMP_212 \def (lift1 TMP_211 u) in 
(let TMP_213 \def (CHead x TMP_210 TMP_212) in (csubc g TMP_213 e2)))))) in 
(let TMP_215 \def (TLRef i) in (let TMP_216 \def (lift1 is TMP_215) in (let 
TMP_217 \def (sc3 g a0 c2 TMP_216) in (let TMP_369 \def (\lambda (x0: 
C).(\lambda (H10: (getl (trans is i) c2 x0)).(\lambda (H11: (csubc g (CHead x 
(Bind Abst) (lift1 (ptrans is i) u)) x0)).(let TMP_218 \def (ptrans is i) in 
(let TMP_219 \def (lift1 TMP_218 u) in (let TMP_220 \def (Bind Abst) in (let 
H_x1 \def (csubc_gen_head_l g x x0 TMP_219 TMP_220 H11) in (let H12 \def H_x1 
in (let TMP_225 \def (\lambda (c3: C).(let TMP_221 \def (Bind Abst) in (let 
TMP_222 \def (ptrans is i) in (let TMP_223 \def (lift1 TMP_222 u) in (let 
TMP_224 \def (CHead c3 TMP_221 TMP_223) in (eq C x0 TMP_224)))))) in (let 
TMP_226 \def (\lambda (c3: C).(csubc g x c3)) in (let TMP_227 \def (ex2 C 
TMP_225 TMP_226) in (let TMP_230 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(let TMP_228 \def (Bind Abst) in (let TMP_229 \def (Bind 
Abst) in (eq K TMP_228 TMP_229)))))) in (let TMP_233 \def (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(let TMP_231 \def (Bind Abbr) in (let 
TMP_232 \def (CHead c3 TMP_231 w) in (eq C x0 TMP_232)))))) in (let TMP_234 
\def (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) in 
(let TMP_238 \def (\lambda (_: C).(\lambda (_: T).(\lambda (a1: A).(let 
TMP_235 \def (asucc g a1) in (let TMP_236 \def (ptrans is i) in (let TMP_237 
\def (lift1 TMP_236 u) in (sc3 g TMP_235 x TMP_237))))))) in (let TMP_239 
\def (\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))) in 
(let TMP_240 \def (ex5_3 C T A TMP_230 TMP_233 TMP_234 TMP_238 TMP_239) in 
(let TMP_243 \def (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(let 
TMP_241 \def (Bind b) in (let TMP_242 \def (CHead c3 TMP_241 v2) in (eq C x0 
TMP_242)))))) in (let TMP_246 \def (\lambda (_: B).(\lambda (_: C).(\lambda 
(_: T).(let TMP_244 \def (Bind Abst) in (let TMP_245 \def (Bind Void) in (eq 
K TMP_244 TMP_245)))))) in (let TMP_248 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(let TMP_247 \def (eq B b Void) in (not TMP_247))))) in 
(let TMP_249 \def (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x 
c3)))) in (let TMP_250 \def (ex4_3 B C T TMP_243 TMP_246 TMP_248 TMP_249) in 
(let TMP_251 \def (TLRef i) in (let TMP_252 \def (lift1 is TMP_251) in (let 
TMP_253 \def (sc3 g a0 c2 TMP_252) in (let TMP_295 \def (\lambda (H13: (ex2 C 
(\lambda (c3: C).(eq C x0 (CHead c3 (Bind Abst) (lift1 (ptrans is i) u)))) 
(\lambda (c3: C).(csubc g x c3)))).(let TMP_258 \def (\lambda (c3: C).(let 
TMP_254 \def (Bind Abst) in (let TMP_255 \def (ptrans is i) in (let TMP_256 
\def (lift1 TMP_255 u) in (let TMP_257 \def (CHead c3 TMP_254 TMP_256) in (eq 
C x0 TMP_257)))))) in (let TMP_259 \def (\lambda (c3: C).(csubc g x c3)) in 
(let TMP_260 \def (TLRef i) in (let TMP_261 \def (lift1 is TMP_260) in (let 
TMP_262 \def (sc3 g a0 c2 TMP_261) in (let TMP_294 \def (\lambda (x1: 
C).(\lambda (H14: (eq C x0 (CHead x1 (Bind Abst) (lift1 (ptrans is i) 
u)))).(\lambda (_: (csubc g x x1)).(let TMP_264 \def (\lambda (c0: C).(let 
TMP_263 \def (trans is i) in (getl TMP_263 c2 c0))) in (let TMP_265 \def 
(Bind Abst) in (let TMP_266 \def (ptrans is i) in (let TMP_267 \def (lift1 
TMP_266 u) in (let TMP_268 \def (CHead x1 TMP_265 TMP_267) in (let H16 \def 
(eq_ind C x0 TMP_264 H10 TMP_268 H14) in (let H_y \def (sc3_abst g a0 TNil) 
in (let TMP_269 \def (trans is i) in (let TMP_270 \def (TLRef TMP_269) in 
(let TMP_271 \def (\lambda (t0: T).(sc3 g a0 c2 t0)) in (let TMP_272 \def 
(trans is i) in (let TMP_273 \def (trans is i) in (let TMP_274 \def (TLRef 
TMP_273) in (let TMP_275 \def (TLRef i) in (let TMP_276 \def (lift1 is 
TMP_275) in (let TMP_277 \def (\lambda (t0: T).(arity g d1 t0 a0)) in (let 
TMP_278 \def (TLRef i) in (let TMP_279 \def (arity_abst g c d u i H0 a0 H1) 
in (let TMP_280 \def (arity_lift1 g a0 c is d1 TMP_278 H3 TMP_279) in (let 
TMP_281 \def (trans is i) in (let TMP_282 \def (TLRef TMP_281) in (let 
TMP_283 \def (lift1_lref is i) in (let TMP_284 \def (eq_ind T TMP_276 TMP_277 
TMP_280 TMP_282 TMP_283) in (let TMP_285 \def (csubc_arity_conf g d1 c2 H4 
TMP_274 a0 TMP_284) in (let TMP_286 \def (ptrans is i) in (let TMP_287 \def 
(lift1 TMP_286 u) in (let TMP_288 \def (trans is i) in (let TMP_289 \def 
(nf2_lref_abst c2 x1 TMP_287 TMP_288 H16) in (let TMP_290 \def (H_y c2 
TMP_272 TMP_285 TMP_289 I) in (let TMP_291 \def (TLRef i) in (let TMP_292 
\def (lift1 is TMP_291) in (let TMP_293 \def (lift1_lref is i) in (eq_ind_r T 
TMP_270 TMP_271 TMP_290 TMP_292 TMP_293)))))))))))))))))))))))))))))))))))) 
in (ex2_ind C TMP_258 TMP_259 TMP_262 TMP_294 H13)))))))) in (let TMP_344 
\def (\lambda (H13: (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K (Bind Abst) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (_: A).(eq C x0 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g x c3)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a1: A).(sc3 g (asucc g a1) x (lift1 (ptrans is i) u))))) 
(\lambda (c3: C).(\lambda (w: T).(\lambda (a1: A).(sc3 g a1 c3 w)))))).(let 
TMP_298 \def (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(let TMP_296 
\def (Bind Abst) in (let TMP_297 \def (Bind Abst) in (eq K TMP_296 
TMP_297)))))) in (let TMP_301 \def (\lambda (c3: C).(\lambda (w: T).(\lambda 
(_: A).(let TMP_299 \def (Bind Abbr) in (let TMP_300 \def (CHead c3 TMP_299 
w) in (eq C x0 TMP_300)))))) in (let TMP_302 \def (\lambda (c3: C).(\lambda 
(_: T).(\lambda (_: A).(csubc g x c3)))) in (let TMP_306 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a1: A).(let TMP_303 \def (asucc g a1) in (let 
TMP_304 \def (ptrans is i) in (let TMP_305 \def (lift1 TMP_304 u) in (sc3 g 
TMP_303 x TMP_305))))))) in (let TMP_307 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a1: A).(sc3 g a1 c3 w)))) in (let TMP_308 \def (TLRef i) in (let 
TMP_309 \def (lift1 is TMP_308) in (let TMP_310 \def (sc3 g a0 c2 TMP_309) in 
(let TMP_343 \def (\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: A).(\lambda 
(_: (eq K (Bind Abst) (Bind Abst))).(\lambda (H15: (eq C x0 (CHead x1 (Bind 
Abbr) x2))).(\lambda (_: (csubc g x x1)).(\lambda (H17: (sc3 g (asucc g x3) x 
(lift1 (ptrans is i) u))).(\lambda (H18: (sc3 g x3 x1 x2)).(let TMP_312 \def 
(\lambda (c0: C).(let TMP_311 \def (trans is i) in (getl TMP_311 c2 c0))) in 
(let TMP_313 \def (Bind Abbr) in (let TMP_314 \def (CHead x1 TMP_313 x2) in 
(let H19 \def (eq_ind C x0 TMP_312 H10 TMP_314 H15) in (let H_y \def 
(sc3_abbr g a0 TNil) in (let TMP_315 \def (trans is i) in (let TMP_316 \def 
(TLRef TMP_315) in (let TMP_317 \def (\lambda (t0: T).(sc3 g a0 c2 t0)) in 
(let TMP_318 \def (trans is i) in (let TMP_319 \def (asucc g a0) in (let 
TMP_320 \def (ptrans is i) in (let H_y0 \def (arity_lift1 g TMP_319 d TMP_320 
x u H7 H1) in (let TMP_321 \def (ptrans is i) in (let TMP_322 \def (lift1 
TMP_321 u) in (let TMP_323 \def (asucc g x3) in (let H_y1 \def (sc3_arity_gen 
g x TMP_322 TMP_323 H17) in (let TMP_324 \def (trans is i) in (let TMP_325 
\def (S TMP_324) in (let TMP_326 \def (lift TMP_325 O x2) in (let TMP_327 
\def (trans is i) in (let TMP_328 \def (S TMP_327) in (let TMP_329 \def 
(trans is i) in (let TMP_330 \def (getl_drop Abbr c2 x1 x2 TMP_329 H19) in 
(let TMP_331 \def (sc3_lift g x3 x1 x2 H18 c2 TMP_328 O TMP_330) in (let 
TMP_332 \def (ptrans is i) in (let TMP_333 \def (lift1 TMP_332 u) in (let 
TMP_334 \def (asucc g x3) in (let TMP_335 \def (asucc g a0) in (let TMP_336 
\def (arity_mono g x TMP_333 TMP_334 H_y1 TMP_335 H_y0) in (let TMP_337 \def 
(asucc_inj g x3 a0 TMP_336) in (let TMP_338 \def (sc3_repl g x3 c2 TMP_326 
TMP_331 a0 TMP_337) in (let TMP_339 \def (H_y TMP_318 x1 x2 c2 TMP_338 H19) 
in (let TMP_340 \def (TLRef i) in (let TMP_341 \def (lift1 is TMP_340) in 
(let TMP_342 \def (lift1_lref is i) in (eq_ind_r T TMP_316 TMP_317 TMP_339 
TMP_341 TMP_342)))))))))))))))))))))))))))))))))))))))))))) in (ex5_3_ind C T 
A TMP_298 TMP_301 TMP_302 TMP_306 TMP_307 TMP_310 TMP_343 H13))))))))))) in 
(let TMP_368 \def (\lambda (H13: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C x0 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Abst) (Bind Void))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))))).(let TMP_347 \def 
(\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_345 \def (Bind b) 
in (let TMP_346 \def (CHead c3 TMP_345 v2) in (eq C x0 TMP_346)))))) in (let 
TMP_350 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_348 
\def (Bind Abst) in (let TMP_349 \def (Bind Void) in (eq K TMP_348 
TMP_349)))))) in (let TMP_352 \def (\lambda (b: B).(\lambda (_: C).(\lambda 
(_: T).(let TMP_351 \def (eq B b Void) in (not TMP_351))))) in (let TMP_353 
\def (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g x c3)))) in 
(let TMP_354 \def (TLRef i) in (let TMP_355 \def (lift1 is TMP_354) in (let 
TMP_356 \def (sc3 g a0 c2 TMP_355) in (let TMP_367 \def (\lambda (x1: 
B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H14: (eq C x0 (CHead x2 (Bind 
x1) x3))).(\lambda (H15: (eq K (Bind Abst) (Bind Void))).(\lambda (_: (not 
(eq B x1 Void))).(\lambda (_: (csubc g x x2)).(let TMP_358 \def (\lambda (c0: 
C).(let TMP_357 \def (trans is i) in (getl TMP_357 c2 c0))) in (let TMP_359 
\def (Bind x1) in (let TMP_360 \def (CHead x2 TMP_359 x3) in (let H18 \def 
(eq_ind C x0 TMP_358 H10 TMP_360 H14) in (let TMP_361 \def (Bind Abst) in 
(let TMP_362 \def (\lambda (ee: K).(match ee with [(Bind b) \Rightarrow 
(match b with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])) in (let TMP_363 \def 
(Bind Void) in (let H19 \def (eq_ind K TMP_361 TMP_362 I TMP_363 H15) in (let 
TMP_364 \def (TLRef i) in (let TMP_365 \def (lift1 is TMP_364) in (let 
TMP_366 \def (sc3 g a0 c2 TMP_365) in (False_ind TMP_366 
H19))))))))))))))))))) in (ex4_3_ind B C T TMP_347 TMP_350 TMP_352 TMP_353 
TMP_356 TMP_367 H13)))))))))) in (or3_ind TMP_227 TMP_240 TMP_250 TMP_253 
TMP_295 TMP_344 TMP_368 H12))))))))))))))))))))))))))))) in (ex2_ind C 
TMP_209 TMP_214 TMP_217 TMP_369 H9))))))))))))))))) in (ex2_ind C TMP_193 
TMP_199 TMP_202 TMP_370 H6))))))))))))))))))))))) in (let TMP_399 \def 
(\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: 
((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: 
C).((csubc g d1 c2) \to (sc3 g a1 c2 (lift1 is u))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c (Bind b) u) t0 
a2)).(\lambda (H4: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 
(CHead c (Bind b) u)) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a2 c2 
(lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H5: 
(drop1 is d1 c)).(\lambda (c2: C).(\lambda (H6: (csubc g d1 c2)).(let H_y 
\def (sc3_bind g b H0 a1 a2 TNil) in (let TMP_372 \def (Bind b) in (let 
TMP_373 \def (lift1 is u) in (let TMP_374 \def (Ss is) in (let TMP_375 \def 
(lift1 TMP_374 t0) in (let TMP_376 \def (THead TMP_372 TMP_373 TMP_375) in 
(let TMP_377 \def (\lambda (t1: T).(sc3 g a2 c2 t1)) in (let TMP_378 \def 
(lift1 is u) in (let TMP_379 \def (Ss is) in (let TMP_380 \def (lift1 TMP_379 
t0) in (let TMP_381 \def (Bind b) in (let TMP_382 \def (lift1 is u) in (let 
TMP_383 \def (CHead d1 TMP_381 TMP_382) in (let TMP_384 \def (Ss is) in (let 
TMP_385 \def (drop1_skip_bind b c is d1 u H5) in (let TMP_386 \def (Bind b) 
in (let TMP_387 \def (lift1 is u) in (let TMP_388 \def (CHead c2 TMP_386 
TMP_387) in (let TMP_389 \def (Bind b) in (let TMP_390 \def (lift1 is u) in 
(let TMP_391 \def (csubc_head g d1 c2 H6 TMP_389 TMP_390) in (let TMP_392 
\def (H4 TMP_383 TMP_384 TMP_385 TMP_388 TMP_391) in (let TMP_393 \def (H2 d1 
is H5 c2 H6) in (let TMP_394 \def (H_y c2 TMP_378 TMP_380 TMP_392 TMP_393) in 
(let TMP_395 \def (Bind b) in (let TMP_396 \def (THead TMP_395 u t0) in (let 
TMP_397 \def (lift1 is TMP_396) in (let TMP_398 \def (lift1_bind b is u t0) 
in (eq_ind_r T TMP_376 TMP_377 TMP_394 TMP_397 
TMP_398))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_547 \def 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H0: (arity g c u 
(asucc g a1))).(\lambda (H1: ((\forall (d1: C).(\forall (is: PList).((drop1 
is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g (asucc g a1) c2 
(lift1 is u))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (H2: (arity g 
(CHead c (Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 (CHead c (Bind Abst) u)) \to (\forall (c2: C).((csubc g 
d1 c2) \to (sc3 g a2 c2 (lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: 
PList).(\lambda (H4: (drop1 is d1 c)).(\lambda (c2: C).(\lambda (H5: (csubc g 
d1 c2)).(let TMP_400 \def (Bind Abst) in (let TMP_401 \def (lift1 is u) in 
(let TMP_402 \def (Ss is) in (let TMP_403 \def (lift1 TMP_402 t0) in (let 
TMP_404 \def (THead TMP_400 TMP_401 TMP_403) in (let TMP_411 \def (\lambda 
(t1: T).(let TMP_405 \def (AHead a1 a2) in (let TMP_406 \def (arity g c2 t1 
TMP_405) in (let TMP_410 \def (\forall (d: C).(\forall (w: T).((sc3 g a1 d w) 
\to (\forall (is0: PList).((drop1 is0 d c2) \to (let TMP_407 \def (Flat Appl) 
in (let TMP_408 \def (lift1 is0 t1) in (let TMP_409 \def (THead TMP_407 w 
TMP_408) in (sc3 g a2 d TMP_409))))))))) in (land TMP_406 TMP_410))))) in 
(let TMP_412 \def (Bind Abst) in (let TMP_413 \def (lift1 is u) in (let 
TMP_414 \def (Ss is) in (let TMP_415 \def (lift1 TMP_414 t0) in (let TMP_416 
\def (THead TMP_412 TMP_413 TMP_415) in (let TMP_417 \def (AHead a1 a2) in 
(let TMP_418 \def (arity g c2 TMP_416 TMP_417) in (let TMP_427 \def (\forall 
(d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is0: PList).((drop1 is0 
d c2) \to (let TMP_419 \def (Flat Appl) in (let TMP_420 \def (Bind Abst) in 
(let TMP_421 \def (lift1 is u) in (let TMP_422 \def (Ss is) in (let TMP_423 
\def (lift1 TMP_422 t0) in (let TMP_424 \def (THead TMP_420 TMP_421 TMP_423) 
in (let TMP_425 \def (lift1 is0 TMP_424) in (let TMP_426 \def (THead TMP_419 
w TMP_425) in (sc3 g a2 d TMP_426)))))))))))))) in (let TMP_428 \def (Bind 
Abst) in (let TMP_429 \def (lift1 is u) in (let TMP_430 \def (Ss is) in (let 
TMP_431 \def (lift1 TMP_430 t0) in (let TMP_432 \def (THead TMP_428 TMP_429 
TMP_431) in (let TMP_433 \def (AHead a1 a2) in (let TMP_434 \def (lift1 is u) 
in (let TMP_435 \def (asucc g a1) in (let TMP_436 \def (arity_lift1 g TMP_435 
c is d1 u H4 H0) in (let TMP_437 \def (Ss is) in (let TMP_438 \def (lift1 
TMP_437 t0) in (let TMP_439 \def (Bind Abst) in (let TMP_440 \def (CHead c 
TMP_439 u) in (let TMP_441 \def (Ss is) in (let TMP_442 \def (Bind Abst) in 
(let TMP_443 \def (lift1 is u) in (let TMP_444 \def (CHead d1 TMP_442 
TMP_443) in (let TMP_445 \def (drop1_skip_bind Abst c is d1 u H4) in (let 
TMP_446 \def (arity_lift1 g a2 TMP_440 TMP_441 TMP_444 t0 TMP_445 H2) in (let 
TMP_447 \def (arity_head g d1 TMP_434 a1 TMP_436 TMP_438 a2 TMP_446) in (let 
TMP_448 \def (csubc_arity_conf g d1 c2 H5 TMP_432 TMP_433 TMP_447) in (let 
TMP_541 \def (\lambda (d: C).(\lambda (w: T).(\lambda (H6: (sc3 g a1 d 
w)).(\lambda (is0: PList).(\lambda (H7: (drop1 is0 d c2)).(let TMP_449 \def 
(Bind Abst) in (let TMP_450 \def (lift1 is u) in (let TMP_451 \def (lift1 is0 
TMP_450) in (let TMP_452 \def (Ss is0) in (let TMP_453 \def (Ss is) in (let 
TMP_454 \def (lift1 TMP_453 t0) in (let TMP_455 \def (lift1 TMP_452 TMP_454) 
in (let TMP_456 \def (THead TMP_449 TMP_451 TMP_455) in (let TMP_459 \def 
(\lambda (t1: T).(let TMP_457 \def (Flat Appl) in (let TMP_458 \def (THead 
TMP_457 w t1) in (sc3 g a2 d TMP_458)))) in (let H8 \def (sc3_appl g a1 a2 
TNil) in (let TMP_460 \def (Ss is0) in (let TMP_461 \def (Ss is) in (let 
TMP_462 \def (lift1 TMP_461 t0) in (let TMP_463 \def (lift1 TMP_460 TMP_462) 
in (let H_y \def (sc3_bind g Abbr not_abbr_abst a1 a2 TNil) in (let TMP_464 
\def (Ss is0) in (let TMP_465 \def (Ss is) in (let TMP_466 \def (lift1 
TMP_465 t0) in (let TMP_467 \def (lift1 TMP_464 TMP_466) in (let H_x \def 
(csubc_drop1_conf_rev g is0 d c2 H7 d1 H5) in (let H9 \def H_x in (let 
TMP_468 \def (\lambda (c3: C).(drop1 is0 c3 d1)) in (let TMP_469 \def 
(\lambda (c3: C).(csubc g c3 d)) in (let TMP_470 \def (Bind Abbr) in (let 
TMP_471 \def (CHead d TMP_470 w) in (let TMP_472 \def (Ss is0) in (let 
TMP_473 \def (Ss is) in (let TMP_474 \def (lift1 TMP_473 t0) in (let TMP_475 
\def (lift1 TMP_472 TMP_474) in (let TMP_476 \def (sc3 g a2 TMP_471 TMP_475) 
in (let TMP_521 \def (\lambda (x: C).(\lambda (H10: (drop1 is0 x 
d1)).(\lambda (H11: (csubc g x d)).(let TMP_477 \def (Ss is0) in (let TMP_478 
\def (Ss is) in (let TMP_479 \def (papp TMP_477 TMP_478) in (let TMP_480 \def 
(lift1 TMP_479 t0) in (let TMP_483 \def (\lambda (t1: T).(let TMP_481 \def 
(Bind Abbr) in (let TMP_482 \def (CHead d TMP_481 w) in (sc3 g a2 TMP_482 
t1)))) in (let TMP_484 \def (papp is0 is) in (let TMP_485 \def (Ss TMP_484) 
in (let TMP_489 \def (\lambda (p: PList).(let TMP_486 \def (Bind Abbr) in 
(let TMP_487 \def (CHead d TMP_486 w) in (let TMP_488 \def (lift1 p t0) in 
(sc3 g a2 TMP_487 TMP_488))))) in (let TMP_490 \def (Bind Abst) in (let 
TMP_491 \def (papp is0 is) in (let TMP_492 \def (lift1 TMP_491 u) in (let 
TMP_493 \def (CHead x TMP_490 TMP_492) in (let TMP_494 \def (papp is0 is) in 
(let TMP_495 \def (Ss TMP_494) in (let TMP_496 \def (papp is0 is) in (let 
TMP_497 \def (drop1_trans is0 x d1 H10 is c H4) in (let TMP_498 \def 
(drop1_skip_bind Abst c TMP_496 x u TMP_497) in (let TMP_499 \def (Bind Abbr) 
in (let TMP_500 \def (CHead d TMP_499 w) in (let TMP_501 \def (papp is0 is) 
in (let TMP_502 \def (lift1 TMP_501 u) in (let TMP_503 \def (papp is0 is) in 
(let TMP_504 \def (drop1_trans is0 x d1 H10 is c H4) in (let TMP_505 \def 
(csubc_refl g x) in (let TMP_506 \def (H1 x TMP_503 TMP_504 x TMP_505) in 
(let TMP_507 \def (csubc_abst g x d H11 TMP_502 a1 TMP_506 w H6) in (let 
TMP_508 \def (H3 TMP_493 TMP_495 TMP_498 TMP_500 TMP_507) in (let TMP_509 
\def (Ss is0) in (let TMP_510 \def (Ss is) in (let TMP_511 \def (papp TMP_509 
TMP_510) in (let TMP_512 \def (papp_ss is0 is) in (let TMP_513 \def (eq_ind_r 
PList TMP_485 TMP_489 TMP_508 TMP_511 TMP_512) in (let TMP_514 \def (Ss is0) 
in (let TMP_515 \def (Ss is) in (let TMP_516 \def (lift1 TMP_515 t0) in (let 
TMP_517 \def (lift1 TMP_514 TMP_516) in (let TMP_518 \def (Ss is0) in (let 
TMP_519 \def (Ss is) in (let TMP_520 \def (lift1_lift1 TMP_518 TMP_519 t0) in 
(eq_ind_r T TMP_480 TMP_483 TMP_513 TMP_517 
TMP_520))))))))))))))))))))))))))))))))))))))))))) in (let TMP_522 \def 
(ex2_ind C TMP_468 TMP_469 TMP_476 TMP_521 H9) in (let TMP_523 \def (H_y d w 
TMP_467 TMP_522 H6) in (let TMP_524 \def (lift1 is u) in (let TMP_525 \def 
(lift1 is0 TMP_524) in (let TMP_526 \def (asucc g a1) in (let TMP_527 \def 
(lift1 is u) in (let TMP_528 \def (H1 d1 is H4 c2 H5) in (let TMP_529 \def 
(sc3_lift1 g c2 TMP_526 is0 d TMP_527 TMP_528 H7) in (let TMP_530 \def (H8 d 
w TMP_463 TMP_523 H6 TMP_525 TMP_529) in (let TMP_531 \def (Bind Abst) in 
(let TMP_532 \def (lift1 is u) in (let TMP_533 \def (Ss is) in (let TMP_534 
\def (lift1 TMP_533 t0) in (let TMP_535 \def (THead TMP_531 TMP_532 TMP_534) 
in (let TMP_536 \def (lift1 is0 TMP_535) in (let TMP_537 \def (lift1 is u) in 
(let TMP_538 \def (Ss is) in (let TMP_539 \def (lift1 TMP_538 t0) in (let 
TMP_540 \def (lift1_bind Abst is0 TMP_537 TMP_539) in (eq_ind_r T TMP_456 
TMP_459 TMP_530 TMP_536 
TMP_540)))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_542 \def (conj TMP_418 TMP_427 TMP_448 TMP_541) in (let TMP_543 \def 
(Bind Abst) in (let TMP_544 \def (THead TMP_543 u t0) in (let TMP_545 \def 
(lift1 is TMP_544) in (let TMP_546 \def (lift1_bind Abst is u t0) in 
(eq_ind_r T TMP_404 TMP_411 TMP_542 TMP_545 
TMP_546)))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_573 \def (\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: 
(arity g c u a1)).(\lambda (H1: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a1 
c2 (lift1 is u))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity 
g c t0 (AHead a1 a2))).(\lambda (H3: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g 
(AHead a1 a2) c2 (lift1 is t0))))))))).(\lambda (d1: C).(\lambda (is: 
PList).(\lambda (H4: (drop1 is d1 c)).(\lambda (c2: C).(\lambda (H5: (csubc g 
d1 c2)).(let H_y \def (H1 d1 is H4 c2 H5) in (let H_y0 \def (H3 d1 is H4 c2 
H5) in (let H6 \def H_y0 in (let TMP_548 \def (lift1 is t0) in (let TMP_549 
\def (AHead a1 a2) in (let TMP_550 \def (arity g c2 TMP_548 TMP_549) in (let 
TMP_555 \def (\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall 
(is0: PList).((drop1 is0 d c2) \to (let TMP_551 \def (Flat Appl) in (let 
TMP_552 \def (lift1 is t0) in (let TMP_553 \def (lift1 is0 TMP_552) in (let 
TMP_554 \def (THead TMP_551 w TMP_553) in (sc3 g a2 d TMP_554)))))))))) in 
(let TMP_556 \def (Flat Appl) in (let TMP_557 \def (THead TMP_556 u t0) in 
(let TMP_558 \def (lift1 is TMP_557) in (let TMP_559 \def (sc3 g a2 c2 
TMP_558) in (let TMP_572 \def (\lambda (_: (arity g c2 (lift1 is t0) (AHead 
a1 a2))).(\lambda (H8: ((\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to 
(\forall (is0: PList).((drop1 is0 d c2) \to (sc3 g a2 d (THead (Flat Appl) w 
(lift1 is0 (lift1 is t0))))))))))).(let TMP_560 \def (lift1 is u) in (let 
H_y1 \def (H8 c2 TMP_560 H_y PNil) in (let TMP_561 \def (Flat Appl) in (let 
TMP_562 \def (lift1 is u) in (let TMP_563 \def (lift1 is t0) in (let TMP_564 
\def (THead TMP_561 TMP_562 TMP_563) in (let TMP_565 \def (\lambda (t1: 
T).(sc3 g a2 c2 t1)) in (let TMP_566 \def (drop1_nil c2) in (let TMP_567 \def 
(H_y1 TMP_566) in (let TMP_568 \def (Flat Appl) in (let TMP_569 \def (THead 
TMP_568 u t0) in (let TMP_570 \def (lift1 is TMP_569) in (let TMP_571 \def 
(lift1_flat Appl is u t0) in (eq_ind_r T TMP_564 TMP_565 TMP_567 TMP_570 
TMP_571)))))))))))))))) in (land_ind TMP_550 TMP_555 TMP_559 TMP_572 
H6))))))))))))))))))))))))))) in (let TMP_588 \def (\lambda (c: C).(\lambda 
(u: T).(\lambda (a0: A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda 
(H1: ((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall 
(c2: C).((csubc g d1 c2) \to (sc3 g (asucc g a0) c2 (lift1 is 
u))))))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: 
((\forall (d1: C).(\forall (is: PList).((drop1 is d1 c) \to (\forall (c2: 
C).((csubc g d1 c2) \to (sc3 g a0 c2 (lift1 is t0))))))))).(\lambda (d1: 
C).(\lambda (is: PList).(\lambda (H4: (drop1 is d1 c)).(\lambda (c2: 
C).(\lambda (H5: (csubc g d1 c2)).(let H_y \def (sc3_cast g a0 TNil) in (let 
TMP_574 \def (Flat Cast) in (let TMP_575 \def (lift1 is u) in (let TMP_576 
\def (lift1 is t0) in (let TMP_577 \def (THead TMP_574 TMP_575 TMP_576) in 
(let TMP_578 \def (\lambda (t1: T).(sc3 g a0 c2 t1)) in (let TMP_579 \def 
(lift1 is u) in (let TMP_580 \def (H1 d1 is H4 c2 H5) in (let TMP_581 \def 
(lift1 is t0) in (let TMP_582 \def (H3 d1 is H4 c2 H5) in (let TMP_583 \def 
(H_y c2 TMP_579 TMP_580 TMP_581 TMP_582) in (let TMP_584 \def (Flat Cast) in 
(let TMP_585 \def (THead TMP_584 u t0) in (let TMP_586 \def (lift1 is 
TMP_585) in (let TMP_587 \def (lift1_flat Cast is u t0) in (eq_ind_r T 
TMP_577 TMP_578 TMP_583 TMP_586 TMP_587))))))))))))))))))))))))))))) in (let 
TMP_591 \def (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: 
(arity g c t0 a1)).(\lambda (H1: ((\forall (d1: C).(\forall (is: 
PList).((drop1 is d1 c) \to (\forall (c2: C).((csubc g d1 c2) \to (sc3 g a1 
c2 (lift1 is t0))))))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 
a2)).(\lambda (d1: C).(\lambda (is: PList).(\lambda (H3: (drop1 is d1 
c)).(\lambda (c2: C).(\lambda (H4: (csubc g d1 c2)).(let TMP_589 \def (lift1 
is t0) in (let TMP_590 \def (H1 d1 is H3 c2 H4) in (sc3_repl g a1 c2 TMP_589 
TMP_590 a2 H2))))))))))))))) in (arity_ind g TMP_2 TMP_21 TMP_191 TMP_371 
TMP_399 TMP_547 TMP_573 TMP_588 TMP_591 c1 t a H)))))))))))))).

theorem sc3_arity:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (sc3 g a c t)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(let H_y \def (sc3_arity_csubc g c t a H c PNil) in (let 
TMP_1 \def (drop1_nil c) in (let TMP_2 \def (csubc_refl g c) in (H_y TMP_1 c 
TMP_2)))))))).

