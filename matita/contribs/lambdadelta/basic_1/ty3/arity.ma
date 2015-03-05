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

include "basic_1/ty3/pr3_props.ma".

include "basic_1/arity/pr3.ma".

include "basic_1/asucc/fwd.ma".

theorem ty3_arity:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (ex2 A (\lambda (a1: A).(arity g c t1 a1)) (\lambda (a1: A).(arity 
g c t2 (asucc g a1))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(let TMP_4 \def (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(let TMP_1 \def (\lambda (a1: A).(arity g c0 t a1)) in 
(let TMP_3 \def (\lambda (a1: A).(let TMP_2 \def (asucc g a1) in (arity g c0 
t0 TMP_2))) in (ex2 A TMP_1 TMP_3)))))) in (let TMP_40 \def (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t3 t)).(\lambda 
(H1: (ex2 A (\lambda (a1: A).(arity g c0 t3 a1)) (\lambda (a1: A).(arity g c0 
t (asucc g a1))))).(\lambda (u: T).(\lambda (t4: T).(\lambda (_: (ty3 g c0 u 
t4)).(\lambda (H3: (ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: 
A).(arity g c0 t4 (asucc g a1))))).(\lambda (H4: (pc3 c0 t4 t3)).(let H5 \def 
H1 in (let TMP_5 \def (\lambda (a1: A).(arity g c0 t3 a1)) in (let TMP_7 \def 
(\lambda (a1: A).(let TMP_6 \def (asucc g a1) in (arity g c0 t TMP_6))) in 
(let TMP_8 \def (\lambda (a1: A).(arity g c0 u a1)) in (let TMP_10 \def 
(\lambda (a1: A).(let TMP_9 \def (asucc g a1) in (arity g c0 t3 TMP_9))) in 
(let TMP_11 \def (ex2 A TMP_8 TMP_10) in (let TMP_39 \def (\lambda (x: 
A).(\lambda (H6: (arity g c0 t3 x)).(\lambda (_: (arity g c0 t (asucc g 
x))).(let H8 \def H3 in (let TMP_12 \def (\lambda (a1: A).(arity g c0 u a1)) 
in (let TMP_14 \def (\lambda (a1: A).(let TMP_13 \def (asucc g a1) in (arity 
g c0 t4 TMP_13))) in (let TMP_15 \def (\lambda (a1: A).(arity g c0 u a1)) in 
(let TMP_17 \def (\lambda (a1: A).(let TMP_16 \def (asucc g a1) in (arity g 
c0 t3 TMP_16))) in (let TMP_18 \def (ex2 A TMP_15 TMP_17) in (let TMP_38 \def 
(\lambda (x0: A).(\lambda (H9: (arity g c0 u x0)).(\lambda (H10: (arity g c0 
t4 (asucc g x0))).(let H11 \def H4 in (let TMP_19 \def (\lambda (t0: T).(pr3 
c0 t4 t0)) in (let TMP_20 \def (\lambda (t0: T).(pr3 c0 t3 t0)) in (let 
TMP_21 \def (\lambda (a1: A).(arity g c0 u a1)) in (let TMP_23 \def (\lambda 
(a1: A).(let TMP_22 \def (asucc g a1) in (arity g c0 t3 TMP_22))) in (let 
TMP_24 \def (ex2 A TMP_21 TMP_23) in (let TMP_37 \def (\lambda (x1: 
T).(\lambda (H12: (pr3 c0 t4 x1)).(\lambda (H13: (pr3 c0 t3 x1)).(let TMP_25 
\def (\lambda (a1: A).(arity g c0 u a1)) in (let TMP_27 \def (\lambda (a1: 
A).(let TMP_26 \def (asucc g a1) in (arity g c0 t3 TMP_26))) in (let TMP_28 
\def (asucc g x0) in (let TMP_29 \def (asucc g x0) in (let TMP_30 \def (asucc 
g x0) in (let TMP_31 \def (asucc g x0) in (let TMP_32 \def (arity_sred_pr3 c0 
t4 x1 H12 g TMP_31 H10) in (let TMP_33 \def (arity_sred_pr3 c0 t3 x1 H13 g x 
H6) in (let TMP_34 \def (arity_mono g c0 x1 TMP_30 TMP_32 x TMP_33) in (let 
TMP_35 \def (leq_sym g TMP_29 x TMP_34) in (let TMP_36 \def (arity_repl g c0 
t3 x H6 TMP_28 TMP_35) in (ex_intro2 A TMP_25 TMP_27 x0 H9 
TMP_36))))))))))))))) in (ex2_ind T TMP_19 TMP_20 TMP_24 TMP_37 
H11))))))))))) in (ex2_ind A TMP_12 TMP_14 TMP_18 TMP_38 H8))))))))))) in 
(ex2_ind A TMP_5 TMP_7 TMP_11 TMP_39 H5)))))))))))))))))) in (let TMP_51 \def 
(\lambda (c0: C).(\lambda (m: nat).(let TMP_42 \def (\lambda (a1: A).(let 
TMP_41 \def (TSort m) in (arity g c0 TMP_41 a1))) in (let TMP_46 \def 
(\lambda (a1: A).(let TMP_43 \def (next g m) in (let TMP_44 \def (TSort 
TMP_43) in (let TMP_45 \def (asucc g a1) in (arity g c0 TMP_44 TMP_45))))) in 
(let TMP_47 \def (ASort O m) in (let TMP_48 \def (arity_sort g c0 m) in (let 
TMP_49 \def (next g m) in (let TMP_50 \def (arity_sort g c0 TMP_49) in 
(ex_intro2 A TMP_42 TMP_46 TMP_47 TMP_48 TMP_50))))))))) in (let TMP_74 \def 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H0: (getl n c0 (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (H2: (ex2 A (\lambda (a1: A).(arity g d u a1)) (\lambda (a1: 
A).(arity g d t (asucc g a1))))).(let H3 \def H2 in (let TMP_52 \def (\lambda 
(a1: A).(arity g d u a1)) in (let TMP_54 \def (\lambda (a1: A).(let TMP_53 
\def (asucc g a1) in (arity g d t TMP_53))) in (let TMP_56 \def (\lambda (a1: 
A).(let TMP_55 \def (TLRef n) in (arity g c0 TMP_55 a1))) in (let TMP_60 \def 
(\lambda (a1: A).(let TMP_57 \def (S n) in (let TMP_58 \def (lift TMP_57 O t) 
in (let TMP_59 \def (asucc g a1) in (arity g c0 TMP_58 TMP_59))))) in (let 
TMP_61 \def (ex2 A TMP_56 TMP_60) in (let TMP_73 \def (\lambda (x: 
A).(\lambda (H4: (arity g d u x)).(\lambda (H5: (arity g d t (asucc g 
x))).(let TMP_63 \def (\lambda (a1: A).(let TMP_62 \def (TLRef n) in (arity g 
c0 TMP_62 a1))) in (let TMP_67 \def (\lambda (a1: A).(let TMP_64 \def (S n) 
in (let TMP_65 \def (lift TMP_64 O t) in (let TMP_66 \def (asucc g a1) in 
(arity g c0 TMP_65 TMP_66))))) in (let TMP_68 \def (arity_abbr g c0 d u n H0 
x H4) in (let TMP_69 \def (asucc g x) in (let TMP_70 \def (S n) in (let 
TMP_71 \def (getl_drop Abbr c0 d u n H0) in (let TMP_72 \def (arity_lift g d 
t TMP_69 H5 c0 TMP_70 O TMP_71) in (ex_intro2 A TMP_63 TMP_67 x TMP_68 
TMP_72))))))))))) in (ex2_ind A TMP_52 TMP_54 TMP_61 TMP_73 
H3)))))))))))))))) in (let TMP_112 \def (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind 
Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: (ex2 A 
(\lambda (a1: A).(arity g d u a1)) (\lambda (a1: A).(arity g d t (asucc g 
a1))))).(let H3 \def H2 in (let TMP_75 \def (\lambda (a1: A).(arity g d u 
a1)) in (let TMP_77 \def (\lambda (a1: A).(let TMP_76 \def (asucc g a1) in 
(arity g d t TMP_76))) in (let TMP_79 \def (\lambda (a1: A).(let TMP_78 \def 
(TLRef n) in (arity g c0 TMP_78 a1))) in (let TMP_83 \def (\lambda (a1: 
A).(let TMP_80 \def (S n) in (let TMP_81 \def (lift TMP_80 O u) in (let 
TMP_82 \def (asucc g a1) in (arity g c0 TMP_81 TMP_82))))) in (let TMP_84 
\def (ex2 A TMP_79 TMP_83) in (let TMP_111 \def (\lambda (x: A).(\lambda (H4: 
(arity g d u x)).(\lambda (_: (arity g d t (asucc g x))).(let H_x \def 
(leq_asucc g x) in (let H6 \def H_x in (let TMP_86 \def (\lambda (a0: A).(let 
TMP_85 \def (asucc g a0) in (leq g x TMP_85))) in (let TMP_88 \def (\lambda 
(a1: A).(let TMP_87 \def (TLRef n) in (arity g c0 TMP_87 a1))) in (let TMP_92 
\def (\lambda (a1: A).(let TMP_89 \def (S n) in (let TMP_90 \def (lift TMP_89 
O u) in (let TMP_91 \def (asucc g a1) in (arity g c0 TMP_90 TMP_91))))) in 
(let TMP_93 \def (ex2 A TMP_88 TMP_92) in (let TMP_110 \def (\lambda (x0: 
A).(\lambda (H7: (leq g x (asucc g x0))).(let TMP_95 \def (\lambda (a1: 
A).(let TMP_94 \def (TLRef n) in (arity g c0 TMP_94 a1))) in (let TMP_99 \def 
(\lambda (a1: A).(let TMP_96 \def (S n) in (let TMP_97 \def (lift TMP_96 O u) 
in (let TMP_98 \def (asucc g a1) in (arity g c0 TMP_97 TMP_98))))) in (let 
TMP_100 \def (asucc g x0) in (let TMP_101 \def (arity_repl g d u x H4 TMP_100 
H7) in (let TMP_102 \def (arity_abst g c0 d u n H0 x0 TMP_101) in (let 
TMP_103 \def (S n) in (let TMP_104 \def (lift TMP_103 O u) in (let TMP_105 
\def (S n) in (let TMP_106 \def (getl_drop Abst c0 d u n H0) in (let TMP_107 
\def (arity_lift g d u x H4 c0 TMP_105 O TMP_106) in (let TMP_108 \def (asucc 
g x0) in (let TMP_109 \def (arity_repl g c0 TMP_104 x TMP_107 TMP_108 H7) in 
(ex_intro2 A TMP_95 TMP_99 x0 TMP_102 TMP_109))))))))))))))) in (ex_ind A 
TMP_86 TMP_93 TMP_110 H6))))))))))) in (ex2_ind A TMP_75 TMP_77 TMP_84 
TMP_111 H3)))))))))))))))) in (let TMP_208 \def (\lambda (c0: C).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (H1: (ex2 A (\lambda 
(a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t (asucc g 
a1))))).(\lambda (b: B).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g 
(CHead c0 (Bind b) u) t3 t4)).(\lambda (H3: (ex2 A (\lambda (a1: A).(arity g 
(CHead c0 (Bind b) u) t3 a1)) (\lambda (a1: A).(arity g (CHead c0 (Bind b) u) 
t4 (asucc g a1))))).(let H4 \def H1 in (let TMP_113 \def (\lambda (a1: 
A).(arity g c0 u a1)) in (let TMP_115 \def (\lambda (a1: A).(let TMP_114 \def 
(asucc g a1) in (arity g c0 t TMP_114))) in (let TMP_118 \def (\lambda (a1: 
A).(let TMP_116 \def (Bind b) in (let TMP_117 \def (THead TMP_116 u t3) in 
(arity g c0 TMP_117 a1)))) in (let TMP_122 \def (\lambda (a1: A).(let TMP_119 
\def (Bind b) in (let TMP_120 \def (THead TMP_119 u t4) in (let TMP_121 \def 
(asucc g a1) in (arity g c0 TMP_120 TMP_121))))) in (let TMP_123 \def (ex2 A 
TMP_118 TMP_122) in (let TMP_207 \def (\lambda (x: A).(\lambda (H5: (arity g 
c0 u x)).(\lambda (_: (arity g c0 t (asucc g x))).(let H7 \def H3 in (let 
TMP_126 \def (\lambda (a1: A).(let TMP_124 \def (Bind b) in (let TMP_125 \def 
(CHead c0 TMP_124 u) in (arity g TMP_125 t3 a1)))) in (let TMP_130 \def 
(\lambda (a1: A).(let TMP_127 \def (Bind b) in (let TMP_128 \def (CHead c0 
TMP_127 u) in (let TMP_129 \def (asucc g a1) in (arity g TMP_128 t4 
TMP_129))))) in (let TMP_133 \def (\lambda (a1: A).(let TMP_131 \def (Bind b) 
in (let TMP_132 \def (THead TMP_131 u t3) in (arity g c0 TMP_132 a1)))) in 
(let TMP_137 \def (\lambda (a1: A).(let TMP_134 \def (Bind b) in (let TMP_135 
\def (THead TMP_134 u t4) in (let TMP_136 \def (asucc g a1) in (arity g c0 
TMP_135 TMP_136))))) in (let TMP_138 \def (ex2 A TMP_133 TMP_137) in (let 
TMP_206 \def (\lambda (x0: A).(\lambda (H8: (arity g (CHead c0 (Bind b) u) t3 
x0)).(\lambda (H9: (arity g (CHead c0 (Bind b) u) t4 (asucc g x0))).(let H_x 
\def (leq_asucc g x) in (let H10 \def H_x in (let TMP_140 \def (\lambda (a0: 
A).(let TMP_139 \def (asucc g a0) in (leq g x TMP_139))) in (let TMP_143 \def 
(\lambda (a1: A).(let TMP_141 \def (Bind b) in (let TMP_142 \def (THead 
TMP_141 u t3) in (arity g c0 TMP_142 a1)))) in (let TMP_147 \def (\lambda 
(a1: A).(let TMP_144 \def (Bind b) in (let TMP_145 \def (THead TMP_144 u t4) 
in (let TMP_146 \def (asucc g a1) in (arity g c0 TMP_145 TMP_146))))) in (let 
TMP_148 \def (ex2 A TMP_143 TMP_147) in (let TMP_205 \def (\lambda (x1: 
A).(\lambda (H11: (leq g x (asucc g x1))).(let TMP_156 \def (\lambda (b0: 
B).((arity g (CHead c0 (Bind b0) u) t3 x0) \to ((arity g (CHead c0 (Bind b0) 
u) t4 (asucc g x0)) \to (let TMP_151 \def (\lambda (a1: A).(let TMP_149 \def 
(Bind b0) in (let TMP_150 \def (THead TMP_149 u t3) in (arity g c0 TMP_150 
a1)))) in (let TMP_155 \def (\lambda (a1: A).(let TMP_152 \def (Bind b0) in 
(let TMP_153 \def (THead TMP_152 u t4) in (let TMP_154 \def (asucc g a1) in 
(arity g c0 TMP_153 TMP_154))))) in (ex2 A TMP_151 TMP_155)))))) in (let 
TMP_167 \def (\lambda (H12: (arity g (CHead c0 (Bind Abbr) u) t3 
x0)).(\lambda (H13: (arity g (CHead c0 (Bind Abbr) u) t4 (asucc g x0))).(let 
TMP_159 \def (\lambda (a1: A).(let TMP_157 \def (Bind Abbr) in (let TMP_158 
\def (THead TMP_157 u t3) in (arity g c0 TMP_158 a1)))) in (let TMP_163 \def 
(\lambda (a1: A).(let TMP_160 \def (Bind Abbr) in (let TMP_161 \def (THead 
TMP_160 u t4) in (let TMP_162 \def (asucc g a1) in (arity g c0 TMP_161 
TMP_162))))) in (let TMP_164 \def (arity_bind g Abbr not_abbr_abst c0 u x H5 
t3 x0 H12) in (let TMP_165 \def (asucc g x0) in (let TMP_166 \def (arity_bind 
g Abbr not_abbr_abst c0 u x H5 t4 TMP_165 H13) in (ex_intro2 A TMP_159 
TMP_163 x0 TMP_164 TMP_166)))))))) in (let TMP_193 \def (\lambda (H12: (arity 
g (CHead c0 (Bind Abst) u) t3 x0)).(\lambda (H13: (arity g (CHead c0 (Bind 
Abst) u) t4 (asucc g x0))).(let TMP_170 \def (\lambda (a1: A).(let TMP_168 
\def (Bind Abst) in (let TMP_169 \def (THead TMP_168 u t3) in (arity g c0 
TMP_169 a1)))) in (let TMP_174 \def (\lambda (a1: A).(let TMP_171 \def (Bind 
Abst) in (let TMP_172 \def (THead TMP_171 u t4) in (let TMP_173 \def (asucc g 
a1) in (arity g c0 TMP_172 TMP_173))))) in (let TMP_175 \def (AHead x1 x0) in 
(let TMP_176 \def (asucc g x1) in (let TMP_177 \def (arity_repl g c0 u x H5 
TMP_176 H11) in (let TMP_178 \def (arity_head g c0 u x1 TMP_177 t3 x0 H12) in 
(let TMP_179 \def (Bind Abst) in (let TMP_180 \def (THead TMP_179 u t4) in 
(let TMP_181 \def (asucc g x0) in (let TMP_182 \def (AHead x1 TMP_181) in 
(let TMP_183 \def (asucc g x1) in (let TMP_184 \def (arity_repl g c0 u x H5 
TMP_183 H11) in (let TMP_185 \def (asucc g x0) in (let TMP_186 \def 
(arity_head g c0 u x1 TMP_184 t4 TMP_185 H13) in (let TMP_187 \def (AHead x1 
x0) in (let TMP_188 \def (asucc g TMP_187) in (let TMP_189 \def (AHead x1 x0) 
in (let TMP_190 \def (asucc g TMP_189) in (let TMP_191 \def (leq_refl g 
TMP_190) in (let TMP_192 \def (arity_repl g c0 TMP_180 TMP_182 TMP_186 
TMP_188 TMP_191) in (ex_intro2 A TMP_170 TMP_174 TMP_175 TMP_178 
TMP_192))))))))))))))))))))))) in (let TMP_204 \def (\lambda (H12: (arity g 
(CHead c0 (Bind Void) u) t3 x0)).(\lambda (H13: (arity g (CHead c0 (Bind 
Void) u) t4 (asucc g x0))).(let TMP_196 \def (\lambda (a1: A).(let TMP_194 
\def (Bind Void) in (let TMP_195 \def (THead TMP_194 u t3) in (arity g c0 
TMP_195 a1)))) in (let TMP_200 \def (\lambda (a1: A).(let TMP_197 \def (Bind 
Void) in (let TMP_198 \def (THead TMP_197 u t4) in (let TMP_199 \def (asucc g 
a1) in (arity g c0 TMP_198 TMP_199))))) in (let TMP_201 \def (arity_bind g 
Void not_void_abst c0 u x H5 t3 x0 H12) in (let TMP_202 \def (asucc g x0) in 
(let TMP_203 \def (arity_bind g Void not_void_abst c0 u x H5 t4 TMP_202 H13) 
in (ex_intro2 A TMP_196 TMP_200 x0 TMP_201 TMP_203)))))))) in (B_ind TMP_156 
TMP_167 TMP_193 TMP_204 b H8 H9))))))) in (ex_ind A TMP_140 TMP_148 TMP_205 
H10))))))))))) in (ex2_ind A TMP_126 TMP_130 TMP_138 TMP_206 H7))))))))))) in 
(ex2_ind A TMP_113 TMP_115 TMP_123 TMP_207 H4)))))))))))))))))) in (let 
TMP_304 \def (\lambda (c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: 
(ty3 g c0 w u)).(\lambda (H1: (ex2 A (\lambda (a1: A).(arity g c0 w a1)) 
(\lambda (a1: A).(arity g c0 u (asucc g a1))))).(\lambda (v: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u t))).(\lambda (H3: (ex2 A 
(\lambda (a1: A).(arity g c0 v a1)) (\lambda (a1: A).(arity g c0 (THead (Bind 
Abst) u t) (asucc g a1))))).(let H4 \def H1 in (let TMP_209 \def (\lambda 
(a1: A).(arity g c0 w a1)) in (let TMP_211 \def (\lambda (a1: A).(let TMP_210 
\def (asucc g a1) in (arity g c0 u TMP_210))) in (let TMP_214 \def (\lambda 
(a1: A).(let TMP_212 \def (Flat Appl) in (let TMP_213 \def (THead TMP_212 w 
v) in (arity g c0 TMP_213 a1)))) in (let TMP_220 \def (\lambda (a1: A).(let 
TMP_215 \def (Flat Appl) in (let TMP_216 \def (Bind Abst) in (let TMP_217 
\def (THead TMP_216 u t) in (let TMP_218 \def (THead TMP_215 w TMP_217) in 
(let TMP_219 \def (asucc g a1) in (arity g c0 TMP_218 TMP_219))))))) in (let 
TMP_221 \def (ex2 A TMP_214 TMP_220) in (let TMP_303 \def (\lambda (x: 
A).(\lambda (H5: (arity g c0 w x)).(\lambda (H6: (arity g c0 u (asucc g 
x))).(let H7 \def H3 in (let TMP_222 \def (\lambda (a1: A).(arity g c0 v a1)) 
in (let TMP_226 \def (\lambda (a1: A).(let TMP_223 \def (Bind Abst) in (let 
TMP_224 \def (THead TMP_223 u t) in (let TMP_225 \def (asucc g a1) in (arity 
g c0 TMP_224 TMP_225))))) in (let TMP_229 \def (\lambda (a1: A).(let TMP_227 
\def (Flat Appl) in (let TMP_228 \def (THead TMP_227 w v) in (arity g c0 
TMP_228 a1)))) in (let TMP_235 \def (\lambda (a1: A).(let TMP_230 \def (Flat 
Appl) in (let TMP_231 \def (Bind Abst) in (let TMP_232 \def (THead TMP_231 u 
t) in (let TMP_233 \def (THead TMP_230 w TMP_232) in (let TMP_234 \def (asucc 
g a1) in (arity g c0 TMP_233 TMP_234))))))) in (let TMP_236 \def (ex2 A 
TMP_229 TMP_235) in (let TMP_302 \def (\lambda (x0: A).(\lambda (H8: (arity g 
c0 v x0)).(\lambda (H9: (arity g c0 (THead (Bind Abst) u t) (asucc g 
x0))).(let TMP_237 \def (asucc g x0) in (let H10 \def (arity_gen_abst g c0 u 
t TMP_237 H9) in (let TMP_240 \def (\lambda (a1: A).(\lambda (a2: A).(let 
TMP_238 \def (asucc g x0) in (let TMP_239 \def (AHead a1 a2) in (eq A TMP_238 
TMP_239))))) in (let TMP_242 \def (\lambda (a1: A).(\lambda (_: A).(let 
TMP_241 \def (asucc g a1) in (arity g c0 u TMP_241)))) in (let TMP_245 \def 
(\lambda (_: A).(\lambda (a2: A).(let TMP_243 \def (Bind Abst) in (let 
TMP_244 \def (CHead c0 TMP_243 u) in (arity g TMP_244 t a2))))) in (let 
TMP_248 \def (\lambda (a1: A).(let TMP_246 \def (Flat Appl) in (let TMP_247 
\def (THead TMP_246 w v) in (arity g c0 TMP_247 a1)))) in (let TMP_254 \def 
(\lambda (a1: A).(let TMP_249 \def (Flat Appl) in (let TMP_250 \def (Bind 
Abst) in (let TMP_251 \def (THead TMP_250 u t) in (let TMP_252 \def (THead 
TMP_249 w TMP_251) in (let TMP_253 \def (asucc g a1) in (arity g c0 TMP_252 
TMP_253))))))) in (let TMP_255 \def (ex2 A TMP_248 TMP_254) in (let TMP_301 
\def (\lambda (x1: A).(\lambda (x2: A).(\lambda (H11: (eq A (asucc g x0) 
(AHead x1 x2))).(\lambda (H12: (arity g c0 u (asucc g x1))).(\lambda (H13: 
(arity g (CHead c0 (Bind Abst) u) t x2)).(let TMP_256 \def (asucc g x0) in 
(let TMP_257 \def (AHead x1 x2) in (let H14 \def (sym_eq A TMP_256 TMP_257 
H11) in (let H15 \def (asucc_gen_head g x1 x2 x0 H14) in (let TMP_259 \def 
(\lambda (a0: A).(let TMP_258 \def (AHead x1 a0) in (eq A x0 TMP_258))) in 
(let TMP_261 \def (\lambda (a0: A).(let TMP_260 \def (asucc g a0) in (eq A x2 
TMP_260))) in (let TMP_264 \def (\lambda (a1: A).(let TMP_262 \def (Flat 
Appl) in (let TMP_263 \def (THead TMP_262 w v) in (arity g c0 TMP_263 a1)))) 
in (let TMP_270 \def (\lambda (a1: A).(let TMP_265 \def (Flat Appl) in (let 
TMP_266 \def (Bind Abst) in (let TMP_267 \def (THead TMP_266 u t) in (let 
TMP_268 \def (THead TMP_265 w TMP_267) in (let TMP_269 \def (asucc g a1) in 
(arity g c0 TMP_268 TMP_269))))))) in (let TMP_271 \def (ex2 A TMP_264 
TMP_270) in (let TMP_300 \def (\lambda (x3: A).(\lambda (H16: (eq A x0 (AHead 
x1 x3))).(\lambda (H17: (eq A x2 (asucc g x3))).(let TMP_274 \def (\lambda 
(a: A).(let TMP_272 \def (Bind Abst) in (let TMP_273 \def (CHead c0 TMP_272 
u) in (arity g TMP_273 t a)))) in (let TMP_275 \def (asucc g x3) in (let H18 
\def (eq_ind A x2 TMP_274 H13 TMP_275 H17) in (let TMP_276 \def (\lambda (a: 
A).(arity g c0 v a)) in (let TMP_277 \def (AHead x1 x3) in (let H19 \def 
(eq_ind A x0 TMP_276 H8 TMP_277 H16) in (let TMP_280 \def (\lambda (a1: 
A).(let TMP_278 \def (Flat Appl) in (let TMP_279 \def (THead TMP_278 w v) in 
(arity g c0 TMP_279 a1)))) in (let TMP_286 \def (\lambda (a1: A).(let TMP_281 
\def (Flat Appl) in (let TMP_282 \def (Bind Abst) in (let TMP_283 \def (THead 
TMP_282 u t) in (let TMP_284 \def (THead TMP_281 w TMP_283) in (let TMP_285 
\def (asucc g a1) in (arity g c0 TMP_284 TMP_285))))))) in (let TMP_287 \def 
(asucc g x1) in (let TMP_288 \def (asucc g x) in (let TMP_289 \def 
(arity_mono g c0 u TMP_287 H12 TMP_288 H6) in (let TMP_290 \def (asucc_inj g 
x1 x TMP_289) in (let TMP_291 \def (leq_sym g x1 x TMP_290) in (let TMP_292 
\def (arity_repl g c0 w x H5 x1 TMP_291) in (let TMP_293 \def (arity_appl g 
c0 w x1 TMP_292 v x3 H19) in (let TMP_294 \def (Bind Abst) in (let TMP_295 
\def (THead TMP_294 u t) in (let TMP_296 \def (asucc g x3) in (let TMP_297 
\def (asucc g x3) in (let TMP_298 \def (arity_head g c0 u x H6 t TMP_297 H18) 
in (let TMP_299 \def (arity_appl g c0 w x H5 TMP_295 TMP_296 TMP_298) in 
(ex_intro2 A TMP_280 TMP_286 x3 TMP_293 TMP_299))))))))))))))))))))))))) in 
(ex2_ind A TMP_259 TMP_261 TMP_271 TMP_300 H15)))))))))))))))) in (ex3_2_ind 
A A TMP_240 TMP_242 TMP_245 TMP_255 TMP_301 H10))))))))))))) in (ex2_ind A 
TMP_222 TMP_226 TMP_236 TMP_302 H7))))))))))) in (ex2_ind A TMP_209 TMP_211 
TMP_221 TMP_303 H4))))))))))))))))) in (let TMP_347 \def (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g c0 t3 t4)).(\lambda 
(H1: (ex2 A (\lambda (a1: A).(arity g c0 t3 a1)) (\lambda (a1: A).(arity g c0 
t4 (asucc g a1))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t4 t0)).(\lambda 
(H3: (ex2 A (\lambda (a1: A).(arity g c0 t4 a1)) (\lambda (a1: A).(arity g c0 
t0 (asucc g a1))))).(let H4 \def H1 in (let TMP_305 \def (\lambda (a1: 
A).(arity g c0 t3 a1)) in (let TMP_307 \def (\lambda (a1: A).(let TMP_306 
\def (asucc g a1) in (arity g c0 t4 TMP_306))) in (let TMP_310 \def (\lambda 
(a1: A).(let TMP_308 \def (Flat Cast) in (let TMP_309 \def (THead TMP_308 t4 
t3) in (arity g c0 TMP_309 a1)))) in (let TMP_314 \def (\lambda (a1: A).(let 
TMP_311 \def (Flat Cast) in (let TMP_312 \def (THead TMP_311 t0 t4) in (let 
TMP_313 \def (asucc g a1) in (arity g c0 TMP_312 TMP_313))))) in (let TMP_315 
\def (ex2 A TMP_310 TMP_314) in (let TMP_346 \def (\lambda (x: A).(\lambda 
(H5: (arity g c0 t3 x)).(\lambda (H6: (arity g c0 t4 (asucc g x))).(let H7 
\def H3 in (let TMP_316 \def (\lambda (a1: A).(arity g c0 t4 a1)) in (let 
TMP_318 \def (\lambda (a1: A).(let TMP_317 \def (asucc g a1) in (arity g c0 
t0 TMP_317))) in (let TMP_321 \def (\lambda (a1: A).(let TMP_319 \def (Flat 
Cast) in (let TMP_320 \def (THead TMP_319 t4 t3) in (arity g c0 TMP_320 
a1)))) in (let TMP_325 \def (\lambda (a1: A).(let TMP_322 \def (Flat Cast) in 
(let TMP_323 \def (THead TMP_322 t0 t4) in (let TMP_324 \def (asucc g a1) in 
(arity g c0 TMP_323 TMP_324))))) in (let TMP_326 \def (ex2 A TMP_321 TMP_325) 
in (let TMP_345 \def (\lambda (x0: A).(\lambda (H8: (arity g c0 t4 
x0)).(\lambda (H9: (arity g c0 t0 (asucc g x0))).(let TMP_329 \def (\lambda 
(a1: A).(let TMP_327 \def (Flat Cast) in (let TMP_328 \def (THead TMP_327 t4 
t3) in (arity g c0 TMP_328 a1)))) in (let TMP_333 \def (\lambda (a1: A).(let 
TMP_330 \def (Flat Cast) in (let TMP_331 \def (THead TMP_330 t0 t4) in (let 
TMP_332 \def (asucc g a1) in (arity g c0 TMP_331 TMP_332))))) in (let TMP_334 
\def (arity_cast g c0 t4 x H6 t3 H5) in (let TMP_335 \def (asucc g x) in (let 
TMP_336 \def (asucc g x0) in (let TMP_337 \def (asucc g x) in (let TMP_338 
\def (asucc g TMP_337) in (let TMP_339 \def (asucc g x) in (let TMP_340 \def 
(asucc g x) in (let TMP_341 \def (arity_mono g c0 t4 x0 H8 TMP_340 H6) in 
(let TMP_342 \def (asucc_repl g x0 TMP_339 TMP_341) in (let TMP_343 \def 
(arity_repl g c0 t0 TMP_336 H9 TMP_338 TMP_342) in (let TMP_344 \def 
(arity_cast g c0 t0 TMP_335 TMP_343 t4 H6) in (ex_intro2 A TMP_329 TMP_333 x 
TMP_334 TMP_344))))))))))))))))) in (ex2_ind A TMP_316 TMP_318 TMP_326 
TMP_345 H7))))))))))) in (ex2_ind A TMP_305 TMP_307 TMP_315 TMP_346 
H4)))))))))))))))) in (ty3_ind g TMP_4 TMP_40 TMP_51 TMP_74 TMP_112 TMP_208 
TMP_304 TMP_347 c t1 t2 H))))))))))))).

