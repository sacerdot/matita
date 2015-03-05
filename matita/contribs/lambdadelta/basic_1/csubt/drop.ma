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

include "basic_1/csubt/fwd.ma".

include "basic_1/drop/fwd.ma".

theorem csubt_drop_flat:
 \forall (g: G).(\forall (f: F).(\forall (n: nat).(\forall (c1: C).(\forall 
(c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 
(CHead d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(drop n O c2 (CHead d2 (Flat f) u))))))))))))
\def
 \lambda (g: G).(\lambda (f: F).(\lambda (n: nat).(let TMP_5 \def (\lambda 
(n0: nat).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall 
(d1: C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Flat f) u)) \to (let TMP_1 
\def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_4 \def (\lambda (d2: 
C).(let TMP_2 \def (Flat f) in (let TMP_3 \def (CHead d2 TMP_2 u) in (drop n0 
O c2 TMP_3)))) in (ex2 C TMP_1 TMP_4)))))))))) in (let TMP_39 \def (\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 c2)).(\lambda (d1: 
C).(\lambda (u: T).(\lambda (H0: (drop O O c1 (CHead d1 (Flat f) u))).(let 
TMP_6 \def (\lambda (c: C).(csubt g c c2)) in (let TMP_7 \def (Flat f) in 
(let TMP_8 \def (CHead d1 TMP_7 u) in (let TMP_9 \def (Flat f) in (let TMP_10 
\def (CHead d1 TMP_9 u) in (let TMP_11 \def (drop_gen_refl c1 TMP_10 H0) in 
(let H1 \def (eq_ind C c1 TMP_6 H TMP_8 TMP_11) in (let H_x \def 
(csubt_gen_flat g d1 c2 u f H1) in (let H2 \def H_x in (let TMP_14 \def 
(\lambda (e2: C).(let TMP_12 \def (Flat f) in (let TMP_13 \def (CHead e2 
TMP_12 u) in (eq C c2 TMP_13)))) in (let TMP_15 \def (\lambda (e2: C).(csubt 
g d1 e2)) in (let TMP_16 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_19 \def (\lambda (d2: C).(let TMP_17 \def (Flat f) in (let TMP_18 \def 
(CHead d2 TMP_17 u) in (drop O O c2 TMP_18)))) in (let TMP_20 \def (ex2 C 
TMP_16 TMP_19) in (let TMP_38 \def (\lambda (x: C).(\lambda (H3: (eq C c2 
(CHead x (Flat f) u))).(\lambda (H4: (csubt g d1 x)).(let TMP_21 \def (Flat 
f) in (let TMP_22 \def (CHead x TMP_21 u) in (let TMP_27 \def (\lambda (c: 
C).(let TMP_23 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_26 \def 
(\lambda (d2: C).(let TMP_24 \def (Flat f) in (let TMP_25 \def (CHead d2 
TMP_24 u) in (drop O O c TMP_25)))) in (ex2 C TMP_23 TMP_26)))) in (let 
TMP_28 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_33 \def (\lambda 
(d2: C).(let TMP_29 \def (Flat f) in (let TMP_30 \def (CHead x TMP_29 u) in 
(let TMP_31 \def (Flat f) in (let TMP_32 \def (CHead d2 TMP_31 u) in (drop O 
O TMP_30 TMP_32)))))) in (let TMP_34 \def (Flat f) in (let TMP_35 \def (CHead 
x TMP_34 u) in (let TMP_36 \def (drop_refl TMP_35) in (let TMP_37 \def 
(ex_intro2 C TMP_28 TMP_33 x H4 TMP_36) in (eq_ind_r C TMP_22 TMP_27 TMP_37 
c2 H3))))))))))))) in (ex2_ind C TMP_14 TMP_15 TMP_20 TMP_38 
H2)))))))))))))))))))))) in (let TMP_204 \def (\lambda (n0: nat).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Flat f) u)) \to (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 (Flat f) 
u)))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H0: (csubt g c1 
c2)).(let TMP_45 \def (\lambda (c: C).(\lambda (c0: C).(\forall (d1: 
C).(\forall (u: T).((drop (S n0) O c (CHead d1 (Flat f) u)) \to (let TMP_40 
\def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_44 \def (\lambda (d2: 
C).(let TMP_41 \def (S n0) in (let TMP_42 \def (Flat f) in (let TMP_43 \def 
(CHead d2 TMP_42 u) in (drop TMP_41 O c0 TMP_43))))) in (ex2 C TMP_40 
TMP_44)))))))) in (let TMP_74 \def (\lambda (n1: nat).(\lambda (d1: 
C).(\lambda (u: T).(\lambda (H1: (drop (S n0) O (CSort n1) (CHead d1 (Flat f) 
u))).(let TMP_46 \def (Flat f) in (let TMP_47 \def (CHead d1 TMP_46 u) in 
(let TMP_48 \def (CSort n1) in (let TMP_49 \def (eq C TMP_47 TMP_48) in (let 
TMP_50 \def (S n0) in (let TMP_51 \def (eq nat TMP_50 O) in (let TMP_52 \def 
(eq nat O O) in (let TMP_53 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_58 \def (\lambda (d2: C).(let TMP_54 \def (S n0) in (let TMP_55 \def 
(CSort n1) in (let TMP_56 \def (Flat f) in (let TMP_57 \def (CHead d2 TMP_56 
u) in (drop TMP_54 O TMP_55 TMP_57)))))) in (let TMP_59 \def (ex2 C TMP_53 
TMP_58) in (let TMP_69 \def (\lambda (_: (eq C (CHead d1 (Flat f) u) (CSort 
n1))).(\lambda (H3: (eq nat (S n0) O)).(\lambda (_: (eq nat O O)).(let TMP_60 
\def (S n0) in (let TMP_61 \def (\lambda (ee: nat).(match ee with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H5 \def (eq_ind nat 
TMP_60 TMP_61 I O H3) in (let TMP_62 \def (\lambda (d2: C).(csubt g d1 d2)) 
in (let TMP_67 \def (\lambda (d2: C).(let TMP_63 \def (S n0) in (let TMP_64 
\def (CSort n1) in (let TMP_65 \def (Flat f) in (let TMP_66 \def (CHead d2 
TMP_65 u) in (drop TMP_63 O TMP_64 TMP_66)))))) in (let TMP_68 \def (ex2 C 
TMP_62 TMP_67) in (False_ind TMP_68 H5)))))))))) in (let TMP_70 \def (S n0) 
in (let TMP_71 \def (Flat f) in (let TMP_72 \def (CHead d1 TMP_71 u) in (let 
TMP_73 \def (drop_gen_sort n1 TMP_70 O TMP_72 H1) in (and3_ind TMP_49 TMP_51 
TMP_52 TMP_59 TMP_69 TMP_73)))))))))))))))))))) in (let TMP_143 \def (\lambda 
(c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 c3)).(\lambda (H2: 
((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 (CHead d1 (Flat f) u)) 
\to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O 
c3 (CHead d2 (Flat f) u))))))))).(\lambda (k: K).(let TMP_81 \def (\lambda 
(k0: K).(\forall (u: T).(\forall (d1: C).(\forall (u0: T).((drop (S n0) O 
(CHead c0 k0 u) (CHead d1 (Flat f) u0)) \to (let TMP_75 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_80 \def (\lambda (d2: C).(let TMP_76 \def (S 
n0) in (let TMP_77 \def (CHead c3 k0 u) in (let TMP_78 \def (Flat f) in (let 
TMP_79 \def (CHead d2 TMP_78 u0) in (drop TMP_76 O TMP_77 TMP_79)))))) in 
(ex2 C TMP_75 TMP_80)))))))) in (let TMP_111 \def (\lambda (b: B).(\lambda 
(u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S n0) O (CHead 
c0 (Bind b) u) (CHead d1 (Flat f) u0))).(let TMP_82 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_85 \def (\lambda (d2: C).(let TMP_83 \def 
(Flat f) in (let TMP_84 \def (CHead d2 TMP_83 u0) in (drop n0 O c3 TMP_84)))) 
in (let TMP_86 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_92 \def 
(\lambda (d2: C).(let TMP_87 \def (S n0) in (let TMP_88 \def (Bind b) in (let 
TMP_89 \def (CHead c3 TMP_88 u) in (let TMP_90 \def (Flat f) in (let TMP_91 
\def (CHead d2 TMP_90 u0) in (drop TMP_87 O TMP_89 TMP_91))))))) in (let 
TMP_93 \def (ex2 C TMP_86 TMP_92) in (let TMP_105 \def (\lambda (x: 
C).(\lambda (H4: (csubt g d1 x)).(\lambda (H5: (drop n0 O c3 (CHead x (Flat 
f) u0))).(let TMP_94 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_100 
\def (\lambda (d2: C).(let TMP_95 \def (S n0) in (let TMP_96 \def (Bind b) in 
(let TMP_97 \def (CHead c3 TMP_96 u) in (let TMP_98 \def (Flat f) in (let 
TMP_99 \def (CHead d2 TMP_98 u0) in (drop TMP_95 O TMP_97 TMP_99))))))) in 
(let TMP_101 \def (Bind b) in (let TMP_102 \def (Flat f) in (let TMP_103 \def 
(CHead x TMP_102 u0) in (let TMP_104 \def (drop_drop TMP_101 n0 c3 TMP_103 H5 
u) in (ex_intro2 C TMP_94 TMP_100 x H4 TMP_104)))))))))) in (let TMP_106 \def 
(Bind b) in (let TMP_107 \def (Flat f) in (let TMP_108 \def (CHead d1 TMP_107 
u0) in (let TMP_109 \def (drop_gen_drop TMP_106 c0 TMP_108 u n0 H3) in (let 
TMP_110 \def (H c0 c3 H1 d1 u0 TMP_109) in (ex2_ind C TMP_82 TMP_85 TMP_93 
TMP_105 TMP_110))))))))))))))))) in (let TMP_142 \def (\lambda (f0: 
F).(\lambda (u: T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S 
n0) O (CHead c0 (Flat f0) u) (CHead d1 (Flat f) u0))).(let TMP_112 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_116 \def (\lambda (d2: C).(let 
TMP_113 \def (S n0) in (let TMP_114 \def (Flat f) in (let TMP_115 \def (CHead 
d2 TMP_114 u0) in (drop TMP_113 O c3 TMP_115))))) in (let TMP_117 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_123 \def (\lambda (d2: C).(let 
TMP_118 \def (S n0) in (let TMP_119 \def (Flat f0) in (let TMP_120 \def 
(CHead c3 TMP_119 u) in (let TMP_121 \def (Flat f) in (let TMP_122 \def 
(CHead d2 TMP_121 u0) in (drop TMP_118 O TMP_120 TMP_122))))))) in (let 
TMP_124 \def (ex2 C TMP_117 TMP_123) in (let TMP_136 \def (\lambda (x: 
C).(\lambda (H4: (csubt g d1 x)).(\lambda (H5: (drop (S n0) O c3 (CHead x 
(Flat f) u0))).(let TMP_125 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_131 \def (\lambda (d2: C).(let TMP_126 \def (S n0) in (let TMP_127 \def 
(Flat f0) in (let TMP_128 \def (CHead c3 TMP_127 u) in (let TMP_129 \def 
(Flat f) in (let TMP_130 \def (CHead d2 TMP_129 u0) in (drop TMP_126 O 
TMP_128 TMP_130))))))) in (let TMP_132 \def (Flat f0) in (let TMP_133 \def 
(Flat f) in (let TMP_134 \def (CHead x TMP_133 u0) in (let TMP_135 \def 
(drop_drop TMP_132 n0 c3 TMP_134 H5 u) in (ex_intro2 C TMP_125 TMP_131 x H4 
TMP_135)))))))))) in (let TMP_137 \def (Flat f0) in (let TMP_138 \def (Flat 
f) in (let TMP_139 \def (CHead d1 TMP_138 u0) in (let TMP_140 \def 
(drop_gen_drop TMP_137 c0 TMP_139 u n0 H3) in (let TMP_141 \def (H2 d1 u0 
TMP_140) in (ex2_ind C TMP_112 TMP_116 TMP_124 TMP_136 
TMP_141))))))))))))))))) in (K_ind TMP_81 TMP_111 TMP_142 k))))))))) in (let 
TMP_173 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 (CHead 
d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O c3 (CHead d2 (Flat f) u))))))))).(\lambda (b: B).(\lambda 
(_: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (d1: 
C).(\lambda (u: T).(\lambda (H4: (drop (S n0) O (CHead c0 (Bind Void) u1) 
(CHead d1 (Flat f) u))).(let TMP_144 \def (\lambda (d2: C).(csubt g d1 d2)) 
in (let TMP_147 \def (\lambda (d2: C).(let TMP_145 \def (Flat f) in (let 
TMP_146 \def (CHead d2 TMP_145 u) in (drop n0 O c3 TMP_146)))) in (let 
TMP_148 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_154 \def (\lambda 
(d2: C).(let TMP_149 \def (S n0) in (let TMP_150 \def (Bind b) in (let 
TMP_151 \def (CHead c3 TMP_150 u2) in (let TMP_152 \def (Flat f) in (let 
TMP_153 \def (CHead d2 TMP_152 u) in (drop TMP_149 O TMP_151 TMP_153))))))) 
in (let TMP_155 \def (ex2 C TMP_148 TMP_154) in (let TMP_167 \def (\lambda 
(x: C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x 
(Flat f) u))).(let TMP_156 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_162 \def (\lambda (d2: C).(let TMP_157 \def (S n0) in (let TMP_158 \def 
(Bind b) in (let TMP_159 \def (CHead c3 TMP_158 u2) in (let TMP_160 \def 
(Flat f) in (let TMP_161 \def (CHead d2 TMP_160 u) in (drop TMP_157 O TMP_159 
TMP_161))))))) in (let TMP_163 \def (Bind b) in (let TMP_164 \def (Flat f) in 
(let TMP_165 \def (CHead x TMP_164 u) in (let TMP_166 \def (drop_drop TMP_163 
n0 c3 TMP_165 H6 u2) in (ex_intro2 C TMP_156 TMP_162 x H5 TMP_166)))))))))) 
in (let TMP_168 \def (Bind Void) in (let TMP_169 \def (Flat f) in (let 
TMP_170 \def (CHead d1 TMP_169 u) in (let TMP_171 \def (drop_gen_drop TMP_168 
c0 TMP_170 u1 n0 H4) in (let TMP_172 \def (H c0 c3 H1 d1 u TMP_171) in 
(ex2_ind C TMP_144 TMP_147 TMP_155 TMP_167 TMP_172))))))))))))))))))))))) in 
(let TMP_203 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 (CHead 
d1 (Flat f) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O c3 (CHead d2 (Flat f) u))))))))).(\lambda (u: T).(\lambda 
(t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (ty3 g c3 u t)).(\lambda 
(d1: C).(\lambda (u0: T).(\lambda (H5: (drop (S n0) O (CHead c0 (Bind Abst) 
t) (CHead d1 (Flat f) u0))).(let TMP_174 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_177 \def (\lambda (d2: C).(let TMP_175 \def (Flat f) in (let 
TMP_176 \def (CHead d2 TMP_175 u0) in (drop n0 O c3 TMP_176)))) in (let 
TMP_178 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_184 \def (\lambda 
(d2: C).(let TMP_179 \def (S n0) in (let TMP_180 \def (Bind Abbr) in (let 
TMP_181 \def (CHead c3 TMP_180 u) in (let TMP_182 \def (Flat f) in (let 
TMP_183 \def (CHead d2 TMP_182 u0) in (drop TMP_179 O TMP_181 TMP_183))))))) 
in (let TMP_185 \def (ex2 C TMP_178 TMP_184) in (let TMP_197 \def (\lambda 
(x: C).(\lambda (H6: (csubt g d1 x)).(\lambda (H7: (drop n0 O c3 (CHead x 
(Flat f) u0))).(let TMP_186 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_192 \def (\lambda (d2: C).(let TMP_187 \def (S n0) in (let TMP_188 \def 
(Bind Abbr) in (let TMP_189 \def (CHead c3 TMP_188 u) in (let TMP_190 \def 
(Flat f) in (let TMP_191 \def (CHead d2 TMP_190 u0) in (drop TMP_187 O 
TMP_189 TMP_191))))))) in (let TMP_193 \def (Bind Abbr) in (let TMP_194 \def 
(Flat f) in (let TMP_195 \def (CHead x TMP_194 u0) in (let TMP_196 \def 
(drop_drop TMP_193 n0 c3 TMP_195 H7 u) in (ex_intro2 C TMP_186 TMP_192 x H6 
TMP_196)))))))))) in (let TMP_198 \def (Bind Abst) in (let TMP_199 \def (Flat 
f) in (let TMP_200 \def (CHead d1 TMP_199 u0) in (let TMP_201 \def 
(drop_gen_drop TMP_198 c0 TMP_200 t n0 H5) in (let TMP_202 \def (H c0 c3 H1 
d1 u0 TMP_201) in (ex2_ind C TMP_174 TMP_177 TMP_185 TMP_197 
TMP_202))))))))))))))))))))))) in (csubt_ind g TMP_45 TMP_74 TMP_143 TMP_173 
TMP_203 c1 c2 H0))))))))))) in (nat_ind TMP_5 TMP_39 TMP_204 n)))))).

theorem csubt_drop_abbr:
 \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (u: T).((drop n O c1 (CHead d1 (Bind 
Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
n O c2 (CHead d2 (Bind Abbr) u)))))))))))
\def
 \lambda (g: G).(\lambda (n: nat).(let TMP_5 \def (\lambda (n0: nat).(\forall 
(c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: C).(\forall (u: 
T).((drop n0 O c1 (CHead d1 (Bind Abbr) u)) \to (let TMP_1 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_4 \def (\lambda (d2: C).(let TMP_2 \def (Bind 
Abbr) in (let TMP_3 \def (CHead d2 TMP_2 u) in (drop n0 O c2 TMP_3)))) in 
(ex2 C TMP_1 TMP_4)))))))))) in (let TMP_39 \def (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (H: (csubt g c1 c2)).(\lambda (d1: C).(\lambda (u: 
T).(\lambda (H0: (drop O O c1 (CHead d1 (Bind Abbr) u))).(let TMP_6 \def 
(\lambda (c: C).(csubt g c c2)) in (let TMP_7 \def (Bind Abbr) in (let TMP_8 
\def (CHead d1 TMP_7 u) in (let TMP_9 \def (Bind Abbr) in (let TMP_10 \def 
(CHead d1 TMP_9 u) in (let TMP_11 \def (drop_gen_refl c1 TMP_10 H0) in (let 
H1 \def (eq_ind C c1 TMP_6 H TMP_8 TMP_11) in (let H2 \def (csubt_gen_abbr g 
d1 c2 u H1) in (let TMP_14 \def (\lambda (e2: C).(let TMP_12 \def (Bind Abbr) 
in (let TMP_13 \def (CHead e2 TMP_12 u) in (eq C c2 TMP_13)))) in (let TMP_15 
\def (\lambda (e2: C).(csubt g d1 e2)) in (let TMP_16 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_19 \def (\lambda (d2: C).(let TMP_17 \def 
(Bind Abbr) in (let TMP_18 \def (CHead d2 TMP_17 u) in (drop O O c2 
TMP_18)))) in (let TMP_20 \def (ex2 C TMP_16 TMP_19) in (let TMP_38 \def 
(\lambda (x: C).(\lambda (H3: (eq C c2 (CHead x (Bind Abbr) u))).(\lambda 
(H4: (csubt g d1 x)).(let TMP_21 \def (Bind Abbr) in (let TMP_22 \def (CHead 
x TMP_21 u) in (let TMP_27 \def (\lambda (c: C).(let TMP_23 \def (\lambda 
(d2: C).(csubt g d1 d2)) in (let TMP_26 \def (\lambda (d2: C).(let TMP_24 
\def (Bind Abbr) in (let TMP_25 \def (CHead d2 TMP_24 u) in (drop O O c 
TMP_25)))) in (ex2 C TMP_23 TMP_26)))) in (let TMP_28 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_33 \def (\lambda (d2: C).(let TMP_29 \def 
(Bind Abbr) in (let TMP_30 \def (CHead x TMP_29 u) in (let TMP_31 \def (Bind 
Abbr) in (let TMP_32 \def (CHead d2 TMP_31 u) in (drop O O TMP_30 
TMP_32)))))) in (let TMP_34 \def (Bind Abbr) in (let TMP_35 \def (CHead x 
TMP_34 u) in (let TMP_36 \def (drop_refl TMP_35) in (let TMP_37 \def 
(ex_intro2 C TMP_28 TMP_33 x H4 TMP_36) in (eq_ind_r C TMP_22 TMP_27 TMP_37 
c2 H3))))))))))))) in (ex2_ind C TMP_14 TMP_15 TMP_20 TMP_38 
H2))))))))))))))))))))) in (let TMP_204 \def (\lambda (n0: nat).(\lambda (H: 
((\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (u: T).((drop n0 O c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c2 (CHead d2 
(Bind Abbr) u)))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H0: 
(csubt g c1 c2)).(let TMP_45 \def (\lambda (c: C).(\lambda (c0: C).(\forall 
(d1: C).(\forall (u: T).((drop (S n0) O c (CHead d1 (Bind Abbr) u)) \to (let 
TMP_40 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_44 \def (\lambda 
(d2: C).(let TMP_41 \def (S n0) in (let TMP_42 \def (Bind Abbr) in (let 
TMP_43 \def (CHead d2 TMP_42 u) in (drop TMP_41 O c0 TMP_43))))) in (ex2 C 
TMP_40 TMP_44)))))))) in (let TMP_74 \def (\lambda (n1: nat).(\lambda (d1: 
C).(\lambda (u: T).(\lambda (H1: (drop (S n0) O (CSort n1) (CHead d1 (Bind 
Abbr) u))).(let TMP_46 \def (Bind Abbr) in (let TMP_47 \def (CHead d1 TMP_46 
u) in (let TMP_48 \def (CSort n1) in (let TMP_49 \def (eq C TMP_47 TMP_48) in 
(let TMP_50 \def (S n0) in (let TMP_51 \def (eq nat TMP_50 O) in (let TMP_52 
\def (eq nat O O) in (let TMP_53 \def (\lambda (d2: C).(csubt g d1 d2)) in 
(let TMP_58 \def (\lambda (d2: C).(let TMP_54 \def (S n0) in (let TMP_55 \def 
(CSort n1) in (let TMP_56 \def (Bind Abbr) in (let TMP_57 \def (CHead d2 
TMP_56 u) in (drop TMP_54 O TMP_55 TMP_57)))))) in (let TMP_59 \def (ex2 C 
TMP_53 TMP_58) in (let TMP_69 \def (\lambda (_: (eq C (CHead d1 (Bind Abbr) 
u) (CSort n1))).(\lambda (H3: (eq nat (S n0) O)).(\lambda (_: (eq nat O 
O)).(let TMP_60 \def (S n0) in (let TMP_61 \def (\lambda (ee: nat).(match ee 
with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H5 \def (eq_ind 
nat TMP_60 TMP_61 I O H3) in (let TMP_62 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_67 \def (\lambda (d2: C).(let TMP_63 \def (S n0) in (let 
TMP_64 \def (CSort n1) in (let TMP_65 \def (Bind Abbr) in (let TMP_66 \def 
(CHead d2 TMP_65 u) in (drop TMP_63 O TMP_64 TMP_66)))))) in (let TMP_68 \def 
(ex2 C TMP_62 TMP_67) in (False_ind TMP_68 H5)))))))))) in (let TMP_70 \def 
(S n0) in (let TMP_71 \def (Bind Abbr) in (let TMP_72 \def (CHead d1 TMP_71 
u) in (let TMP_73 \def (drop_gen_sort n1 TMP_70 O TMP_72 H1) in (and3_ind 
TMP_49 TMP_51 TMP_52 TMP_59 TMP_69 TMP_73)))))))))))))))))))) in (let TMP_143 
\def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (H2: ((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 
(CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u))))))))).(\lambda 
(k: K).(let TMP_81 \def (\lambda (k0: K).(\forall (u: T).(\forall (d1: 
C).(\forall (u0: T).((drop (S n0) O (CHead c0 k0 u) (CHead d1 (Bind Abbr) 
u0)) \to (let TMP_75 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_80 
\def (\lambda (d2: C).(let TMP_76 \def (S n0) in (let TMP_77 \def (CHead c3 
k0 u) in (let TMP_78 \def (Bind Abbr) in (let TMP_79 \def (CHead d2 TMP_78 
u0) in (drop TMP_76 O TMP_77 TMP_79)))))) in (ex2 C TMP_75 TMP_80)))))))) in 
(let TMP_111 \def (\lambda (b: B).(\lambda (u: T).(\lambda (d1: C).(\lambda 
(u0: T).(\lambda (H3: (drop (S n0) O (CHead c0 (Bind b) u) (CHead d1 (Bind 
Abbr) u0))).(let TMP_82 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_85 
\def (\lambda (d2: C).(let TMP_83 \def (Bind Abbr) in (let TMP_84 \def (CHead 
d2 TMP_83 u0) in (drop n0 O c3 TMP_84)))) in (let TMP_86 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_92 \def (\lambda (d2: C).(let TMP_87 \def (S 
n0) in (let TMP_88 \def (Bind b) in (let TMP_89 \def (CHead c3 TMP_88 u) in 
(let TMP_90 \def (Bind Abbr) in (let TMP_91 \def (CHead d2 TMP_90 u0) in 
(drop TMP_87 O TMP_89 TMP_91))))))) in (let TMP_93 \def (ex2 C TMP_86 TMP_92) 
in (let TMP_105 \def (\lambda (x: C).(\lambda (H4: (csubt g d1 x)).(\lambda 
(H5: (drop n0 O c3 (CHead x (Bind Abbr) u0))).(let TMP_94 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_100 \def (\lambda (d2: C).(let TMP_95 \def (S 
n0) in (let TMP_96 \def (Bind b) in (let TMP_97 \def (CHead c3 TMP_96 u) in 
(let TMP_98 \def (Bind Abbr) in (let TMP_99 \def (CHead d2 TMP_98 u0) in 
(drop TMP_95 O TMP_97 TMP_99))))))) in (let TMP_101 \def (Bind b) in (let 
TMP_102 \def (Bind Abbr) in (let TMP_103 \def (CHead x TMP_102 u0) in (let 
TMP_104 \def (drop_drop TMP_101 n0 c3 TMP_103 H5 u) in (ex_intro2 C TMP_94 
TMP_100 x H4 TMP_104)))))))))) in (let TMP_106 \def (Bind b) in (let TMP_107 
\def (Bind Abbr) in (let TMP_108 \def (CHead d1 TMP_107 u0) in (let TMP_109 
\def (drop_gen_drop TMP_106 c0 TMP_108 u n0 H3) in (let TMP_110 \def (H c0 c3 
H1 d1 u0 TMP_109) in (ex2_ind C TMP_82 TMP_85 TMP_93 TMP_105 
TMP_110))))))))))))))))) in (let TMP_142 \def (\lambda (f: F).(\lambda (u: 
T).(\lambda (d1: C).(\lambda (u0: T).(\lambda (H3: (drop (S n0) O (CHead c0 
(Flat f) u) (CHead d1 (Bind Abbr) u0))).(let TMP_112 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_116 \def (\lambda (d2: C).(let TMP_113 \def 
(S n0) in (let TMP_114 \def (Bind Abbr) in (let TMP_115 \def (CHead d2 
TMP_114 u0) in (drop TMP_113 O c3 TMP_115))))) in (let TMP_117 \def (\lambda 
(d2: C).(csubt g d1 d2)) in (let TMP_123 \def (\lambda (d2: C).(let TMP_118 
\def (S n0) in (let TMP_119 \def (Flat f) in (let TMP_120 \def (CHead c3 
TMP_119 u) in (let TMP_121 \def (Bind Abbr) in (let TMP_122 \def (CHead d2 
TMP_121 u0) in (drop TMP_118 O TMP_120 TMP_122))))))) in (let TMP_124 \def 
(ex2 C TMP_117 TMP_123) in (let TMP_136 \def (\lambda (x: C).(\lambda (H4: 
(csubt g d1 x)).(\lambda (H5: (drop (S n0) O c3 (CHead x (Bind Abbr) 
u0))).(let TMP_125 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_131 
\def (\lambda (d2: C).(let TMP_126 \def (S n0) in (let TMP_127 \def (Flat f) 
in (let TMP_128 \def (CHead c3 TMP_127 u) in (let TMP_129 \def (Bind Abbr) in 
(let TMP_130 \def (CHead d2 TMP_129 u0) in (drop TMP_126 O TMP_128 
TMP_130))))))) in (let TMP_132 \def (Flat f) in (let TMP_133 \def (Bind Abbr) 
in (let TMP_134 \def (CHead x TMP_133 u0) in (let TMP_135 \def (drop_drop 
TMP_132 n0 c3 TMP_134 H5 u) in (ex_intro2 C TMP_125 TMP_131 x H4 
TMP_135)))))))))) in (let TMP_137 \def (Flat f) in (let TMP_138 \def (Bind 
Abbr) in (let TMP_139 \def (CHead d1 TMP_138 u0) in (let TMP_140 \def 
(drop_gen_drop TMP_137 c0 TMP_139 u n0 H3) in (let TMP_141 \def (H2 d1 u0 
TMP_140) in (ex2_ind C TMP_112 TMP_116 TMP_124 TMP_136 
TMP_141))))))))))))))))) in (K_ind TMP_81 TMP_111 TMP_142 k))))))))) in (let 
TMP_173 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (_: ((\forall (d1: C).(\forall (u: T).((drop (S n0) O c0 (CHead 
d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u))))))))).(\lambda (b: 
B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (d1: C).(\lambda (u: T).(\lambda (H4: (drop (S n0) O (CHead c0 
(Bind Void) u1) (CHead d1 (Bind Abbr) u))).(let TMP_144 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_147 \def (\lambda (d2: C).(let TMP_145 \def 
(Bind Abbr) in (let TMP_146 \def (CHead d2 TMP_145 u) in (drop n0 O c3 
TMP_146)))) in (let TMP_148 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_154 \def (\lambda (d2: C).(let TMP_149 \def (S n0) in (let TMP_150 \def 
(Bind b) in (let TMP_151 \def (CHead c3 TMP_150 u2) in (let TMP_152 \def 
(Bind Abbr) in (let TMP_153 \def (CHead d2 TMP_152 u) in (drop TMP_149 O 
TMP_151 TMP_153))))))) in (let TMP_155 \def (ex2 C TMP_148 TMP_154) in (let 
TMP_167 \def (\lambda (x: C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: 
(drop n0 O c3 (CHead x (Bind Abbr) u))).(let TMP_156 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_162 \def (\lambda (d2: C).(let TMP_157 \def 
(S n0) in (let TMP_158 \def (Bind b) in (let TMP_159 \def (CHead c3 TMP_158 
u2) in (let TMP_160 \def (Bind Abbr) in (let TMP_161 \def (CHead d2 TMP_160 
u) in (drop TMP_157 O TMP_159 TMP_161))))))) in (let TMP_163 \def (Bind b) in 
(let TMP_164 \def (Bind Abbr) in (let TMP_165 \def (CHead x TMP_164 u) in 
(let TMP_166 \def (drop_drop TMP_163 n0 c3 TMP_165 H6 u2) in (ex_intro2 C 
TMP_156 TMP_162 x H5 TMP_166)))))))))) in (let TMP_168 \def (Bind Void) in 
(let TMP_169 \def (Bind Abbr) in (let TMP_170 \def (CHead d1 TMP_169 u) in 
(let TMP_171 \def (drop_gen_drop TMP_168 c0 TMP_170 u1 n0 H4) in (let TMP_172 
\def (H c0 c3 H1 d1 u TMP_171) in (ex2_ind C TMP_144 TMP_147 TMP_155 TMP_167 
TMP_172))))))))))))))))))))))) in (let TMP_203 \def (\lambda (c0: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: 
C).(\forall (u: T).((drop (S n0) O c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead 
d2 (Bind Abbr) u))))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g 
c0 u t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (d1: C).(\lambda (u0: 
T).(\lambda (H5: (drop (S n0) O (CHead c0 (Bind Abst) t) (CHead d1 (Bind 
Abbr) u0))).(let TMP_174 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_177 \def (\lambda (d2: C).(let TMP_175 \def (Bind Abbr) in (let TMP_176 
\def (CHead d2 TMP_175 u0) in (drop n0 O c3 TMP_176)))) in (let TMP_178 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_184 \def (\lambda (d2: C).(let 
TMP_179 \def (S n0) in (let TMP_180 \def (Bind Abbr) in (let TMP_181 \def 
(CHead c3 TMP_180 u) in (let TMP_182 \def (Bind Abbr) in (let TMP_183 \def 
(CHead d2 TMP_182 u0) in (drop TMP_179 O TMP_181 TMP_183))))))) in (let 
TMP_185 \def (ex2 C TMP_178 TMP_184) in (let TMP_197 \def (\lambda (x: 
C).(\lambda (H6: (csubt g d1 x)).(\lambda (H7: (drop n0 O c3 (CHead x (Bind 
Abbr) u0))).(let TMP_186 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_192 \def (\lambda (d2: C).(let TMP_187 \def (S n0) in (let TMP_188 \def 
(Bind Abbr) in (let TMP_189 \def (CHead c3 TMP_188 u) in (let TMP_190 \def 
(Bind Abbr) in (let TMP_191 \def (CHead d2 TMP_190 u0) in (drop TMP_187 O 
TMP_189 TMP_191))))))) in (let TMP_193 \def (Bind Abbr) in (let TMP_194 \def 
(Bind Abbr) in (let TMP_195 \def (CHead x TMP_194 u0) in (let TMP_196 \def 
(drop_drop TMP_193 n0 c3 TMP_195 H7 u) in (ex_intro2 C TMP_186 TMP_192 x H6 
TMP_196)))))))))) in (let TMP_198 \def (Bind Abst) in (let TMP_199 \def (Bind 
Abbr) in (let TMP_200 \def (CHead d1 TMP_199 u0) in (let TMP_201 \def 
(drop_gen_drop TMP_198 c0 TMP_200 t n0 H5) in (let TMP_202 \def (H c0 c3 H1 
d1 u0 TMP_201) in (ex2_ind C TMP_174 TMP_177 TMP_185 TMP_197 
TMP_202))))))))))))))))))))))) in (csubt_ind g TMP_45 TMP_74 TMP_143 TMP_173 
TMP_203 c1 c2 H0))))))))))) in (nat_ind TMP_5 TMP_39 TMP_204 n))))).

theorem csubt_drop_abst:
 \forall (g: G).(\forall (n: nat).(\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (t: T).((drop n O c1 (CHead d1 (Bind 
Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop n 
O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))
\def
 \lambda (g: G).(\lambda (n: nat).(let TMP_13 \def (\lambda (n0: 
nat).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall (d1: 
C).(\forall (t: T).((drop n0 O c1 (CHead d1 (Bind Abst) t)) \to (let TMP_1 
\def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_4 \def (\lambda (d2: 
C).(let TMP_2 \def (Bind Abst) in (let TMP_3 \def (CHead d2 TMP_2 t) in (drop 
n0 O c2 TMP_3)))) in (let TMP_5 \def (ex2 C TMP_1 TMP_4) in (let TMP_6 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_9 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_7 \def (Bind Abbr) in (let TMP_8 
\def (CHead d2 TMP_7 u) in (drop n0 O c2 TMP_8))))) in (let TMP_10 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_11 \def (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_12 \def (ex4_2 C T TMP_6 
TMP_9 TMP_10 TMP_11) in (or TMP_5 TMP_12)))))))))))))))) in (let TMP_171 \def 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 c2)).(\lambda (d1: 
C).(\lambda (t: T).(\lambda (H0: (drop O O c1 (CHead d1 (Bind Abst) t))).(let 
TMP_14 \def (\lambda (c: C).(csubt g c c2)) in (let TMP_15 \def (Bind Abst) 
in (let TMP_16 \def (CHead d1 TMP_15 t) in (let TMP_17 \def (Bind Abst) in 
(let TMP_18 \def (CHead d1 TMP_17 t) in (let TMP_19 \def (drop_gen_refl c1 
TMP_18 H0) in (let H1 \def (eq_ind C c1 TMP_14 H TMP_16 TMP_19) in (let H2 
\def (csubt_gen_abst g d1 c2 t H1) in (let TMP_22 \def (\lambda (e2: C).(let 
TMP_20 \def (Bind Abst) in (let TMP_21 \def (CHead e2 TMP_20 t) in (eq C c2 
TMP_21)))) in (let TMP_23 \def (\lambda (e2: C).(csubt g d1 e2)) in (let 
TMP_24 \def (ex2 C TMP_22 TMP_23) in (let TMP_27 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_25 \def (Bind Abbr) in (let TMP_26 \def (CHead 
e2 TMP_25 v2) in (eq C c2 TMP_26))))) in (let TMP_28 \def (\lambda (e2: 
C).(\lambda (_: T).(csubt g d1 e2))) in (let TMP_29 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g d1 v2 t))) in (let TMP_30 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 t))) in (let TMP_31 \def (ex4_2 C T TMP_27 
TMP_28 TMP_29 TMP_30) in (let TMP_32 \def (\lambda (d2: C).(csubt g d1 d2)) 
in (let TMP_35 \def (\lambda (d2: C).(let TMP_33 \def (Bind Abst) in (let 
TMP_34 \def (CHead d2 TMP_33 t) in (drop O O c2 TMP_34)))) in (let TMP_36 
\def (ex2 C TMP_32 TMP_35) in (let TMP_37 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_40 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_38 \def (Bind Abbr) in (let TMP_39 \def (CHead d2 TMP_38 u) in 
(drop O O c2 TMP_39))))) in (let TMP_41 \def (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) in (let TMP_42 \def (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t))) in (let TMP_43 \def (ex4_2 C T TMP_37 TMP_40 TMP_41 TMP_42) in 
(let TMP_44 \def (or TMP_36 TMP_43) in (let TMP_105 \def (\lambda (H3: (ex2 C 
(\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csubt 
g d1 e2)))).(let TMP_47 \def (\lambda (e2: C).(let TMP_45 \def (Bind Abst) in 
(let TMP_46 \def (CHead e2 TMP_45 t) in (eq C c2 TMP_46)))) in (let TMP_48 
\def (\lambda (e2: C).(csubt g d1 e2)) in (let TMP_49 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_52 \def (\lambda (d2: C).(let TMP_50 \def 
(Bind Abst) in (let TMP_51 \def (CHead d2 TMP_50 t) in (drop O O c2 
TMP_51)))) in (let TMP_53 \def (ex2 C TMP_49 TMP_52) in (let TMP_54 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_57 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_55 \def (Bind Abbr) in (let TMP_56 
\def (CHead d2 TMP_55 u) in (drop O O c2 TMP_56))))) in (let TMP_58 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_59 \def (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_60 \def (ex4_2 C T 
TMP_54 TMP_57 TMP_58 TMP_59) in (let TMP_61 \def (or TMP_53 TMP_60) in (let 
TMP_104 \def (\lambda (x: C).(\lambda (H4: (eq C c2 (CHead x (Bind Abst) 
t))).(\lambda (H5: (csubt g d1 x)).(let TMP_62 \def (Bind Abst) in (let 
TMP_63 \def (CHead x TMP_62 t) in (let TMP_76 \def (\lambda (c: C).(let 
TMP_64 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_67 \def (\lambda 
(d2: C).(let TMP_65 \def (Bind Abst) in (let TMP_66 \def (CHead d2 TMP_65 t) 
in (drop O O c TMP_66)))) in (let TMP_68 \def (ex2 C TMP_64 TMP_67) in (let 
TMP_69 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_72 
\def (\lambda (d2: C).(\lambda (u: T).(let TMP_70 \def (Bind Abbr) in (let 
TMP_71 \def (CHead d2 TMP_70 u) in (drop O O c TMP_71))))) in (let TMP_73 
\def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_74 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_75 \def (ex4_2 
C T TMP_69 TMP_72 TMP_73 TMP_74) in (or TMP_68 TMP_75)))))))))) in (let 
TMP_77 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_82 \def (\lambda 
(d2: C).(let TMP_78 \def (Bind Abst) in (let TMP_79 \def (CHead x TMP_78 t) 
in (let TMP_80 \def (Bind Abst) in (let TMP_81 \def (CHead d2 TMP_80 t) in 
(drop O O TMP_79 TMP_81)))))) in (let TMP_83 \def (ex2 C TMP_77 TMP_82) in 
(let TMP_84 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_89 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_85 \def (Bind Abst) in 
(let TMP_86 \def (CHead x TMP_85 t) in (let TMP_87 \def (Bind Abbr) in (let 
TMP_88 \def (CHead d2 TMP_87 u) in (drop O O TMP_86 TMP_88))))))) in (let 
TMP_90 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_91 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_92 \def 
(ex4_2 C T TMP_84 TMP_89 TMP_90 TMP_91) in (let TMP_93 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_98 \def (\lambda (d2: C).(let TMP_94 \def 
(Bind Abst) in (let TMP_95 \def (CHead x TMP_94 t) in (let TMP_96 \def (Bind 
Abst) in (let TMP_97 \def (CHead d2 TMP_96 t) in (drop O O TMP_95 
TMP_97)))))) in (let TMP_99 \def (Bind Abst) in (let TMP_100 \def (CHead x 
TMP_99 t) in (let TMP_101 \def (drop_refl TMP_100) in (let TMP_102 \def 
(ex_intro2 C TMP_93 TMP_98 x H5 TMP_101) in (let TMP_103 \def (or_introl 
TMP_83 TMP_92 TMP_102) in (eq_ind_r C TMP_63 TMP_76 TMP_103 c2 
H4)))))))))))))))))))))) in (ex2_ind C TMP_47 TMP_48 TMP_61 TMP_104 
H3)))))))))))))) in (let TMP_170 \def (\lambda (H3: (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g d1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
d1 v2 t))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))))).(let TMP_108 
\def (\lambda (e2: C).(\lambda (v2: T).(let TMP_106 \def (Bind Abbr) in (let 
TMP_107 \def (CHead e2 TMP_106 v2) in (eq C c2 TMP_107))))) in (let TMP_109 
\def (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) in (let TMP_110 \def 
(\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) in (let TMP_111 \def 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))) in (let TMP_112 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_115 \def (\lambda (d2: C).(let 
TMP_113 \def (Bind Abst) in (let TMP_114 \def (CHead d2 TMP_113 t) in (drop O 
O c2 TMP_114)))) in (let TMP_116 \def (ex2 C TMP_112 TMP_115) in (let TMP_117 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_120 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_118 \def (Bind Abbr) in (let 
TMP_119 \def (CHead d2 TMP_118 u) in (drop O O c2 TMP_119))))) in (let 
TMP_121 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_122 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_123 \def 
(ex4_2 C T TMP_117 TMP_120 TMP_121 TMP_122) in (let TMP_124 \def (or TMP_116 
TMP_123) in (let TMP_169 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H4: 
(eq C c2 (CHead x0 (Bind Abbr) x1))).(\lambda (H5: (csubt g d1 x0)).(\lambda 
(H6: (ty3 g d1 x1 t)).(\lambda (H7: (ty3 g x0 x1 t)).(let TMP_125 \def (Bind 
Abbr) in (let TMP_126 \def (CHead x0 TMP_125 x1) in (let TMP_139 \def 
(\lambda (c: C).(let TMP_127 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_130 \def (\lambda (d2: C).(let TMP_128 \def (Bind Abst) in (let TMP_129 
\def (CHead d2 TMP_128 t) in (drop O O c TMP_129)))) in (let TMP_131 \def 
(ex2 C TMP_127 TMP_130) in (let TMP_132 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_135 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_133 \def (Bind Abbr) in (let TMP_134 \def (CHead d2 TMP_133 u) in 
(drop O O c TMP_134))))) in (let TMP_136 \def (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) in (let TMP_137 \def (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))) in (let TMP_138 \def (ex4_2 C T TMP_132 TMP_135 TMP_136 
TMP_137) in (or TMP_131 TMP_138)))))))))) in (let TMP_140 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_145 \def (\lambda (d2: C).(let TMP_141 \def 
(Bind Abbr) in (let TMP_142 \def (CHead x0 TMP_141 x1) in (let TMP_143 \def 
(Bind Abst) in (let TMP_144 \def (CHead d2 TMP_143 t) in (drop O O TMP_142 
TMP_144)))))) in (let TMP_146 \def (ex2 C TMP_140 TMP_145) in (let TMP_147 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_152 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_148 \def (Bind Abbr) in (let 
TMP_149 \def (CHead x0 TMP_148 x1) in (let TMP_150 \def (Bind Abbr) in (let 
TMP_151 \def (CHead d2 TMP_150 u) in (drop O O TMP_149 TMP_151))))))) in (let 
TMP_153 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_154 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_155 \def 
(ex4_2 C T TMP_147 TMP_152 TMP_153 TMP_154) in (let TMP_156 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_161 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_157 \def (Bind Abbr) in (let TMP_158 \def (CHead 
x0 TMP_157 x1) in (let TMP_159 \def (Bind Abbr) in (let TMP_160 \def (CHead 
d2 TMP_159 u) in (drop O O TMP_158 TMP_160))))))) in (let TMP_162 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_163 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_164 \def (Bind 
Abbr) in (let TMP_165 \def (CHead x0 TMP_164 x1) in (let TMP_166 \def 
(drop_refl TMP_165) in (let TMP_167 \def (ex4_2_intro C T TMP_156 TMP_161 
TMP_162 TMP_163 x0 x1 H5 TMP_166 H6 H7) in (let TMP_168 \def (or_intror 
TMP_146 TMP_155 TMP_167) in (eq_ind_r C TMP_126 TMP_139 TMP_168 c2 
H4))))))))))))))))))))))))))) in (ex4_2_ind C T TMP_108 TMP_109 TMP_110 
TMP_111 TMP_124 TMP_169 H3)))))))))))))))) in (or_ind TMP_24 TMP_31 TMP_44 
TMP_105 TMP_170 H2)))))))))))))))))))))))))))))))))) in (let TMP_862 \def 
(\lambda (n0: nat).(\lambda (H: ((\forall (c1: C).(\forall (c2: C).((csubt g 
c1 c2) \to (\forall (d1: C).(\forall (t: T).((drop n0 O c1 (CHead d1 (Bind 
Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n0 O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 
u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))).(\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H0: (csubt g c1 c2)).(let TMP_186 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (d1: C).(\forall (t: T).((drop (S 
n0) O c (CHead d1 (Bind Abst) t)) \to (let TMP_172 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_176 \def (\lambda (d2: C).(let TMP_173 \def 
(S n0) in (let TMP_174 \def (Bind Abst) in (let TMP_175 \def (CHead d2 
TMP_174 t) in (drop TMP_173 O c0 TMP_175))))) in (let TMP_177 \def (ex2 C 
TMP_172 TMP_176) in (let TMP_178 \def (\lambda (d2: C).(\lambda (_: T).(csubt 
g d1 d2))) in (let TMP_182 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_179 
\def (S n0) in (let TMP_180 \def (Bind Abbr) in (let TMP_181 \def (CHead d2 
TMP_180 u) in (drop TMP_179 O c0 TMP_181)))))) in (let TMP_183 \def (\lambda 
(_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_184 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_185 \def (ex4_2 C T TMP_178 
TMP_182 TMP_183 TMP_184) in (or TMP_177 TMP_185)))))))))))))) in (let TMP_235 
\def (\lambda (n1: nat).(\lambda (d1: C).(\lambda (t: T).(\lambda (H1: (drop 
(S n0) O (CSort n1) (CHead d1 (Bind Abst) t))).(let TMP_187 \def (Bind Abst) 
in (let TMP_188 \def (CHead d1 TMP_187 t) in (let TMP_189 \def (CSort n1) in 
(let TMP_190 \def (eq C TMP_188 TMP_189) in (let TMP_191 \def (S n0) in (let 
TMP_192 \def (eq nat TMP_191 O) in (let TMP_193 \def (eq nat O O) in (let 
TMP_194 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_199 \def (\lambda 
(d2: C).(let TMP_195 \def (S n0) in (let TMP_196 \def (CSort n1) in (let 
TMP_197 \def (Bind Abst) in (let TMP_198 \def (CHead d2 TMP_197 t) in (drop 
TMP_195 O TMP_196 TMP_198)))))) in (let TMP_200 \def (ex2 C TMP_194 TMP_199) 
in (let TMP_201 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in 
(let TMP_206 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_202 \def (S n0) 
in (let TMP_203 \def (CSort n1) in (let TMP_204 \def (Bind Abbr) in (let 
TMP_205 \def (CHead d2 TMP_204 u) in (drop TMP_202 O TMP_203 TMP_205))))))) 
in (let TMP_207 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let 
TMP_208 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let 
TMP_209 \def (ex4_2 C T TMP_201 TMP_206 TMP_207 TMP_208) in (let TMP_210 \def 
(or TMP_200 TMP_209) in (let TMP_230 \def (\lambda (_: (eq C (CHead d1 (Bind 
Abst) t) (CSort n1))).(\lambda (H3: (eq nat (S n0) O)).(\lambda (_: (eq nat O 
O)).(let TMP_211 \def (S n0) in (let TMP_212 \def (\lambda (ee: nat).(match 
ee with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H5 \def 
(eq_ind nat TMP_211 TMP_212 I O H3) in (let TMP_213 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_218 \def (\lambda (d2: C).(let TMP_214 \def 
(S n0) in (let TMP_215 \def (CSort n1) in (let TMP_216 \def (Bind Abst) in 
(let TMP_217 \def (CHead d2 TMP_216 t) in (drop TMP_214 O TMP_215 
TMP_217)))))) in (let TMP_219 \def (ex2 C TMP_213 TMP_218) in (let TMP_220 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_225 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_221 \def (S n0) in (let TMP_222 
\def (CSort n1) in (let TMP_223 \def (Bind Abbr) in (let TMP_224 \def (CHead 
d2 TMP_223 u) in (drop TMP_221 O TMP_222 TMP_224))))))) in (let TMP_226 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_227 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_228 \def (ex4_2 
C T TMP_220 TMP_225 TMP_226 TMP_227) in (let TMP_229 \def (or TMP_219 
TMP_228) in (False_ind TMP_229 H5)))))))))))))))) in (let TMP_231 \def (S n0) 
in (let TMP_232 \def (Bind Abst) in (let TMP_233 \def (CHead d1 TMP_232 t) in 
(let TMP_234 \def (drop_gen_sort n1 TMP_231 O TMP_233 H1) in (and3_ind 
TMP_190 TMP_192 TMP_193 TMP_210 TMP_230 TMP_234)))))))))))))))))))))))))) in 
(let TMP_559 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 
c3)).(\lambda (H2: ((\forall (d1: C).(\forall (t: T).((drop (S n0) O c0 
(CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t)))))))))).(\lambda (k: K).(let TMP_252 \def (\lambda (k0: K).(\forall (u: 
T).(\forall (d1: C).(\forall (t: T).((drop (S n0) O (CHead c0 k0 u) (CHead d1 
(Bind Abst) t)) \to (let TMP_236 \def (\lambda (d2: C).(csubt g d1 d2)) in 
(let TMP_241 \def (\lambda (d2: C).(let TMP_237 \def (S n0) in (let TMP_238 
\def (CHead c3 k0 u) in (let TMP_239 \def (Bind Abst) in (let TMP_240 \def 
(CHead d2 TMP_239 t) in (drop TMP_237 O TMP_238 TMP_240)))))) in (let TMP_242 
\def (ex2 C TMP_236 TMP_241) in (let TMP_243 \def (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) in (let TMP_248 \def (\lambda (d2: C).(\lambda (u0: 
T).(let TMP_244 \def (S n0) in (let TMP_245 \def (CHead c3 k0 u) in (let 
TMP_246 \def (Bind Abbr) in (let TMP_247 \def (CHead d2 TMP_246 u0) in (drop 
TMP_244 O TMP_245 TMP_247))))))) in (let TMP_249 \def (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_250 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_251 \def (ex4_2 C T TMP_243 
TMP_248 TMP_249 TMP_250) in (or TMP_242 TMP_251)))))))))))))) in (let TMP_403 
\def (\lambda (b: B).(\lambda (u: T).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H3: (drop (S n0) O (CHead c0 (Bind b) u) (CHead d1 (Bind Abst) 
t))).(let TMP_253 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_256 \def 
(\lambda (d2: C).(let TMP_254 \def (Bind Abst) in (let TMP_255 \def (CHead d2 
TMP_254 t) in (drop n0 O c3 TMP_255)))) in (let TMP_257 \def (ex2 C TMP_253 
TMP_256) in (let TMP_258 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) in (let TMP_261 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_259 
\def (Bind Abbr) in (let TMP_260 \def (CHead d2 TMP_259 u0) in (drop n0 O c3 
TMP_260))))) in (let TMP_262 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 
u0 t))) in (let TMP_263 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t))) in (let TMP_264 \def (ex4_2 C T TMP_258 TMP_261 TMP_262 TMP_263) in (let 
TMP_265 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_271 \def (\lambda 
(d2: C).(let TMP_266 \def (S n0) in (let TMP_267 \def (Bind b) in (let 
TMP_268 \def (CHead c3 TMP_267 u) in (let TMP_269 \def (Bind Abst) in (let 
TMP_270 \def (CHead d2 TMP_269 t) in (drop TMP_266 O TMP_268 TMP_270))))))) 
in (let TMP_272 \def (ex2 C TMP_265 TMP_271) in (let TMP_273 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_279 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_274 \def (S n0) in (let TMP_275 \def (Bind b) in 
(let TMP_276 \def (CHead c3 TMP_275 u) in (let TMP_277 \def (Bind Abbr) in 
(let TMP_278 \def (CHead d2 TMP_277 u0) in (drop TMP_274 O TMP_276 
TMP_278)))))))) in (let TMP_280 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) in (let TMP_281 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t))) in (let TMP_282 \def (ex4_2 C T TMP_273 TMP_279 TMP_280 TMP_281) in 
(let TMP_283 \def (or TMP_272 TMP_282) in (let TMP_338 \def (\lambda (H4: 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 
(CHead d2 (Bind Abst) t))))).(let TMP_284 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_287 \def (\lambda (d2: C).(let TMP_285 \def (Bind Abst) in 
(let TMP_286 \def (CHead d2 TMP_285 t) in (drop n0 O c3 TMP_286)))) in (let 
TMP_288 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_294 \def (\lambda 
(d2: C).(let TMP_289 \def (S n0) in (let TMP_290 \def (Bind b) in (let 
TMP_291 \def (CHead c3 TMP_290 u) in (let TMP_292 \def (Bind Abst) in (let 
TMP_293 \def (CHead d2 TMP_292 t) in (drop TMP_289 O TMP_291 TMP_293))))))) 
in (let TMP_295 \def (ex2 C TMP_288 TMP_294) in (let TMP_296 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_302 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_297 \def (S n0) in (let TMP_298 \def (Bind b) in 
(let TMP_299 \def (CHead c3 TMP_298 u) in (let TMP_300 \def (Bind Abbr) in 
(let TMP_301 \def (CHead d2 TMP_300 u0) in (drop TMP_297 O TMP_299 
TMP_301)))))))) in (let TMP_303 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) in (let TMP_304 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t))) in (let TMP_305 \def (ex4_2 C T TMP_296 TMP_302 TMP_303 TMP_304) in 
(let TMP_306 \def (or TMP_295 TMP_305) in (let TMP_337 \def (\lambda (x: 
C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: (drop n0 O c3 (CHead x (Bind 
Abst) t))).(let TMP_307 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_313 \def (\lambda (d2: C).(let TMP_308 \def (S n0) in (let TMP_309 \def 
(Bind b) in (let TMP_310 \def (CHead c3 TMP_309 u) in (let TMP_311 \def (Bind 
Abst) in (let TMP_312 \def (CHead d2 TMP_311 t) in (drop TMP_308 O TMP_310 
TMP_312))))))) in (let TMP_314 \def (ex2 C TMP_307 TMP_313) in (let TMP_315 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_321 \def 
(\lambda (d2: C).(\lambda (u0: T).(let TMP_316 \def (S n0) in (let TMP_317 
\def (Bind b) in (let TMP_318 \def (CHead c3 TMP_317 u) in (let TMP_319 \def 
(Bind Abbr) in (let TMP_320 \def (CHead d2 TMP_319 u0) in (drop TMP_316 O 
TMP_318 TMP_320)))))))) in (let TMP_322 \def (\lambda (_: C).(\lambda (u0: 
T).(ty3 g d1 u0 t))) in (let TMP_323 \def (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))) in (let TMP_324 \def (ex4_2 C T TMP_315 TMP_321 TMP_322 
TMP_323) in (let TMP_325 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_331 \def (\lambda (d2: C).(let TMP_326 \def (S n0) in (let TMP_327 \def 
(Bind b) in (let TMP_328 \def (CHead c3 TMP_327 u) in (let TMP_329 \def (Bind 
Abst) in (let TMP_330 \def (CHead d2 TMP_329 t) in (drop TMP_326 O TMP_328 
TMP_330))))))) in (let TMP_332 \def (Bind b) in (let TMP_333 \def (Bind Abst) 
in (let TMP_334 \def (CHead x TMP_333 t) in (let TMP_335 \def (drop_drop 
TMP_332 n0 c3 TMP_334 H6 u) in (let TMP_336 \def (ex_intro2 C TMP_325 TMP_331 
x H5 TMP_335) in (or_introl TMP_314 TMP_324 TMP_336))))))))))))))))))) in 
(ex2_ind C TMP_284 TMP_287 TMP_306 TMP_337 H4)))))))))))))) in (let TMP_397 
\def (\lambda (H4: (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u0: T).(drop n0 O c3 (CHead d2 (Bind Abbr) 
u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))))).(let TMP_339 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_342 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_340 \def (Bind Abbr) in (let TMP_341 \def (CHead 
d2 TMP_340 u0) in (drop n0 O c3 TMP_341))))) in (let TMP_343 \def (\lambda 
(_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_344 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_345 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_351 \def (\lambda (d2: C).(let TMP_346 \def 
(S n0) in (let TMP_347 \def (Bind b) in (let TMP_348 \def (CHead c3 TMP_347 
u) in (let TMP_349 \def (Bind Abst) in (let TMP_350 \def (CHead d2 TMP_349 t) 
in (drop TMP_346 O TMP_348 TMP_350))))))) in (let TMP_352 \def (ex2 C TMP_345 
TMP_351) in (let TMP_353 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) in (let TMP_359 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_354 
\def (S n0) in (let TMP_355 \def (Bind b) in (let TMP_356 \def (CHead c3 
TMP_355 u) in (let TMP_357 \def (Bind Abbr) in (let TMP_358 \def (CHead d2 
TMP_357 u0) in (drop TMP_354 O TMP_356 TMP_358)))))))) in (let TMP_360 \def 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_361 \def 
(\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_362 \def 
(ex4_2 C T TMP_353 TMP_359 TMP_360 TMP_361) in (let TMP_363 \def (or TMP_352 
TMP_362) in (let TMP_396 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: 
(csubt g d1 x0)).(\lambda (H6: (drop n0 O c3 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H7: (ty3 g d1 x1 t)).(\lambda (H8: (ty3 g x0 x1 t)).(let 
TMP_364 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_370 \def (\lambda 
(d2: C).(let TMP_365 \def (S n0) in (let TMP_366 \def (Bind b) in (let 
TMP_367 \def (CHead c3 TMP_366 u) in (let TMP_368 \def (Bind Abst) in (let 
TMP_369 \def (CHead d2 TMP_368 t) in (drop TMP_365 O TMP_367 TMP_369))))))) 
in (let TMP_371 \def (ex2 C TMP_364 TMP_370) in (let TMP_372 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_378 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_373 \def (S n0) in (let TMP_374 \def (Bind b) in 
(let TMP_375 \def (CHead c3 TMP_374 u) in (let TMP_376 \def (Bind Abbr) in 
(let TMP_377 \def (CHead d2 TMP_376 u0) in (drop TMP_373 O TMP_375 
TMP_377)))))))) in (let TMP_379 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) in (let TMP_380 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t))) in (let TMP_381 \def (ex4_2 C T TMP_372 TMP_378 TMP_379 TMP_380) in 
(let TMP_382 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_388 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_383 \def (S n0) in 
(let TMP_384 \def (Bind b) in (let TMP_385 \def (CHead c3 TMP_384 u) in (let 
TMP_386 \def (Bind Abbr) in (let TMP_387 \def (CHead d2 TMP_386 u0) in (drop 
TMP_383 O TMP_385 TMP_387)))))))) in (let TMP_389 \def (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_390 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_391 \def (Bind b) in (let 
TMP_392 \def (Bind Abbr) in (let TMP_393 \def (CHead x0 TMP_392 x1) in (let 
TMP_394 \def (drop_drop TMP_391 n0 c3 TMP_393 H6 u) in (let TMP_395 \def 
(ex4_2_intro C T TMP_382 TMP_388 TMP_389 TMP_390 x0 x1 H5 TMP_394 H7 H8) in 
(or_intror TMP_371 TMP_381 TMP_395)))))))))))))))))))))))) in (ex4_2_ind C T 
TMP_339 TMP_342 TMP_343 TMP_344 TMP_363 TMP_396 H4)))))))))))))))) in (let 
TMP_398 \def (Bind b) in (let TMP_399 \def (Bind Abst) in (let TMP_400 \def 
(CHead d1 TMP_399 t) in (let TMP_401 \def (drop_gen_drop TMP_398 c0 TMP_400 u 
n0 H3) in (let TMP_402 \def (H c0 c3 H1 d1 t TMP_401) in (or_ind TMP_257 
TMP_264 TMP_283 TMP_338 TMP_397 TMP_402)))))))))))))))))))))))))))))) in (let 
TMP_558 \def (\lambda (f: F).(\lambda (u: T).(\lambda (d1: C).(\lambda (t: 
T).(\lambda (H3: (drop (S n0) O (CHead c0 (Flat f) u) (CHead d1 (Bind Abst) 
t))).(let TMP_404 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_408 \def 
(\lambda (d2: C).(let TMP_405 \def (S n0) in (let TMP_406 \def (Bind Abst) in 
(let TMP_407 \def (CHead d2 TMP_406 t) in (drop TMP_405 O c3 TMP_407))))) in 
(let TMP_409 \def (ex2 C TMP_404 TMP_408) in (let TMP_410 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_414 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_411 \def (S n0) in (let TMP_412 \def (Bind Abbr) 
in (let TMP_413 \def (CHead d2 TMP_412 u0) in (drop TMP_411 O c3 
TMP_413)))))) in (let TMP_415 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 
u0 t))) in (let TMP_416 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 
t))) in (let TMP_417 \def (ex4_2 C T TMP_410 TMP_414 TMP_415 TMP_416) in (let 
TMP_418 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_424 \def (\lambda 
(d2: C).(let TMP_419 \def (S n0) in (let TMP_420 \def (Flat f) in (let 
TMP_421 \def (CHead c3 TMP_420 u) in (let TMP_422 \def (Bind Abst) in (let 
TMP_423 \def (CHead d2 TMP_422 t) in (drop TMP_419 O TMP_421 TMP_423))))))) 
in (let TMP_425 \def (ex2 C TMP_418 TMP_424) in (let TMP_426 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_432 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_427 \def (S n0) in (let TMP_428 \def (Flat f) in 
(let TMP_429 \def (CHead c3 TMP_428 u) in (let TMP_430 \def (Bind Abbr) in 
(let TMP_431 \def (CHead d2 TMP_430 u0) in (drop TMP_427 O TMP_429 
TMP_431)))))))) in (let TMP_433 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) in (let TMP_434 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t))) in (let TMP_435 \def (ex4_2 C T TMP_426 TMP_432 TMP_433 TMP_434) in 
(let TMP_436 \def (or TMP_425 TMP_435) in (let TMP_492 \def (\lambda (H4: 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 
(CHead d2 (Bind Abst) t))))).(let TMP_437 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_441 \def (\lambda (d2: C).(let TMP_438 \def (S n0) in (let 
TMP_439 \def (Bind Abst) in (let TMP_440 \def (CHead d2 TMP_439 t) in (drop 
TMP_438 O c3 TMP_440))))) in (let TMP_442 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_448 \def (\lambda (d2: C).(let TMP_443 \def (S n0) in (let 
TMP_444 \def (Flat f) in (let TMP_445 \def (CHead c3 TMP_444 u) in (let 
TMP_446 \def (Bind Abst) in (let TMP_447 \def (CHead d2 TMP_446 t) in (drop 
TMP_443 O TMP_445 TMP_447))))))) in (let TMP_449 \def (ex2 C TMP_442 TMP_448) 
in (let TMP_450 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in 
(let TMP_456 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_451 \def (S n0) 
in (let TMP_452 \def (Flat f) in (let TMP_453 \def (CHead c3 TMP_452 u) in 
(let TMP_454 \def (Bind Abbr) in (let TMP_455 \def (CHead d2 TMP_454 u0) in 
(drop TMP_451 O TMP_453 TMP_455)))))))) in (let TMP_457 \def (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_458 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_459 \def (ex4_2 C T TMP_450 
TMP_456 TMP_457 TMP_458) in (let TMP_460 \def (or TMP_449 TMP_459) in (let 
TMP_491 \def (\lambda (x: C).(\lambda (H5: (csubt g d1 x)).(\lambda (H6: 
(drop (S n0) O c3 (CHead x (Bind Abst) t))).(let TMP_461 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_467 \def (\lambda (d2: C).(let TMP_462 \def 
(S n0) in (let TMP_463 \def (Flat f) in (let TMP_464 \def (CHead c3 TMP_463 
u) in (let TMP_465 \def (Bind Abst) in (let TMP_466 \def (CHead d2 TMP_465 t) 
in (drop TMP_462 O TMP_464 TMP_466))))))) in (let TMP_468 \def (ex2 C TMP_461 
TMP_467) in (let TMP_469 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) in (let TMP_475 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_470 
\def (S n0) in (let TMP_471 \def (Flat f) in (let TMP_472 \def (CHead c3 
TMP_471 u) in (let TMP_473 \def (Bind Abbr) in (let TMP_474 \def (CHead d2 
TMP_473 u0) in (drop TMP_470 O TMP_472 TMP_474)))))))) in (let TMP_476 \def 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_477 \def 
(\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_478 \def 
(ex4_2 C T TMP_469 TMP_475 TMP_476 TMP_477) in (let TMP_479 \def (\lambda 
(d2: C).(csubt g d1 d2)) in (let TMP_485 \def (\lambda (d2: C).(let TMP_480 
\def (S n0) in (let TMP_481 \def (Flat f) in (let TMP_482 \def (CHead c3 
TMP_481 u) in (let TMP_483 \def (Bind Abst) in (let TMP_484 \def (CHead d2 
TMP_483 t) in (drop TMP_480 O TMP_482 TMP_484))))))) in (let TMP_486 \def 
(Flat f) in (let TMP_487 \def (Bind Abst) in (let TMP_488 \def (CHead x 
TMP_487 t) in (let TMP_489 \def (drop_drop TMP_486 n0 c3 TMP_488 H6 u) in 
(let TMP_490 \def (ex_intro2 C TMP_479 TMP_485 x H5 TMP_489) in (or_introl 
TMP_468 TMP_478 TMP_490))))))))))))))))))) in (ex2_ind C TMP_437 TMP_441 
TMP_460 TMP_491 H4)))))))))))))) in (let TMP_552 \def (\lambda (H4: (ex4_2 C 
T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u0: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda 
(_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))))).(let TMP_493 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_497 \def (\lambda (d2: C).(\lambda (u0: 
T).(let TMP_494 \def (S n0) in (let TMP_495 \def (Bind Abbr) in (let TMP_496 
\def (CHead d2 TMP_495 u0) in (drop TMP_494 O c3 TMP_496)))))) in (let 
TMP_498 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let 
TMP_499 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let 
TMP_500 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_506 \def (\lambda 
(d2: C).(let TMP_501 \def (S n0) in (let TMP_502 \def (Flat f) in (let 
TMP_503 \def (CHead c3 TMP_502 u) in (let TMP_504 \def (Bind Abst) in (let 
TMP_505 \def (CHead d2 TMP_504 t) in (drop TMP_501 O TMP_503 TMP_505))))))) 
in (let TMP_507 \def (ex2 C TMP_500 TMP_506) in (let TMP_508 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_514 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_509 \def (S n0) in (let TMP_510 \def (Flat f) in 
(let TMP_511 \def (CHead c3 TMP_510 u) in (let TMP_512 \def (Bind Abbr) in 
(let TMP_513 \def (CHead d2 TMP_512 u0) in (drop TMP_509 O TMP_511 
TMP_513)))))))) in (let TMP_515 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t))) in (let TMP_516 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t))) in (let TMP_517 \def (ex4_2 C T TMP_508 TMP_514 TMP_515 TMP_516) in 
(let TMP_518 \def (or TMP_507 TMP_517) in (let TMP_551 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H5: (csubt g d1 x0)).(\lambda (H6: (drop (S n0) 
O c3 (CHead x0 (Bind Abbr) x1))).(\lambda (H7: (ty3 g d1 x1 t)).(\lambda (H8: 
(ty3 g x0 x1 t)).(let TMP_519 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_525 \def (\lambda (d2: C).(let TMP_520 \def (S n0) in (let TMP_521 \def 
(Flat f) in (let TMP_522 \def (CHead c3 TMP_521 u) in (let TMP_523 \def (Bind 
Abst) in (let TMP_524 \def (CHead d2 TMP_523 t) in (drop TMP_520 O TMP_522 
TMP_524))))))) in (let TMP_526 \def (ex2 C TMP_519 TMP_525) in (let TMP_527 
\def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_533 \def 
(\lambda (d2: C).(\lambda (u0: T).(let TMP_528 \def (S n0) in (let TMP_529 
\def (Flat f) in (let TMP_530 \def (CHead c3 TMP_529 u) in (let TMP_531 \def 
(Bind Abbr) in (let TMP_532 \def (CHead d2 TMP_531 u0) in (drop TMP_528 O 
TMP_530 TMP_532)))))))) in (let TMP_534 \def (\lambda (_: C).(\lambda (u0: 
T).(ty3 g d1 u0 t))) in (let TMP_535 \def (\lambda (d2: C).(\lambda (u0: 
T).(ty3 g d2 u0 t))) in (let TMP_536 \def (ex4_2 C T TMP_527 TMP_533 TMP_534 
TMP_535) in (let TMP_537 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) in (let TMP_543 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_538 
\def (S n0) in (let TMP_539 \def (Flat f) in (let TMP_540 \def (CHead c3 
TMP_539 u) in (let TMP_541 \def (Bind Abbr) in (let TMP_542 \def (CHead d2 
TMP_541 u0) in (drop TMP_538 O TMP_540 TMP_542)))))))) in (let TMP_544 \def 
(\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t))) in (let TMP_545 \def 
(\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t))) in (let TMP_546 \def 
(Flat f) in (let TMP_547 \def (Bind Abbr) in (let TMP_548 \def (CHead x0 
TMP_547 x1) in (let TMP_549 \def (drop_drop TMP_546 n0 c3 TMP_548 H6 u) in 
(let TMP_550 \def (ex4_2_intro C T TMP_537 TMP_543 TMP_544 TMP_545 x0 x1 H5 
TMP_549 H7 H8) in (or_intror TMP_526 TMP_536 TMP_550)))))))))))))))))))))))) 
in (ex4_2_ind C T TMP_493 TMP_497 TMP_498 TMP_499 TMP_518 TMP_551 
H4)))))))))))))))) in (let TMP_553 \def (Flat f) in (let TMP_554 \def (Bind 
Abst) in (let TMP_555 \def (CHead d1 TMP_554 t) in (let TMP_556 \def 
(drop_gen_drop TMP_553 c0 TMP_555 u n0 H3) in (let TMP_557 \def (H2 d1 t 
TMP_556) in (or_ind TMP_409 TMP_417 TMP_436 TMP_492 TMP_552 
TMP_557)))))))))))))))))))))))))))))) in (K_ind TMP_252 TMP_403 TMP_558 
k))))))))) in (let TMP_710 \def (\lambda (c0: C).(\lambda (c3: C).(\lambda 
(H1: (csubt g c0 c3)).(\lambda (_: ((\forall (d1: C).(\forall (t: T).((drop 
(S n0) O c0 (CHead d1 (Bind Abst) t)) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(drop (S n0) O c3 (CHead d2 (Bind Abst) t)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop (S n0) O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t)))))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (d1: C).(\lambda (t: T).(\lambda (H4: (drop 
(S n0) O (CHead c0 (Bind Void) u1) (CHead d1 (Bind Abst) t))).(let TMP_560 
\def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_563 \def (\lambda (d2: 
C).(let TMP_561 \def (Bind Abst) in (let TMP_562 \def (CHead d2 TMP_561 t) in 
(drop n0 O c3 TMP_562)))) in (let TMP_564 \def (ex2 C TMP_560 TMP_563) in 
(let TMP_565 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_568 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_566 \def (Bind Abbr) 
in (let TMP_567 \def (CHead d2 TMP_566 u) in (drop n0 O c3 TMP_567))))) in 
(let TMP_569 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let 
TMP_570 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let 
TMP_571 \def (ex4_2 C T TMP_565 TMP_568 TMP_569 TMP_570) in (let TMP_572 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_578 \def (\lambda (d2: C).(let 
TMP_573 \def (S n0) in (let TMP_574 \def (Bind b) in (let TMP_575 \def (CHead 
c3 TMP_574 u2) in (let TMP_576 \def (Bind Abst) in (let TMP_577 \def (CHead 
d2 TMP_576 t) in (drop TMP_573 O TMP_575 TMP_577))))))) in (let TMP_579 \def 
(ex2 C TMP_572 TMP_578) in (let TMP_580 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_586 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_581 \def (S n0) in (let TMP_582 \def (Bind b) in (let TMP_583 
\def (CHead c3 TMP_582 u2) in (let TMP_584 \def (Bind Abbr) in (let TMP_585 
\def (CHead d2 TMP_584 u) in (drop TMP_581 O TMP_583 TMP_585)))))))) in (let 
TMP_587 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_588 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_589 \def 
(ex4_2 C T TMP_580 TMP_586 TMP_587 TMP_588) in (let TMP_590 \def (or TMP_579 
TMP_589) in (let TMP_645 \def (\lambda (H5: (ex2 C (\lambda (d2: C).(csubt g 
d1 d2)) (\lambda (d2: C).(drop n0 O c3 (CHead d2 (Bind Abst) t))))).(let 
TMP_591 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_594 \def (\lambda 
(d2: C).(let TMP_592 \def (Bind Abst) in (let TMP_593 \def (CHead d2 TMP_592 
t) in (drop n0 O c3 TMP_593)))) in (let TMP_595 \def (\lambda (d2: C).(csubt 
g d1 d2)) in (let TMP_601 \def (\lambda (d2: C).(let TMP_596 \def (S n0) in 
(let TMP_597 \def (Bind b) in (let TMP_598 \def (CHead c3 TMP_597 u2) in (let 
TMP_599 \def (Bind Abst) in (let TMP_600 \def (CHead d2 TMP_599 t) in (drop 
TMP_596 O TMP_598 TMP_600))))))) in (let TMP_602 \def (ex2 C TMP_595 TMP_601) 
in (let TMP_603 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in 
(let TMP_609 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_604 \def (S n0) 
in (let TMP_605 \def (Bind b) in (let TMP_606 \def (CHead c3 TMP_605 u2) in 
(let TMP_607 \def (Bind Abbr) in (let TMP_608 \def (CHead d2 TMP_607 u) in 
(drop TMP_604 O TMP_606 TMP_608)))))))) in (let TMP_610 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_611 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_612 \def (ex4_2 C T TMP_603 
TMP_609 TMP_610 TMP_611) in (let TMP_613 \def (or TMP_602 TMP_612) in (let 
TMP_644 \def (\lambda (x: C).(\lambda (H6: (csubt g d1 x)).(\lambda (H7: 
(drop n0 O c3 (CHead x (Bind Abst) t))).(let TMP_614 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_620 \def (\lambda (d2: C).(let TMP_615 \def 
(S n0) in (let TMP_616 \def (Bind b) in (let TMP_617 \def (CHead c3 TMP_616 
u2) in (let TMP_618 \def (Bind Abst) in (let TMP_619 \def (CHead d2 TMP_618 
t) in (drop TMP_615 O TMP_617 TMP_619))))))) in (let TMP_621 \def (ex2 C 
TMP_614 TMP_620) in (let TMP_622 \def (\lambda (d2: C).(\lambda (_: T).(csubt 
g d1 d2))) in (let TMP_628 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_623 
\def (S n0) in (let TMP_624 \def (Bind b) in (let TMP_625 \def (CHead c3 
TMP_624 u2) in (let TMP_626 \def (Bind Abbr) in (let TMP_627 \def (CHead d2 
TMP_626 u) in (drop TMP_623 O TMP_625 TMP_627)))))))) in (let TMP_629 \def 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_630 \def 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_631 \def (ex4_2 
C T TMP_622 TMP_628 TMP_629 TMP_630) in (let TMP_632 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_638 \def (\lambda (d2: C).(let TMP_633 \def 
(S n0) in (let TMP_634 \def (Bind b) in (let TMP_635 \def (CHead c3 TMP_634 
u2) in (let TMP_636 \def (Bind Abst) in (let TMP_637 \def (CHead d2 TMP_636 
t) in (drop TMP_633 O TMP_635 TMP_637))))))) in (let TMP_639 \def (Bind b) in 
(let TMP_640 \def (Bind Abst) in (let TMP_641 \def (CHead x TMP_640 t) in 
(let TMP_642 \def (drop_drop TMP_639 n0 c3 TMP_641 H7 u2) in (let TMP_643 
\def (ex_intro2 C TMP_632 TMP_638 x H6 TMP_642) in (or_introl TMP_621 TMP_631 
TMP_643))))))))))))))))))) in (ex2_ind C TMP_591 TMP_594 TMP_613 TMP_644 
H5)))))))))))))) in (let TMP_704 \def (\lambda (H5: (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 
u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(let TMP_646 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_649 \def 
(\lambda (d2: C).(\lambda (u: T).(let TMP_647 \def (Bind Abbr) in (let 
TMP_648 \def (CHead d2 TMP_647 u) in (drop n0 O c3 TMP_648))))) in (let 
TMP_650 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_651 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_652 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_658 \def (\lambda (d2: C).(let 
TMP_653 \def (S n0) in (let TMP_654 \def (Bind b) in (let TMP_655 \def (CHead 
c3 TMP_654 u2) in (let TMP_656 \def (Bind Abst) in (let TMP_657 \def (CHead 
d2 TMP_656 t) in (drop TMP_653 O TMP_655 TMP_657))))))) in (let TMP_659 \def 
(ex2 C TMP_652 TMP_658) in (let TMP_660 \def (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) in (let TMP_666 \def (\lambda (d2: C).(\lambda (u: 
T).(let TMP_661 \def (S n0) in (let TMP_662 \def (Bind b) in (let TMP_663 
\def (CHead c3 TMP_662 u2) in (let TMP_664 \def (Bind Abbr) in (let TMP_665 
\def (CHead d2 TMP_664 u) in (drop TMP_661 O TMP_663 TMP_665)))))))) in (let 
TMP_667 \def (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_668 
\def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_669 \def 
(ex4_2 C T TMP_660 TMP_666 TMP_667 TMP_668) in (let TMP_670 \def (or TMP_659 
TMP_669) in (let TMP_703 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: 
(csubt g d1 x0)).(\lambda (H7: (drop n0 O c3 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H8: (ty3 g d1 x1 t)).(\lambda (H9: (ty3 g x0 x1 t)).(let 
TMP_671 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_677 \def (\lambda 
(d2: C).(let TMP_672 \def (S n0) in (let TMP_673 \def (Bind b) in (let 
TMP_674 \def (CHead c3 TMP_673 u2) in (let TMP_675 \def (Bind Abst) in (let 
TMP_676 \def (CHead d2 TMP_675 t) in (drop TMP_672 O TMP_674 TMP_676))))))) 
in (let TMP_678 \def (ex2 C TMP_671 TMP_677) in (let TMP_679 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_685 \def (\lambda (d2: 
C).(\lambda (u: T).(let TMP_680 \def (S n0) in (let TMP_681 \def (Bind b) in 
(let TMP_682 \def (CHead c3 TMP_681 u2) in (let TMP_683 \def (Bind Abbr) in 
(let TMP_684 \def (CHead d2 TMP_683 u) in (drop TMP_680 O TMP_682 
TMP_684)))))))) in (let TMP_686 \def (\lambda (_: C).(\lambda (u: T).(ty3 g 
d1 u t))) in (let TMP_687 \def (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))) in (let TMP_688 \def (ex4_2 C T TMP_679 TMP_685 TMP_686 TMP_687) in (let 
TMP_689 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_695 \def (\lambda (d2: C).(\lambda (u: T).(let TMP_690 \def (S n0) in 
(let TMP_691 \def (Bind b) in (let TMP_692 \def (CHead c3 TMP_691 u2) in (let 
TMP_693 \def (Bind Abbr) in (let TMP_694 \def (CHead d2 TMP_693 u) in (drop 
TMP_690 O TMP_692 TMP_694)))))))) in (let TMP_696 \def (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) in (let TMP_697 \def (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))) in (let TMP_698 \def (Bind b) in (let 
TMP_699 \def (Bind Abbr) in (let TMP_700 \def (CHead x0 TMP_699 x1) in (let 
TMP_701 \def (drop_drop TMP_698 n0 c3 TMP_700 H7 u2) in (let TMP_702 \def 
(ex4_2_intro C T TMP_689 TMP_695 TMP_696 TMP_697 x0 x1 H6 TMP_701 H8 H9) in 
(or_intror TMP_678 TMP_688 TMP_702)))))))))))))))))))))))) in (ex4_2_ind C T 
TMP_646 TMP_649 TMP_650 TMP_651 TMP_670 TMP_703 H5)))))))))))))))) in (let 
TMP_705 \def (Bind Void) in (let TMP_706 \def (Bind Abst) in (let TMP_707 
\def (CHead d1 TMP_706 t) in (let TMP_708 \def (drop_gen_drop TMP_705 c0 
TMP_707 u1 n0 H4) in (let TMP_709 \def (H c0 c3 H1 d1 t TMP_708) in (or_ind 
TMP_564 TMP_571 TMP_590 TMP_645 TMP_704 
TMP_709)))))))))))))))))))))))))))))))))))) in (let TMP_861 \def (\lambda 
(c0: C).(\lambda (c3: C).(\lambda (H1: (csubt g c0 c3)).(\lambda (_: 
((\forall (d1: C).(\forall (t: T).((drop (S n0) O c0 (CHead d1 (Bind Abst) 
t)) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop 
(S n0) O c3 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (ty3 g c3 u 
t)).(\lambda (d1: C).(\lambda (t0: T).(\lambda (H5: (drop (S n0) O (CHead c0 
(Bind Abst) t) (CHead d1 (Bind Abst) t0))).(let TMP_711 \def (\lambda (d2: 
C).(csubt g d1 d2)) in (let TMP_714 \def (\lambda (d2: C).(let TMP_712 \def 
(Bind Abst) in (let TMP_713 \def (CHead d2 TMP_712 t0) in (drop n0 O c3 
TMP_713)))) in (let TMP_715 \def (ex2 C TMP_711 TMP_714) in (let TMP_716 \def 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_719 \def 
(\lambda (d2: C).(\lambda (u0: T).(let TMP_717 \def (Bind Abbr) in (let 
TMP_718 \def (CHead d2 TMP_717 u0) in (drop n0 O c3 TMP_718))))) in (let 
TMP_720 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) in (let 
TMP_721 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))) in (let 
TMP_722 \def (ex4_2 C T TMP_716 TMP_719 TMP_720 TMP_721) in (let TMP_723 \def 
(\lambda (d2: C).(csubt g d1 d2)) in (let TMP_729 \def (\lambda (d2: C).(let 
TMP_724 \def (S n0) in (let TMP_725 \def (Bind Abbr) in (let TMP_726 \def 
(CHead c3 TMP_725 u) in (let TMP_727 \def (Bind Abst) in (let TMP_728 \def 
(CHead d2 TMP_727 t0) in (drop TMP_724 O TMP_726 TMP_728))))))) in (let 
TMP_730 \def (ex2 C TMP_723 TMP_729) in (let TMP_731 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_737 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_732 \def (S n0) in (let TMP_733 \def (Bind Abbr) 
in (let TMP_734 \def (CHead c3 TMP_733 u) in (let TMP_735 \def (Bind Abbr) in 
(let TMP_736 \def (CHead d2 TMP_735 u0) in (drop TMP_732 O TMP_734 
TMP_736)))))))) in (let TMP_738 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) in (let TMP_739 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t0))) in (let TMP_740 \def (ex4_2 C T TMP_731 TMP_737 TMP_738 TMP_739) in 
(let TMP_741 \def (or TMP_730 TMP_740) in (let TMP_796 \def (\lambda (H6: 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n0 O c3 
(CHead d2 (Bind Abst) t0))))).(let TMP_742 \def (\lambda (d2: C).(csubt g d1 
d2)) in (let TMP_745 \def (\lambda (d2: C).(let TMP_743 \def (Bind Abst) in 
(let TMP_744 \def (CHead d2 TMP_743 t0) in (drop n0 O c3 TMP_744)))) in (let 
TMP_746 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_752 \def (\lambda 
(d2: C).(let TMP_747 \def (S n0) in (let TMP_748 \def (Bind Abbr) in (let 
TMP_749 \def (CHead c3 TMP_748 u) in (let TMP_750 \def (Bind Abst) in (let 
TMP_751 \def (CHead d2 TMP_750 t0) in (drop TMP_747 O TMP_749 TMP_751))))))) 
in (let TMP_753 \def (ex2 C TMP_746 TMP_752) in (let TMP_754 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_760 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_755 \def (S n0) in (let TMP_756 \def (Bind Abbr) 
in (let TMP_757 \def (CHead c3 TMP_756 u) in (let TMP_758 \def (Bind Abbr) in 
(let TMP_759 \def (CHead d2 TMP_758 u0) in (drop TMP_755 O TMP_757 
TMP_759)))))))) in (let TMP_761 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) in (let TMP_762 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t0))) in (let TMP_763 \def (ex4_2 C T TMP_754 TMP_760 TMP_761 TMP_762) in 
(let TMP_764 \def (or TMP_753 TMP_763) in (let TMP_795 \def (\lambda (x: 
C).(\lambda (H7: (csubt g d1 x)).(\lambda (H8: (drop n0 O c3 (CHead x (Bind 
Abst) t0))).(let TMP_765 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_771 \def (\lambda (d2: C).(let TMP_766 \def (S n0) in (let TMP_767 \def 
(Bind Abbr) in (let TMP_768 \def (CHead c3 TMP_767 u) in (let TMP_769 \def 
(Bind Abst) in (let TMP_770 \def (CHead d2 TMP_769 t0) in (drop TMP_766 O 
TMP_768 TMP_770))))))) in (let TMP_772 \def (ex2 C TMP_765 TMP_771) in (let 
TMP_773 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_779 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_774 \def (S n0) in 
(let TMP_775 \def (Bind Abbr) in (let TMP_776 \def (CHead c3 TMP_775 u) in 
(let TMP_777 \def (Bind Abbr) in (let TMP_778 \def (CHead d2 TMP_777 u0) in 
(drop TMP_774 O TMP_776 TMP_778)))))))) in (let TMP_780 \def (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t0))) in (let TMP_781 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t0))) in (let TMP_782 \def (ex4_2 C T 
TMP_773 TMP_779 TMP_780 TMP_781) in (let TMP_783 \def (\lambda (d2: C).(csubt 
g d1 d2)) in (let TMP_789 \def (\lambda (d2: C).(let TMP_784 \def (S n0) in 
(let TMP_785 \def (Bind Abbr) in (let TMP_786 \def (CHead c3 TMP_785 u) in 
(let TMP_787 \def (Bind Abst) in (let TMP_788 \def (CHead d2 TMP_787 t0) in 
(drop TMP_784 O TMP_786 TMP_788))))))) in (let TMP_790 \def (Bind Abbr) in 
(let TMP_791 \def (Bind Abst) in (let TMP_792 \def (CHead x TMP_791 t0) in 
(let TMP_793 \def (drop_drop TMP_790 n0 c3 TMP_792 H8 u) in (let TMP_794 \def 
(ex_intro2 C TMP_783 TMP_789 x H7 TMP_793) in (or_introl TMP_772 TMP_782 
TMP_794))))))))))))))))))) in (ex2_ind C TMP_742 TMP_745 TMP_764 TMP_795 
H6)))))))))))))) in (let TMP_855 \def (\lambda (H6: (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u0: T).(drop 
n0 O c3 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))))).(let 
TMP_797 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_800 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_798 \def (Bind Abbr) 
in (let TMP_799 \def (CHead d2 TMP_798 u0) in (drop n0 O c3 TMP_799))))) in 
(let TMP_801 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d1 u0 t0))) in (let 
TMP_802 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 t0))) in (let 
TMP_803 \def (\lambda (d2: C).(csubt g d1 d2)) in (let TMP_809 \def (\lambda 
(d2: C).(let TMP_804 \def (S n0) in (let TMP_805 \def (Bind Abbr) in (let 
TMP_806 \def (CHead c3 TMP_805 u) in (let TMP_807 \def (Bind Abst) in (let 
TMP_808 \def (CHead d2 TMP_807 t0) in (drop TMP_804 O TMP_806 TMP_808))))))) 
in (let TMP_810 \def (ex2 C TMP_803 TMP_809) in (let TMP_811 \def (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_817 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_812 \def (S n0) in (let TMP_813 \def (Bind Abbr) 
in (let TMP_814 \def (CHead c3 TMP_813 u) in (let TMP_815 \def (Bind Abbr) in 
(let TMP_816 \def (CHead d2 TMP_815 u0) in (drop TMP_812 O TMP_814 
TMP_816)))))))) in (let TMP_818 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) in (let TMP_819 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t0))) in (let TMP_820 \def (ex4_2 C T TMP_811 TMP_817 TMP_818 TMP_819) in 
(let TMP_821 \def (or TMP_810 TMP_820) in (let TMP_854 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H7: (csubt g d1 x0)).(\lambda (H8: (drop n0 O 
c3 (CHead x0 (Bind Abbr) x1))).(\lambda (H9: (ty3 g d1 x1 t0)).(\lambda (H10: 
(ty3 g x0 x1 t0)).(let TMP_822 \def (\lambda (d2: C).(csubt g d1 d2)) in (let 
TMP_828 \def (\lambda (d2: C).(let TMP_823 \def (S n0) in (let TMP_824 \def 
(Bind Abbr) in (let TMP_825 \def (CHead c3 TMP_824 u) in (let TMP_826 \def 
(Bind Abst) in (let TMP_827 \def (CHead d2 TMP_826 t0) in (drop TMP_823 O 
TMP_825 TMP_827))))))) in (let TMP_829 \def (ex2 C TMP_822 TMP_828) in (let 
TMP_830 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) in (let 
TMP_836 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_831 \def (S n0) in 
(let TMP_832 \def (Bind Abbr) in (let TMP_833 \def (CHead c3 TMP_832 u) in 
(let TMP_834 \def (Bind Abbr) in (let TMP_835 \def (CHead d2 TMP_834 u0) in 
(drop TMP_831 O TMP_833 TMP_835)))))))) in (let TMP_837 \def (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d1 u0 t0))) in (let TMP_838 \def (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 t0))) in (let TMP_839 \def (ex4_2 C T 
TMP_830 TMP_836 TMP_837 TMP_838) in (let TMP_840 \def (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) in (let TMP_846 \def (\lambda (d2: 
C).(\lambda (u0: T).(let TMP_841 \def (S n0) in (let TMP_842 \def (Bind Abbr) 
in (let TMP_843 \def (CHead c3 TMP_842 u) in (let TMP_844 \def (Bind Abbr) in 
(let TMP_845 \def (CHead d2 TMP_844 u0) in (drop TMP_841 O TMP_843 
TMP_845)))))))) in (let TMP_847 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g 
d1 u0 t0))) in (let TMP_848 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 t0))) in (let TMP_849 \def (Bind Abbr) in (let TMP_850 \def (Bind Abbr) in 
(let TMP_851 \def (CHead x0 TMP_850 x1) in (let TMP_852 \def (drop_drop 
TMP_849 n0 c3 TMP_851 H8 u) in (let TMP_853 \def (ex4_2_intro C T TMP_840 
TMP_846 TMP_847 TMP_848 x0 x1 H7 TMP_852 H9 H10) in (or_intror TMP_829 
TMP_839 TMP_853)))))))))))))))))))))))) in (ex4_2_ind C T TMP_797 TMP_800 
TMP_801 TMP_802 TMP_821 TMP_854 H6)))))))))))))))) in (let TMP_856 \def (Bind 
Abst) in (let TMP_857 \def (Bind Abst) in (let TMP_858 \def (CHead d1 TMP_857 
t0) in (let TMP_859 \def (drop_gen_drop TMP_856 c0 TMP_858 t n0 H5) in (let 
TMP_860 \def (H c0 c3 H1 d1 t0 TMP_859) in (or_ind TMP_715 TMP_722 TMP_741 
TMP_796 TMP_855 TMP_860)))))))))))))))))))))))))))))))))))) in (csubt_ind g 
TMP_186 TMP_235 TMP_559 TMP_710 TMP_861 c1 c2 H0))))))))))) in (nat_ind 
TMP_13 TMP_171 TMP_862 n))))).

