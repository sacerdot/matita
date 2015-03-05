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

include "basic_1/wf3/clear.ma".

include "basic_1/ty3/dec.ma".

theorem wf3_getl_conf:
 \forall (b: B).(\forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall 
(v: T).((getl i c1 (CHead d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: 
C).((wf3 g c1 c2) \to (\forall (w: T).((ty3 g d1 v w) \to (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2)))))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(let TMP_5 \def (\lambda (n: nat).(\forall 
(c1: C).(\forall (d1: C).(\forall (v: T).((getl n c1 (CHead d1 (Bind b) v)) 
\to (\forall (g: G).(\forall (c2: C).((wf3 g c1 c2) \to (\forall (w: T).((ty3 
g d1 v w) \to (let TMP_3 \def (\lambda (d2: C).(let TMP_1 \def (Bind b) in 
(let TMP_2 \def (CHead d2 TMP_1 v) in (getl n c2 TMP_2)))) in (let TMP_4 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (ex2 C TMP_3 TMP_4))))))))))))) in (let 
TMP_86 \def (\lambda (c1: C).(\lambda (d1: C).(\lambda (v: T).(\lambda (H: 
(getl O c1 (CHead d1 (Bind b) v))).(\lambda (g: G).(\lambda (c2: C).(\lambda 
(H0: (wf3 g c1 c2)).(\lambda (w: T).(\lambda (H1: (ty3 g d1 v w)).(let TMP_6 
\def (Bind b) in (let TMP_7 \def (CHead d1 TMP_6 v) in (let TMP_8 \def (Bind 
b) in (let TMP_9 \def (CHead d1 TMP_8 v) in (let TMP_10 \def (getl_gen_O c1 
TMP_9 H) in (let H_y \def (wf3_clear_conf c1 TMP_7 TMP_10 g c2 H0) in (let 
H_x \def (wf3_gen_bind1 g d1 c2 v b H_y) in (let H2 \def H_x in (let TMP_13 
\def (\lambda (c3: C).(\lambda (_: T).(let TMP_11 \def (Bind b) in (let 
TMP_12 \def (CHead c3 TMP_11 v) in (eq C c2 TMP_12))))) in (let TMP_14 \def 
(\lambda (c3: C).(\lambda (_: T).(wf3 g d1 c3))) in (let TMP_15 \def (\lambda 
(_: C).(\lambda (w0: T).(ty3 g d1 v w0))) in (let TMP_16 \def (ex3_2 C T 
TMP_13 TMP_14 TMP_15) in (let TMP_20 \def (\lambda (c3: C).(let TMP_17 \def 
(Bind Void) in (let TMP_18 \def (TSort O) in (let TMP_19 \def (CHead c3 
TMP_17 TMP_18) in (eq C c2 TMP_19))))) in (let TMP_21 \def (\lambda (c3: 
C).(wf3 g d1 c3)) in (let TMP_22 \def (\lambda (_: C).(\forall (w0: T).((ty3 
g d1 v w0) \to False))) in (let TMP_23 \def (ex3 C TMP_20 TMP_21 TMP_22) in 
(let TMP_26 \def (\lambda (d2: C).(let TMP_24 \def (Bind b) in (let TMP_25 
\def (CHead d2 TMP_24 v) in (getl O c2 TMP_25)))) in (let TMP_27 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_28 \def (ex2 C TMP_26 TMP_27) in 
(let TMP_55 \def (\lambda (H3: (ex3_2 C T (\lambda (c3: C).(\lambda (_: 
T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g 
d1 c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 g d1 v w0))))).(let TMP_31 
\def (\lambda (c3: C).(\lambda (_: T).(let TMP_29 \def (Bind b) in (let 
TMP_30 \def (CHead c3 TMP_29 v) in (eq C c2 TMP_30))))) in (let TMP_32 \def 
(\lambda (c3: C).(\lambda (_: T).(wf3 g d1 c3))) in (let TMP_33 \def (\lambda 
(_: C).(\lambda (w0: T).(ty3 g d1 v w0))) in (let TMP_36 \def (\lambda (d2: 
C).(let TMP_34 \def (Bind b) in (let TMP_35 \def (CHead d2 TMP_34 v) in (getl 
O c2 TMP_35)))) in (let TMP_37 \def (\lambda (d2: C).(wf3 g d1 d2)) in (let 
TMP_38 \def (ex2 C TMP_36 TMP_37) in (let TMP_54 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H4: (eq C c2 (CHead x0 (Bind b) v))).(\lambda 
(H5: (wf3 g d1 x0)).(\lambda (_: (ty3 g d1 v x1)).(let TMP_39 \def (Bind b) 
in (let TMP_40 \def (CHead x0 TMP_39 v) in (let TMP_45 \def (\lambda (c: 
C).(let TMP_43 \def (\lambda (d2: C).(let TMP_41 \def (Bind b) in (let TMP_42 
\def (CHead d2 TMP_41 v) in (getl O c TMP_42)))) in (let TMP_44 \def (\lambda 
(d2: C).(wf3 g d1 d2)) in (ex2 C TMP_43 TMP_44)))) in (let TMP_50 \def 
(\lambda (d2: C).(let TMP_46 \def (Bind b) in (let TMP_47 \def (CHead x0 
TMP_46 v) in (let TMP_48 \def (Bind b) in (let TMP_49 \def (CHead d2 TMP_48 
v) in (getl O TMP_47 TMP_49)))))) in (let TMP_51 \def (\lambda (d2: C).(wf3 g 
d1 d2)) in (let TMP_52 \def (getl_refl b x0 v) in (let TMP_53 \def (ex_intro2 
C TMP_50 TMP_51 x0 TMP_52 H5) in (eq_ind_r C TMP_40 TMP_45 TMP_53 c2 
H4))))))))))))) in (ex3_2_ind C T TMP_31 TMP_32 TMP_33 TMP_38 TMP_54 
H3))))))))) in (let TMP_85 \def (\lambda (H3: (ex3 C (\lambda (c3: C).(eq C 
c2 (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g d1 c3)) 
(\lambda (_: C).(\forall (w0: T).((ty3 g d1 v w0) \to False))))).(let TMP_59 
\def (\lambda (c3: C).(let TMP_56 \def (Bind Void) in (let TMP_57 \def (TSort 
O) in (let TMP_58 \def (CHead c3 TMP_56 TMP_57) in (eq C c2 TMP_58))))) in 
(let TMP_60 \def (\lambda (c3: C).(wf3 g d1 c3)) in (let TMP_61 \def (\lambda 
(_: C).(\forall (w0: T).((ty3 g d1 v w0) \to False))) in (let TMP_64 \def 
(\lambda (d2: C).(let TMP_62 \def (Bind b) in (let TMP_63 \def (CHead d2 
TMP_62 v) in (getl O c2 TMP_63)))) in (let TMP_65 \def (\lambda (d2: C).(wf3 
g d1 d2)) in (let TMP_66 \def (ex2 C TMP_64 TMP_65) in (let TMP_84 \def 
(\lambda (x0: C).(\lambda (H4: (eq C c2 (CHead x0 (Bind Void) (TSort 
O)))).(\lambda (_: (wf3 g d1 x0)).(\lambda (H6: ((\forall (w0: T).((ty3 g d1 
v w0) \to False)))).(let TMP_67 \def (Bind Void) in (let TMP_68 \def (TSort 
O) in (let TMP_69 \def (CHead x0 TMP_67 TMP_68) in (let TMP_74 \def (\lambda 
(c: C).(let TMP_72 \def (\lambda (d2: C).(let TMP_70 \def (Bind b) in (let 
TMP_71 \def (CHead d2 TMP_70 v) in (getl O c TMP_71)))) in (let TMP_73 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (ex2 C TMP_72 TMP_73)))) in (let H_x0 \def 
(H6 w H1) in (let H7 \def H_x0 in (let TMP_80 \def (\lambda (d2: C).(let 
TMP_75 \def (Bind Void) in (let TMP_76 \def (TSort O) in (let TMP_77 \def 
(CHead x0 TMP_75 TMP_76) in (let TMP_78 \def (Bind b) in (let TMP_79 \def 
(CHead d2 TMP_78 v) in (getl O TMP_77 TMP_79))))))) in (let TMP_81 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_82 \def (ex2 C TMP_80 TMP_81) in 
(let TMP_83 \def (False_ind TMP_82 H7) in (eq_ind_r C TMP_69 TMP_74 TMP_83 c2 
H4))))))))))))))) in (ex3_ind C TMP_59 TMP_60 TMP_61 TMP_66 TMP_84 
H3))))))))) in (or_ind TMP_16 TMP_23 TMP_28 TMP_55 TMP_85 
H2))))))))))))))))))))))))))))))) in (let TMP_231 \def (\lambda (n: 
nat).(\lambda (H: ((\forall (c1: C).(\forall (d1: C).(\forall (v: T).((getl n 
c1 (CHead d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: C).((wf3 g c1 c2) 
\to (\forall (w: T).((ty3 g d1 v w) \to (ex2 C (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)))))))))))))).(\lambda 
(c1: C).(let TMP_92 \def (\lambda (c: C).(\forall (d1: C).(\forall (v: 
T).((getl (S n) c (CHead d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: 
C).((wf3 g c c2) \to (\forall (w: T).((ty3 g d1 v w) \to (let TMP_90 \def 
(\lambda (d2: C).(let TMP_87 \def (S n) in (let TMP_88 \def (Bind b) in (let 
TMP_89 \def (CHead d2 TMP_88 v) in (getl TMP_87 c2 TMP_89))))) in (let TMP_91 
\def (\lambda (d2: C).(wf3 g d1 d2)) in (ex2 C TMP_90 TMP_91)))))))))))) in 
(let TMP_102 \def (\lambda (n0: nat).(\lambda (d1: C).(\lambda (v: 
T).(\lambda (H0: (getl (S n) (CSort n0) (CHead d1 (Bind b) v))).(\lambda (g: 
G).(\lambda (c2: C).(\lambda (_: (wf3 g (CSort n0) c2)).(\lambda (w: 
T).(\lambda (_: (ty3 g d1 v w)).(let TMP_93 \def (S n) in (let TMP_94 \def 
(Bind b) in (let TMP_95 \def (CHead d1 TMP_94 v) in (let TMP_99 \def (\lambda 
(d2: C).(let TMP_96 \def (S n) in (let TMP_97 \def (Bind b) in (let TMP_98 
\def (CHead d2 TMP_97 v) in (getl TMP_96 c2 TMP_98))))) in (let TMP_100 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_101 \def (ex2 C TMP_99 TMP_100) 
in (getl_gen_sort n0 TMP_93 TMP_95 H0 TMP_101)))))))))))))))) in (let TMP_230 
\def (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).(\forall (v: T).((getl 
(S n) c (CHead d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: C).((wf3 g c 
c2) \to (\forall (w: T).((ty3 g d1 v w) \to (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (v: 
T).(\lambda (H1: (getl (S n) (CHead c k t) (CHead d1 (Bind b) v))).(\lambda 
(g: G).(\lambda (c2: C).(\lambda (H2: (wf3 g (CHead c k t) c2)).(\lambda (w: 
T).(\lambda (H3: (ty3 g d1 v w)).(let TMP_108 \def (\lambda (k0: K).((wf3 g 
(CHead c k0 t) c2) \to ((getl (r k0 n) c (CHead d1 (Bind b) v)) \to (let 
TMP_106 \def (\lambda (d2: C).(let TMP_103 \def (S n) in (let TMP_104 \def 
(Bind b) in (let TMP_105 \def (CHead d2 TMP_104 v) in (getl TMP_103 c2 
TMP_105))))) in (let TMP_107 \def (\lambda (d2: C).(wf3 g d1 d2)) in (ex2 C 
TMP_106 TMP_107)))))) in (let TMP_225 \def (\lambda (b0: B).(\lambda (H4: 
(wf3 g (CHead c (Bind b0) t) c2)).(\lambda (H5: (getl (r (Bind b0) n) c 
(CHead d1 (Bind b) v))).(let H_x \def (wf3_gen_bind1 g c c2 t b0 H4) in (let 
H6 \def H_x in (let TMP_111 \def (\lambda (c3: C).(\lambda (_: T).(let 
TMP_109 \def (Bind b0) in (let TMP_110 \def (CHead c3 TMP_109 t) in (eq C c2 
TMP_110))))) in (let TMP_112 \def (\lambda (c3: C).(\lambda (_: T).(wf3 g c 
c3))) in (let TMP_113 \def (\lambda (_: C).(\lambda (w0: T).(ty3 g c t w0))) 
in (let TMP_114 \def (ex3_2 C T TMP_111 TMP_112 TMP_113) in (let TMP_118 \def 
(\lambda (c3: C).(let TMP_115 \def (Bind Void) in (let TMP_116 \def (TSort O) 
in (let TMP_117 \def (CHead c3 TMP_115 TMP_116) in (eq C c2 TMP_117))))) in 
(let TMP_119 \def (\lambda (c3: C).(wf3 g c c3)) in (let TMP_120 \def 
(\lambda (_: C).(\forall (w0: T).((ty3 g c t w0) \to False))) in (let TMP_121 
\def (ex3 C TMP_118 TMP_119 TMP_120) in (let TMP_125 \def (\lambda (d2: 
C).(let TMP_122 \def (S n) in (let TMP_123 \def (Bind b) in (let TMP_124 \def 
(CHead d2 TMP_123 v) in (getl TMP_122 c2 TMP_124))))) in (let TMP_126 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_127 \def (ex2 C TMP_125 TMP_126) 
in (let TMP_173 \def (\lambda (H7: (ex3_2 C T (\lambda (c3: C).(\lambda (_: 
T).(eq C c2 (CHead c3 (Bind b0) t)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g 
c c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 g c t w0))))).(let TMP_130 \def 
(\lambda (c3: C).(\lambda (_: T).(let TMP_128 \def (Bind b0) in (let TMP_129 
\def (CHead c3 TMP_128 t) in (eq C c2 TMP_129))))) in (let TMP_131 \def 
(\lambda (c3: C).(\lambda (_: T).(wf3 g c c3))) in (let TMP_132 \def (\lambda 
(_: C).(\lambda (w0: T).(ty3 g c t w0))) in (let TMP_136 \def (\lambda (d2: 
C).(let TMP_133 \def (S n) in (let TMP_134 \def (Bind b) in (let TMP_135 \def 
(CHead d2 TMP_134 v) in (getl TMP_133 c2 TMP_135))))) in (let TMP_137 \def 
(\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_138 \def (ex2 C TMP_136 TMP_137) 
in (let TMP_172 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H8: (eq C c2 
(CHead x0 (Bind b0) t))).(\lambda (H9: (wf3 g c x0)).(\lambda (_: (ty3 g c t 
x1)).(let TMP_139 \def (Bind b0) in (let TMP_140 \def (CHead x0 TMP_139 t) in 
(let TMP_146 \def (\lambda (c0: C).(let TMP_144 \def (\lambda (d2: C).(let 
TMP_141 \def (S n) in (let TMP_142 \def (Bind b) in (let TMP_143 \def (CHead 
d2 TMP_142 v) in (getl TMP_141 c0 TMP_143))))) in (let TMP_145 \def (\lambda 
(d2: C).(wf3 g d1 d2)) in (ex2 C TMP_144 TMP_145)))) in (let H_x0 \def (H c 
d1 v H5 g x0 H9 w H3) in (let H11 \def H_x0 in (let TMP_149 \def (\lambda 
(d2: C).(let TMP_147 \def (Bind b) in (let TMP_148 \def (CHead d2 TMP_147 v) 
in (getl n x0 TMP_148)))) in (let TMP_150 \def (\lambda (d2: C).(wf3 g d1 
d2)) in (let TMP_156 \def (\lambda (d2: C).(let TMP_151 \def (S n) in (let 
TMP_152 \def (Bind b0) in (let TMP_153 \def (CHead x0 TMP_152 t) in (let 
TMP_154 \def (Bind b) in (let TMP_155 \def (CHead d2 TMP_154 v) in (getl 
TMP_151 TMP_153 TMP_155))))))) in (let TMP_157 \def (\lambda (d2: C).(wf3 g 
d1 d2)) in (let TMP_158 \def (ex2 C TMP_156 TMP_157) in (let TMP_170 \def 
(\lambda (x: C).(\lambda (H12: (getl n x0 (CHead x (Bind b) v))).(\lambda 
(H13: (wf3 g d1 x)).(let TMP_164 \def (\lambda (d2: C).(let TMP_159 \def (S 
n) in (let TMP_160 \def (Bind b0) in (let TMP_161 \def (CHead x0 TMP_160 t) 
in (let TMP_162 \def (Bind b) in (let TMP_163 \def (CHead d2 TMP_162 v) in 
(getl TMP_159 TMP_161 TMP_163))))))) in (let TMP_165 \def (\lambda (d2: 
C).(wf3 g d1 d2)) in (let TMP_166 \def (Bind b0) in (let TMP_167 \def (Bind 
b) in (let TMP_168 \def (CHead x TMP_167 v) in (let TMP_169 \def (getl_head 
TMP_166 n x0 TMP_168 H12 t) in (ex_intro2 C TMP_164 TMP_165 x TMP_169 
H13)))))))))) in (let TMP_171 \def (ex2_ind C TMP_149 TMP_150 TMP_158 TMP_170 
H11) in (eq_ind_r C TMP_140 TMP_146 TMP_171 c2 H8)))))))))))))))))) in 
(ex3_2_ind C T TMP_130 TMP_131 TMP_132 TMP_138 TMP_172 H7))))))))) in (let 
TMP_224 \def (\lambda (H7: (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind 
Void) (TSort O)))) (\lambda (c3: C).(wf3 g c c3)) (\lambda (_: C).(\forall 
(w0: T).((ty3 g c t w0) \to False))))).(let TMP_177 \def (\lambda (c3: 
C).(let TMP_174 \def (Bind Void) in (let TMP_175 \def (TSort O) in (let 
TMP_176 \def (CHead c3 TMP_174 TMP_175) in (eq C c2 TMP_176))))) in (let 
TMP_178 \def (\lambda (c3: C).(wf3 g c c3)) in (let TMP_179 \def (\lambda (_: 
C).(\forall (w0: T).((ty3 g c t w0) \to False))) in (let TMP_183 \def 
(\lambda (d2: C).(let TMP_180 \def (S n) in (let TMP_181 \def (Bind b) in 
(let TMP_182 \def (CHead d2 TMP_181 v) in (getl TMP_180 c2 TMP_182))))) in 
(let TMP_184 \def (\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_185 \def (ex2 C 
TMP_183 TMP_184) in (let TMP_223 \def (\lambda (x0: C).(\lambda (H8: (eq C c2 
(CHead x0 (Bind Void) (TSort O)))).(\lambda (H9: (wf3 g c x0)).(\lambda (_: 
((\forall (w0: T).((ty3 g c t w0) \to False)))).(let TMP_186 \def (Bind Void) 
in (let TMP_187 \def (TSort O) in (let TMP_188 \def (CHead x0 TMP_186 
TMP_187) in (let TMP_194 \def (\lambda (c0: C).(let TMP_192 \def (\lambda 
(d2: C).(let TMP_189 \def (S n) in (let TMP_190 \def (Bind b) in (let TMP_191 
\def (CHead d2 TMP_190 v) in (getl TMP_189 c0 TMP_191))))) in (let TMP_193 
\def (\lambda (d2: C).(wf3 g d1 d2)) in (ex2 C TMP_192 TMP_193)))) in (let 
H_x0 \def (H c d1 v H5 g x0 H9 w H3) in (let H11 \def H_x0 in (let TMP_197 
\def (\lambda (d2: C).(let TMP_195 \def (Bind b) in (let TMP_196 \def (CHead 
d2 TMP_195 v) in (getl n x0 TMP_196)))) in (let TMP_198 \def (\lambda (d2: 
C).(wf3 g d1 d2)) in (let TMP_205 \def (\lambda (d2: C).(let TMP_199 \def (S 
n) in (let TMP_200 \def (Bind Void) in (let TMP_201 \def (TSort O) in (let 
TMP_202 \def (CHead x0 TMP_200 TMP_201) in (let TMP_203 \def (Bind b) in (let 
TMP_204 \def (CHead d2 TMP_203 v) in (getl TMP_199 TMP_202 TMP_204)))))))) in 
(let TMP_206 \def (\lambda (d2: C).(wf3 g d1 d2)) in (let TMP_207 \def (ex2 C 
TMP_205 TMP_206) in (let TMP_221 \def (\lambda (x: C).(\lambda (H12: (getl n 
x0 (CHead x (Bind b) v))).(\lambda (H13: (wf3 g d1 x)).(let TMP_214 \def 
(\lambda (d2: C).(let TMP_208 \def (S n) in (let TMP_209 \def (Bind Void) in 
(let TMP_210 \def (TSort O) in (let TMP_211 \def (CHead x0 TMP_209 TMP_210) 
in (let TMP_212 \def (Bind b) in (let TMP_213 \def (CHead d2 TMP_212 v) in 
(getl TMP_208 TMP_211 TMP_213)))))))) in (let TMP_215 \def (\lambda (d2: 
C).(wf3 g d1 d2)) in (let TMP_216 \def (Bind Void) in (let TMP_217 \def (Bind 
b) in (let TMP_218 \def (CHead x TMP_217 v) in (let TMP_219 \def (TSort O) in 
(let TMP_220 \def (getl_head TMP_216 n x0 TMP_218 H12 TMP_219) in (ex_intro2 
C TMP_214 TMP_215 x TMP_220 H13))))))))))) in (let TMP_222 \def (ex2_ind C 
TMP_197 TMP_198 TMP_207 TMP_221 H11) in (eq_ind_r C TMP_188 TMP_194 TMP_222 
c2 H8)))))))))))))))))) in (ex3_ind C TMP_177 TMP_178 TMP_179 TMP_185 TMP_223 
H7))))))))) in (or_ind TMP_114 TMP_121 TMP_127 TMP_173 TMP_224 
H6))))))))))))))))))) in (let TMP_226 \def (\lambda (f: F).(\lambda (H4: (wf3 
g (CHead c (Flat f) t) c2)).(\lambda (H5: (getl (r (Flat f) n) c (CHead d1 
(Bind b) v))).(let H_y \def (wf3_gen_flat1 g c c2 t f H4) in (H0 d1 v H5 g c2 
H_y w H3))))) in (let TMP_227 \def (Bind b) in (let TMP_228 \def (CHead d1 
TMP_227 v) in (let TMP_229 \def (getl_gen_S k c TMP_228 t n H1) in (K_ind 
TMP_108 TMP_225 TMP_226 k H2 TMP_229))))))))))))))))))) in (C_ind TMP_92 
TMP_102 TMP_230 c1))))))) in (nat_ind TMP_5 TMP_86 TMP_231 i))))).

theorem getl_wf3_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).((getl i c1 d1) \to 
(\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (c2: C).(getl i c2 d2)))))))))
\def
 \lambda (i: nat).(let TMP_3 \def (\lambda (n: nat).(\forall (c1: C).(\forall 
(d1: C).((getl n c1 d1) \to (\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) 
\to (let TMP_1 \def (\lambda (c2: C).(wf3 g c1 c2)) in (let TMP_2 \def 
(\lambda (c2: C).(getl n c2 d2)) in (ex2 C TMP_1 TMP_2)))))))))) in (let 
TMP_15 \def (\lambda (c1: C).(\lambda (d1: C).(\lambda (H: (getl O c1 
d1)).(\lambda (g: G).(\lambda (d2: C).(\lambda (H0: (wf3 g d1 d2)).(let TMP_4 
\def (getl_gen_O c1 d1 H) in (let H_x \def (clear_wf3_trans c1 d1 TMP_4 g d2 
H0) in (let H1 \def H_x in (let TMP_5 \def (\lambda (c2: C).(wf3 g c1 c2)) in 
(let TMP_6 \def (\lambda (c2: C).(clear c2 d2)) in (let TMP_7 \def (\lambda 
(c2: C).(wf3 g c1 c2)) in (let TMP_8 \def (\lambda (c2: C).(getl O c2 d2)) in 
(let TMP_9 \def (ex2 C TMP_7 TMP_8) in (let TMP_14 \def (\lambda (x: 
C).(\lambda (H2: (wf3 g c1 x)).(\lambda (H3: (clear x d2)).(let TMP_10 \def 
(\lambda (c2: C).(wf3 g c1 c2)) in (let TMP_11 \def (\lambda (c2: C).(getl O 
c2 d2)) in (let TMP_12 \def (drop_refl x) in (let TMP_13 \def (getl_intro O x 
d2 x TMP_12 H3) in (ex_intro2 C TMP_10 TMP_11 x H2 TMP_13)))))))) in (ex2_ind 
C TMP_5 TMP_6 TMP_9 TMP_14 H1)))))))))))))))) in (let TMP_102 \def (\lambda 
(n: nat).(\lambda (H: ((\forall (c1: C).(\forall (d1: C).((getl n c1 d1) \to 
(\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (c2: C).(getl n c2 d2))))))))))).(\lambda (c1: 
C).(let TMP_19 \def (\lambda (c: C).(\forall (d1: C).((getl (S n) c d1) \to 
(\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (let TMP_16 \def (\lambda 
(c2: C).(wf3 g c c2)) in (let TMP_18 \def (\lambda (c2: C).(let TMP_17 \def 
(S n) in (getl TMP_17 c2 d2))) in (ex2 C TMP_16 TMP_18))))))))) in (let 
TMP_26 \def (\lambda (n0: nat).(\lambda (d1: C).(\lambda (H0: (getl (S n) 
(CSort n0) d1)).(\lambda (g: G).(\lambda (d2: C).(\lambda (_: (wf3 g d1 
d2)).(let TMP_20 \def (S n) in (let TMP_22 \def (\lambda (c2: C).(let TMP_21 
\def (CSort n0) in (wf3 g TMP_21 c2))) in (let TMP_24 \def (\lambda (c2: 
C).(let TMP_23 \def (S n) in (getl TMP_23 c2 d2))) in (let TMP_25 \def (ex2 C 
TMP_22 TMP_24) in (getl_gen_sort n0 TMP_20 d1 H0 TMP_25))))))))))) in (let 
TMP_101 \def (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).((getl (S n) c 
d1) \to (\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda 
(c2: C).(wf3 g c c2)) (\lambda (c2: C).(getl (S n) c2 d2)))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (H1: (getl (S n) (CHead c k 
t) d1)).(\lambda (g: G).(\lambda (d2: C).(\lambda (H2: (wf3 g d1 d2)).(let 
TMP_31 \def (\lambda (k0: K).((getl (r k0 n) c d1) \to (let TMP_28 \def 
(\lambda (c2: C).(let TMP_27 \def (CHead c k0 t) in (wf3 g TMP_27 c2))) in 
(let TMP_30 \def (\lambda (c2: C).(let TMP_29 \def (S n) in (getl TMP_29 c2 
d2))) in (ex2 C TMP_28 TMP_30))))) in (let TMP_82 \def (\lambda (b: 
B).(\lambda (H3: (getl (r (Bind b) n) c d1)).(let H_x \def (H c d1 H3 g d2 
H2) in (let H4 \def H_x in (let TMP_32 \def (\lambda (c2: C).(wf3 g c c2)) in 
(let TMP_33 \def (\lambda (c2: C).(getl n c2 d2)) in (let TMP_36 \def 
(\lambda (c2: C).(let TMP_34 \def (Bind b) in (let TMP_35 \def (CHead c 
TMP_34 t) in (wf3 g TMP_35 c2)))) in (let TMP_38 \def (\lambda (c2: C).(let 
TMP_37 \def (S n) in (getl TMP_37 c2 d2))) in (let TMP_39 \def (ex2 C TMP_36 
TMP_38) in (let TMP_81 \def (\lambda (x: C).(\lambda (H5: (wf3 g c 
x)).(\lambda (H6: (getl n x d2)).(let H_x0 \def (ty3_inference g c t) in (let 
H7 \def H_x0 in (let TMP_40 \def (\lambda (t2: T).(ty3 g c t t2)) in (let 
TMP_41 \def (ex T TMP_40) in (let TMP_42 \def (\forall (t2: T).((ty3 g c t 
t2) \to False)) in (let TMP_45 \def (\lambda (c2: C).(let TMP_43 \def (Bind 
b) in (let TMP_44 \def (CHead c TMP_43 t) in (wf3 g TMP_44 c2)))) in (let 
TMP_47 \def (\lambda (c2: C).(let TMP_46 \def (S n) in (getl TMP_46 c2 d2))) 
in (let TMP_48 \def (ex2 C TMP_45 TMP_47) in (let TMP_67 \def (\lambda (H8: 
(ex T (\lambda (t2: T).(ty3 g c t t2)))).(let TMP_49 \def (\lambda (t2: 
T).(ty3 g c t t2)) in (let TMP_52 \def (\lambda (c2: C).(let TMP_50 \def 
(Bind b) in (let TMP_51 \def (CHead c TMP_50 t) in (wf3 g TMP_51 c2)))) in 
(let TMP_54 \def (\lambda (c2: C).(let TMP_53 \def (S n) in (getl TMP_53 c2 
d2))) in (let TMP_55 \def (ex2 C TMP_52 TMP_54) in (let TMP_66 \def (\lambda 
(x0: T).(\lambda (H9: (ty3 g c t x0)).(let TMP_58 \def (\lambda (c2: C).(let 
TMP_56 \def (Bind b) in (let TMP_57 \def (CHead c TMP_56 t) in (wf3 g TMP_57 
c2)))) in (let TMP_60 \def (\lambda (c2: C).(let TMP_59 \def (S n) in (getl 
TMP_59 c2 d2))) in (let TMP_61 \def (Bind b) in (let TMP_62 \def (CHead x 
TMP_61 t) in (let TMP_63 \def (wf3_bind g c x H5 t x0 H9 b) in (let TMP_64 
\def (Bind b) in (let TMP_65 \def (getl_head TMP_64 n x d2 H6 t) in 
(ex_intro2 C TMP_58 TMP_60 TMP_62 TMP_63 TMP_65)))))))))) in (ex_ind T TMP_49 
TMP_55 TMP_66 H8))))))) in (let TMP_80 \def (\lambda (H8: ((\forall (t2: 
T).((ty3 g c t t2) \to False)))).(let TMP_70 \def (\lambda (c2: C).(let 
TMP_68 \def (Bind b) in (let TMP_69 \def (CHead c TMP_68 t) in (wf3 g TMP_69 
c2)))) in (let TMP_72 \def (\lambda (c2: C).(let TMP_71 \def (S n) in (getl 
TMP_71 c2 d2))) in (let TMP_73 \def (Bind Void) in (let TMP_74 \def (TSort O) 
in (let TMP_75 \def (CHead x TMP_73 TMP_74) in (let TMP_76 \def (wf3_void g c 
x H5 t H8 b) in (let TMP_77 \def (Bind Void) in (let TMP_78 \def (TSort O) in 
(let TMP_79 \def (getl_head TMP_77 n x d2 H6 TMP_78) in (ex_intro2 C TMP_70 
TMP_72 TMP_75 TMP_76 TMP_79))))))))))) in (or_ind TMP_41 TMP_42 TMP_48 TMP_67 
TMP_80 H7)))))))))))))) in (ex2_ind C TMP_32 TMP_33 TMP_39 TMP_81 
H4))))))))))) in (let TMP_99 \def (\lambda (f: F).(\lambda (H3: (getl (r 
(Flat f) n) c d1)).(let H_x \def (H0 d1 H3 g d2 H2) in (let H4 \def H_x in 
(let TMP_83 \def (\lambda (c2: C).(wf3 g c c2)) in (let TMP_85 \def (\lambda 
(c2: C).(let TMP_84 \def (S n) in (getl TMP_84 c2 d2))) in (let TMP_88 \def 
(\lambda (c2: C).(let TMP_86 \def (Flat f) in (let TMP_87 \def (CHead c 
TMP_86 t) in (wf3 g TMP_87 c2)))) in (let TMP_90 \def (\lambda (c2: C).(let 
TMP_89 \def (S n) in (getl TMP_89 c2 d2))) in (let TMP_91 \def (ex2 C TMP_88 
TMP_90) in (let TMP_98 \def (\lambda (x: C).(\lambda (H5: (wf3 g c 
x)).(\lambda (H6: (getl (S n) x d2)).(let TMP_94 \def (\lambda (c2: C).(let 
TMP_92 \def (Flat f) in (let TMP_93 \def (CHead c TMP_92 t) in (wf3 g TMP_93 
c2)))) in (let TMP_96 \def (\lambda (c2: C).(let TMP_95 \def (S n) in (getl 
TMP_95 c2 d2))) in (let TMP_97 \def (wf3_flat g c x H5 t f) in (ex_intro2 C 
TMP_94 TMP_96 x TMP_97 H6))))))) in (ex2_ind C TMP_83 TMP_85 TMP_91 TMP_98 
H4))))))))))) in (let TMP_100 \def (getl_gen_S k c d1 t n H1) in (K_ind 
TMP_31 TMP_82 TMP_99 k TMP_100)))))))))))))) in (C_ind TMP_19 TMP_26 TMP_101 
c1))))))) in (nat_ind TMP_3 TMP_15 TMP_102 i)))).

