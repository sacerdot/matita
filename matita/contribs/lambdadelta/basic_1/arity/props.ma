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

include "basic_1/arity/fwd.ma".

theorem node_inh:
 \forall (g: G).(\forall (n: nat).(\forall (k: nat).(ex_2 C T (\lambda (c: 
C).(\lambda (t: T).(arity g c t (ASort k n)))))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (k: nat).(let TMP_3 \def (\lambda 
(n0: nat).(let TMP_2 \def (\lambda (c: C).(\lambda (t: T).(let TMP_1 \def 
(ASort n0 n) in (arity g c t TMP_1)))) in (ex_2 C T TMP_2))) in (let TMP_5 
\def (\lambda (c: C).(\lambda (t: T).(let TMP_4 \def (ASort O n) in (arity g 
c t TMP_4)))) in (let TMP_6 \def (CSort O) in (let TMP_7 \def (TSort n) in 
(let TMP_8 \def (CSort O) in (let TMP_9 \def (arity_sort g TMP_8 n) in (let 
TMP_10 \def (ex_2_intro C T TMP_5 TMP_6 TMP_7 TMP_9) in (let TMP_30 \def 
(\lambda (n0: nat).(\lambda (H: (ex_2 C T (\lambda (c: C).(\lambda (t: 
T).(arity g c t (ASort n0 n)))))).(let H0 \def H in (let TMP_12 \def (\lambda 
(c: C).(\lambda (t: T).(let TMP_11 \def (ASort n0 n) in (arity g c t 
TMP_11)))) in (let TMP_15 \def (\lambda (c: C).(\lambda (t: T).(let TMP_13 
\def (S n0) in (let TMP_14 \def (ASort TMP_13 n) in (arity g c t TMP_14))))) 
in (let TMP_16 \def (ex_2 C T TMP_15) in (let TMP_29 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H1: (arity g x0 x1 (ASort n0 n))).(let TMP_19 
\def (\lambda (c: C).(\lambda (t: T).(let TMP_17 \def (S n0) in (let TMP_18 
\def (ASort TMP_17 n) in (arity g c t TMP_18))))) in (let TMP_20 \def (Bind 
Abst) in (let TMP_21 \def (CHead x0 TMP_20 x1) in (let TMP_22 \def (TLRef O) 
in (let TMP_23 \def (Bind Abst) in (let TMP_24 \def (CHead x0 TMP_23 x1) in 
(let TMP_25 \def (getl_refl Abst x0 x1) in (let TMP_26 \def (S n0) in (let 
TMP_27 \def (ASort TMP_26 n) in (let TMP_28 \def (arity_abst g TMP_24 x0 x1 O 
TMP_25 TMP_27 H1) in (ex_2_intro C T TMP_19 TMP_21 TMP_22 
TMP_28)))))))))))))) in (ex_2_ind C T TMP_12 TMP_16 TMP_29 H0)))))))) in 
(nat_ind TMP_3 TMP_10 TMP_30 k))))))))))).

theorem arity_lift:
 \forall (g: G).(\forall (c2: C).(\forall (t: T).(\forall (a: A).((arity g c2 
t a) \to (\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 
c2) \to (arity g c1 (lift h d t) a)))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c2 t a)).(let TMP_2 \def (\lambda (c: C).(\lambda (t0: T).(\lambda 
(a0: A).(\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) 
\to (let TMP_1 \def (lift h d t0) in (arity g c1 TMP_1 a0))))))))) in (let 
TMP_10 \def (\lambda (c: C).(\lambda (n: nat).(\lambda (c1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (_: (drop h d c1 c)).(let TMP_3 \def (TSort 
n) in (let TMP_5 \def (\lambda (t0: T).(let TMP_4 \def (ASort O n) in (arity 
g c1 t0 TMP_4))) in (let TMP_6 \def (arity_sort g c1 n) in (let TMP_7 \def 
(TSort n) in (let TMP_8 \def (lift h d TMP_7) in (let TMP_9 \def (lift_sort n 
h d) in (eq_ind_r T TMP_3 TMP_5 TMP_6 TMP_8 TMP_9))))))))))))) in (let TMP_86 
\def (\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (a0: 
A).(\lambda (H1: (arity g d u a0)).(\lambda (H2: ((\forall (c1: C).(\forall 
(h: nat).(\forall (d0: nat).((drop h d0 c1 d) \to (arity g c1 (lift h d0 u) 
a0))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda (H3: 
(drop h d0 c1 c)).(let TMP_11 \def (TLRef i) in (let TMP_12 \def (lift h d0 
TMP_11) in (let TMP_13 \def (arity g c1 TMP_12 a0) in (let TMP_73 \def 
(\lambda (H4: (lt i d0)).(let TMP_14 \def (TLRef i) in (let TMP_15 \def 
(\lambda (t0: T).(arity g c1 t0 a0)) in (let TMP_16 \def (S i) in (let TMP_17 
\def (S d0) in (let TMP_18 \def (S i) in (let TMP_19 \def (S TMP_18) in (let 
TMP_20 \def (S d0) in (let TMP_21 \def (S i) in (let TMP_22 \def (le_n_S 
TMP_21 d0 H4) in (let TMP_23 \def (le_S TMP_19 TMP_20 TMP_22) in (let TMP_24 
\def (le_S_n TMP_16 TMP_17 TMP_23) in (let TMP_25 \def (le_S_n i d0 TMP_24) 
in (let TMP_26 \def (Bind Abbr) in (let TMP_27 \def (CHead d TMP_26 u) in 
(let H5 \def (drop_getl_trans_le i d0 TMP_25 c1 c h H3 TMP_27 H0) in (let 
TMP_28 \def (\lambda (e0: C).(\lambda (_: C).(drop i O c1 e0))) in (let 
TMP_30 \def (\lambda (e0: C).(\lambda (e1: C).(let TMP_29 \def (minus d0 i) 
in (drop h TMP_29 e0 e1)))) in (let TMP_33 \def (\lambda (_: C).(\lambda (e1: 
C).(let TMP_31 \def (Bind Abbr) in (let TMP_32 \def (CHead d TMP_31 u) in 
(clear e1 TMP_32))))) in (let TMP_34 \def (TLRef i) in (let TMP_35 \def 
(arity g c1 TMP_34 a0) in (let TMP_68 \def (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop i O c1 x0)).(\lambda (H7: (drop h (minus d0 i) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abbr) u))).(let TMP_36 \def 
(minus d0 i) in (let TMP_37 \def (\lambda (n: nat).(drop h n x0 x1)) in (let 
TMP_38 \def (S i) in (let TMP_39 \def (minus d0 TMP_38) in (let TMP_40 \def 
(S TMP_39) in (let TMP_41 \def (minus_x_Sy d0 i H4) in (let H9 \def (eq_ind 
nat TMP_36 TMP_37 H7 TMP_40 TMP_41) in (let TMP_42 \def (S i) in (let TMP_43 
\def (minus d0 TMP_42) in (let H10 \def (drop_clear_S x1 x0 h TMP_43 H9 Abbr 
d u H8) in (let TMP_49 \def (\lambda (c3: C).(let TMP_44 \def (Bind Abbr) in 
(let TMP_45 \def (S i) in (let TMP_46 \def (minus d0 TMP_45) in (let TMP_47 
\def (lift h TMP_46 u) in (let TMP_48 \def (CHead c3 TMP_44 TMP_47) in (clear 
x0 TMP_48))))))) in (let TMP_52 \def (\lambda (c3: C).(let TMP_50 \def (S i) 
in (let TMP_51 \def (minus d0 TMP_50) in (drop h TMP_51 c3 d)))) in (let 
TMP_53 \def (TLRef i) in (let TMP_54 \def (arity g c1 TMP_53 a0) in (let 
TMP_67 \def (\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abbr) 
(lift h (minus d0 (S i)) u)))).(\lambda (H12: (drop h (minus d0 (S i)) x 
d)).(let TMP_55 \def (S i) in (let TMP_56 \def (minus d0 TMP_55) in (let 
TMP_57 \def (lift h TMP_56 u) in (let TMP_58 \def (Bind Abbr) in (let TMP_59 
\def (S i) in (let TMP_60 \def (minus d0 TMP_59) in (let TMP_61 \def (lift h 
TMP_60 u) in (let TMP_62 \def (CHead x TMP_58 TMP_61) in (let TMP_63 \def 
(getl_intro i c1 TMP_62 x0 H6 H11) in (let TMP_64 \def (S i) in (let TMP_65 
\def (minus d0 TMP_64) in (let TMP_66 \def (H2 x h TMP_65 H12) in (arity_abbr 
g c1 x TMP_57 i TMP_63 a0 TMP_66)))))))))))))))) in (ex2_ind C TMP_49 TMP_52 
TMP_54 TMP_67 H10))))))))))))))))))))) in (let TMP_69 \def (ex3_2_ind C C 
TMP_28 TMP_30 TMP_33 TMP_35 TMP_68 H5) in (let TMP_70 \def (TLRef i) in (let 
TMP_71 \def (lift h d0 TMP_70) in (let TMP_72 \def (lift_lref_lt i h d0 H4) 
in (eq_ind_r T TMP_14 TMP_15 TMP_69 TMP_71 TMP_72))))))))))))))))))))))))))) 
in (let TMP_85 \def (\lambda (H4: (le d0 i)).(let TMP_74 \def (plus i h) in 
(let TMP_75 \def (TLRef TMP_74) in (let TMP_76 \def (\lambda (t0: T).(arity g 
c1 t0 a0)) in (let TMP_77 \def (plus i h) in (let TMP_78 \def (Bind Abbr) in 
(let TMP_79 \def (CHead d TMP_78 u) in (let TMP_80 \def (drop_getl_trans_ge i 
c1 c d0 h H3 TMP_79 H0 H4) in (let TMP_81 \def (arity_abbr g c1 d u TMP_77 
TMP_80 a0 H1) in (let TMP_82 \def (TLRef i) in (let TMP_83 \def (lift h d0 
TMP_82) in (let TMP_84 \def (lift_lref_ge i h d0 H4) in (eq_ind_r T TMP_75 
TMP_76 TMP_81 TMP_83 TMP_84))))))))))))) in (lt_le_e i d0 TMP_13 TMP_73 
TMP_85)))))))))))))))))) in (let TMP_162 \def (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abst) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u (asucc g 
a0))).(\lambda (H2: ((\forall (c1: C).(\forall (h: nat).(\forall (d0: 
nat).((drop h d0 c1 d) \to (arity g c1 (lift h d0 u) (asucc g 
a0)))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda 
(H3: (drop h d0 c1 c)).(let TMP_87 \def (TLRef i) in (let TMP_88 \def (lift h 
d0 TMP_87) in (let TMP_89 \def (arity g c1 TMP_88 a0) in (let TMP_149 \def 
(\lambda (H4: (lt i d0)).(let TMP_90 \def (TLRef i) in (let TMP_91 \def 
(\lambda (t0: T).(arity g c1 t0 a0)) in (let TMP_92 \def (S i) in (let TMP_93 
\def (S d0) in (let TMP_94 \def (S i) in (let TMP_95 \def (S TMP_94) in (let 
TMP_96 \def (S d0) in (let TMP_97 \def (S i) in (let TMP_98 \def (le_n_S 
TMP_97 d0 H4) in (let TMP_99 \def (le_S TMP_95 TMP_96 TMP_98) in (let TMP_100 
\def (le_S_n TMP_92 TMP_93 TMP_99) in (let TMP_101 \def (le_S_n i d0 TMP_100) 
in (let TMP_102 \def (Bind Abst) in (let TMP_103 \def (CHead d TMP_102 u) in 
(let H5 \def (drop_getl_trans_le i d0 TMP_101 c1 c h H3 TMP_103 H0) in (let 
TMP_104 \def (\lambda (e0: C).(\lambda (_: C).(drop i O c1 e0))) in (let 
TMP_106 \def (\lambda (e0: C).(\lambda (e1: C).(let TMP_105 \def (minus d0 i) 
in (drop h TMP_105 e0 e1)))) in (let TMP_109 \def (\lambda (_: C).(\lambda 
(e1: C).(let TMP_107 \def (Bind Abst) in (let TMP_108 \def (CHead d TMP_107 
u) in (clear e1 TMP_108))))) in (let TMP_110 \def (TLRef i) in (let TMP_111 
\def (arity g c1 TMP_110 a0) in (let TMP_144 \def (\lambda (x0: C).(\lambda 
(x1: C).(\lambda (H6: (drop i O c1 x0)).(\lambda (H7: (drop h (minus d0 i) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abst) u))).(let TMP_112 \def 
(minus d0 i) in (let TMP_113 \def (\lambda (n: nat).(drop h n x0 x1)) in (let 
TMP_114 \def (S i) in (let TMP_115 \def (minus d0 TMP_114) in (let TMP_116 
\def (S TMP_115) in (let TMP_117 \def (minus_x_Sy d0 i H4) in (let H9 \def 
(eq_ind nat TMP_112 TMP_113 H7 TMP_116 TMP_117) in (let TMP_118 \def (S i) in 
(let TMP_119 \def (minus d0 TMP_118) in (let H10 \def (drop_clear_S x1 x0 h 
TMP_119 H9 Abst d u H8) in (let TMP_125 \def (\lambda (c3: C).(let TMP_120 
\def (Bind Abst) in (let TMP_121 \def (S i) in (let TMP_122 \def (minus d0 
TMP_121) in (let TMP_123 \def (lift h TMP_122 u) in (let TMP_124 \def (CHead 
c3 TMP_120 TMP_123) in (clear x0 TMP_124))))))) in (let TMP_128 \def (\lambda 
(c3: C).(let TMP_126 \def (S i) in (let TMP_127 \def (minus d0 TMP_126) in 
(drop h TMP_127 c3 d)))) in (let TMP_129 \def (TLRef i) in (let TMP_130 \def 
(arity g c1 TMP_129 a0) in (let TMP_143 \def (\lambda (x: C).(\lambda (H11: 
(clear x0 (CHead x (Bind Abst) (lift h (minus d0 (S i)) u)))).(\lambda (H12: 
(drop h (minus d0 (S i)) x d)).(let TMP_131 \def (S i) in (let TMP_132 \def 
(minus d0 TMP_131) in (let TMP_133 \def (lift h TMP_132 u) in (let TMP_134 
\def (Bind Abst) in (let TMP_135 \def (S i) in (let TMP_136 \def (minus d0 
TMP_135) in (let TMP_137 \def (lift h TMP_136 u) in (let TMP_138 \def (CHead 
x TMP_134 TMP_137) in (let TMP_139 \def (getl_intro i c1 TMP_138 x0 H6 H11) 
in (let TMP_140 \def (S i) in (let TMP_141 \def (minus d0 TMP_140) in (let 
TMP_142 \def (H2 x h TMP_141 H12) in (arity_abst g c1 x TMP_133 i TMP_139 a0 
TMP_142)))))))))))))))) in (ex2_ind C TMP_125 TMP_128 TMP_130 TMP_143 
H10))))))))))))))))))))) in (let TMP_145 \def (ex3_2_ind C C TMP_104 TMP_106 
TMP_109 TMP_111 TMP_144 H5) in (let TMP_146 \def (TLRef i) in (let TMP_147 
\def (lift h d0 TMP_146) in (let TMP_148 \def (lift_lref_lt i h d0 H4) in 
(eq_ind_r T TMP_90 TMP_91 TMP_145 TMP_147 TMP_148))))))))))))))))))))))))))) 
in (let TMP_161 \def (\lambda (H4: (le d0 i)).(let TMP_150 \def (plus i h) in 
(let TMP_151 \def (TLRef TMP_150) in (let TMP_152 \def (\lambda (t0: 
T).(arity g c1 t0 a0)) in (let TMP_153 \def (plus i h) in (let TMP_154 \def 
(Bind Abst) in (let TMP_155 \def (CHead d TMP_154 u) in (let TMP_156 \def 
(drop_getl_trans_ge i c1 c d0 h H3 TMP_155 H0 H4) in (let TMP_157 \def 
(arity_abst g c1 d u TMP_153 TMP_156 a0 H1) in (let TMP_158 \def (TLRef i) in 
(let TMP_159 \def (lift h d0 TMP_158) in (let TMP_160 \def (lift_lref_ge i h 
d0 H4) in (eq_ind_r T TMP_151 TMP_152 TMP_157 TMP_159 TMP_160))))))))))))) in 
(lt_le_e i d0 TMP_89 TMP_149 TMP_161)))))))))))))))))) in (let TMP_188 \def 
(\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: 
((\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to 
(arity g c1 (lift h d u) a1))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda 
(_: (arity g (CHead c (Bind b) u) t0 a2)).(\lambda (H4: ((\forall (c1: 
C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 (CHead c (Bind b) u)) 
\to (arity g c1 (lift h d t0) a2))))))).(\lambda (c1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H5: (drop h d c1 c)).(let TMP_163 \def (Bind 
b) in (let TMP_164 \def (lift h d u) in (let TMP_165 \def (Bind b) in (let 
TMP_166 \def (s TMP_165 d) in (let TMP_167 \def (lift h TMP_166 t0) in (let 
TMP_168 \def (THead TMP_163 TMP_164 TMP_167) in (let TMP_169 \def (\lambda 
(t1: T).(arity g c1 t1 a2)) in (let TMP_170 \def (lift h d u) in (let TMP_171 
\def (H2 c1 h d H5) in (let TMP_172 \def (Bind b) in (let TMP_173 \def (s 
TMP_172 d) in (let TMP_174 \def (lift h TMP_173 t0) in (let TMP_175 \def 
(Bind b) in (let TMP_176 \def (lift h d u) in (let TMP_177 \def (CHead c1 
TMP_175 TMP_176) in (let TMP_178 \def (Bind b) in (let TMP_179 \def (s 
TMP_178 d) in (let TMP_180 \def (drop_skip_bind h d c1 c H5 b u) in (let 
TMP_181 \def (H4 TMP_177 h TMP_179 TMP_180) in (let TMP_182 \def (arity_bind 
g b H0 c1 TMP_170 a1 TMP_171 TMP_174 a2 TMP_181) in (let TMP_183 \def (Bind 
b) in (let TMP_184 \def (THead TMP_183 u t0) in (let TMP_185 \def (lift h d 
TMP_184) in (let TMP_186 \def (Bind b) in (let TMP_187 \def (lift_head 
TMP_186 u t0 h d) in (eq_ind_r T TMP_168 TMP_169 TMP_182 TMP_185 
TMP_187))))))))))))))))))))))))))))))))))))))))) in (let TMP_215 \def 
(\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u 
(asucc g a1))).(\lambda (H1: ((\forall (c1: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c1 c) \to (arity g c1 (lift h d u) (asucc g 
a1)))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c 
(Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 (CHead c (Bind Abst) u)) \to (arity g c1 
(lift h d t0) a2))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H4: (drop h d c1 c)).(let TMP_189 \def (Bind Abst) in (let 
TMP_190 \def (lift h d u) in (let TMP_191 \def (Bind Abst) in (let TMP_192 
\def (s TMP_191 d) in (let TMP_193 \def (lift h TMP_192 t0) in (let TMP_194 
\def (THead TMP_189 TMP_190 TMP_193) in (let TMP_196 \def (\lambda (t1: 
T).(let TMP_195 \def (AHead a1 a2) in (arity g c1 t1 TMP_195))) in (let 
TMP_197 \def (lift h d u) in (let TMP_198 \def (H1 c1 h d H4) in (let TMP_199 
\def (Bind Abst) in (let TMP_200 \def (s TMP_199 d) in (let TMP_201 \def 
(lift h TMP_200 t0) in (let TMP_202 \def (Bind Abst) in (let TMP_203 \def 
(lift h d u) in (let TMP_204 \def (CHead c1 TMP_202 TMP_203) in (let TMP_205 
\def (Bind Abst) in (let TMP_206 \def (s TMP_205 d) in (let TMP_207 \def 
(drop_skip_bind h d c1 c H4 Abst u) in (let TMP_208 \def (H3 TMP_204 h 
TMP_206 TMP_207) in (let TMP_209 \def (arity_head g c1 TMP_197 a1 TMP_198 
TMP_201 a2 TMP_208) in (let TMP_210 \def (Bind Abst) in (let TMP_211 \def 
(THead TMP_210 u t0) in (let TMP_212 \def (lift h d TMP_211) in (let TMP_213 
\def (Bind Abst) in (let TMP_214 \def (lift_head TMP_213 u t0 h d) in 
(eq_ind_r T TMP_194 TMP_196 TMP_209 TMP_212 
TMP_214))))))))))))))))))))))))))))))))))))))) in (let TMP_237 \def (\lambda 
(c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u 
a1)).(\lambda (H1: ((\forall (c1: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c1 c) \to (arity g c1 (lift h d u) a1))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g c t0 (AHead a1 a2))).(\lambda (H3: 
((\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to 
(arity g c1 (lift h d t0) (AHead a1 a2)))))))).(\lambda (c1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H4: (drop h d c1 c)).(let TMP_216 \def (Flat 
Appl) in (let TMP_217 \def (lift h d u) in (let TMP_218 \def (Flat Appl) in 
(let TMP_219 \def (s TMP_218 d) in (let TMP_220 \def (lift h TMP_219 t0) in 
(let TMP_221 \def (THead TMP_216 TMP_217 TMP_220) in (let TMP_222 \def 
(\lambda (t1: T).(arity g c1 t1 a2)) in (let TMP_223 \def (lift h d u) in 
(let TMP_224 \def (H1 c1 h d H4) in (let TMP_225 \def (Flat Appl) in (let 
TMP_226 \def (s TMP_225 d) in (let TMP_227 \def (lift h TMP_226 t0) in (let 
TMP_228 \def (Flat Appl) in (let TMP_229 \def (s TMP_228 d) in (let TMP_230 
\def (H3 c1 h TMP_229 H4) in (let TMP_231 \def (arity_appl g c1 TMP_223 a1 
TMP_224 TMP_227 a2 TMP_230) in (let TMP_232 \def (Flat Appl) in (let TMP_233 
\def (THead TMP_232 u t0) in (let TMP_234 \def (lift h d TMP_233) in (let 
TMP_235 \def (Flat Appl) in (let TMP_236 \def (lift_head TMP_235 u t0 h d) in 
(eq_ind_r T TMP_221 TMP_222 TMP_231 TMP_234 
TMP_236))))))))))))))))))))))))))))))))))) in (let TMP_259 \def (\lambda (c: 
C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: (arity g c u (asucc g 
a0))).(\lambda (H1: ((\forall (c1: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c1 c) \to (arity g c1 (lift h d u) (asucc g 
a0)))))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 a0)).(\lambda (H3: 
((\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to 
(arity g c1 (lift h d t0) a0))))))).(\lambda (c1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H4: (drop h d c1 c)).(let TMP_238 \def (Flat 
Cast) in (let TMP_239 \def (lift h d u) in (let TMP_240 \def (Flat Cast) in 
(let TMP_241 \def (s TMP_240 d) in (let TMP_242 \def (lift h TMP_241 t0) in 
(let TMP_243 \def (THead TMP_238 TMP_239 TMP_242) in (let TMP_244 \def 
(\lambda (t1: T).(arity g c1 t1 a0)) in (let TMP_245 \def (lift h d u) in 
(let TMP_246 \def (H1 c1 h d H4) in (let TMP_247 \def (Flat Cast) in (let 
TMP_248 \def (s TMP_247 d) in (let TMP_249 \def (lift h TMP_248 t0) in (let 
TMP_250 \def (Flat Cast) in (let TMP_251 \def (s TMP_250 d) in (let TMP_252 
\def (H3 c1 h TMP_251 H4) in (let TMP_253 \def (arity_cast g c1 TMP_245 a0 
TMP_246 TMP_249 TMP_252) in (let TMP_254 \def (Flat Cast) in (let TMP_255 
\def (THead TMP_254 u t0) in (let TMP_256 \def (lift h d TMP_255) in (let 
TMP_257 \def (Flat Cast) in (let TMP_258 \def (lift_head TMP_257 u t0 h d) in 
(eq_ind_r T TMP_243 TMP_244 TMP_253 TMP_256 
TMP_258)))))))))))))))))))))))))))))))))) in (let TMP_262 \def (\lambda (c: 
C).(\lambda (t0: T).(\lambda (a1: A).(\lambda (_: (arity g c t0 a1)).(\lambda 
(H1: ((\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) 
\to (arity g c1 (lift h d t0) a1))))))).(\lambda (a2: A).(\lambda (H2: (leq g 
a1 a2)).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H3: 
(drop h d c1 c)).(let TMP_260 \def (lift h d t0) in (let TMP_261 \def (H1 c1 
h d H3) in (arity_repl g c1 TMP_260 a1 TMP_261 a2 H2)))))))))))))) in 
(arity_ind g TMP_2 TMP_10 TMP_86 TMP_162 TMP_188 TMP_215 TMP_237 TMP_259 
TMP_262 c2 t a H)))))))))))))).

theorem arity_mono:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a1: A).((arity g c 
t a1) \to (\forall (a2: A).((arity g c t a2) \to (leq g a1 a2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a1: A).(\lambda (H: 
(arity g c t a1)).(let TMP_1 \def (\lambda (c0: C).(\lambda (t0: T).(\lambda 
(a: A).(\forall (a2: A).((arity g c0 t0 a2) \to (leq g a a2)))))) in (let 
TMP_4 \def (\lambda (c0: C).(\lambda (n: nat).(\lambda (a2: A).(\lambda (H0: 
(arity g c0 (TSort n) a2)).(let TMP_2 \def (ASort O n) in (let TMP_3 \def 
(arity_gen_sort g c0 n a2 H0) in (leq_sym g a2 TMP_2 TMP_3))))))) in (let 
TMP_92 \def (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (a: 
A).(\lambda (_: (arity g d u a)).(\lambda (H2: ((\forall (a2: A).((arity g d 
u a2) \to (leq g a a2))))).(\lambda (a2: A).(\lambda (H3: (arity g c0 (TLRef 
i) a2)).(let H4 \def (arity_gen_lref g c0 i a2 H3) in (let TMP_7 \def 
(\lambda (d0: C).(\lambda (u0: T).(let TMP_5 \def (Bind Abbr) in (let TMP_6 
\def (CHead d0 TMP_5 u0) in (getl i c0 TMP_6))))) in (let TMP_8 \def (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 a2))) in (let TMP_9 \def (ex2_2 C T 
TMP_7 TMP_8) in (let TMP_12 \def (\lambda (d0: C).(\lambda (u0: T).(let 
TMP_10 \def (Bind Abst) in (let TMP_11 \def (CHead d0 TMP_10 u0) in (getl i 
c0 TMP_11))))) in (let TMP_14 \def (\lambda (d0: C).(\lambda (u0: T).(let 
TMP_13 \def (asucc g a2) in (arity g d0 u0 TMP_13)))) in (let TMP_15 \def 
(ex2_2 C T TMP_12 TMP_14) in (let TMP_16 \def (leq g a a2) in (let TMP_62 
\def (\lambda (H5: (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 
(CHead d0 (Bind Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
a2))))).(let TMP_19 \def (\lambda (d0: C).(\lambda (u0: T).(let TMP_17 \def 
(Bind Abbr) in (let TMP_18 \def (CHead d0 TMP_17 u0) in (getl i c0 
TMP_18))))) in (let TMP_20 \def (\lambda (d0: C).(\lambda (u0: T).(arity g d0 
u0 a2))) in (let TMP_21 \def (leq g a a2) in (let TMP_61 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H6: (getl i c0 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H7: (arity g x0 x1 a2)).(let TMP_22 \def (Bind Abbr) in (let 
TMP_23 \def (CHead d TMP_22 u) in (let TMP_24 \def (\lambda (c1: C).(getl i 
c0 c1)) in (let TMP_25 \def (Bind Abbr) in (let TMP_26 \def (CHead x0 TMP_25 
x1) in (let TMP_27 \def (Bind Abbr) in (let TMP_28 \def (CHead d TMP_27 u) in 
(let TMP_29 \def (Bind Abbr) in (let TMP_30 \def (CHead x0 TMP_29 x1) in (let 
TMP_31 \def (getl_mono c0 TMP_28 i H0 TMP_30 H6) in (let H8 \def (eq_ind C 
TMP_23 TMP_24 H0 TMP_26 TMP_31) in (let TMP_32 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) in (let 
TMP_33 \def (Bind Abbr) in (let TMP_34 \def (CHead d TMP_33 u) in (let TMP_35 
\def (Bind Abbr) in (let TMP_36 \def (CHead x0 TMP_35 x1) in (let TMP_37 \def 
(Bind Abbr) in (let TMP_38 \def (CHead d TMP_37 u) in (let TMP_39 \def (Bind 
Abbr) in (let TMP_40 \def (CHead x0 TMP_39 x1) in (let TMP_41 \def (getl_mono 
c0 TMP_38 i H0 TMP_40 H6) in (let H9 \def (f_equal C C TMP_32 TMP_34 TMP_36 
TMP_41) in (let TMP_42 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_43 \def (Bind 
Abbr) in (let TMP_44 \def (CHead d TMP_43 u) in (let TMP_45 \def (Bind Abbr) 
in (let TMP_46 \def (CHead x0 TMP_45 x1) in (let TMP_47 \def (Bind Abbr) in 
(let TMP_48 \def (CHead d TMP_47 u) in (let TMP_49 \def (Bind Abbr) in (let 
TMP_50 \def (CHead x0 TMP_49 x1) in (let TMP_51 \def (getl_mono c0 TMP_48 i 
H0 TMP_50 H6) in (let H10 \def (f_equal C T TMP_42 TMP_44 TMP_46 TMP_51) in 
(let TMP_60 \def (\lambda (H11: (eq C d x0)).(let TMP_54 \def (\lambda (t0: 
T).(let TMP_52 \def (Bind Abbr) in (let TMP_53 \def (CHead x0 TMP_52 t0) in 
(getl i c0 TMP_53)))) in (let H12 \def (eq_ind_r T x1 TMP_54 H8 u H10) in 
(let TMP_55 \def (\lambda (t0: T).(arity g x0 t0 a2)) in (let H13 \def 
(eq_ind_r T x1 TMP_55 H7 u H10) in (let TMP_58 \def (\lambda (c1: C).(let 
TMP_56 \def (Bind Abbr) in (let TMP_57 \def (CHead c1 TMP_56 u) in (getl i c0 
TMP_57)))) in (let H14 \def (eq_ind_r C x0 TMP_58 H12 d H11) in (let TMP_59 
\def (\lambda (c1: C).(arity g c1 u a2)) in (let H15 \def (eq_ind_r C x0 
TMP_59 H13 d H11) in (H2 a2 H15)))))))))) in (TMP_60 
H9))))))))))))))))))))))))))))))))))))))) in (ex2_2_ind C T TMP_19 TMP_20 
TMP_21 TMP_61 H5)))))) in (let TMP_91 \def (\lambda (H5: (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2)))))).(let TMP_65 \def 
(\lambda (d0: C).(\lambda (u0: T).(let TMP_63 \def (Bind Abst) in (let TMP_64 
\def (CHead d0 TMP_63 u0) in (getl i c0 TMP_64))))) in (let TMP_67 \def 
(\lambda (d0: C).(\lambda (u0: T).(let TMP_66 \def (asucc g a2) in (arity g 
d0 u0 TMP_66)))) in (let TMP_68 \def (leq g a a2) in (let TMP_90 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 (CHead x0 (Bind 
Abst) x1))).(\lambda (_: (arity g x0 x1 (asucc g a2))).(let TMP_69 \def (Bind 
Abbr) in (let TMP_70 \def (CHead d TMP_69 u) in (let TMP_71 \def (\lambda 
(c1: C).(getl i c0 c1)) in (let TMP_72 \def (Bind Abst) in (let TMP_73 \def 
(CHead x0 TMP_72 x1) in (let TMP_74 \def (Bind Abbr) in (let TMP_75 \def 
(CHead d TMP_74 u) in (let TMP_76 \def (Bind Abst) in (let TMP_77 \def (CHead 
x0 TMP_76 x1) in (let TMP_78 \def (getl_mono c0 TMP_75 i H0 TMP_77 H6) in 
(let H8 \def (eq_ind C TMP_70 TMP_71 H0 TMP_73 TMP_78) in (let TMP_79 \def 
(Bind Abbr) in (let TMP_80 \def (CHead d TMP_79 u) in (let TMP_81 \def 
(\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_82 \def (Bind Abst) in (let TMP_83 \def 
(CHead x0 TMP_82 x1) in (let TMP_84 \def (Bind Abbr) in (let TMP_85 \def 
(CHead d TMP_84 u) in (let TMP_86 \def (Bind Abst) in (let TMP_87 \def (CHead 
x0 TMP_86 x1) in (let TMP_88 \def (getl_mono c0 TMP_85 i H0 TMP_87 H6) in 
(let H9 \def (eq_ind C TMP_80 TMP_81 I TMP_83 TMP_88) in (let TMP_89 \def 
(leq g a a2) in (False_ind TMP_89 H9)))))))))))))))))))))))))))) in 
(ex2_2_ind C T TMP_65 TMP_67 TMP_68 TMP_90 H5)))))) in (or_ind TMP_9 TMP_15 
TMP_16 TMP_62 TMP_91 H4))))))))))))))))))))) in (let TMP_184 \def (\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c0 (CHead d (Bind Abst) u))).(\lambda (a: A).(\lambda (_: (arity g d u 
(asucc g a))).(\lambda (H2: ((\forall (a2: A).((arity g d u a2) \to (leq g 
(asucc g a) a2))))).(\lambda (a2: A).(\lambda (H3: (arity g c0 (TLRef i) 
a2)).(let H4 \def (arity_gen_lref g c0 i a2 H3) in (let TMP_95 \def (\lambda 
(d0: C).(\lambda (u0: T).(let TMP_93 \def (Bind Abbr) in (let TMP_94 \def 
(CHead d0 TMP_93 u0) in (getl i c0 TMP_94))))) in (let TMP_96 \def (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 a2))) in (let TMP_97 \def (ex2_2 C T 
TMP_95 TMP_96) in (let TMP_100 \def (\lambda (d0: C).(\lambda (u0: T).(let 
TMP_98 \def (Bind Abst) in (let TMP_99 \def (CHead d0 TMP_98 u0) in (getl i 
c0 TMP_99))))) in (let TMP_102 \def (\lambda (d0: C).(\lambda (u0: T).(let 
TMP_101 \def (asucc g a2) in (arity g d0 u0 TMP_101)))) in (let TMP_103 \def 
(ex2_2 C T TMP_100 TMP_102) in (let TMP_104 \def (leq g a a2) in (let TMP_132 
\def (\lambda (H5: (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 
(CHead d0 (Bind Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
a2))))).(let TMP_107 \def (\lambda (d0: C).(\lambda (u0: T).(let TMP_105 \def 
(Bind Abbr) in (let TMP_106 \def (CHead d0 TMP_105 u0) in (getl i c0 
TMP_106))))) in (let TMP_108 \def (\lambda (d0: C).(\lambda (u0: T).(arity g 
d0 u0 a2))) in (let TMP_109 \def (leq g a a2) in (let TMP_131 \def (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (arity g x0 x1 a2)).(let TMP_110 \def (Bind Abst) in (let 
TMP_111 \def (CHead d TMP_110 u) in (let TMP_112 \def (\lambda (c1: C).(getl 
i c0 c1)) in (let TMP_113 \def (Bind Abbr) in (let TMP_114 \def (CHead x0 
TMP_113 x1) in (let TMP_115 \def (Bind Abst) in (let TMP_116 \def (CHead d 
TMP_115 u) in (let TMP_117 \def (Bind Abbr) in (let TMP_118 \def (CHead x0 
TMP_117 x1) in (let TMP_119 \def (getl_mono c0 TMP_116 i H0 TMP_118 H6) in 
(let H8 \def (eq_ind C TMP_111 TMP_112 H0 TMP_114 TMP_119) in (let TMP_120 
\def (Bind Abst) in (let TMP_121 \def (CHead d TMP_120 u) in (let TMP_122 
\def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ 
k _) \Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_123 \def (Bind Abbr) in (let TMP_124 
\def (CHead x0 TMP_123 x1) in (let TMP_125 \def (Bind Abst) in (let TMP_126 
\def (CHead d TMP_125 u) in (let TMP_127 \def (Bind Abbr) in (let TMP_128 
\def (CHead x0 TMP_127 x1) in (let TMP_129 \def (getl_mono c0 TMP_126 i H0 
TMP_128 H6) in (let H9 \def (eq_ind C TMP_121 TMP_122 I TMP_124 TMP_129) in 
(let TMP_130 \def (leq g a a2) in (False_ind TMP_130 
H9)))))))))))))))))))))))))))) in (ex2_2_ind C T TMP_107 TMP_108 TMP_109 
TMP_131 H5)))))) in (let TMP_183 \def (\lambda (H5: (ex2_2 C T (\lambda (d0: 
C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda (d0: 
C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2)))))).(let TMP_135 \def 
(\lambda (d0: C).(\lambda (u0: T).(let TMP_133 \def (Bind Abst) in (let 
TMP_134 \def (CHead d0 TMP_133 u0) in (getl i c0 TMP_134))))) in (let TMP_137 
\def (\lambda (d0: C).(\lambda (u0: T).(let TMP_136 \def (asucc g a2) in 
(arity g d0 u0 TMP_136)))) in (let TMP_138 \def (leq g a a2) in (let TMP_182 
\def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 (CHead x0 
(Bind Abst) x1))).(\lambda (H7: (arity g x0 x1 (asucc g a2))).(let TMP_139 
\def (Bind Abst) in (let TMP_140 \def (CHead d TMP_139 u) in (let TMP_141 
\def (\lambda (c1: C).(getl i c0 c1)) in (let TMP_142 \def (Bind Abst) in 
(let TMP_143 \def (CHead x0 TMP_142 x1) in (let TMP_144 \def (Bind Abst) in 
(let TMP_145 \def (CHead d TMP_144 u) in (let TMP_146 \def (Bind Abst) in 
(let TMP_147 \def (CHead x0 TMP_146 x1) in (let TMP_148 \def (getl_mono c0 
TMP_145 i H0 TMP_147 H6) in (let H8 \def (eq_ind C TMP_140 TMP_141 H0 TMP_143 
TMP_148) in (let TMP_149 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_150 \def (Bind 
Abst) in (let TMP_151 \def (CHead d TMP_150 u) in (let TMP_152 \def (Bind 
Abst) in (let TMP_153 \def (CHead x0 TMP_152 x1) in (let TMP_154 \def (Bind 
Abst) in (let TMP_155 \def (CHead d TMP_154 u) in (let TMP_156 \def (Bind 
Abst) in (let TMP_157 \def (CHead x0 TMP_156 x1) in (let TMP_158 \def 
(getl_mono c0 TMP_155 i H0 TMP_157 H6) in (let H9 \def (f_equal C C TMP_149 
TMP_151 TMP_153 TMP_158) in (let TMP_159 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_160 
\def (Bind Abst) in (let TMP_161 \def (CHead d TMP_160 u) in (let TMP_162 
\def (Bind Abst) in (let TMP_163 \def (CHead x0 TMP_162 x1) in (let TMP_164 
\def (Bind Abst) in (let TMP_165 \def (CHead d TMP_164 u) in (let TMP_166 
\def (Bind Abst) in (let TMP_167 \def (CHead x0 TMP_166 x1) in (let TMP_168 
\def (getl_mono c0 TMP_165 i H0 TMP_167 H6) in (let H10 \def (f_equal C T 
TMP_159 TMP_161 TMP_163 TMP_168) in (let TMP_181 \def (\lambda (H11: (eq C d 
x0)).(let TMP_171 \def (\lambda (t0: T).(let TMP_169 \def (Bind Abst) in (let 
TMP_170 \def (CHead x0 TMP_169 t0) in (getl i c0 TMP_170)))) in (let H12 \def 
(eq_ind_r T x1 TMP_171 H8 u H10) in (let TMP_173 \def (\lambda (t0: T).(let 
TMP_172 \def (asucc g a2) in (arity g x0 t0 TMP_172))) in (let H13 \def 
(eq_ind_r T x1 TMP_173 H7 u H10) in (let TMP_176 \def (\lambda (c1: C).(let 
TMP_174 \def (Bind Abst) in (let TMP_175 \def (CHead c1 TMP_174 u) in (getl i 
c0 TMP_175)))) in (let H14 \def (eq_ind_r C x0 TMP_176 H12 d H11) in (let 
TMP_178 \def (\lambda (c1: C).(let TMP_177 \def (asucc g a2) in (arity g c1 u 
TMP_177))) in (let H15 \def (eq_ind_r C x0 TMP_178 H13 d H11) in (let TMP_179 
\def (asucc g a2) in (let TMP_180 \def (H2 TMP_179 H15) in (asucc_inj g a a2 
TMP_180)))))))))))) in (TMP_181 H9))))))))))))))))))))))))))))))))))))))) in 
(ex2_2_ind C T TMP_135 TMP_137 TMP_138 TMP_182 H5)))))) in (or_ind TMP_97 
TMP_103 TMP_104 TMP_132 TMP_183 H4))))))))))))))))))))) in (let TMP_191 \def 
(\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c0: C).(\lambda 
(u: T).(\lambda (a2: A).(\lambda (_: (arity g c0 u a2)).(\lambda (_: 
((\forall (a3: A).((arity g c0 u a3) \to (leq g a2 a3))))).(\lambda (t0: 
T).(\lambda (a3: A).(\lambda (_: (arity g (CHead c0 (Bind b) u) t0 
a3)).(\lambda (H4: ((\forall (a4: A).((arity g (CHead c0 (Bind b) u) t0 a4) 
\to (leq g a3 a4))))).(\lambda (a0: A).(\lambda (H5: (arity g c0 (THead (Bind 
b) u t0) a0)).(let H6 \def (arity_gen_bind b H0 g c0 u t0 a0 H5) in (let 
TMP_185 \def (\lambda (a4: A).(arity g c0 u a4)) in (let TMP_188 \def 
(\lambda (_: A).(let TMP_186 \def (Bind b) in (let TMP_187 \def (CHead c0 
TMP_186 u) in (arity g TMP_187 t0 a0)))) in (let TMP_189 \def (leq g a3 a0) 
in (let TMP_190 \def (\lambda (x: A).(\lambda (_: (arity g c0 u x)).(\lambda 
(H8: (arity g (CHead c0 (Bind b) u) t0 a0)).(H4 a0 H8)))) in (ex2_ind A 
TMP_185 TMP_188 TMP_189 TMP_190 H6))))))))))))))))))) in (let TMP_210 \def 
(\lambda (c0: C).(\lambda (u: T).(\lambda (a2: A).(\lambda (_: (arity g c0 u 
(asucc g a2))).(\lambda (H1: ((\forall (a3: A).((arity g c0 u a3) \to (leq g 
(asucc g a2) a3))))).(\lambda (t0: T).(\lambda (a3: A).(\lambda (_: (arity g 
(CHead c0 (Bind Abst) u) t0 a3)).(\lambda (H3: ((\forall (a4: A).((arity g 
(CHead c0 (Bind Abst) u) t0 a4) \to (leq g a3 a4))))).(\lambda (a0: 
A).(\lambda (H4: (arity g c0 (THead (Bind Abst) u t0) a0)).(let H5 \def 
(arity_gen_abst g c0 u t0 a0 H4) in (let TMP_193 \def (\lambda (a4: 
A).(\lambda (a5: A).(let TMP_192 \def (AHead a4 a5) in (eq A a0 TMP_192)))) 
in (let TMP_195 \def (\lambda (a4: A).(\lambda (_: A).(let TMP_194 \def 
(asucc g a4) in (arity g c0 u TMP_194)))) in (let TMP_198 \def (\lambda (_: 
A).(\lambda (a5: A).(let TMP_196 \def (Bind Abst) in (let TMP_197 \def (CHead 
c0 TMP_196 u) in (arity g TMP_197 t0 a5))))) in (let TMP_199 \def (AHead a2 
a3) in (let TMP_200 \def (leq g TMP_199 a0) in (let TMP_209 \def (\lambda 
(x0: A).(\lambda (x1: A).(\lambda (H6: (eq A a0 (AHead x0 x1))).(\lambda (H7: 
(arity g c0 u (asucc g x0))).(\lambda (H8: (arity g (CHead c0 (Bind Abst) u) 
t0 x1)).(let TMP_201 \def (AHead x0 x1) in (let TMP_203 \def (\lambda (a: 
A).(let TMP_202 \def (AHead a2 a3) in (leq g TMP_202 a))) in (let TMP_204 
\def (asucc g x0) in (let TMP_205 \def (H1 TMP_204 H7) in (let TMP_206 \def 
(asucc_inj g a2 x0 TMP_205) in (let TMP_207 \def (H3 x1 H8) in (let TMP_208 
\def (leq_head g a2 x0 TMP_206 a3 x1 TMP_207) in (eq_ind_r A TMP_201 TMP_203 
TMP_208 a0 H6))))))))))))) in (ex3_2_ind A A TMP_193 TMP_195 TMP_198 TMP_200 
TMP_209 H5))))))))))))))))))) in (let TMP_218 \def (\lambda (c0: C).(\lambda 
(u: T).(\lambda (a2: A).(\lambda (_: (arity g c0 u a2)).(\lambda (_: 
((\forall (a3: A).((arity g c0 u a3) \to (leq g a2 a3))))).(\lambda (t0: 
T).(\lambda (a3: A).(\lambda (_: (arity g c0 t0 (AHead a2 a3))).(\lambda (H3: 
((\forall (a4: A).((arity g c0 t0 a4) \to (leq g (AHead a2 a3) 
a4))))).(\lambda (a0: A).(\lambda (H4: (arity g c0 (THead (Flat Appl) u t0) 
a0)).(let H5 \def (arity_gen_appl g c0 u t0 a0 H4) in (let TMP_211 \def 
(\lambda (a4: A).(arity g c0 u a4)) in (let TMP_213 \def (\lambda (a4: 
A).(let TMP_212 \def (AHead a4 a0) in (arity g c0 t0 TMP_212))) in (let 
TMP_214 \def (leq g a3 a0) in (let TMP_217 \def (\lambda (x: A).(\lambda (_: 
(arity g c0 u x)).(\lambda (H7: (arity g c0 t0 (AHead x a0))).(let TMP_215 
\def (AHead x a0) in (let TMP_216 \def (H3 TMP_215 H7) in (ahead_inj_snd g a2 
a3 x a0 TMP_216)))))) in (ex2_ind A TMP_211 TMP_213 TMP_214 TMP_217 
H5))))))))))))))))) in (let TMP_224 \def (\lambda (c0: C).(\lambda (u: 
T).(\lambda (a: A).(\lambda (_: (arity g c0 u (asucc g a))).(\lambda (_: 
((\forall (a2: A).((arity g c0 u a2) \to (leq g (asucc g a) a2))))).(\lambda 
(t0: T).(\lambda (_: (arity g c0 t0 a)).(\lambda (H3: ((\forall (a2: 
A).((arity g c0 t0 a2) \to (leq g a a2))))).(\lambda (a2: A).(\lambda (H4: 
(arity g c0 (THead (Flat Cast) u t0) a2)).(let H5 \def (arity_gen_cast g c0 u 
t0 a2 H4) in (let TMP_219 \def (asucc g a2) in (let TMP_220 \def (arity g c0 
u TMP_219) in (let TMP_221 \def (arity g c0 t0 a2) in (let TMP_222 \def (leq 
g a a2) in (let TMP_223 \def (\lambda (_: (arity g c0 u (asucc g 
a2))).(\lambda (H7: (arity g c0 t0 a2)).(H3 a2 H7))) in (land_ind TMP_220 
TMP_221 TMP_222 TMP_223 H5))))))))))))))))) in (let TMP_227 \def (\lambda 
(c0: C).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 
a2)).(\lambda (H1: ((\forall (a3: A).((arity g c0 t0 a3) \to (leq g a2 
a3))))).(\lambda (a3: A).(\lambda (H2: (leq g a2 a3)).(\lambda (a0: 
A).(\lambda (H3: (arity g c0 t0 a0)).(let TMP_225 \def (leq_sym g a2 a3 H2) 
in (let TMP_226 \def (H1 a0 H3) in (leq_trans g a3 a2 TMP_225 a0 
TMP_226)))))))))))) in (arity_ind g TMP_1 TMP_4 TMP_92 TMP_184 TMP_191 
TMP_210 TMP_218 TMP_224 TMP_227 c t a1 H)))))))))))))).

theorem arity_repellent:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (t: T).(\forall (a1: 
A).((arity g (CHead c (Bind Abst) w) t a1) \to (\forall (a2: A).((arity g c 
(THead (Bind Abst) w t) a2) \to ((leq g a1 a2) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (t: T).(\lambda (a1: 
A).(\lambda (H: (arity g (CHead c (Bind Abst) w) t a1)).(\lambda (a2: 
A).(\lambda (H0: (arity g c (THead (Bind Abst) w t) a2)).(\lambda (H1: (leq g 
a1 a2)).(\lambda (P: Prop).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def 
(CHead c TMP_1 w) in (let H_y \def (arity_repl g TMP_2 t a1 H a2 H1) in (let 
H2 \def (arity_gen_abst g c w t a2 H0) in (let TMP_4 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_3 \def (AHead a3 a4) in (eq A a2 TMP_3)))) in 
(let TMP_6 \def (\lambda (a3: A).(\lambda (_: A).(let TMP_5 \def (asucc g a3) 
in (arity g c w TMP_5)))) in (let TMP_9 \def (\lambda (_: A).(\lambda (a4: 
A).(let TMP_7 \def (Bind Abst) in (let TMP_8 \def (CHead c TMP_7 w) in (arity 
g TMP_8 t a4))))) in (let TMP_18 \def (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (eq A a2 (AHead x0 x1))).(\lambda (_: (arity g c w (asucc g 
x0))).(\lambda (H5: (arity g (CHead c (Bind Abst) w) t x1)).(let TMP_12 \def 
(\lambda (a: A).(let TMP_10 \def (Bind Abst) in (let TMP_11 \def (CHead c 
TMP_10 w) in (arity g TMP_11 t a)))) in (let TMP_13 \def (AHead x0 x1) in 
(let H6 \def (eq_ind A a2 TMP_12 H_y TMP_13 H3) in (let TMP_14 \def (Bind 
Abst) in (let TMP_15 \def (CHead c TMP_14 w) in (let TMP_16 \def (AHead x0 
x1) in (let TMP_17 \def (arity_mono g TMP_15 t TMP_16 H6 x1 H5) in 
(leq_ahead_false_2 g x1 x0 TMP_17 P))))))))))))) in (ex3_2_ind A A TMP_4 
TMP_6 TMP_9 P TMP_18 H2)))))))))))))))))).

theorem arity_appls_cast:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (vs: 
TList).(\forall (a: A).((arity g c (THeads (Flat Appl) vs u) (asucc g a)) \to 
((arity g c (THeads (Flat Appl) vs t) a) \to (arity g c (THeads (Flat Appl) 
vs (THead (Flat Cast) u t)) a))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (vs: 
TList).(let TMP_5 \def (\lambda (t0: TList).(\forall (a: A).((arity g c 
(THeads (Flat Appl) t0 u) (asucc g a)) \to ((arity g c (THeads (Flat Appl) t0 
t) a) \to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Flat Cast) in (let 
TMP_3 \def (THead TMP_2 u t) in (let TMP_4 \def (THeads TMP_1 t0 TMP_3) in 
(arity g c TMP_4 a))))))))) in (let TMP_6 \def (\lambda (a: A).(\lambda (H: 
(arity g c u (asucc g a))).(\lambda (H0: (arity g c t a)).(arity_cast g c u a 
H t H0)))) in (let TMP_68 \def (\lambda (t0: T).(\lambda (t1: TList).(\lambda 
(H: ((\forall (a: A).((arity g c (THeads (Flat Appl) t1 u) (asucc g a)) \to 
((arity g c (THeads (Flat Appl) t1 t) a) \to (arity g c (THeads (Flat Appl) 
t1 (THead (Flat Cast) u t)) a)))))).(\lambda (a: A).(\lambda (H0: (arity g c 
(THead (Flat Appl) t0 (THeads (Flat Appl) t1 u)) (asucc g a))).(\lambda (H1: 
(arity g c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 t)) a)).(let TMP_7 
\def (Flat Appl) in (let TMP_8 \def (THeads TMP_7 t1 t) in (let H2 \def 
(arity_gen_appl g c t0 TMP_8 a H1) in (let TMP_9 \def (\lambda (a1: A).(arity 
g c t0 a1)) in (let TMP_13 \def (\lambda (a1: A).(let TMP_10 \def (Flat Appl) 
in (let TMP_11 \def (THeads TMP_10 t1 t) in (let TMP_12 \def (AHead a1 a) in 
(arity g c TMP_11 TMP_12))))) in (let TMP_14 \def (Flat Appl) in (let TMP_15 
\def (Flat Appl) in (let TMP_16 \def (Flat Cast) in (let TMP_17 \def (THead 
TMP_16 u t) in (let TMP_18 \def (THeads TMP_15 t1 TMP_17) in (let TMP_19 \def 
(THead TMP_14 t0 TMP_18) in (let TMP_20 \def (arity g c TMP_19 a) in (let 
TMP_67 \def (\lambda (x: A).(\lambda (H3: (arity g c t0 x)).(\lambda (H4: 
(arity g c (THeads (Flat Appl) t1 t) (AHead x a))).(let TMP_21 \def (Flat 
Appl) in (let TMP_22 \def (THeads TMP_21 t1 u) in (let TMP_23 \def (asucc g 
a) in (let H5 \def (arity_gen_appl g c t0 TMP_22 TMP_23 H0) in (let TMP_24 
\def (\lambda (a1: A).(arity g c t0 a1)) in (let TMP_29 \def (\lambda (a1: 
A).(let TMP_25 \def (Flat Appl) in (let TMP_26 \def (THeads TMP_25 t1 u) in 
(let TMP_27 \def (asucc g a) in (let TMP_28 \def (AHead a1 TMP_27) in (arity 
g c TMP_26 TMP_28)))))) in (let TMP_30 \def (Flat Appl) in (let TMP_31 \def 
(Flat Appl) in (let TMP_32 \def (Flat Cast) in (let TMP_33 \def (THead TMP_32 
u t) in (let TMP_34 \def (THeads TMP_31 t1 TMP_33) in (let TMP_35 \def (THead 
TMP_30 t0 TMP_34) in (let TMP_36 \def (arity g c TMP_35 a) in (let TMP_66 
\def (\lambda (x0: A).(\lambda (H6: (arity g c t0 x0)).(\lambda (H7: (arity g 
c (THeads (Flat Appl) t1 u) (AHead x0 (asucc g a)))).(let TMP_37 \def (Flat 
Appl) in (let TMP_38 \def (Flat Cast) in (let TMP_39 \def (THead TMP_38 u t) 
in (let TMP_40 \def (THeads TMP_37 t1 TMP_39) in (let TMP_41 \def (AHead x a) 
in (let TMP_42 \def (Flat Appl) in (let TMP_43 \def (THeads TMP_42 t1 u) in 
(let TMP_44 \def (asucc g a) in (let TMP_45 \def (AHead x TMP_44) in (let 
TMP_46 \def (Flat Appl) in (let TMP_47 \def (THeads TMP_46 t1 u) in (let 
TMP_48 \def (asucc g a) in (let TMP_49 \def (AHead x0 TMP_48) in (let TMP_50 
\def (asucc g a) in (let TMP_51 \def (AHead x TMP_50) in (let TMP_52 \def 
(arity_mono g c t0 x0 H6 x H3) in (let TMP_53 \def (asucc g a) in (let TMP_54 
\def (asucc g a) in (let TMP_55 \def (asucc g a) in (let TMP_56 \def 
(leq_refl g TMP_55) in (let TMP_57 \def (leq_head g x0 x TMP_52 TMP_53 TMP_54 
TMP_56) in (let TMP_58 \def (arity_repl g c TMP_47 TMP_49 H7 TMP_51 TMP_57) 
in (let TMP_59 \def (AHead x a) in (let TMP_60 \def (asucc g TMP_59) in (let 
TMP_61 \def (AHead x a) in (let TMP_62 \def (asucc g TMP_61) in (let TMP_63 
\def (leq_refl g TMP_62) in (let TMP_64 \def (arity_repl g c TMP_43 TMP_45 
TMP_58 TMP_60 TMP_63) in (let TMP_65 \def (H TMP_41 TMP_64 H4) in (arity_appl 
g c t0 x H3 TMP_40 a TMP_65))))))))))))))))))))))))))))))))) in (ex2_ind A 
TMP_24 TMP_29 TMP_36 TMP_66 H5)))))))))))))))))) in (ex2_ind A TMP_9 TMP_13 
TMP_20 TMP_67 H2)))))))))))))))))))) in (TList_ind TMP_5 TMP_6 TMP_68 
vs)))))))).

theorem arity_appls_abbr:
 \forall (g: G).(\forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (vs: TList).(\forall 
(a: A).((arity g c (THeads (Flat Appl) vs (lift (S i) O v)) a) \to (arity g c 
(THeads (Flat Appl) vs (TLRef i)) a)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (H: (getl i c (CHead d (Bind Abbr) v))).(\lambda (vs: 
TList).(let TMP_4 \def (\lambda (t: TList).(\forall (a: A).((arity g c 
(THeads (Flat Appl) t (lift (S i) O v)) a) \to (let TMP_1 \def (Flat Appl) in 
(let TMP_2 \def (TLRef i) in (let TMP_3 \def (THeads TMP_1 t TMP_2) in (arity 
g c TMP_3 a))))))) in (let TMP_8 \def (\lambda (a: A).(\lambda (H0: (arity g 
c (lift (S i) O v) a)).(let TMP_5 \def (S i) in (let TMP_6 \def (getl_drop 
Abbr c d v i H) in (let TMP_7 \def (arity_gen_lift g c v a TMP_5 O H0 d 
TMP_6) in (arity_abbr g c d v i H a TMP_7)))))) in (let TMP_32 \def (\lambda 
(t: T).(\lambda (t0: TList).(\lambda (H0: ((\forall (a: A).((arity g c 
(THeads (Flat Appl) t0 (lift (S i) O v)) a) \to (arity g c (THeads (Flat 
Appl) t0 (TLRef i)) a))))).(\lambda (a: A).(\lambda (H1: (arity g c (THead 
(Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O v))) a)).(let TMP_9 \def 
(Flat Appl) in (let TMP_10 \def (S i) in (let TMP_11 \def (lift TMP_10 O v) 
in (let TMP_12 \def (THeads TMP_9 t0 TMP_11) in (let H2 \def (arity_gen_appl 
g c t TMP_12 a H1) in (let TMP_13 \def (\lambda (a1: A).(arity g c t a1)) in 
(let TMP_19 \def (\lambda (a1: A).(let TMP_14 \def (Flat Appl) in (let TMP_15 
\def (S i) in (let TMP_16 \def (lift TMP_15 O v) in (let TMP_17 \def (THeads 
TMP_14 t0 TMP_16) in (let TMP_18 \def (AHead a1 a) in (arity g c TMP_17 
TMP_18))))))) in (let TMP_20 \def (Flat Appl) in (let TMP_21 \def (Flat Appl) 
in (let TMP_22 \def (TLRef i) in (let TMP_23 \def (THeads TMP_21 t0 TMP_22) 
in (let TMP_24 \def (THead TMP_20 t TMP_23) in (let TMP_25 \def (arity g c 
TMP_24 a) in (let TMP_31 \def (\lambda (x: A).(\lambda (H3: (arity g c t 
x)).(\lambda (H4: (arity g c (THeads (Flat Appl) t0 (lift (S i) O v)) (AHead 
x a))).(let TMP_26 \def (Flat Appl) in (let TMP_27 \def (TLRef i) in (let 
TMP_28 \def (THeads TMP_26 t0 TMP_27) in (let TMP_29 \def (AHead x a) in (let 
TMP_30 \def (H0 TMP_29 H4) in (arity_appl g c t x H3 TMP_28 a TMP_30))))))))) 
in (ex2_ind A TMP_13 TMP_19 TMP_25 TMP_31 H2)))))))))))))))))))) in 
(TList_ind TMP_4 TMP_8 TMP_32 vs)))))))))).

theorem arity_appls_bind:
 \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (c: 
C).(\forall (v: T).(\forall (a1: A).((arity g c v a1) \to (\forall (t: 
T).(\forall (vs: TList).(\forall (a2: A).((arity g (CHead c (Bind b) v) 
(THeads (Flat Appl) (lifts (S O) O vs) t) a2) \to (arity g c (THeads (Flat 
Appl) vs (THead (Bind b) v t)) a2)))))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda 
(c: C).(\lambda (v: T).(\lambda (a1: A).(\lambda (H0: (arity g c v 
a1)).(\lambda (t: T).(\lambda (vs: TList).(let TMP_5 \def (\lambda (t0: 
TList).(\forall (a2: A).((arity g (CHead c (Bind b) v) (THeads (Flat Appl) 
(lifts (S O) O t0) t) a2) \to (let TMP_1 \def (Flat Appl) in (let TMP_2 \def 
(Bind b) in (let TMP_3 \def (THead TMP_2 v t) in (let TMP_4 \def (THeads 
TMP_1 t0 TMP_3) in (arity g c TMP_4 a2)))))))) in (let TMP_6 \def (\lambda 
(a2: A).(\lambda (H1: (arity g (CHead c (Bind b) v) t a2)).(arity_bind g b H 
c v a1 H0 t a2 H1))) in (let TMP_49 \def (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (H1: ((\forall (a2: A).((arity g (CHead c (Bind b) v) (THeads 
(Flat Appl) (lifts (S O) O t1) t) a2) \to (arity g c (THeads (Flat Appl) t1 
(THead (Bind b) v t)) a2))))).(\lambda (a2: A).(\lambda (H2: (arity g (CHead 
c (Bind b) v) (THead (Flat Appl) (lift (S O) O t0) (THeads (Flat Appl) (lifts 
(S O) O t1) t)) a2)).(let TMP_7 \def (Bind b) in (let TMP_8 \def (CHead c 
TMP_7 v) in (let TMP_9 \def (S O) in (let TMP_10 \def (lift TMP_9 O t0) in 
(let TMP_11 \def (Flat Appl) in (let TMP_12 \def (S O) in (let TMP_13 \def 
(lifts TMP_12 O t1) in (let TMP_14 \def (THeads TMP_11 TMP_13 t) in (let H3 
\def (arity_gen_appl g TMP_8 TMP_10 TMP_14 a2 H2) in (let TMP_19 \def 
(\lambda (a3: A).(let TMP_15 \def (Bind b) in (let TMP_16 \def (CHead c 
TMP_15 v) in (let TMP_17 \def (S O) in (let TMP_18 \def (lift TMP_17 O t0) in 
(arity g TMP_16 TMP_18 a3)))))) in (let TMP_27 \def (\lambda (a3: A).(let 
TMP_20 \def (Bind b) in (let TMP_21 \def (CHead c TMP_20 v) in (let TMP_22 
\def (Flat Appl) in (let TMP_23 \def (S O) in (let TMP_24 \def (lifts TMP_23 
O t1) in (let TMP_25 \def (THeads TMP_22 TMP_24 t) in (let TMP_26 \def (AHead 
a3 a2) in (arity g TMP_21 TMP_25 TMP_26))))))))) in (let TMP_28 \def (Flat 
Appl) in (let TMP_29 \def (Flat Appl) in (let TMP_30 \def (Bind b) in (let 
TMP_31 \def (THead TMP_30 v t) in (let TMP_32 \def (THeads TMP_29 t1 TMP_31) 
in (let TMP_33 \def (THead TMP_28 t0 TMP_32) in (let TMP_34 \def (arity g c 
TMP_33 a2) in (let TMP_48 \def (\lambda (x: A).(\lambda (H4: (arity g (CHead 
c (Bind b) v) (lift (S O) O t0) x)).(\lambda (H5: (arity g (CHead c (Bind b) 
v) (THeads (Flat Appl) (lifts (S O) O t1) t) (AHead x a2))).(let TMP_35 \def 
(Bind b) in (let TMP_36 \def (CHead c TMP_35 v) in (let TMP_37 \def (S O) in 
(let TMP_38 \def (Bind b) in (let TMP_39 \def (drop_refl c) in (let TMP_40 
\def (drop_drop TMP_38 O c c TMP_39 v) in (let TMP_41 \def (arity_gen_lift g 
TMP_36 t0 x TMP_37 O H4 c TMP_40) in (let TMP_42 \def (Flat Appl) in (let 
TMP_43 \def (Bind b) in (let TMP_44 \def (THead TMP_43 v t) in (let TMP_45 
\def (THeads TMP_42 t1 TMP_44) in (let TMP_46 \def (AHead x a2) in (let 
TMP_47 \def (H1 TMP_46 H5) in (arity_appl g c t0 x TMP_41 TMP_45 a2 
TMP_47))))))))))))))))) in (ex2_ind A TMP_19 TMP_27 TMP_34 TMP_48 
H3))))))))))))))))))))))))) in (TList_ind TMP_5 TMP_6 TMP_49 vs)))))))))))).

