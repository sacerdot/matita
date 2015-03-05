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

include "basic_1/sty0/fwd.ma".

theorem ty3_sty0:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((sty0 g c u t2) \to (ty3 g c u t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(let TMP_1 \def (\lambda (c0: C).(\lambda (t: T).(\lambda (_: 
T).(\forall (t2: T).((sty0 g c0 t t2) \to (ty3 g c0 t t2)))))) in (let TMP_2 
\def (\lambda (c0: C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 
t2 t)).(\lambda (_: ((\forall (t3: T).((sty0 g c0 t2 t3) \to (ty3 g c0 t2 
t3))))).(\lambda (u0: T).(\lambda (t3: T).(\lambda (_: (ty3 g c0 u0 
t3)).(\lambda (H3: ((\forall (t4: T).((sty0 g c0 u0 t4) \to (ty3 g c0 u0 
t4))))).(\lambda (_: (pc3 c0 t3 t2)).(\lambda (t0: T).(\lambda (H5: (sty0 g 
c0 u0 t0)).(H3 t0 H5))))))))))))) in (let TMP_11 \def (\lambda (c0: 
C).(\lambda (m: nat).(\lambda (t2: T).(\lambda (H0: (sty0 g c0 (TSort m) 
t2)).(let H_y \def (sty0_gen_sort g c0 t2 m H0) in (let TMP_3 \def (\lambda 
(e: T).e) in (let TMP_4 \def (next g m) in (let TMP_5 \def (TSort TMP_4) in 
(let H1 \def (f_equal T T TMP_3 t2 TMP_5 H_y) in (let TMP_6 \def (next g m) 
in (let TMP_7 \def (TSort TMP_6) in (let TMP_9 \def (\lambda (t: T).(let 
TMP_8 \def (TSort m) in (ty3 g c0 TMP_8 t))) in (let TMP_10 \def (ty3_sort g 
c0 m) in (eq_ind_r T TMP_7 TMP_9 TMP_10 t2 H1)))))))))))))) in (let TMP_132 
\def (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: 
T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) u0))).(\lambda (t: 
T).(\lambda (_: (ty3 g d u0 t)).(\lambda (H2: ((\forall (t2: T).((sty0 g d u0 
t2) \to (ty3 g d u0 t2))))).(\lambda (t2: T).(\lambda (H3: (sty0 g c0 (TLRef 
n) t2)).(let H_x \def (sty0_gen_lref g c0 t2 n H3) in (let H4 \def H_x in 
(let TMP_14 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_12 
\def (Bind Abbr) in (let TMP_13 \def (CHead e TMP_12 u1) in (getl n c0 
TMP_13)))))) in (let TMP_15 \def (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(sty0 g e u1 t0)))) in (let TMP_18 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(let TMP_16 \def (S n) in (let TMP_17 \def (lift TMP_16 O 
t0) in (eq T t2 TMP_17)))))) in (let TMP_19 \def (ex3_3 C T T TMP_14 TMP_15 
TMP_18) in (let TMP_22 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(let TMP_20 \def (Bind Abst) in (let TMP_21 \def (CHead e TMP_20 u1) in 
(getl n c0 TMP_21)))))) in (let TMP_23 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) in (let TMP_26 \def (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(let TMP_24 \def (S n) in (let TMP_25 
\def (lift TMP_24 O u1) in (eq T t2 TMP_25)))))) in (let TMP_27 \def (ex3_3 C 
T T TMP_22 TMP_23 TMP_26) in (let TMP_28 \def (TLRef n) in (let TMP_29 \def 
(ty3 g c0 TMP_28 t2) in (let TMP_88 \def (\lambda (H5: (ex3_3 C T T (\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift (S n) O 
t0))))))).(let TMP_32 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(let TMP_30 \def (Bind Abbr) in (let TMP_31 \def (CHead e TMP_30 u1) in 
(getl n c0 TMP_31)))))) in (let TMP_33 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) in (let TMP_36 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(let TMP_34 \def (S n) in (let TMP_35 
\def (lift TMP_34 O t0) in (eq T t2 TMP_35)))))) in (let TMP_37 \def (TLRef 
n) in (let TMP_38 \def (ty3 g c0 TMP_37 t2) in (let TMP_87 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H6: (getl n c0 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H7: (sty0 g x0 x1 x2)).(\lambda (H8: (eq T t2 (lift (S 
n) O x2))).(let TMP_39 \def (\lambda (e: T).e) in (let TMP_40 \def (S n) in 
(let TMP_41 \def (lift TMP_40 O x2) in (let H9 \def (f_equal T T TMP_39 t2 
TMP_41 H8) in (let TMP_42 \def (S n) in (let TMP_43 \def (lift TMP_42 O x2) 
in (let TMP_45 \def (\lambda (t0: T).(let TMP_44 \def (TLRef n) in (ty3 g c0 
TMP_44 t0))) in (let TMP_46 \def (Bind Abbr) in (let TMP_47 \def (CHead d 
TMP_46 u0) in (let TMP_48 \def (\lambda (c1: C).(getl n c0 c1)) in (let 
TMP_49 \def (Bind Abbr) in (let TMP_50 \def (CHead x0 TMP_49 x1) in (let 
TMP_51 \def (Bind Abbr) in (let TMP_52 \def (CHead d TMP_51 u0) in (let 
TMP_53 \def (Bind Abbr) in (let TMP_54 \def (CHead x0 TMP_53 x1) in (let 
TMP_55 \def (getl_mono c0 TMP_52 n H0 TMP_54 H6) in (let H10 \def (eq_ind C 
TMP_47 TMP_48 H0 TMP_50 TMP_55) in (let TMP_56 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) in (let 
TMP_57 \def (Bind Abbr) in (let TMP_58 \def (CHead d TMP_57 u0) in (let 
TMP_59 \def (Bind Abbr) in (let TMP_60 \def (CHead x0 TMP_59 x1) in (let 
TMP_61 \def (Bind Abbr) in (let TMP_62 \def (CHead d TMP_61 u0) in (let 
TMP_63 \def (Bind Abbr) in (let TMP_64 \def (CHead x0 TMP_63 x1) in (let 
TMP_65 \def (getl_mono c0 TMP_62 n H0 TMP_64 H6) in (let H11 \def (f_equal C 
C TMP_56 TMP_58 TMP_60 TMP_65) in (let TMP_66 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t0) \Rightarrow t0])) in (let 
TMP_67 \def (Bind Abbr) in (let TMP_68 \def (CHead d TMP_67 u0) in (let 
TMP_69 \def (Bind Abbr) in (let TMP_70 \def (CHead x0 TMP_69 x1) in (let 
TMP_71 \def (Bind Abbr) in (let TMP_72 \def (CHead d TMP_71 u0) in (let 
TMP_73 \def (Bind Abbr) in (let TMP_74 \def (CHead x0 TMP_73 x1) in (let 
TMP_75 \def (getl_mono c0 TMP_72 n H0 TMP_74 H6) in (let H12 \def (f_equal C 
T TMP_66 TMP_68 TMP_70 TMP_75) in (let TMP_85 \def (\lambda (H13: (eq C d 
x0)).(let TMP_78 \def (\lambda (t0: T).(let TMP_76 \def (Bind Abbr) in (let 
TMP_77 \def (CHead x0 TMP_76 t0) in (getl n c0 TMP_77)))) in (let H14 \def 
(eq_ind_r T x1 TMP_78 H10 u0 H12) in (let TMP_79 \def (\lambda (t0: T).(sty0 
g x0 t0 x2)) in (let H15 \def (eq_ind_r T x1 TMP_79 H7 u0 H12) in (let TMP_82 
\def (\lambda (c1: C).(let TMP_80 \def (Bind Abbr) in (let TMP_81 \def (CHead 
c1 TMP_80 u0) in (getl n c0 TMP_81)))) in (let H16 \def (eq_ind_r C x0 TMP_82 
H14 d H13) in (let TMP_83 \def (\lambda (c1: C).(sty0 g c1 u0 x2)) in (let 
H17 \def (eq_ind_r C x0 TMP_83 H15 d H13) in (let TMP_84 \def (H2 x2 H17) in 
(ty3_abbr g n c0 d u0 H16 x2 TMP_84))))))))))) in (let TMP_86 \def (TMP_85 
H11) in (eq_ind_r T TMP_43 TMP_45 TMP_86 t2 
H9))))))))))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind C T T 
TMP_32 TMP_33 TMP_36 TMP_38 TMP_87 H5)))))))) in (let TMP_131 \def (\lambda 
(H5: (ex3_3 C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: 
T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq T 
t2 (lift (S n) O u1))))))).(let TMP_91 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(let TMP_89 \def (Bind Abst) in (let TMP_90 \def (CHead e 
TMP_89 u1) in (getl n c0 TMP_90)))))) in (let TMP_92 \def (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) in (let TMP_95 \def 
(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_93 \def (S n) in 
(let TMP_94 \def (lift TMP_93 O u1) in (eq T t2 TMP_94)))))) in (let TMP_96 
\def (TLRef n) in (let TMP_97 \def (ty3 g c0 TMP_96 t2) in (let TMP_130 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abst) x1))).(\lambda (_: (sty0 g x0 x1 x2)).(\lambda (H8: (eq 
T t2 (lift (S n) O x1))).(let TMP_98 \def (\lambda (e: T).e) in (let TMP_99 
\def (S n) in (let TMP_100 \def (lift TMP_99 O x1) in (let H9 \def (f_equal T 
T TMP_98 t2 TMP_100 H8) in (let TMP_101 \def (S n) in (let TMP_102 \def (lift 
TMP_101 O x1) in (let TMP_104 \def (\lambda (t0: T).(let TMP_103 \def (TLRef 
n) in (ty3 g c0 TMP_103 t0))) in (let TMP_105 \def (Bind Abbr) in (let 
TMP_106 \def (CHead d TMP_105 u0) in (let TMP_107 \def (\lambda (c1: C).(getl 
n c0 c1)) in (let TMP_108 \def (Bind Abst) in (let TMP_109 \def (CHead x0 
TMP_108 x1) in (let TMP_110 \def (Bind Abbr) in (let TMP_111 \def (CHead d 
TMP_110 u0) in (let TMP_112 \def (Bind Abst) in (let TMP_113 \def (CHead x0 
TMP_112 x1) in (let TMP_114 \def (getl_mono c0 TMP_111 n H0 TMP_113 H6) in 
(let H10 \def (eq_ind C TMP_106 TMP_107 H0 TMP_109 TMP_114) in (let TMP_115 
\def (Bind Abbr) in (let TMP_116 \def (CHead d TMP_115 u0) in (let TMP_117 
\def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ 
k _) \Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_118 \def (Bind Abst) in (let TMP_119 
\def (CHead x0 TMP_118 x1) in (let TMP_120 \def (Bind Abbr) in (let TMP_121 
\def (CHead d TMP_120 u0) in (let TMP_122 \def (Bind Abst) in (let TMP_123 
\def (CHead x0 TMP_122 x1) in (let TMP_124 \def (getl_mono c0 TMP_121 n H0 
TMP_123 H6) in (let H11 \def (eq_ind C TMP_116 TMP_117 I TMP_119 TMP_124) in 
(let TMP_125 \def (TLRef n) in (let TMP_126 \def (S n) in (let TMP_127 \def 
(lift TMP_126 O x1) in (let TMP_128 \def (ty3 g c0 TMP_125 TMP_127) in (let 
TMP_129 \def (False_ind TMP_128 H11) in (eq_ind_r T TMP_102 TMP_104 TMP_129 
t2 H9))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind C T T TMP_91 
TMP_92 TMP_95 TMP_97 TMP_130 H5)))))))) in (or_ind TMP_19 TMP_27 TMP_29 
TMP_88 TMP_131 H4))))))))))))))))))))))))) in (let TMP_257 \def (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abst) u0))).(\lambda (t: T).(\lambda (H1: (ty3 g d u0 
t)).(\lambda (_: ((\forall (t2: T).((sty0 g d u0 t2) \to (ty3 g d u0 
t2))))).(\lambda (t2: T).(\lambda (H3: (sty0 g c0 (TLRef n) t2)).(let H_x 
\def (sty0_gen_lref g c0 t2 n H3) in (let H4 \def H_x in (let TMP_135 \def 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_133 \def (Bind 
Abbr) in (let TMP_134 \def (CHead e TMP_133 u1) in (getl n c0 TMP_134)))))) 
in (let TMP_136 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 
g e u1 t0)))) in (let TMP_139 \def (\lambda (_: C).(\lambda (_: T).(\lambda 
(t0: T).(let TMP_137 \def (S n) in (let TMP_138 \def (lift TMP_137 O t0) in 
(eq T t2 TMP_138)))))) in (let TMP_140 \def (ex3_3 C T T TMP_135 TMP_136 
TMP_139) in (let TMP_143 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(let TMP_141 \def (Bind Abst) in (let TMP_142 \def (CHead e TMP_141 u1) in 
(getl n c0 TMP_142)))))) in (let TMP_144 \def (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) in (let TMP_147 \def (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(let TMP_145 \def (S n) in (let TMP_146 
\def (lift TMP_145 O u1) in (eq T t2 TMP_146)))))) in (let TMP_148 \def 
(ex3_3 C T T TMP_143 TMP_144 TMP_147) in (let TMP_149 \def (TLRef n) in (let 
TMP_150 \def (ty3 g c0 TMP_149 t2) in (let TMP_193 \def (\lambda (H5: (ex3_3 
C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g 
e u1 t0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift 
(S n) O t0))))))).(let TMP_153 \def (\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(let TMP_151 \def (Bind Abbr) in (let TMP_152 \def (CHead e TMP_151 
u1) in (getl n c0 TMP_152)))))) in (let TMP_154 \def (\lambda (e: C).(\lambda 
(u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) in (let TMP_157 \def (\lambda 
(_: C).(\lambda (_: T).(\lambda (t0: T).(let TMP_155 \def (S n) in (let 
TMP_156 \def (lift TMP_155 O t0) in (eq T t2 TMP_156)))))) in (let TMP_158 
\def (TLRef n) in (let TMP_159 \def (ty3 g c0 TMP_158 t2) in (let TMP_192 
\def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H6: (getl n 
c0 (CHead x0 (Bind Abbr) x1))).(\lambda (_: (sty0 g x0 x1 x2)).(\lambda (H8: 
(eq T t2 (lift (S n) O x2))).(let TMP_160 \def (\lambda (e: T).e) in (let 
TMP_161 \def (S n) in (let TMP_162 \def (lift TMP_161 O x2) in (let H9 \def 
(f_equal T T TMP_160 t2 TMP_162 H8) in (let TMP_163 \def (S n) in (let 
TMP_164 \def (lift TMP_163 O x2) in (let TMP_166 \def (\lambda (t0: T).(let 
TMP_165 \def (TLRef n) in (ty3 g c0 TMP_165 t0))) in (let TMP_167 \def (Bind 
Abst) in (let TMP_168 \def (CHead d TMP_167 u0) in (let TMP_169 \def (\lambda 
(c1: C).(getl n c0 c1)) in (let TMP_170 \def (Bind Abbr) in (let TMP_171 \def 
(CHead x0 TMP_170 x1) in (let TMP_172 \def (Bind Abst) in (let TMP_173 \def 
(CHead d TMP_172 u0) in (let TMP_174 \def (Bind Abbr) in (let TMP_175 \def 
(CHead x0 TMP_174 x1) in (let TMP_176 \def (getl_mono c0 TMP_173 n H0 TMP_175 
H6) in (let H10 \def (eq_ind C TMP_168 TMP_169 H0 TMP_171 TMP_176) in (let 
TMP_177 \def (Bind Abst) in (let TMP_178 \def (CHead d TMP_177 u0) in (let 
TMP_179 \def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k with [(Bind b) \Rightarrow (match b with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) in (let TMP_180 \def (Bind Abbr) in (let 
TMP_181 \def (CHead x0 TMP_180 x1) in (let TMP_182 \def (Bind Abst) in (let 
TMP_183 \def (CHead d TMP_182 u0) in (let TMP_184 \def (Bind Abbr) in (let 
TMP_185 \def (CHead x0 TMP_184 x1) in (let TMP_186 \def (getl_mono c0 TMP_183 
n H0 TMP_185 H6) in (let H11 \def (eq_ind C TMP_178 TMP_179 I TMP_181 
TMP_186) in (let TMP_187 \def (TLRef n) in (let TMP_188 \def (S n) in (let 
TMP_189 \def (lift TMP_188 O x2) in (let TMP_190 \def (ty3 g c0 TMP_187 
TMP_189) in (let TMP_191 \def (False_ind TMP_190 H11) in (eq_ind_r T TMP_164 
TMP_166 TMP_191 t2 H9))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind 
C T T TMP_153 TMP_154 TMP_157 TMP_159 TMP_192 H5)))))))) in (let TMP_256 \def 
(\lambda (H5: (ex3_3 C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq T t2 (lift (S n) O u1))))))).(let TMP_196 \def 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(let TMP_194 \def (Bind 
Abst) in (let TMP_195 \def (CHead e TMP_194 u1) in (getl n c0 TMP_195)))))) 
in (let TMP_197 \def (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 
g e u1 t0)))) in (let TMP_200 \def (\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(let TMP_198 \def (S n) in (let TMP_199 \def (lift TMP_198 O u1) in 
(eq T t2 TMP_199)))))) in (let TMP_201 \def (TLRef n) in (let TMP_202 \def 
(ty3 g c0 TMP_201 t2) in (let TMP_255 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abst) 
x1))).(\lambda (H7: (sty0 g x0 x1 x2)).(\lambda (H8: (eq T t2 (lift (S n) O 
x1))).(let TMP_203 \def (\lambda (e: T).e) in (let TMP_204 \def (S n) in (let 
TMP_205 \def (lift TMP_204 O x1) in (let H9 \def (f_equal T T TMP_203 t2 
TMP_205 H8) in (let TMP_206 \def (S n) in (let TMP_207 \def (lift TMP_206 O 
x1) in (let TMP_209 \def (\lambda (t0: T).(let TMP_208 \def (TLRef n) in (ty3 
g c0 TMP_208 t0))) in (let TMP_210 \def (Bind Abst) in (let TMP_211 \def 
(CHead d TMP_210 u0) in (let TMP_212 \def (\lambda (c1: C).(getl n c0 c1)) in 
(let TMP_213 \def (Bind Abst) in (let TMP_214 \def (CHead x0 TMP_213 x1) in 
(let TMP_215 \def (Bind Abst) in (let TMP_216 \def (CHead d TMP_215 u0) in 
(let TMP_217 \def (Bind Abst) in (let TMP_218 \def (CHead x0 TMP_217 x1) in 
(let TMP_219 \def (getl_mono c0 TMP_216 n H0 TMP_218 H6) in (let H10 \def 
(eq_ind C TMP_211 TMP_212 H0 TMP_214 TMP_219) in (let TMP_220 \def (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow 
c1])) in (let TMP_221 \def (Bind Abst) in (let TMP_222 \def (CHead d TMP_221 
u0) in (let TMP_223 \def (Bind Abst) in (let TMP_224 \def (CHead x0 TMP_223 
x1) in (let TMP_225 \def (Bind Abst) in (let TMP_226 \def (CHead d TMP_225 
u0) in (let TMP_227 \def (Bind Abst) in (let TMP_228 \def (CHead x0 TMP_227 
x1) in (let TMP_229 \def (getl_mono c0 TMP_226 n H0 TMP_228 H6) in (let H11 
\def (f_equal C C TMP_220 TMP_222 TMP_224 TMP_229) in (let TMP_230 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_231 \def (Bind Abst) in (let TMP_232 \def 
(CHead d TMP_231 u0) in (let TMP_233 \def (Bind Abst) in (let TMP_234 \def 
(CHead x0 TMP_233 x1) in (let TMP_235 \def (Bind Abst) in (let TMP_236 \def 
(CHead d TMP_235 u0) in (let TMP_237 \def (Bind Abst) in (let TMP_238 \def 
(CHead x0 TMP_237 x1) in (let TMP_239 \def (getl_mono c0 TMP_236 n H0 TMP_238 
H6) in (let H12 \def (f_equal C T TMP_230 TMP_232 TMP_234 TMP_239) in (let 
TMP_253 \def (\lambda (H13: (eq C d x0)).(let TMP_242 \def (\lambda (t0: 
T).(let TMP_240 \def (Bind Abst) in (let TMP_241 \def (CHead x0 TMP_240 t0) 
in (getl n c0 TMP_241)))) in (let H14 \def (eq_ind_r T x1 TMP_242 H10 u0 H12) 
in (let TMP_243 \def (\lambda (t0: T).(sty0 g x0 t0 x2)) in (let H15 \def 
(eq_ind_r T x1 TMP_243 H7 u0 H12) in (let TMP_247 \def (\lambda (t0: T).(let 
TMP_244 \def (TLRef n) in (let TMP_245 \def (S n) in (let TMP_246 \def (lift 
TMP_245 O t0) in (ty3 g c0 TMP_244 TMP_246))))) in (let TMP_250 \def (\lambda 
(c1: C).(let TMP_248 \def (Bind Abst) in (let TMP_249 \def (CHead c1 TMP_248 
u0) in (getl n c0 TMP_249)))) in (let H16 \def (eq_ind_r C x0 TMP_250 H14 d 
H13) in (let TMP_251 \def (\lambda (c1: C).(sty0 g c1 u0 x2)) in (let H17 
\def (eq_ind_r C x0 TMP_251 H15 d H13) in (let TMP_252 \def (ty3_abst g n c0 
d u0 H16 t H1) in (eq_ind T u0 TMP_247 TMP_252 x1 H12)))))))))))) in (let 
TMP_254 \def (TMP_253 H11) in (eq_ind_r T TMP_207 TMP_209 TMP_254 t2 
H9))))))))))))))))))))))))))))))))))))))))))))))))) in (ex3_3_ind C T T 
TMP_196 TMP_197 TMP_200 TMP_202 TMP_255 H5)))))))) in (or_ind TMP_140 TMP_148 
TMP_150 TMP_193 TMP_256 H4))))))))))))))))))))))))) in (let TMP_278 \def 
(\lambda (c0: C).(\lambda (u0: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u0 
t)).(\lambda (_: ((\forall (t2: T).((sty0 g c0 u0 t2) \to (ty3 g c0 u0 
t2))))).(\lambda (b: B).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (ty3 g 
(CHead c0 (Bind b) u0) t2 t3)).(\lambda (H3: ((\forall (t4: T).((sty0 g 
(CHead c0 (Bind b) u0) t2 t4) \to (ty3 g (CHead c0 (Bind b) u0) t2 
t4))))).(\lambda (t0: T).(\lambda (H4: (sty0 g c0 (THead (Bind b) u0 t2) 
t0)).(let H_x \def (sty0_gen_bind g b c0 u0 t2 t0 H4) in (let H5 \def H_x in 
(let TMP_260 \def (\lambda (t4: T).(let TMP_258 \def (Bind b) in (let TMP_259 
\def (CHead c0 TMP_258 u0) in (sty0 g TMP_259 t2 t4)))) in (let TMP_263 \def 
(\lambda (t4: T).(let TMP_261 \def (Bind b) in (let TMP_262 \def (THead 
TMP_261 u0 t4) in (eq T t0 TMP_262)))) in (let TMP_264 \def (Bind b) in (let 
TMP_265 \def (THead TMP_264 u0 t2) in (let TMP_266 \def (ty3 g c0 TMP_265 t0) 
in (let TMP_277 \def (\lambda (x: T).(\lambda (H6: (sty0 g (CHead c0 (Bind b) 
u0) t2 x)).(\lambda (H7: (eq T t0 (THead (Bind b) u0 x))).(let TMP_267 \def 
(\lambda (e: T).e) in (let TMP_268 \def (Bind b) in (let TMP_269 \def (THead 
TMP_268 u0 x) in (let H8 \def (f_equal T T TMP_267 t0 TMP_269 H7) in (let 
TMP_270 \def (Bind b) in (let TMP_271 \def (THead TMP_270 u0 x) in (let 
TMP_274 \def (\lambda (t4: T).(let TMP_272 \def (Bind b) in (let TMP_273 \def 
(THead TMP_272 u0 t2) in (ty3 g c0 TMP_273 t4)))) in (let TMP_275 \def (H3 x 
H6) in (let TMP_276 \def (ty3_bind g c0 u0 t H0 b t2 x TMP_275) in (eq_ind_r 
T TMP_271 TMP_274 TMP_276 t0 H8))))))))))))) in (ex2_ind T TMP_260 TMP_263 
TMP_266 TMP_277 H5))))))))))))))))))))) in (let TMP_366 \def (\lambda (c0: 
C).(\lambda (w: T).(\lambda (u0: T).(\lambda (H0: (ty3 g c0 w u0)).(\lambda 
(_: ((\forall (t2: T).((sty0 g c0 w t2) \to (ty3 g c0 w t2))))).(\lambda (v: 
T).(\lambda (t: T).(\lambda (H2: (ty3 g c0 v (THead (Bind Abst) u0 
t))).(\lambda (H3: ((\forall (t2: T).((sty0 g c0 v t2) \to (ty3 g c0 v 
t2))))).(\lambda (t2: T).(\lambda (H4: (sty0 g c0 (THead (Flat Appl) w v) 
t2)).(let H_x \def (sty0_gen_appl g c0 w v t2 H4) in (let H5 \def H_x in (let 
TMP_279 \def (\lambda (t3: T).(sty0 g c0 v t3)) in (let TMP_282 \def (\lambda 
(t3: T).(let TMP_280 \def (Flat Appl) in (let TMP_281 \def (THead TMP_280 w 
t3) in (eq T t2 TMP_281)))) in (let TMP_283 \def (Flat Appl) in (let TMP_284 
\def (THead TMP_283 w v) in (let TMP_285 \def (ty3 g c0 TMP_284 t2) in (let 
TMP_365 \def (\lambda (x: T).(\lambda (H6: (sty0 g c0 v x)).(\lambda (H7: (eq 
T t2 (THead (Flat Appl) w x))).(let TMP_286 \def (\lambda (e: T).e) in (let 
TMP_287 \def (Flat Appl) in (let TMP_288 \def (THead TMP_287 w x) in (let H8 
\def (f_equal T T TMP_286 t2 TMP_288 H7) in (let TMP_289 \def (Flat Appl) in 
(let TMP_290 \def (THead TMP_289 w x) in (let TMP_293 \def (\lambda (t0: 
T).(let TMP_291 \def (Flat Appl) in (let TMP_292 \def (THead TMP_291 w v) in 
(ty3 g c0 TMP_292 t0)))) in (let H_y \def (H3 x H6) in (let TMP_294 \def 
(Bind Abst) in (let TMP_295 \def (THead TMP_294 u0 t) in (let H9 \def 
(ty3_unique g c0 v x H_y TMP_295 H2) in (let TMP_296 \def (\lambda (t0: 
T).(ty3 g c0 x t0)) in (let TMP_297 \def (Flat Appl) in (let TMP_298 \def 
(THead TMP_297 w v) in (let TMP_299 \def (Flat Appl) in (let TMP_300 \def 
(THead TMP_299 w x) in (let TMP_301 \def (ty3 g c0 TMP_298 TMP_300) in (let 
TMP_362 \def (\lambda (x0: T).(\lambda (H10: (ty3 g c0 x x0)).(let TMP_302 
\def (\lambda (t0: T).(ty3 g c0 u0 t0)) in (let TMP_303 \def (Flat Appl) in 
(let TMP_304 \def (THead TMP_303 w v) in (let TMP_305 \def (Flat Appl) in 
(let TMP_306 \def (THead TMP_305 w x) in (let TMP_307 \def (ty3 g c0 TMP_304 
TMP_306) in (let TMP_360 \def (\lambda (x1: T).(\lambda (_: (ty3 g c0 u0 
x1)).(let TMP_310 \def (\lambda (t0: T).(let TMP_308 \def (Bind Abst) in (let 
TMP_309 \def (THead TMP_308 u0 t) in (ty3 g c0 TMP_309 t0)))) in (let TMP_311 
\def (Flat Appl) in (let TMP_312 \def (THead TMP_311 w v) in (let TMP_313 
\def (Flat Appl) in (let TMP_314 \def (THead TMP_313 w x) in (let TMP_315 
\def (ty3 g c0 TMP_312 TMP_314) in (let TMP_356 \def (\lambda (x2: 
T).(\lambda (H12: (ty3 g c0 (THead (Bind Abst) u0 t) x2)).(let TMP_318 \def 
(\lambda (t3: T).(\lambda (_: T).(let TMP_316 \def (Bind Abst) in (let 
TMP_317 \def (THead TMP_316 u0 t3) in (pc3 c0 TMP_317 x2))))) in (let TMP_319 
\def (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u0 t0))) in (let TMP_322 \def 
(\lambda (t3: T).(\lambda (_: T).(let TMP_320 \def (Bind Abst) in (let 
TMP_321 \def (CHead c0 TMP_320 u0) in (ty3 g TMP_321 t t3))))) in (let 
TMP_323 \def (Flat Appl) in (let TMP_324 \def (THead TMP_323 w v) in (let 
TMP_325 \def (Flat Appl) in (let TMP_326 \def (THead TMP_325 w x) in (let 
TMP_327 \def (ty3 g c0 TMP_324 TMP_326) in (let TMP_354 \def (\lambda (x3: 
T).(\lambda (x4: T).(\lambda (_: (pc3 c0 (THead (Bind Abst) u0 x3) 
x2)).(\lambda (H14: (ty3 g c0 u0 x4)).(\lambda (H15: (ty3 g (CHead c0 (Bind 
Abst) u0) t x3)).(let TMP_328 \def (Flat Appl) in (let TMP_329 \def (THead 
TMP_328 w x) in (let TMP_330 \def (Flat Appl) in (let TMP_331 \def (Bind 
Abst) in (let TMP_332 \def (THead TMP_331 u0 x3) in (let TMP_333 \def (THead 
TMP_330 w TMP_332) in (let TMP_334 \def (Bind Abst) in (let TMP_335 \def 
(THead TMP_334 u0 t) in (let TMP_336 \def (Bind Abst) in (let TMP_337 \def 
(THead TMP_336 u0 x3) in (let TMP_338 \def (ty3_bind g c0 u0 x4 H14 Abst t x3 
H15) in (let TMP_339 \def (ty3_sconv g c0 x x0 H10 TMP_335 TMP_337 TMP_338 
H9) in (let TMP_340 \def (ty3_appl g c0 w u0 H0 x x3 TMP_339) in (let TMP_341 
\def (Flat Appl) in (let TMP_342 \def (THead TMP_341 w v) in (let TMP_343 
\def (Flat Appl) in (let TMP_344 \def (Bind Abst) in (let TMP_345 \def (THead 
TMP_344 u0 t) in (let TMP_346 \def (THead TMP_343 w TMP_345) in (let TMP_347 
\def (ty3_appl g c0 w u0 H0 v t H2) in (let TMP_348 \def (Bind Abst) in (let 
TMP_349 \def (THead TMP_348 u0 t) in (let TMP_350 \def (Bind Abst) in (let 
TMP_351 \def (THead TMP_350 u0 t) in (let TMP_352 \def (ty3_unique g c0 v 
TMP_351 H2 x H_y) in (let TMP_353 \def (pc3_thin_dx c0 TMP_349 x TMP_352 w 
Appl) in (ty3_conv g c0 TMP_329 TMP_333 TMP_340 TMP_342 TMP_346 TMP_347 
TMP_353)))))))))))))))))))))))))))))))) in (let TMP_355 \def (ty3_gen_bind g 
Abst c0 u0 t x2 H12) in (ex3_2_ind T T TMP_318 TMP_319 TMP_322 TMP_327 
TMP_354 TMP_355))))))))))))) in (let TMP_357 \def (Bind Abst) in (let TMP_358 
\def (THead TMP_357 u0 t) in (let TMP_359 \def (ty3_correct g c0 v TMP_358 
H2) in (ex_ind T TMP_310 TMP_315 TMP_356 TMP_359))))))))))))) in (let TMP_361 
\def (ty3_correct g c0 w u0 H0) in (ex_ind T TMP_302 TMP_307 TMP_360 
TMP_361))))))))))) in (let TMP_363 \def (ty3_correct g c0 v x H_y) in (let 
TMP_364 \def (ex_ind T TMP_296 TMP_301 TMP_362 TMP_363) in (eq_ind_r T 
TMP_290 TMP_293 TMP_364 t2 H8)))))))))))))))))))))))) in (ex2_ind T TMP_279 
TMP_282 TMP_285 TMP_365 H5)))))))))))))))))))) in (let TMP_414 \def (\lambda 
(c0: C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: (ty3 g c0 t2 
t3)).(\lambda (H1: ((\forall (t4: T).((sty0 g c0 t2 t4) \to (ty3 g c0 t2 
t4))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t3 t0)).(\lambda (H3: 
((\forall (t4: T).((sty0 g c0 t3 t4) \to (ty3 g c0 t3 t4))))).(\lambda (t4: 
T).(\lambda (H4: (sty0 g c0 (THead (Flat Cast) t3 t2) t4)).(let H_x \def 
(sty0_gen_cast g c0 t3 t2 t4 H4) in (let H5 \def H_x in (let TMP_367 \def 
(\lambda (v2: T).(\lambda (_: T).(sty0 g c0 t3 v2))) in (let TMP_368 \def 
(\lambda (_: T).(\lambda (t5: T).(sty0 g c0 t2 t5))) in (let TMP_371 \def 
(\lambda (v2: T).(\lambda (t5: T).(let TMP_369 \def (Flat Cast) in (let 
TMP_370 \def (THead TMP_369 v2 t5) in (eq T t4 TMP_370))))) in (let TMP_372 
\def (Flat Cast) in (let TMP_373 \def (THead TMP_372 t3 t2) in (let TMP_374 
\def (ty3 g c0 TMP_373 t4) in (let TMP_413 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H6: (sty0 g c0 t3 x0)).(\lambda (H7: (sty0 g c0 t2 
x1)).(\lambda (H8: (eq T t4 (THead (Flat Cast) x0 x1))).(let TMP_375 \def 
(\lambda (e: T).e) in (let TMP_376 \def (Flat Cast) in (let TMP_377 \def 
(THead TMP_376 x0 x1) in (let H9 \def (f_equal T T TMP_375 t4 TMP_377 H8) in 
(let TMP_378 \def (Flat Cast) in (let TMP_379 \def (THead TMP_378 x0 x1) in 
(let TMP_382 \def (\lambda (t: T).(let TMP_380 \def (Flat Cast) in (let 
TMP_381 \def (THead TMP_380 t3 t2) in (ty3 g c0 TMP_381 t)))) in (let H_y 
\def (H1 x1 H7) in (let H_y0 \def (H3 x0 H6) in (let H10 \def (ty3_unique g 
c0 t2 x1 H_y t3 H0) in (let TMP_383 \def (\lambda (t: T).(ty3 g c0 x0 t)) in 
(let TMP_384 \def (Flat Cast) in (let TMP_385 \def (THead TMP_384 t3 t2) in 
(let TMP_386 \def (Flat Cast) in (let TMP_387 \def (THead TMP_386 x0 x1) in 
(let TMP_388 \def (ty3 g c0 TMP_385 TMP_387) in (let TMP_410 \def (\lambda 
(x: T).(\lambda (H11: (ty3 g c0 x0 x)).(let TMP_389 \def (\lambda (t: T).(ty3 
g c0 x1 t)) in (let TMP_390 \def (Flat Cast) in (let TMP_391 \def (THead 
TMP_390 t3 t2) in (let TMP_392 \def (Flat Cast) in (let TMP_393 \def (THead 
TMP_392 x0 x1) in (let TMP_394 \def (ty3 g c0 TMP_391 TMP_393) in (let 
TMP_408 \def (\lambda (x2: T).(\lambda (H12: (ty3 g c0 x1 x2)).(let TMP_395 
\def (Flat Cast) in (let TMP_396 \def (THead TMP_395 x0 x1) in (let TMP_397 
\def (Flat Cast) in (let TMP_398 \def (THead TMP_397 x x0) in (let TMP_399 
\def (ty3_sconv g c0 x1 x2 H12 t3 x0 H_y0 H10) in (let TMP_400 \def (ty3_cast 
g c0 x1 x0 TMP_399 x H11) in (let TMP_401 \def (Flat Cast) in (let TMP_402 
\def (THead TMP_401 t3 t2) in (let TMP_403 \def (Flat Cast) in (let TMP_404 
\def (THead TMP_403 x0 t3) in (let TMP_405 \def (ty3_cast g c0 t2 t3 H0 x0 
H_y0) in (let TMP_406 \def (ty3_unique g c0 t2 t3 H0 x1 H_y) in (let TMP_407 
\def (pc3_thin_dx c0 t3 x1 TMP_406 x0 Cast) in (ty3_conv g c0 TMP_396 TMP_398 
TMP_400 TMP_402 TMP_404 TMP_405 TMP_407)))))))))))))))) in (let TMP_409 \def 
(ty3_correct g c0 t2 x1 H_y) in (ex_ind T TMP_389 TMP_394 TMP_408 
TMP_409))))))))))) in (let TMP_411 \def (ty3_correct g c0 t3 x0 H_y0) in (let 
TMP_412 \def (ex_ind T TMP_383 TMP_388 TMP_410 TMP_411) in (eq_ind_r T 
TMP_379 TMP_382 TMP_412 t4 H9))))))))))))))))))))))))) in (ex3_2_ind T T 
TMP_367 TMP_368 TMP_371 TMP_374 TMP_413 H5)))))))))))))))))))) in (ty3_ind g 
TMP_1 TMP_2 TMP_11 TMP_132 TMP_257 TMP_278 TMP_366 TMP_414 c u t1 
H))))))))))))).

