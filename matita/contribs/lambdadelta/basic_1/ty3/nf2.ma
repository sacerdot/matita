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

include "basic_1/ty3/arity.ma".

include "basic_1/pc3/nf2.ma".

include "basic_1/nf2/arity.ma".

definition ty3_nf2_inv_abst_premise:
 C \to (T \to (T \to Prop))
\def
 \lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\forall (d: C).(\forall (wi: 
T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) wi)) \to (\forall (vs: 
TList).((pc3 c (THeads (Flat Appl) vs (lift (S i) O wi)) (THead (Bind Abst) w 
u)) \to False)))))))).

theorem ty3_nf2_inv_abst_premise_csort:
 \forall (w: T).(\forall (u: T).(\forall (m: nat).(ty3_nf2_inv_abst_premise 
(CSort m) w u)))
\def
 \lambda (w: T).(\lambda (u: T).(\lambda (m: nat).(\lambda (d: C).(\lambda 
(wi: T).(\lambda (i: nat).(\lambda (H: (getl i (CSort m) (CHead d (Bind Abst) 
wi))).(\lambda (vs: TList).(\lambda (_: (pc3 (CSort m) (THeads (Flat Appl) vs 
(lift (S i) O wi)) (THead (Bind Abst) w u))).(let TMP_1 \def (Bind Abst) in 
(let TMP_2 \def (CHead d TMP_1 wi) in (getl_gen_sort m i TMP_2 H 
False))))))))))).

theorem ty3_nf2_inv_all:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to ((nf2 c t) \to (or3 (ex3_2 T T (\lambda (w: T).(\lambda (u0: T).(eq T 
t (THead (Bind Abst) w u0)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) 
(\lambda (w: T).(\lambda (u0: T).(nf2 (CHead c (Bind Abst) w) u0)))) (ex nat 
(\lambda (n: nat).(eq T t (TSort n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(\lambda (H0: (nf2 c t)).(let H_x \def (ty3_arity g c t u H) 
in (let H1 \def H_x in (let TMP_1 \def (\lambda (a1: A).(arity g c t a1)) in 
(let TMP_3 \def (\lambda (a1: A).(let TMP_2 \def (asucc g a1) in (arity g c u 
TMP_2))) in (let TMP_6 \def (\lambda (w: T).(\lambda (u0: T).(let TMP_4 \def 
(Bind Abst) in (let TMP_5 \def (THead TMP_4 w u0) in (eq T t TMP_5))))) in 
(let TMP_7 \def (\lambda (w: T).(\lambda (_: T).(nf2 c w))) in (let TMP_10 
\def (\lambda (w: T).(\lambda (u0: T).(let TMP_8 \def (Bind Abst) in (let 
TMP_9 \def (CHead c TMP_8 w) in (nf2 TMP_9 u0))))) in (let TMP_11 \def (ex3_2 
T T TMP_6 TMP_7 TMP_10) in (let TMP_13 \def (\lambda (n: nat).(let TMP_12 
\def (TSort n) in (eq T t TMP_12))) in (let TMP_14 \def (ex nat TMP_13) in 
(let TMP_18 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_15 \def 
(Flat Appl) in (let TMP_16 \def (TLRef i) in (let TMP_17 \def (THeads TMP_15 
ws TMP_16) in (eq T t TMP_17)))))) in (let TMP_19 \def (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_21 \def (\lambda (_: 
TList).(\lambda (i: nat).(let TMP_20 \def (TLRef i) in (nf2 c TMP_20)))) in 
(let TMP_22 \def (ex3_2 TList nat TMP_18 TMP_19 TMP_21) in (let TMP_23 \def 
(or3 TMP_11 TMP_14 TMP_22) in (let TMP_24 \def (\lambda (x: A).(\lambda (H2: 
(arity g c t x)).(\lambda (_: (arity g c u (asucc g x))).(arity_nf2_inv_all g 
c t x H2 H0)))) in (ex2_ind A TMP_1 TMP_3 TMP_23 TMP_24 
H1)))))))))))))))))))))).

theorem ty3_nf2_inv_sort:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (m: nat).((ty3 g c t 
(TSort m)) \to ((nf2 c t) \to (or (ex2 nat (\lambda (n: nat).(eq T t (TSort 
n))) (\lambda (n: nat).(eq nat m (next g n)))) (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (m: nat).(\lambda 
(H: (ty3 g c t (TSort m))).(\lambda (H0: (nf2 c t)).(let TMP_1 \def (TSort m) 
in (let H_x \def (ty3_nf2_inv_all g c t TMP_1 H H0) in (let H1 \def H_x in 
(let TMP_4 \def (\lambda (w: T).(\lambda (u: T).(let TMP_2 \def (Bind Abst) 
in (let TMP_3 \def (THead TMP_2 w u) in (eq T t TMP_3))))) in (let TMP_5 \def 
(\lambda (w: T).(\lambda (_: T).(nf2 c w))) in (let TMP_8 \def (\lambda (w: 
T).(\lambda (u: T).(let TMP_6 \def (Bind Abst) in (let TMP_7 \def (CHead c 
TMP_6 w) in (nf2 TMP_7 u))))) in (let TMP_9 \def (ex3_2 T T TMP_4 TMP_5 
TMP_8) in (let TMP_11 \def (\lambda (n: nat).(let TMP_10 \def (TSort n) in 
(eq T t TMP_10))) in (let TMP_12 \def (ex nat TMP_11) in (let TMP_16 \def 
(\lambda (ws: TList).(\lambda (i: nat).(let TMP_13 \def (Flat Appl) in (let 
TMP_14 \def (TLRef i) in (let TMP_15 \def (THeads TMP_13 ws TMP_14) in (eq T 
t TMP_15)))))) in (let TMP_17 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_19 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_18 \def (TLRef i) in (nf2 c TMP_18)))) in (let TMP_20 \def 
(ex3_2 TList nat TMP_16 TMP_17 TMP_19) in (let TMP_22 \def (\lambda (n: 
nat).(let TMP_21 \def (TSort n) in (eq T t TMP_21))) in (let TMP_24 \def 
(\lambda (n: nat).(let TMP_23 \def (next g n) in (eq nat m TMP_23))) in (let 
TMP_25 \def (ex2 nat TMP_22 TMP_24) in (let TMP_29 \def (\lambda (ws: 
TList).(\lambda (i: nat).(let TMP_26 \def (Flat Appl) in (let TMP_27 \def 
(TLRef i) in (let TMP_28 \def (THeads TMP_26 ws TMP_27) in (eq T t 
TMP_28)))))) in (let TMP_30 \def (\lambda (ws: TList).(\lambda (_: nat).(nfs2 
c ws))) in (let TMP_32 \def (\lambda (_: TList).(\lambda (i: nat).(let TMP_31 
\def (TLRef i) in (nf2 c TMP_31)))) in (let TMP_33 \def (ex3_2 TList nat 
TMP_29 TMP_30 TMP_32) in (let TMP_34 \def (or TMP_25 TMP_33) in (let TMP_129 
\def (\lambda (H2: (ex3_2 T T (\lambda (w: T).(\lambda (u: T).(eq T t (THead 
(Bind Abst) w u)))) (\lambda (w: T).(\lambda (_: T).(nf2 c w))) (\lambda (w: 
T).(\lambda (u: T).(nf2 (CHead c (Bind Abst) w) u))))).(let TMP_37 \def 
(\lambda (w: T).(\lambda (u: T).(let TMP_35 \def (Bind Abst) in (let TMP_36 
\def (THead TMP_35 w u) in (eq T t TMP_36))))) in (let TMP_38 \def (\lambda 
(w: T).(\lambda (_: T).(nf2 c w))) in (let TMP_41 \def (\lambda (w: 
T).(\lambda (u: T).(let TMP_39 \def (Bind Abst) in (let TMP_40 \def (CHead c 
TMP_39 w) in (nf2 TMP_40 u))))) in (let TMP_43 \def (\lambda (n: nat).(let 
TMP_42 \def (TSort n) in (eq T t TMP_42))) in (let TMP_45 \def (\lambda (n: 
nat).(let TMP_44 \def (next g n) in (eq nat m TMP_44))) in (let TMP_46 \def 
(ex2 nat TMP_43 TMP_45) in (let TMP_50 \def (\lambda (ws: TList).(\lambda (i: 
nat).(let TMP_47 \def (Flat Appl) in (let TMP_48 \def (TLRef i) in (let 
TMP_49 \def (THeads TMP_47 ws TMP_48) in (eq T t TMP_49)))))) in (let TMP_51 
\def (\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_53 \def 
(\lambda (_: TList).(\lambda (i: nat).(let TMP_52 \def (TLRef i) in (nf2 c 
TMP_52)))) in (let TMP_54 \def (ex3_2 TList nat TMP_50 TMP_51 TMP_53) in (let 
TMP_55 \def (or TMP_46 TMP_54) in (let TMP_128 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H3: (eq T t (THead (Bind Abst) x0 x1))).(\lambda (_: (nf2 c 
x0)).(\lambda (_: (nf2 (CHead c (Bind Abst) x0) x1)).(let TMP_57 \def 
(\lambda (t0: T).(let TMP_56 \def (TSort m) in (ty3 g c t0 TMP_56))) in (let 
TMP_58 \def (Bind Abst) in (let TMP_59 \def (THead TMP_58 x0 x1) in (let H6 
\def (eq_ind T t TMP_57 H TMP_59 H3) in (let TMP_60 \def (Bind Abst) in (let 
TMP_61 \def (THead TMP_60 x0 x1) in (let TMP_75 \def (\lambda (t0: T).(let 
TMP_63 \def (\lambda (n: nat).(let TMP_62 \def (TSort n) in (eq T t0 
TMP_62))) in (let TMP_65 \def (\lambda (n: nat).(let TMP_64 \def (next g n) 
in (eq nat m TMP_64))) in (let TMP_66 \def (ex2 nat TMP_63 TMP_65) in (let 
TMP_70 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_67 \def (Flat 
Appl) in (let TMP_68 \def (TLRef i) in (let TMP_69 \def (THeads TMP_67 ws 
TMP_68) in (eq T t0 TMP_69)))))) in (let TMP_71 \def (\lambda (ws: 
TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_73 \def (\lambda (_: 
TList).(\lambda (i: nat).(let TMP_72 \def (TLRef i) in (nf2 c TMP_72)))) in 
(let TMP_74 \def (ex3_2 TList nat TMP_70 TMP_71 TMP_73) in (or TMP_66 
TMP_74))))))))) in (let TMP_79 \def (\lambda (t2: T).(\lambda (_: T).(let 
TMP_76 \def (Bind Abst) in (let TMP_77 \def (THead TMP_76 x0 t2) in (let 
TMP_78 \def (TSort m) in (pc3 c TMP_77 TMP_78)))))) in (let TMP_80 \def 
(\lambda (_: T).(\lambda (t0: T).(ty3 g c x0 t0))) in (let TMP_83 \def 
(\lambda (t2: T).(\lambda (_: T).(let TMP_81 \def (Bind Abst) in (let TMP_82 
\def (CHead c TMP_81 x0) in (ty3 g TMP_82 x1 t2))))) in (let TMP_87 \def 
(\lambda (n: nat).(let TMP_84 \def (Bind Abst) in (let TMP_85 \def (THead 
TMP_84 x0 x1) in (let TMP_86 \def (TSort n) in (eq T TMP_85 TMP_86))))) in 
(let TMP_89 \def (\lambda (n: nat).(let TMP_88 \def (next g n) in (eq nat m 
TMP_88))) in (let TMP_90 \def (ex2 nat TMP_87 TMP_89) in (let TMP_96 \def 
(\lambda (ws: TList).(\lambda (i: nat).(let TMP_91 \def (Bind Abst) in (let 
TMP_92 \def (THead TMP_91 x0 x1) in (let TMP_93 \def (Flat Appl) in (let 
TMP_94 \def (TLRef i) in (let TMP_95 \def (THeads TMP_93 ws TMP_94) in (eq T 
TMP_92 TMP_95)))))))) in (let TMP_97 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_99 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_98 \def (TLRef i) in (nf2 c TMP_98)))) in (let TMP_100 \def 
(ex3_2 TList nat TMP_96 TMP_97 TMP_99) in (let TMP_101 \def (or TMP_90 
TMP_100) in (let TMP_124 \def (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: 
(pc3 c (THead (Bind Abst) x0 x2) (TSort m))).(\lambda (_: (ty3 g c x0 
x3)).(\lambda (_: (ty3 g (CHead c (Bind Abst) x0) x1 x2)).(let TMP_102 \def 
(TSort m) in (let TMP_103 \def (Bind Abst) in (let TMP_104 \def (THead 
TMP_103 x0 x2) in (let TMP_105 \def (pc3_s c TMP_102 TMP_104 H7) in (let 
TMP_109 \def (\lambda (n: nat).(let TMP_106 \def (Bind Abst) in (let TMP_107 
\def (THead TMP_106 x0 x1) in (let TMP_108 \def (TSort n) in (eq T TMP_107 
TMP_108))))) in (let TMP_111 \def (\lambda (n: nat).(let TMP_110 \def (next g 
n) in (eq nat m TMP_110))) in (let TMP_112 \def (ex2 nat TMP_109 TMP_111) in 
(let TMP_118 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_113 \def 
(Bind Abst) in (let TMP_114 \def (THead TMP_113 x0 x1) in (let TMP_115 \def 
(Flat Appl) in (let TMP_116 \def (TLRef i) in (let TMP_117 \def (THeads 
TMP_115 ws TMP_116) in (eq T TMP_114 TMP_117)))))))) in (let TMP_119 \def 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_121 \def 
(\lambda (_: TList).(\lambda (i: nat).(let TMP_120 \def (TLRef i) in (nf2 c 
TMP_120)))) in (let TMP_122 \def (ex3_2 TList nat TMP_118 TMP_119 TMP_121) in 
(let TMP_123 \def (or TMP_112 TMP_122) in (pc3_gen_sort_abst c x0 x2 m 
TMP_105 TMP_123)))))))))))))))))) in (let TMP_125 \def (TSort m) in (let 
TMP_126 \def (ty3_gen_bind g Abst c x0 x1 TMP_125 H6) in (let TMP_127 \def 
(ex3_2_ind T T TMP_79 TMP_80 TMP_83 TMP_101 TMP_124 TMP_126) in (eq_ind_r T 
TMP_61 TMP_75 TMP_127 t H3)))))))))))))))))))))))))))) in (ex3_2_ind T T 
TMP_37 TMP_38 TMP_41 TMP_55 TMP_128 H2)))))))))))))) in (let TMP_215 \def 
(\lambda (H2: (ex nat (\lambda (n: nat).(eq T t (TSort n))))).(let TMP_131 
\def (\lambda (n: nat).(let TMP_130 \def (TSort n) in (eq T t TMP_130))) in 
(let TMP_133 \def (\lambda (n: nat).(let TMP_132 \def (TSort n) in (eq T t 
TMP_132))) in (let TMP_135 \def (\lambda (n: nat).(let TMP_134 \def (next g 
n) in (eq nat m TMP_134))) in (let TMP_136 \def (ex2 nat TMP_133 TMP_135) in 
(let TMP_140 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_137 \def 
(Flat Appl) in (let TMP_138 \def (TLRef i) in (let TMP_139 \def (THeads 
TMP_137 ws TMP_138) in (eq T t TMP_139)))))) in (let TMP_141 \def (\lambda 
(ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_143 \def (\lambda (_: 
TList).(\lambda (i: nat).(let TMP_142 \def (TLRef i) in (nf2 c TMP_142)))) in 
(let TMP_144 \def (ex3_2 TList nat TMP_140 TMP_141 TMP_143) in (let TMP_145 
\def (or TMP_136 TMP_144) in (let TMP_214 \def (\lambda (x: nat).(\lambda 
(H3: (eq T t (TSort x))).(let TMP_147 \def (\lambda (t0: T).(let TMP_146 \def 
(TSort m) in (ty3 g c t0 TMP_146))) in (let TMP_148 \def (TSort x) in (let H4 
\def (eq_ind T t TMP_147 H TMP_148 H3) in (let TMP_149 \def (TSort x) in (let 
TMP_163 \def (\lambda (t0: T).(let TMP_151 \def (\lambda (n: nat).(let 
TMP_150 \def (TSort n) in (eq T t0 TMP_150))) in (let TMP_153 \def (\lambda 
(n: nat).(let TMP_152 \def (next g n) in (eq nat m TMP_152))) in (let TMP_154 
\def (ex2 nat TMP_151 TMP_153) in (let TMP_158 \def (\lambda (ws: 
TList).(\lambda (i: nat).(let TMP_155 \def (Flat Appl) in (let TMP_156 \def 
(TLRef i) in (let TMP_157 \def (THeads TMP_155 ws TMP_156) in (eq T t0 
TMP_157)))))) in (let TMP_159 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_161 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_160 \def (TLRef i) in (nf2 c TMP_160)))) in (let TMP_162 \def 
(ex3_2 TList nat TMP_158 TMP_159 TMP_161) in (or TMP_154 TMP_162))))))))) in 
(let TMP_164 \def (next g x) in (let TMP_180 \def (\lambda (n: nat).(let 
TMP_167 \def (\lambda (n0: nat).(let TMP_165 \def (TSort x) in (let TMP_166 
\def (TSort n0) in (eq T TMP_165 TMP_166)))) in (let TMP_169 \def (\lambda 
(n0: nat).(let TMP_168 \def (next g n0) in (eq nat n TMP_168))) in (let 
TMP_170 \def (ex2 nat TMP_167 TMP_169) in (let TMP_175 \def (\lambda (ws: 
TList).(\lambda (i: nat).(let TMP_171 \def (TSort x) in (let TMP_172 \def 
(Flat Appl) in (let TMP_173 \def (TLRef i) in (let TMP_174 \def (THeads 
TMP_172 ws TMP_173) in (eq T TMP_171 TMP_174))))))) in (let TMP_176 \def 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_178 \def 
(\lambda (_: TList).(\lambda (i: nat).(let TMP_177 \def (TLRef i) in (nf2 c 
TMP_177)))) in (let TMP_179 \def (ex3_2 TList nat TMP_175 TMP_176 TMP_178) in 
(or TMP_170 TMP_179))))))))) in (let TMP_183 \def (\lambda (n: nat).(let 
TMP_181 \def (TSort x) in (let TMP_182 \def (TSort n) in (eq T TMP_181 
TMP_182)))) in (let TMP_186 \def (\lambda (n: nat).(let TMP_184 \def (next g 
x) in (let TMP_185 \def (next g n) in (eq nat TMP_184 TMP_185)))) in (let 
TMP_187 \def (ex2 nat TMP_183 TMP_186) in (let TMP_192 \def (\lambda (ws: 
TList).(\lambda (i: nat).(let TMP_188 \def (TSort x) in (let TMP_189 \def 
(Flat Appl) in (let TMP_190 \def (TLRef i) in (let TMP_191 \def (THeads 
TMP_189 ws TMP_190) in (eq T TMP_188 TMP_191))))))) in (let TMP_193 \def 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_195 \def 
(\lambda (_: TList).(\lambda (i: nat).(let TMP_194 \def (TLRef i) in (nf2 c 
TMP_194)))) in (let TMP_196 \def (ex3_2 TList nat TMP_192 TMP_193 TMP_195) in 
(let TMP_199 \def (\lambda (n: nat).(let TMP_197 \def (TSort x) in (let 
TMP_198 \def (TSort n) in (eq T TMP_197 TMP_198)))) in (let TMP_202 \def 
(\lambda (n: nat).(let TMP_200 \def (next g x) in (let TMP_201 \def (next g 
n) in (eq nat TMP_200 TMP_201)))) in (let TMP_203 \def (TSort x) in (let 
TMP_204 \def (refl_equal T TMP_203) in (let TMP_205 \def (next g x) in (let 
TMP_206 \def (refl_equal nat TMP_205) in (let TMP_207 \def (ex_intro2 nat 
TMP_199 TMP_202 x TMP_204 TMP_206) in (let TMP_208 \def (or_introl TMP_187 
TMP_196 TMP_207) in (let TMP_209 \def (next g x) in (let TMP_210 \def (TSort 
m) in (let TMP_211 \def (ty3_gen_sort g c TMP_210 x H4) in (let TMP_212 \def 
(pc3_gen_sort c TMP_209 m TMP_211) in (let TMP_213 \def (eq_ind nat TMP_164 
TMP_180 TMP_208 m TMP_212) in (eq_ind_r T TMP_149 TMP_163 TMP_213 t 
H3)))))))))))))))))))))))))))))) in (ex_ind nat TMP_131 TMP_145 TMP_214 
H2)))))))))))) in (let TMP_295 \def (\lambda (H2: (ex3_2 TList nat (\lambda 
(ws: TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))).(let TMP_219 \def (\lambda 
(ws: TList).(\lambda (i: nat).(let TMP_216 \def (Flat Appl) in (let TMP_217 
\def (TLRef i) in (let TMP_218 \def (THeads TMP_216 ws TMP_217) in (eq T t 
TMP_218)))))) in (let TMP_220 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_222 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_221 \def (TLRef i) in (nf2 c TMP_221)))) in (let TMP_224 \def 
(\lambda (n: nat).(let TMP_223 \def (TSort n) in (eq T t TMP_223))) in (let 
TMP_226 \def (\lambda (n: nat).(let TMP_225 \def (next g n) in (eq nat m 
TMP_225))) in (let TMP_227 \def (ex2 nat TMP_224 TMP_226) in (let TMP_231 
\def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_228 \def (Flat Appl) in 
(let TMP_229 \def (TLRef i) in (let TMP_230 \def (THeads TMP_228 ws TMP_229) 
in (eq T t TMP_230)))))) in (let TMP_232 \def (\lambda (ws: TList).(\lambda 
(_: nat).(nfs2 c ws))) in (let TMP_234 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_233 \def (TLRef i) in (nf2 c TMP_233)))) in (let TMP_235 \def 
(ex3_2 TList nat TMP_231 TMP_232 TMP_234) in (let TMP_236 \def (or TMP_227 
TMP_235) in (let TMP_294 \def (\lambda (x0: TList).(\lambda (x1: 
nat).(\lambda (H3: (eq T t (THeads (Flat Appl) x0 (TLRef x1)))).(\lambda (H4: 
(nfs2 c x0)).(\lambda (H5: (nf2 c (TLRef x1))).(let TMP_238 \def (\lambda 
(t0: T).(let TMP_237 \def (TSort m) in (ty3 g c t0 TMP_237))) in (let TMP_239 
\def (Flat Appl) in (let TMP_240 \def (TLRef x1) in (let TMP_241 \def (THeads 
TMP_239 x0 TMP_240) in (let H6 \def (eq_ind T t TMP_238 H TMP_241 H3) in (let 
TMP_242 \def (Flat Appl) in (let TMP_243 \def (TLRef x1) in (let TMP_244 \def 
(THeads TMP_242 x0 TMP_243) in (let TMP_258 \def (\lambda (t0: T).(let 
TMP_246 \def (\lambda (n: nat).(let TMP_245 \def (TSort n) in (eq T t0 
TMP_245))) in (let TMP_248 \def (\lambda (n: nat).(let TMP_247 \def (next g 
n) in (eq nat m TMP_247))) in (let TMP_249 \def (ex2 nat TMP_246 TMP_248) in 
(let TMP_253 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_250 \def 
(Flat Appl) in (let TMP_251 \def (TLRef i) in (let TMP_252 \def (THeads 
TMP_250 ws TMP_251) in (eq T t0 TMP_252)))))) in (let TMP_254 \def (\lambda 
(ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_256 \def (\lambda (_: 
TList).(\lambda (i: nat).(let TMP_255 \def (TLRef i) in (nf2 c TMP_255)))) in 
(let TMP_257 \def (ex3_2 TList nat TMP_253 TMP_254 TMP_256) in (or TMP_249 
TMP_257))))))))) in (let TMP_263 \def (\lambda (n: nat).(let TMP_259 \def 
(Flat Appl) in (let TMP_260 \def (TLRef x1) in (let TMP_261 \def (THeads 
TMP_259 x0 TMP_260) in (let TMP_262 \def (TSort n) in (eq T TMP_261 
TMP_262)))))) in (let TMP_265 \def (\lambda (n: nat).(let TMP_264 \def (next 
g n) in (eq nat m TMP_264))) in (let TMP_266 \def (ex2 nat TMP_263 TMP_265) 
in (let TMP_273 \def (\lambda (ws: TList).(\lambda (i: nat).(let TMP_267 \def 
(Flat Appl) in (let TMP_268 \def (TLRef x1) in (let TMP_269 \def (THeads 
TMP_267 x0 TMP_268) in (let TMP_270 \def (Flat Appl) in (let TMP_271 \def 
(TLRef i) in (let TMP_272 \def (THeads TMP_270 ws TMP_271) in (eq T TMP_269 
TMP_272))))))))) in (let TMP_274 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_276 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_275 \def (TLRef i) in (nf2 c TMP_275)))) in (let TMP_277 \def 
(ex3_2 TList nat TMP_273 TMP_274 TMP_276) in (let TMP_284 \def (\lambda (ws: 
TList).(\lambda (i: nat).(let TMP_278 \def (Flat Appl) in (let TMP_279 \def 
(TLRef x1) in (let TMP_280 \def (THeads TMP_278 x0 TMP_279) in (let TMP_281 
\def (Flat Appl) in (let TMP_282 \def (TLRef i) in (let TMP_283 \def (THeads 
TMP_281 ws TMP_282) in (eq T TMP_280 TMP_283))))))))) in (let TMP_285 \def 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) in (let TMP_287 \def 
(\lambda (_: TList).(\lambda (i: nat).(let TMP_286 \def (TLRef i) in (nf2 c 
TMP_286)))) in (let TMP_288 \def (Flat Appl) in (let TMP_289 \def (TLRef x1) 
in (let TMP_290 \def (THeads TMP_288 x0 TMP_289) in (let TMP_291 \def 
(refl_equal T TMP_290) in (let TMP_292 \def (ex3_2_intro TList nat TMP_284 
TMP_285 TMP_287 x0 x1 TMP_291 H4 H5) in (let TMP_293 \def (or_intror TMP_266 
TMP_277 TMP_292) in (eq_ind_r T TMP_244 TMP_258 TMP_293 t 
H3))))))))))))))))))))))))))))))) in (ex3_2_ind TList nat TMP_219 TMP_220 
TMP_222 TMP_236 TMP_294 H2)))))))))))))) in (or3_ind TMP_9 TMP_12 TMP_20 
TMP_34 TMP_129 TMP_215 TMP_295 H1)))))))))))))))))))))))))))))).

theorem ty3_nf2_gen__ty3_nf2_inv_abst_aux:
 \forall (c: C).(\forall (w1: T).(\forall (u1: T).((ty3_nf2_inv_abst_premise 
c w1 u1) \to (\forall (t: T).(\forall (w2: T).(\forall (u2: T).((pc3 c (THead 
(Flat Appl) t (THead (Bind Abst) w2 u2)) (THead (Bind Abst) w1 u1)) \to 
(ty3_nf2_inv_abst_premise c w2 u2))))))))
\def
 \lambda (c: C).(\lambda (w1: T).(\lambda (u1: T).(\lambda (H: ((\forall (d: 
C).(\forall (wi: T).(\forall (i: nat).((getl i c (CHead d (Bind Abst) wi)) 
\to (\forall (vs: TList).((pc3 c (THeads (Flat Appl) vs (lift (S i) O wi)) 
(THead (Bind Abst) w1 u1)) \to False)))))))).(\lambda (t: T).(\lambda (w2: 
T).(\lambda (u2: T).(\lambda (H0: (pc3 c (THead (Flat Appl) t (THead (Bind 
Abst) w2 u2)) (THead (Bind Abst) w1 u1))).(\lambda (d: C).(\lambda (wi: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c (CHead d (Bind Abst) 
wi))).(\lambda (vs: TList).(\lambda (H2: (pc3 c (THeads (Flat Appl) vs (lift 
(S i) O wi)) (THead (Bind Abst) w2 u2))).(let TMP_1 \def (TCons t vs) in (let 
TMP_2 \def (Flat Appl) in (let TMP_3 \def (Bind Abst) in (let TMP_4 \def 
(THead TMP_3 w2 u2) in (let TMP_5 \def (THead TMP_2 t TMP_4) in (let TMP_6 
\def (Flat Appl) in (let TMP_7 \def (Flat Appl) in (let TMP_8 \def (S i) in 
(let TMP_9 \def (lift TMP_8 O wi) in (let TMP_10 \def (THeads TMP_7 vs TMP_9) 
in (let TMP_11 \def (THead TMP_6 t TMP_10) in (let TMP_12 \def (Flat Appl) in 
(let TMP_13 \def (S i) in (let TMP_14 \def (lift TMP_13 O wi) in (let TMP_15 
\def (THeads TMP_12 vs TMP_14) in (let TMP_16 \def (Bind Abst) in (let TMP_17 
\def (THead TMP_16 w2 u2) in (let TMP_18 \def (pc3_thin_dx c TMP_15 TMP_17 H2 
t Appl) in (let TMP_19 \def (Bind Abst) in (let TMP_20 \def (THead TMP_19 w1 
u1) in (let TMP_21 \def (pc3_t TMP_5 c TMP_11 TMP_18 TMP_20 H0) in (H d wi i 
H1 TMP_1 TMP_21))))))))))))))))))))))))))))))))))).

theorem ty3_nf2_inv_abst:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (w: T).(\forall (u: 
T).((ty3 g c t (THead (Bind Abst) w u)) \to ((nf2 c t) \to ((nf2 c w) \to 
((ty3_nf2_inv_abst_premise c w u) \to (ex4_2 T T (\lambda (v: T).(\lambda (_: 
T).(eq T t (THead (Bind Abst) w v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g 
c w w0))) (\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) w) v 
u))) (\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) w) 
v))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (w: T).(\lambda (u: 
T).(\lambda (H: (ty3 g c t (THead (Bind Abst) w u))).(\lambda (H0: (nf2 c 
t)).(\lambda (H1: (nf2 c w)).(\lambda (H2: (ty3_nf2_inv_abst_premise c w 
u)).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (THead TMP_1 w u) in (let 
H_x \def (ty3_nf2_inv_all g c t TMP_2 H H0) in (let H3 \def H_x in (let TMP_5 
\def (\lambda (w0: T).(\lambda (u0: T).(let TMP_3 \def (Bind Abst) in (let 
TMP_4 \def (THead TMP_3 w0 u0) in (eq T t TMP_4))))) in (let TMP_6 \def 
(\lambda (w0: T).(\lambda (_: T).(nf2 c w0))) in (let TMP_9 \def (\lambda 
(w0: T).(\lambda (u0: T).(let TMP_7 \def (Bind Abst) in (let TMP_8 \def 
(CHead c TMP_7 w0) in (nf2 TMP_8 u0))))) in (let TMP_10 \def (ex3_2 T T TMP_5 
TMP_6 TMP_9) in (let TMP_12 \def (\lambda (n: nat).(let TMP_11 \def (TSort n) 
in (eq T t TMP_11))) in (let TMP_13 \def (ex nat TMP_12) in (let TMP_17 \def 
(\lambda (ws: TList).(\lambda (i: nat).(let TMP_14 \def (Flat Appl) in (let 
TMP_15 \def (TLRef i) in (let TMP_16 \def (THeads TMP_14 ws TMP_15) in (eq T 
t TMP_16)))))) in (let TMP_18 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_20 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_19 \def (TLRef i) in (nf2 c TMP_19)))) in (let TMP_21 \def 
(ex3_2 TList nat TMP_17 TMP_18 TMP_20) in (let TMP_24 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_22 \def (Bind Abst) in (let TMP_23 \def (THead 
TMP_22 w v) in (eq T t TMP_23))))) in (let TMP_25 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_28 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_26 \def (Bind Abst) in (let TMP_27 \def (CHead c 
TMP_26 w) in (ty3 g TMP_27 v u))))) in (let TMP_31 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_29 \def (Bind Abst) in (let TMP_30 \def (CHead c 
TMP_29 w) in (nf2 TMP_30 v))))) in (let TMP_32 \def (ex4_2 T T TMP_24 TMP_25 
TMP_28 TMP_31) in (let TMP_199 \def (\lambda (H4: (ex3_2 T T (\lambda (w0: 
T).(\lambda (u0: T).(eq T t (THead (Bind Abst) w0 u0)))) (\lambda (w0: 
T).(\lambda (_: T).(nf2 c w0))) (\lambda (w0: T).(\lambda (u0: T).(nf2 (CHead 
c (Bind Abst) w0) u0))))).(let TMP_35 \def (\lambda (w0: T).(\lambda (u0: 
T).(let TMP_33 \def (Bind Abst) in (let TMP_34 \def (THead TMP_33 w0 u0) in 
(eq T t TMP_34))))) in (let TMP_36 \def (\lambda (w0: T).(\lambda (_: T).(nf2 
c w0))) in (let TMP_39 \def (\lambda (w0: T).(\lambda (u0: T).(let TMP_37 
\def (Bind Abst) in (let TMP_38 \def (CHead c TMP_37 w0) in (nf2 TMP_38 
u0))))) in (let TMP_42 \def (\lambda (v: T).(\lambda (_: T).(let TMP_40 \def 
(Bind Abst) in (let TMP_41 \def (THead TMP_40 w v) in (eq T t TMP_41))))) in 
(let TMP_43 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let 
TMP_46 \def (\lambda (v: T).(\lambda (_: T).(let TMP_44 \def (Bind Abst) in 
(let TMP_45 \def (CHead c TMP_44 w) in (ty3 g TMP_45 v u))))) in (let TMP_49 
\def (\lambda (v: T).(\lambda (_: T).(let TMP_47 \def (Bind Abst) in (let 
TMP_48 \def (CHead c TMP_47 w) in (nf2 TMP_48 v))))) in (let TMP_50 \def 
(ex4_2 T T TMP_42 TMP_43 TMP_46 TMP_49) in (let TMP_198 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H5: (eq T t (THead (Bind Abst) x0 
x1))).(\lambda (H6: (nf2 c x0)).(\lambda (H7: (nf2 (CHead c (Bind Abst) x0) 
x1)).(let TMP_53 \def (\lambda (t0: T).(let TMP_51 \def (Bind Abst) in (let 
TMP_52 \def (THead TMP_51 w u) in (ty3 g c t0 TMP_52)))) in (let TMP_54 \def 
(Bind Abst) in (let TMP_55 \def (THead TMP_54 x0 x1) in (let H8 \def (eq_ind 
T t TMP_53 H TMP_55 H5) in (let TMP_56 \def (Bind Abst) in (let TMP_57 \def 
(THead TMP_56 x0 x1) in (let TMP_68 \def (\lambda (t0: T).(let TMP_60 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_58 \def (Bind Abst) in (let TMP_59 
\def (THead TMP_58 w v) in (eq T t0 TMP_59))))) in (let TMP_61 \def (\lambda 
(_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_64 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_62 \def (Bind Abst) in (let TMP_63 \def (CHead c 
TMP_62 w) in (ty3 g TMP_63 v u))))) in (let TMP_67 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_65 \def (Bind Abst) in (let TMP_66 \def (CHead c 
TMP_65 w) in (nf2 TMP_66 v))))) in (ex4_2 T T TMP_60 TMP_61 TMP_64 
TMP_67)))))) in (let TMP_71 \def (\lambda (t0: T).(let TMP_69 \def (Bind 
Abst) in (let TMP_70 \def (THead TMP_69 w u) in (ty3 g c TMP_70 t0)))) in 
(let TMP_76 \def (\lambda (v: T).(\lambda (_: T).(let TMP_72 \def (Bind Abst) 
in (let TMP_73 \def (THead TMP_72 x0 x1) in (let TMP_74 \def (Bind Abst) in 
(let TMP_75 \def (THead TMP_74 w v) in (eq T TMP_73 TMP_75))))))) in (let 
TMP_77 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_80 
\def (\lambda (v: T).(\lambda (_: T).(let TMP_78 \def (Bind Abst) in (let 
TMP_79 \def (CHead c TMP_78 w) in (ty3 g TMP_79 v u))))) in (let TMP_83 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_81 \def (Bind Abst) in (let TMP_82 
\def (CHead c TMP_81 w) in (nf2 TMP_82 v))))) in (let TMP_84 \def (ex4_2 T T 
TMP_76 TMP_77 TMP_80 TMP_83) in (let TMP_191 \def (\lambda (x: T).(\lambda 
(H9: (ty3 g c (THead (Bind Abst) w u) x)).(let TMP_87 \def (\lambda (t2: 
T).(\lambda (_: T).(let TMP_85 \def (Bind Abst) in (let TMP_86 \def (THead 
TMP_85 w t2) in (pc3 c TMP_86 x))))) in (let TMP_88 \def (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c w t0))) in (let TMP_91 \def (\lambda (t2: 
T).(\lambda (_: T).(let TMP_89 \def (Bind Abst) in (let TMP_90 \def (CHead c 
TMP_89 w) in (ty3 g TMP_90 u t2))))) in (let TMP_96 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_92 \def (Bind Abst) in (let TMP_93 \def (THead 
TMP_92 x0 x1) in (let TMP_94 \def (Bind Abst) in (let TMP_95 \def (THead 
TMP_94 w v) in (eq T TMP_93 TMP_95))))))) in (let TMP_97 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_100 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_98 \def (Bind Abst) in (let TMP_99 \def (CHead c 
TMP_98 w) in (ty3 g TMP_99 v u))))) in (let TMP_103 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_101 \def (Bind Abst) in (let TMP_102 \def (CHead 
c TMP_101 w) in (nf2 TMP_102 v))))) in (let TMP_104 \def (ex4_2 T T TMP_96 
TMP_97 TMP_100 TMP_103) in (let TMP_189 \def (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (_: (pc3 c (THead (Bind Abst) w x2) x)).(\lambda (H11: (ty3 g c w 
x3)).(\lambda (H12: (ty3 g (CHead c (Bind Abst) w) u x2)).(let TMP_109 \def 
(\lambda (t2: T).(\lambda (_: T).(let TMP_105 \def (Bind Abst) in (let 
TMP_106 \def (THead TMP_105 x0 t2) in (let TMP_107 \def (Bind Abst) in (let 
TMP_108 \def (THead TMP_107 w u) in (pc3 c TMP_106 TMP_108))))))) in (let 
TMP_110 \def (\lambda (_: T).(\lambda (t0: T).(ty3 g c x0 t0))) in (let 
TMP_113 \def (\lambda (t2: T).(\lambda (_: T).(let TMP_111 \def (Bind Abst) 
in (let TMP_112 \def (CHead c TMP_111 x0) in (ty3 g TMP_112 x1 t2))))) in 
(let TMP_118 \def (\lambda (v: T).(\lambda (_: T).(let TMP_114 \def (Bind 
Abst) in (let TMP_115 \def (THead TMP_114 x0 x1) in (let TMP_116 \def (Bind 
Abst) in (let TMP_117 \def (THead TMP_116 w v) in (eq T TMP_115 
TMP_117))))))) in (let TMP_119 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c 
w w0))) in (let TMP_122 \def (\lambda (v: T).(\lambda (_: T).(let TMP_120 
\def (Bind Abst) in (let TMP_121 \def (CHead c TMP_120 w) in (ty3 g TMP_121 v 
u))))) in (let TMP_125 \def (\lambda (v: T).(\lambda (_: T).(let TMP_123 \def 
(Bind Abst) in (let TMP_124 \def (CHead c TMP_123 w) in (nf2 TMP_124 v))))) 
in (let TMP_126 \def (ex4_2 T T TMP_118 TMP_119 TMP_122 TMP_125) in (let 
TMP_185 \def (\lambda (x4: T).(\lambda (x5: T).(\lambda (H13: (pc3 c (THead 
(Bind Abst) x0 x4) (THead (Bind Abst) w u))).(\lambda (_: (ty3 g c x0 
x5)).(\lambda (H15: (ty3 g (CHead c (Bind Abst) x0) x1 x4)).(let TMP_127 \def 
(pc3 c x0 w) in (let TMP_130 \def (\forall (b: B).(\forall (u0: T).(let 
TMP_128 \def (Bind b) in (let TMP_129 \def (CHead c TMP_128 u0) in (pc3 
TMP_129 x4 u))))) in (let TMP_135 \def (\lambda (v: T).(\lambda (_: T).(let 
TMP_131 \def (Bind Abst) in (let TMP_132 \def (THead TMP_131 x0 x1) in (let 
TMP_133 \def (Bind Abst) in (let TMP_134 \def (THead TMP_133 w v) in (eq T 
TMP_132 TMP_134))))))) in (let TMP_136 \def (\lambda (_: T).(\lambda (w0: 
T).(ty3 g c w w0))) in (let TMP_139 \def (\lambda (v: T).(\lambda (_: T).(let 
TMP_137 \def (Bind Abst) in (let TMP_138 \def (CHead c TMP_137 w) in (ty3 g 
TMP_138 v u))))) in (let TMP_142 \def (\lambda (v: T).(\lambda (_: T).(let 
TMP_140 \def (Bind Abst) in (let TMP_141 \def (CHead c TMP_140 w) in (nf2 
TMP_141 v))))) in (let TMP_143 \def (ex4_2 T T TMP_135 TMP_136 TMP_139 
TMP_142) in (let TMP_183 \def (\lambda (H16: (pc3 c x0 w)).(\lambda (H17: 
((\forall (b: B).(\forall (u0: T).(pc3 (CHead c (Bind b) u0) x4 u))))).(let 
H_y \def (pc3_nf2 c x0 w H16 H6 H1) in (let TMP_146 \def (\lambda (t0: 
T).(let TMP_144 \def (Bind Abst) in (let TMP_145 \def (CHead c TMP_144 t0) in 
(ty3 g TMP_145 x1 x4)))) in (let H18 \def (eq_ind T x0 TMP_146 H15 w H_y) in 
(let TMP_149 \def (\lambda (t0: T).(let TMP_147 \def (Bind Abst) in (let 
TMP_148 \def (CHead c TMP_147 t0) in (nf2 TMP_148 x1)))) in (let H19 \def 
(eq_ind T x0 TMP_149 H7 w H_y) in (let TMP_162 \def (\lambda (t0: T).(let 
TMP_154 \def (\lambda (v: T).(\lambda (_: T).(let TMP_150 \def (Bind Abst) in 
(let TMP_151 \def (THead TMP_150 t0 x1) in (let TMP_152 \def (Bind Abst) in 
(let TMP_153 \def (THead TMP_152 w v) in (eq T TMP_151 TMP_153))))))) in (let 
TMP_155 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let 
TMP_158 \def (\lambda (v: T).(\lambda (_: T).(let TMP_156 \def (Bind Abst) in 
(let TMP_157 \def (CHead c TMP_156 w) in (ty3 g TMP_157 v u))))) in (let 
TMP_161 \def (\lambda (v: T).(\lambda (_: T).(let TMP_159 \def (Bind Abst) in 
(let TMP_160 \def (CHead c TMP_159 w) in (nf2 TMP_160 v))))) in (ex4_2 T T 
TMP_154 TMP_155 TMP_158 TMP_161)))))) in (let TMP_167 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_163 \def (Bind Abst) in (let TMP_164 \def (THead 
TMP_163 w x1) in (let TMP_165 \def (Bind Abst) in (let TMP_166 \def (THead 
TMP_165 w v) in (eq T TMP_164 TMP_166))))))) in (let TMP_168 \def (\lambda 
(_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_171 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_169 \def (Bind Abst) in (let TMP_170 \def (CHead 
c TMP_169 w) in (ty3 g TMP_170 v u))))) in (let TMP_174 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_172 \def (Bind Abst) in (let TMP_173 \def (CHead 
c TMP_172 w) in (nf2 TMP_173 v))))) in (let TMP_175 \def (Bind Abst) in (let 
TMP_176 \def (THead TMP_175 w x1) in (let TMP_177 \def (refl_equal T TMP_176) 
in (let TMP_178 \def (Bind Abst) in (let TMP_179 \def (CHead c TMP_178 w) in 
(let TMP_180 \def (H17 Abst w) in (let TMP_181 \def (ty3_conv g TMP_179 u x2 
H12 x1 x4 H18 TMP_180) in (let TMP_182 \def (ex4_2_intro T T TMP_167 TMP_168 
TMP_171 TMP_174 x1 x3 TMP_177 H11 TMP_181 H19) in (eq_ind_r T w TMP_162 
TMP_182 x0 H_y))))))))))))))))))))) in (let TMP_184 \def (pc3_gen_abst c x0 w 
x4 u H13) in (land_ind TMP_127 TMP_130 TMP_143 TMP_183 TMP_184))))))))))))))) 
in (let TMP_186 \def (Bind Abst) in (let TMP_187 \def (THead TMP_186 w u) in 
(let TMP_188 \def (ty3_gen_bind g Abst c x0 x1 TMP_187 H8) in (ex3_2_ind T T 
TMP_109 TMP_110 TMP_113 TMP_126 TMP_185 TMP_188)))))))))))))))))) in (let 
TMP_190 \def (ty3_gen_bind g Abst c w u x H9) in (ex3_2_ind T T TMP_87 TMP_88 
TMP_91 TMP_104 TMP_189 TMP_190))))))))))))) in (let TMP_192 \def (Bind Abst) 
in (let TMP_193 \def (THead TMP_192 x0 x1) in (let TMP_194 \def (Bind Abst) 
in (let TMP_195 \def (THead TMP_194 w u) in (let TMP_196 \def (ty3_correct g 
c TMP_193 TMP_195 H8) in (let TMP_197 \def (ex_ind T TMP_71 TMP_84 TMP_191 
TMP_196) in (eq_ind_r T TMP_57 TMP_68 TMP_197 t H5)))))))))))))))))))))))))) 
in (ex3_2_ind T T TMP_35 TMP_36 TMP_39 TMP_50 TMP_198 H4))))))))))) in (let 
TMP_247 \def (\lambda (H4: (ex nat (\lambda (n: nat).(eq T t (TSort 
n))))).(let TMP_201 \def (\lambda (n: nat).(let TMP_200 \def (TSort n) in (eq 
T t TMP_200))) in (let TMP_204 \def (\lambda (v: T).(\lambda (_: T).(let 
TMP_202 \def (Bind Abst) in (let TMP_203 \def (THead TMP_202 w v) in (eq T t 
TMP_203))))) in (let TMP_205 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w 
w0))) in (let TMP_208 \def (\lambda (v: T).(\lambda (_: T).(let TMP_206 \def 
(Bind Abst) in (let TMP_207 \def (CHead c TMP_206 w) in (ty3 g TMP_207 v 
u))))) in (let TMP_211 \def (\lambda (v: T).(\lambda (_: T).(let TMP_209 \def 
(Bind Abst) in (let TMP_210 \def (CHead c TMP_209 w) in (nf2 TMP_210 v))))) 
in (let TMP_212 \def (ex4_2 T T TMP_204 TMP_205 TMP_208 TMP_211) in (let 
TMP_246 \def (\lambda (x: nat).(\lambda (H5: (eq T t (TSort x))).(let TMP_215 
\def (\lambda (t0: T).(let TMP_213 \def (Bind Abst) in (let TMP_214 \def 
(THead TMP_213 w u) in (ty3 g c t0 TMP_214)))) in (let TMP_216 \def (TSort x) 
in (let H6 \def (eq_ind T t TMP_215 H TMP_216 H5) in (let TMP_217 \def (TSort 
x) in (let TMP_228 \def (\lambda (t0: T).(let TMP_220 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_218 \def (Bind Abst) in (let TMP_219 \def (THead 
TMP_218 w v) in (eq T t0 TMP_219))))) in (let TMP_221 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_224 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_222 \def (Bind Abst) in (let TMP_223 \def (CHead 
c TMP_222 w) in (ty3 g TMP_223 v u))))) in (let TMP_227 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_225 \def (Bind Abst) in (let TMP_226 \def (CHead 
c TMP_225 w) in (nf2 TMP_226 v))))) in (ex4_2 T T TMP_220 TMP_221 TMP_224 
TMP_227)))))) in (let TMP_229 \def (next g x) in (let TMP_230 \def (Bind 
Abst) in (let TMP_231 \def (THead TMP_230 w u) in (let TMP_232 \def 
(ty3_gen_sort g c TMP_231 x H6) in (let TMP_236 \def (\lambda (v: T).(\lambda 
(_: T).(let TMP_233 \def (TSort x) in (let TMP_234 \def (Bind Abst) in (let 
TMP_235 \def (THead TMP_234 w v) in (eq T TMP_233 TMP_235)))))) in (let 
TMP_237 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let 
TMP_240 \def (\lambda (v: T).(\lambda (_: T).(let TMP_238 \def (Bind Abst) in 
(let TMP_239 \def (CHead c TMP_238 w) in (ty3 g TMP_239 v u))))) in (let 
TMP_243 \def (\lambda (v: T).(\lambda (_: T).(let TMP_241 \def (Bind Abst) in 
(let TMP_242 \def (CHead c TMP_241 w) in (nf2 TMP_242 v))))) in (let TMP_244 
\def (ex4_2 T T TMP_236 TMP_237 TMP_240 TMP_243) in (let TMP_245 \def 
(pc3_gen_sort_abst c w u TMP_229 TMP_232 TMP_244) in (eq_ind_r T TMP_217 
TMP_228 TMP_245 t H5)))))))))))))))))) in (ex_ind nat TMP_201 TMP_212 TMP_246 
H4))))))))) in (let TMP_570 \def (\lambda (H4: (ex3_2 TList nat (\lambda (ws: 
TList).(\lambda (i: nat).(eq T t (THeads (Flat Appl) ws (TLRef i))))) 
(\lambda (ws: TList).(\lambda (_: nat).(nfs2 c ws))) (\lambda (_: 
TList).(\lambda (i: nat).(nf2 c (TLRef i)))))).(let TMP_251 \def (\lambda 
(ws: TList).(\lambda (i: nat).(let TMP_248 \def (Flat Appl) in (let TMP_249 
\def (TLRef i) in (let TMP_250 \def (THeads TMP_248 ws TMP_249) in (eq T t 
TMP_250)))))) in (let TMP_252 \def (\lambda (ws: TList).(\lambda (_: 
nat).(nfs2 c ws))) in (let TMP_254 \def (\lambda (_: TList).(\lambda (i: 
nat).(let TMP_253 \def (TLRef i) in (nf2 c TMP_253)))) in (let TMP_257 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_255 \def (Bind Abst) in (let TMP_256 
\def (THead TMP_255 w v) in (eq T t TMP_256))))) in (let TMP_258 \def 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_261 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_259 \def (Bind Abst) in (let TMP_260 
\def (CHead c TMP_259 w) in (ty3 g TMP_260 v u))))) in (let TMP_264 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_262 \def (Bind Abst) in (let TMP_263 
\def (CHead c TMP_262 w) in (nf2 TMP_263 v))))) in (let TMP_265 \def (ex4_2 T 
T TMP_257 TMP_258 TMP_261 TMP_264) in (let TMP_569 \def (\lambda (x0: 
TList).(\lambda (x1: nat).(\lambda (H5: (eq T t (THeads (Flat Appl) x0 (TLRef 
x1)))).(\lambda (_: (nfs2 c x0)).(\lambda (H7: (nf2 c (TLRef x1))).(let 
TMP_268 \def (\lambda (t0: T).(let TMP_266 \def (Bind Abst) in (let TMP_267 
\def (THead TMP_266 w u) in (ty3 g c t0 TMP_267)))) in (let TMP_269 \def 
(Flat Appl) in (let TMP_270 \def (TLRef x1) in (let TMP_271 \def (THeads 
TMP_269 x0 TMP_270) in (let H8 \def (eq_ind T t TMP_268 H TMP_271 H5) in (let 
TMP_272 \def (Flat Appl) in (let TMP_273 \def (TLRef x1) in (let TMP_274 \def 
(THeads TMP_272 x0 TMP_273) in (let TMP_285 \def (\lambda (t0: T).(let 
TMP_277 \def (\lambda (v: T).(\lambda (_: T).(let TMP_275 \def (Bind Abst) in 
(let TMP_276 \def (THead TMP_275 w v) in (eq T t0 TMP_276))))) in (let 
TMP_278 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c w w0))) in (let 
TMP_281 \def (\lambda (v: T).(\lambda (_: T).(let TMP_279 \def (Bind Abst) in 
(let TMP_280 \def (CHead c TMP_279 w) in (ty3 g TMP_280 v u))))) in (let 
TMP_284 \def (\lambda (v: T).(\lambda (_: T).(let TMP_282 \def (Bind Abst) in 
(let TMP_283 \def (CHead c TMP_282 w) in (nf2 TMP_283 v))))) in (ex4_2 T T 
TMP_277 TMP_278 TMP_281 TMP_284)))))) in (let H9 \def H2 in (let H10 \def H8 
in (let TMP_299 \def (\lambda (t0: T).((ty3 g c (THeads (Flat Appl) x0 (TLRef 
x1)) (THead (Bind Abst) w t0)) \to ((ty3_nf2_inv_abst_premise c w t0) \to 
(let TMP_291 \def (\lambda (v: T).(\lambda (_: T).(let TMP_286 \def (Flat 
Appl) in (let TMP_287 \def (TLRef x1) in (let TMP_288 \def (THeads TMP_286 x0 
TMP_287) in (let TMP_289 \def (Bind Abst) in (let TMP_290 \def (THead TMP_289 
w v) in (eq T TMP_288 TMP_290)))))))) in (let TMP_292 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c w w0))) in (let TMP_295 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_293 \def (Bind Abst) in (let TMP_294 \def (CHead 
c TMP_293 w) in (ty3 g TMP_294 v t0))))) in (let TMP_298 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_296 \def (Bind Abst) in (let TMP_297 \def (CHead 
c TMP_296 w) in (nf2 TMP_297 v))))) in (ex4_2 T T TMP_291 TMP_292 TMP_295 
TMP_298)))))))) in (let TMP_313 \def (\lambda (t0: T).(\forall (x: T).((ty3 g 
c (THeads (Flat Appl) x0 (TLRef x1)) (THead (Bind Abst) t0 x)) \to 
((ty3_nf2_inv_abst_premise c t0 x) \to (let TMP_305 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_300 \def (Flat Appl) in (let TMP_301 \def (TLRef 
x1) in (let TMP_302 \def (THeads TMP_300 x0 TMP_301) in (let TMP_303 \def 
(Bind Abst) in (let TMP_304 \def (THead TMP_303 t0 v) in (eq T TMP_302 
TMP_304)))))))) in (let TMP_306 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g 
c t0 w0))) in (let TMP_309 \def (\lambda (v: T).(\lambda (_: T).(let TMP_307 
\def (Bind Abst) in (let TMP_308 \def (CHead c TMP_307 t0) in (ty3 g TMP_308 
v x))))) in (let TMP_312 \def (\lambda (v: T).(\lambda (_: T).(let TMP_310 
\def (Bind Abst) in (let TMP_311 \def (CHead c TMP_310 t0) in (nf2 TMP_311 
v))))) in (ex4_2 T T TMP_305 TMP_306 TMP_309 TMP_312))))))))) in (let TMP_327 
\def (\lambda (t0: TList).(\forall (x: T).(\forall (x2: T).((ty3 g c (THeads 
(Flat Appl) t0 (TLRef x1)) (THead (Bind Abst) x x2)) \to 
((ty3_nf2_inv_abst_premise c x x2) \to (let TMP_319 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_314 \def (Flat Appl) in (let TMP_315 \def (TLRef 
x1) in (let TMP_316 \def (THeads TMP_314 t0 TMP_315) in (let TMP_317 \def 
(Bind Abst) in (let TMP_318 \def (THead TMP_317 x v) in (eq T TMP_316 
TMP_318)))))))) in (let TMP_320 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g 
c x w0))) in (let TMP_323 \def (\lambda (v: T).(\lambda (_: T).(let TMP_321 
\def (Bind Abst) in (let TMP_322 \def (CHead c TMP_321 x) in (ty3 g TMP_322 v 
x2))))) in (let TMP_326 \def (\lambda (v: T).(\lambda (_: T).(let TMP_324 
\def (Bind Abst) in (let TMP_325 \def (CHead c TMP_324 x) in (nf2 TMP_325 
v))))) in (ex4_2 T T TMP_319 TMP_320 TMP_323 TMP_326)))))))))) in (let 
TMP_433 \def (\lambda (x: T).(\lambda (x2: T).(\lambda (H11: (ty3 g c (TLRef 
x1) (THead (Bind Abst) x x2))).(\lambda (H12: (ty3_nf2_inv_abst_premise c x 
x2)).(let TMP_332 \def (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(let 
TMP_328 \def (S x1) in (let TMP_329 \def (lift TMP_328 O t0) in (let TMP_330 
\def (Bind Abst) in (let TMP_331 \def (THead TMP_330 x x2) in (pc3 c TMP_329 
TMP_331)))))))) in (let TMP_335 \def (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(let TMP_333 \def (Bind Abbr) in (let TMP_334 \def (CHead 
e TMP_333 u0) in (getl x1 c TMP_334)))))) in (let TMP_336 \def (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))) in (let TMP_337 \def 
(ex3_3 C T T TMP_332 TMP_335 TMP_336) in (let TMP_342 \def (\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(let TMP_338 \def (S x1) in (let TMP_339 
\def (lift TMP_338 O u0) in (let TMP_340 \def (Bind Abst) in (let TMP_341 
\def (THead TMP_340 x x2) in (pc3 c TMP_339 TMP_341)))))))) in (let TMP_345 
\def (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(let TMP_343 \def (Bind 
Abst) in (let TMP_344 \def (CHead e TMP_343 u0) in (getl x1 c TMP_344)))))) 
in (let TMP_346 \def (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))) in (let TMP_347 \def (ex3_3 C T T TMP_342 TMP_345 TMP_346) in 
(let TMP_351 \def (\lambda (v: T).(\lambda (_: T).(let TMP_348 \def (TLRef 
x1) in (let TMP_349 \def (Bind Abst) in (let TMP_350 \def (THead TMP_349 x v) 
in (eq T TMP_348 TMP_350)))))) in (let TMP_352 \def (\lambda (_: T).(\lambda 
(w0: T).(ty3 g c x w0))) in (let TMP_355 \def (\lambda (v: T).(\lambda (_: 
T).(let TMP_353 \def (Bind Abst) in (let TMP_354 \def (CHead c TMP_353 x) in 
(ty3 g TMP_354 v x2))))) in (let TMP_358 \def (\lambda (v: T).(\lambda (_: 
T).(let TMP_356 \def (Bind Abst) in (let TMP_357 \def (CHead c TMP_356 x) in 
(nf2 TMP_357 v))))) in (let TMP_359 \def (ex4_2 T T TMP_351 TMP_352 TMP_355 
TMP_358) in (let TMP_394 \def (\lambda (H13: (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c (lift (S x1) O t0) (THead (Bind 
Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl x1 c 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0)))))).(let TMP_364 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(let TMP_360 \def (S x1) in (let TMP_361 \def (lift 
TMP_360 O t0) in (let TMP_362 \def (Bind Abst) in (let TMP_363 \def (THead 
TMP_362 x x2) in (pc3 c TMP_361 TMP_363)))))))) in (let TMP_367 \def (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(let TMP_365 \def (Bind Abbr) in (let 
TMP_366 \def (CHead e TMP_365 u0) in (getl x1 c TMP_366)))))) in (let TMP_368 
\def (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))) in 
(let TMP_372 \def (\lambda (v: T).(\lambda (_: T).(let TMP_369 \def (TLRef 
x1) in (let TMP_370 \def (Bind Abst) in (let TMP_371 \def (THead TMP_370 x v) 
in (eq T TMP_369 TMP_371)))))) in (let TMP_373 \def (\lambda (_: T).(\lambda 
(w0: T).(ty3 g c x w0))) in (let TMP_376 \def (\lambda (v: T).(\lambda (_: 
T).(let TMP_374 \def (Bind Abst) in (let TMP_375 \def (CHead c TMP_374 x) in 
(ty3 g TMP_375 v x2))))) in (let TMP_379 \def (\lambda (v: T).(\lambda (_: 
T).(let TMP_377 \def (Bind Abst) in (let TMP_378 \def (CHead c TMP_377 x) in 
(nf2 TMP_378 v))))) in (let TMP_380 \def (ex4_2 T T TMP_372 TMP_373 TMP_376 
TMP_379) in (let TMP_393 \def (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (_: (pc3 c (lift (S x1) O x5) (THead (Bind Abst) x x2))).(\lambda 
(H15: (getl x1 c (CHead x3 (Bind Abbr) x4))).(\lambda (_: (ty3 g x3 x4 
x5)).(let TMP_384 \def (\lambda (v: T).(\lambda (_: T).(let TMP_381 \def 
(TLRef x1) in (let TMP_382 \def (Bind Abst) in (let TMP_383 \def (THead 
TMP_382 x v) in (eq T TMP_381 TMP_383)))))) in (let TMP_385 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c x w0))) in (let TMP_388 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_386 \def (Bind Abst) in (let TMP_387 \def (CHead 
c TMP_386 x) in (ty3 g TMP_387 v x2))))) in (let TMP_391 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_389 \def (Bind Abst) in (let TMP_390 \def (CHead 
c TMP_389 x) in (nf2 TMP_390 v))))) in (let TMP_392 \def (ex4_2 T T TMP_384 
TMP_385 TMP_388 TMP_391) in (nf2_gen_lref c x3 x4 x1 H15 H7 
TMP_392)))))))))))) in (ex3_3_ind C T T TMP_364 TMP_367 TMP_368 TMP_380 
TMP_393 H13))))))))))) in (let TMP_429 \def (\lambda (H13: (ex3_3 C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c (lift (S x1) O u0) 
(THead (Bind Abst) x x2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl x1 c (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0)))))).(let TMP_399 \def (\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(let TMP_395 \def (S x1) in (let TMP_396 
\def (lift TMP_395 O u0) in (let TMP_397 \def (Bind Abst) in (let TMP_398 
\def (THead TMP_397 x x2) in (pc3 c TMP_396 TMP_398)))))))) in (let TMP_402 
\def (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(let TMP_400 \def (Bind 
Abst) in (let TMP_401 \def (CHead e TMP_400 u0) in (getl x1 c TMP_401)))))) 
in (let TMP_403 \def (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))) in (let TMP_407 \def (\lambda (v: T).(\lambda (_: T).(let TMP_404 
\def (TLRef x1) in (let TMP_405 \def (Bind Abst) in (let TMP_406 \def (THead 
TMP_405 x v) in (eq T TMP_404 TMP_406)))))) in (let TMP_408 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c x w0))) in (let TMP_411 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_409 \def (Bind Abst) in (let TMP_410 \def (CHead 
c TMP_409 x) in (ty3 g TMP_410 v x2))))) in (let TMP_414 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_412 \def (Bind Abst) in (let TMP_413 \def (CHead 
c TMP_412 x) in (nf2 TMP_413 v))))) in (let TMP_415 \def (ex4_2 T T TMP_407 
TMP_408 TMP_411 TMP_414) in (let TMP_428 \def (\lambda (x3: C).(\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H14: (pc3 c (lift (S x1) O x4) (THead (Bind 
Abst) x x2))).(\lambda (H15: (getl x1 c (CHead x3 (Bind Abst) x4))).(\lambda 
(_: (ty3 g x3 x4 x5)).(let H_x0 \def (H12 x3 x4 x1 H15 TNil H14) in (let H17 
\def H_x0 in (let TMP_419 \def (\lambda (v: T).(\lambda (_: T).(let TMP_416 
\def (TLRef x1) in (let TMP_417 \def (Bind Abst) in (let TMP_418 \def (THead 
TMP_417 x v) in (eq T TMP_416 TMP_418)))))) in (let TMP_420 \def (\lambda (_: 
T).(\lambda (w0: T).(ty3 g c x w0))) in (let TMP_423 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_421 \def (Bind Abst) in (let TMP_422 \def (CHead 
c TMP_421 x) in (ty3 g TMP_422 v x2))))) in (let TMP_426 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_424 \def (Bind Abst) in (let TMP_425 \def (CHead 
c TMP_424 x) in (nf2 TMP_425 v))))) in (let TMP_427 \def (ex4_2 T T TMP_419 
TMP_420 TMP_423 TMP_426) in (False_ind TMP_427 H17)))))))))))))) in 
(ex3_3_ind C T T TMP_399 TMP_402 TMP_403 TMP_415 TMP_428 H13))))))))))) in 
(let TMP_430 \def (Bind Abst) in (let TMP_431 \def (THead TMP_430 x x2) in 
(let TMP_432 \def (ty3_gen_lref g c TMP_431 x1 H11) in (or_ind TMP_337 
TMP_347 TMP_359 TMP_394 TMP_429 TMP_432))))))))))))))))))))))) in (let 
TMP_564 \def (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H11: ((\forall 
(x: T).(\forall (x2: T).((ty3 g c (THeads (Flat Appl) t1 (TLRef x1)) (THead 
(Bind Abst) x x2)) \to ((ty3_nf2_inv_abst_premise c x x2) \to (ex4_2 T T 
(\lambda (v: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t1 (TLRef x1)) 
(THead (Bind Abst) x v)))) (\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) 
(\lambda (v: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) 
(\lambda (v: T).(\lambda (_: T).(nf2 (CHead c (Bind Abst) x) 
v)))))))))).(\lambda (x: T).(\lambda (x2: T).(\lambda (H12: (ty3 g c (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 (TLRef x1))) (THead (Bind Abst) x 
x2))).(\lambda (H13: (ty3_nf2_inv_abst_premise c x x2)).(let TMP_440 \def 
(\lambda (u0: T).(\lambda (t2: T).(let TMP_434 \def (Flat Appl) in (let 
TMP_435 \def (Bind Abst) in (let TMP_436 \def (THead TMP_435 u0 t2) in (let 
TMP_437 \def (THead TMP_434 t0 TMP_436) in (let TMP_438 \def (Bind Abst) in 
(let TMP_439 \def (THead TMP_438 x x2) in (pc3 c TMP_437 TMP_439))))))))) in 
(let TMP_446 \def (\lambda (u0: T).(\lambda (t2: T).(let TMP_441 \def (Flat 
Appl) in (let TMP_442 \def (TLRef x1) in (let TMP_443 \def (THeads TMP_441 t1 
TMP_442) in (let TMP_444 \def (Bind Abst) in (let TMP_445 \def (THead TMP_444 
u0 t2) in (ty3 g c TMP_443 TMP_445)))))))) in (let TMP_447 \def (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c t0 u0))) in (let TMP_455 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_448 \def (Flat Appl) in (let TMP_449 \def (Flat 
Appl) in (let TMP_450 \def (TLRef x1) in (let TMP_451 \def (THeads TMP_449 t1 
TMP_450) in (let TMP_452 \def (THead TMP_448 t0 TMP_451) in (let TMP_453 \def 
(Bind Abst) in (let TMP_454 \def (THead TMP_453 x v) in (eq T TMP_452 
TMP_454)))))))))) in (let TMP_456 \def (\lambda (_: T).(\lambda (w0: T).(ty3 
g c x w0))) in (let TMP_459 \def (\lambda (v: T).(\lambda (_: T).(let TMP_457 
\def (Bind Abst) in (let TMP_458 \def (CHead c TMP_457 x) in (ty3 g TMP_458 v 
x2))))) in (let TMP_462 \def (\lambda (v: T).(\lambda (_: T).(let TMP_460 
\def (Bind Abst) in (let TMP_461 \def (CHead c TMP_460 x) in (nf2 TMP_461 
v))))) in (let TMP_463 \def (ex4_2 T T TMP_455 TMP_456 TMP_459 TMP_462) in 
(let TMP_557 \def (\lambda (x3: T).(\lambda (x4: T).(\lambda (H14: (pc3 c 
(THead (Flat Appl) t0 (THead (Bind Abst) x3 x4)) (THead (Bind Abst) x 
x2))).(\lambda (H15: (ty3 g c (THeads (Flat Appl) t1 (TLRef x1)) (THead (Bind 
Abst) x3 x4))).(\lambda (_: (ty3 g c t0 x3)).(let H_y \def 
(ty3_nf2_gen__ty3_nf2_inv_abst_aux c x x2 H13 t0 x3 x4 H14) in (let H_x0 \def 
(H11 x3 x4 H15 H_y) in (let H17 \def H_x0 in (let TMP_469 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_464 \def (Flat Appl) in (let TMP_465 \def (TLRef 
x1) in (let TMP_466 \def (THeads TMP_464 t1 TMP_465) in (let TMP_467 \def 
(Bind Abst) in (let TMP_468 \def (THead TMP_467 x3 v) in (eq T TMP_466 
TMP_468)))))))) in (let TMP_470 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g 
c x3 w0))) in (let TMP_473 \def (\lambda (v: T).(\lambda (_: T).(let TMP_471 
\def (Bind Abst) in (let TMP_472 \def (CHead c TMP_471 x3) in (ty3 g TMP_472 
v x4))))) in (let TMP_476 \def (\lambda (v: T).(\lambda (_: T).(let TMP_474 
\def (Bind Abst) in (let TMP_475 \def (CHead c TMP_474 x3) in (nf2 TMP_475 
v))))) in (let TMP_484 \def (\lambda (v: T).(\lambda (_: T).(let TMP_477 \def 
(Flat Appl) in (let TMP_478 \def (Flat Appl) in (let TMP_479 \def (TLRef x1) 
in (let TMP_480 \def (THeads TMP_478 t1 TMP_479) in (let TMP_481 \def (THead 
TMP_477 t0 TMP_480) in (let TMP_482 \def (Bind Abst) in (let TMP_483 \def 
(THead TMP_482 x v) in (eq T TMP_481 TMP_483)))))))))) in (let TMP_485 \def 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) in (let TMP_488 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_486 \def (Bind Abst) in (let TMP_487 
\def (CHead c TMP_486 x) in (ty3 g TMP_487 v x2))))) in (let TMP_491 \def 
(\lambda (v: T).(\lambda (_: T).(let TMP_489 \def (Bind Abst) in (let TMP_490 
\def (CHead c TMP_489 x) in (nf2 TMP_490 v))))) in (let TMP_492 \def (ex4_2 T 
T TMP_484 TMP_485 TMP_488 TMP_491) in (let TMP_556 \def (\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H18: (eq T (THeads (Flat Appl) t1 (TLRef x1)) 
(THead (Bind Abst) x3 x5))).(\lambda (_: (ty3 g c x3 x6)).(\lambda (_: (ty3 g 
(CHead c (Bind Abst) x3) x5 x4)).(\lambda (_: (nf2 (CHead c (Bind Abst) x3) 
x5)).(let TMP_508 \def (\lambda (t2: TList).((eq T (THeads (Flat Appl) t2 
(TLRef x1)) (THead (Bind Abst) x3 x5)) \to (let TMP_500 \def (\lambda (v: 
T).(\lambda (_: T).(let TMP_493 \def (Flat Appl) in (let TMP_494 \def (Flat 
Appl) in (let TMP_495 \def (TLRef x1) in (let TMP_496 \def (THeads TMP_494 t2 
TMP_495) in (let TMP_497 \def (THead TMP_493 t0 TMP_496) in (let TMP_498 \def 
(Bind Abst) in (let TMP_499 \def (THead TMP_498 x v) in (eq T TMP_497 
TMP_499)))))))))) in (let TMP_501 \def (\lambda (_: T).(\lambda (w0: T).(ty3 
g c x w0))) in (let TMP_504 \def (\lambda (v: T).(\lambda (_: T).(let TMP_502 
\def (Bind Abst) in (let TMP_503 \def (CHead c TMP_502 x) in (ty3 g TMP_503 v 
x2))))) in (let TMP_507 \def (\lambda (v: T).(\lambda (_: T).(let TMP_505 
\def (Bind Abst) in (let TMP_506 \def (CHead c TMP_505 x) in (nf2 TMP_506 
v))))) in (ex4_2 T T TMP_500 TMP_501 TMP_504 TMP_507))))))) in (let TMP_529 
\def (\lambda (H22: (eq T (THeads (Flat Appl) TNil (TLRef x1)) (THead (Bind 
Abst) x3 x5))).(let TMP_509 \def (TLRef x1) in (let TMP_510 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
True | (THead _ _ _) \Rightarrow False])) in (let TMP_511 \def (Bind Abst) in 
(let TMP_512 \def (THead TMP_511 x3 x5) in (let H23 \def (eq_ind T TMP_509 
TMP_510 I TMP_512 H22) in (let TMP_520 \def (\lambda (v: T).(\lambda (_: 
T).(let TMP_513 \def (Flat Appl) in (let TMP_514 \def (Flat Appl) in (let 
TMP_515 \def (TLRef x1) in (let TMP_516 \def (THeads TMP_514 TNil TMP_515) in 
(let TMP_517 \def (THead TMP_513 t0 TMP_516) in (let TMP_518 \def (Bind Abst) 
in (let TMP_519 \def (THead TMP_518 x v) in (eq T TMP_517 TMP_519)))))))))) 
in (let TMP_521 \def (\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) in 
(let TMP_524 \def (\lambda (v: T).(\lambda (_: T).(let TMP_522 \def (Bind 
Abst) in (let TMP_523 \def (CHead c TMP_522 x) in (ty3 g TMP_523 v x2))))) in 
(let TMP_527 \def (\lambda (v: T).(\lambda (_: T).(let TMP_525 \def (Bind 
Abst) in (let TMP_526 \def (CHead c TMP_525 x) in (nf2 TMP_526 v))))) in (let 
TMP_528 \def (ex4_2 T T TMP_520 TMP_521 TMP_524 TMP_527) in (False_ind 
TMP_528 H23)))))))))))) in (let TMP_555 \def (\lambda (t2: T).(\lambda (t3: 
TList).(\lambda (_: (((eq T (THeads (Flat Appl) t3 (TLRef x1)) (THead (Bind 
Abst) x3 x5)) \to (ex4_2 T T (\lambda (v: T).(\lambda (_: T).(eq T (THead 
(Flat Appl) t0 (THeads (Flat Appl) t3 (TLRef x1))) (THead (Bind Abst) x v)))) 
(\lambda (_: T).(\lambda (w0: T).(ty3 g c x w0))) (\lambda (v: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind Abst) x) v x2))) (\lambda (v: T).(\lambda (_: 
T).(nf2 (CHead c (Bind Abst) x) v))))))).(\lambda (H22: (eq T (THeads (Flat 
Appl) (TCons t2 t3) (TLRef x1)) (THead (Bind Abst) x3 x5))).(let TMP_530 \def 
(Flat Appl) in (let TMP_531 \def (Flat Appl) in (let TMP_532 \def (TLRef x1) 
in (let TMP_533 \def (THeads TMP_531 t3 TMP_532) in (let TMP_534 \def (THead 
TMP_530 t2 TMP_533) in (let TMP_535 \def (\lambda (ee: T).(match ee with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) in (let TMP_536 \def (Bind Abst) in (let TMP_537 \def (THead 
TMP_536 x3 x5) in (let H23 \def (eq_ind T TMP_534 TMP_535 I TMP_537 H22) in 
(let TMP_546 \def (\lambda (v: T).(\lambda (_: T).(let TMP_538 \def (Flat 
Appl) in (let TMP_539 \def (Flat Appl) in (let TMP_540 \def (TCons t2 t3) in 
(let TMP_541 \def (TLRef x1) in (let TMP_542 \def (THeads TMP_539 TMP_540 
TMP_541) in (let TMP_543 \def (THead TMP_538 t0 TMP_542) in (let TMP_544 \def 
(Bind Abst) in (let TMP_545 \def (THead TMP_544 x v) in (eq T TMP_543 
TMP_545))))))))))) in (let TMP_547 \def (\lambda (_: T).(\lambda (w0: T).(ty3 
g c x w0))) in (let TMP_550 \def (\lambda (v: T).(\lambda (_: T).(let TMP_548 
\def (Bind Abst) in (let TMP_549 \def (CHead c TMP_548 x) in (ty3 g TMP_549 v 
x2))))) in (let TMP_553 \def (\lambda (v: T).(\lambda (_: T).(let TMP_551 
\def (Bind Abst) in (let TMP_552 \def (CHead c TMP_551 x) in (nf2 TMP_552 
v))))) in (let TMP_554 \def (ex4_2 T T TMP_546 TMP_547 TMP_550 TMP_553) in 
(False_ind TMP_554 H23))))))))))))))))))) in (TList_ind TMP_508 TMP_529 
TMP_555 t1 H18)))))))))) in (ex4_2_ind T T TMP_469 TMP_470 TMP_473 TMP_476 
TMP_492 TMP_556 H17))))))))))))))))))) in (let TMP_558 \def (Flat Appl) in 
(let TMP_559 \def (TLRef x1) in (let TMP_560 \def (THeads TMP_558 t1 TMP_559) 
in (let TMP_561 \def (Bind Abst) in (let TMP_562 \def (THead TMP_561 x x2) in 
(let TMP_563 \def (ty3_gen_appl g c t0 TMP_560 TMP_562 H12) in (ex3_2_ind T T 
TMP_440 TMP_446 TMP_447 TMP_463 TMP_557 TMP_563))))))))))))))))))))))) in 
(let TMP_565 \def (TList_ind TMP_327 TMP_433 TMP_564 x0) in (let TMP_566 \def 
(unintro T w TMP_313 TMP_565) in (let TMP_567 \def (unintro T u TMP_299 
TMP_566 H10) in (let TMP_568 \def (TMP_567 H9) in (eq_ind_r T TMP_274 TMP_285 
TMP_568 t H5)))))))))))))))))))))))))) in (ex3_2_ind TList nat TMP_251 
TMP_252 TMP_254 TMP_265 TMP_569 H4))))))))))) in (or3_ind TMP_10 TMP_13 
TMP_21 TMP_32 TMP_199 TMP_247 TMP_570 H3))))))))))))))))))))))))))))))).

