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

include "basic_1/clen/defs.ma".

include "basic_1/getl/props.ma".

theorem getl_ctail_clen:
 \forall (b: B).(\forall (t: T).(\forall (c: C).(ex nat (\lambda (n: 
nat).(getl (clen c) (CTail (Bind b) t c) (CHead (CSort n) (Bind b) t))))))
\def
 \lambda (b: B).(\lambda (t: T).(\lambda (c: C).(let TMP_8 \def (\lambda (c0: 
C).(let TMP_7 \def (\lambda (n: nat).(let TMP_1 \def (clen c0) in (let TMP_2 
\def (Bind b) in (let TMP_3 \def (CTail TMP_2 t c0) in (let TMP_4 \def (CSort 
n) in (let TMP_5 \def (Bind b) in (let TMP_6 \def (CHead TMP_4 TMP_5 t) in 
(getl TMP_1 TMP_3 TMP_6)))))))) in (ex nat TMP_7))) in (let TMP_18 \def 
(\lambda (n: nat).(let TMP_15 \def (\lambda (n0: nat).(let TMP_9 \def (CSort 
n) in (let TMP_10 \def (Bind b) in (let TMP_11 \def (CHead TMP_9 TMP_10 t) in 
(let TMP_12 \def (CSort n0) in (let TMP_13 \def (Bind b) in (let TMP_14 \def 
(CHead TMP_12 TMP_13 t) in (getl O TMP_11 TMP_14)))))))) in (let TMP_16 \def 
(CSort n) in (let TMP_17 \def (getl_refl b TMP_16 t) in (ex_intro nat TMP_15 
n TMP_17))))) in (let TMP_83 \def (\lambda (c0: C).(\lambda (H: (ex nat 
(\lambda (n: nat).(getl (clen c0) (CTail (Bind b) t c0) (CHead (CSort n) 
(Bind b) t))))).(\lambda (k: K).(\lambda (t0: T).(let H0 \def H in (let 
TMP_25 \def (\lambda (n: nat).(let TMP_19 \def (clen c0) in (let TMP_20 \def 
(Bind b) in (let TMP_21 \def (CTail TMP_20 t c0) in (let TMP_22 \def (CSort 
n) in (let TMP_23 \def (Bind b) in (let TMP_24 \def (CHead TMP_22 TMP_23 t) 
in (getl TMP_19 TMP_21 TMP_24)))))))) in (let TMP_34 \def (\lambda (n: 
nat).(let TMP_26 \def (clen c0) in (let TMP_27 \def (s k TMP_26) in (let 
TMP_28 \def (Bind b) in (let TMP_29 \def (CTail TMP_28 t c0) in (let TMP_30 
\def (CHead TMP_29 k t0) in (let TMP_31 \def (CSort n) in (let TMP_32 \def 
(Bind b) in (let TMP_33 \def (CHead TMP_31 TMP_32 t) in (getl TMP_27 TMP_30 
TMP_33)))))))))) in (let TMP_35 \def (ex nat TMP_34) in (let TMP_82 \def 
(\lambda (x: nat).(\lambda (H1: (getl (clen c0) (CTail (Bind b) t c0) (CHead 
(CSort x) (Bind b) t))).(let TMP_45 \def (\lambda (k0: K).(let TMP_44 \def 
(\lambda (n: nat).(let TMP_36 \def (clen c0) in (let TMP_37 \def (s k0 
TMP_36) in (let TMP_38 \def (Bind b) in (let TMP_39 \def (CTail TMP_38 t c0) 
in (let TMP_40 \def (CHead TMP_39 k0 t0) in (let TMP_41 \def (CSort n) in 
(let TMP_42 \def (Bind b) in (let TMP_43 \def (CHead TMP_41 TMP_42 t) in 
(getl TMP_37 TMP_40 TMP_43)))))))))) in (ex nat TMP_44))) in (let TMP_64 \def 
(\lambda (b0: B).(let TMP_55 \def (\lambda (n: nat).(let TMP_46 \def (clen 
c0) in (let TMP_47 \def (S TMP_46) in (let TMP_48 \def (Bind b) in (let 
TMP_49 \def (CTail TMP_48 t c0) in (let TMP_50 \def (Bind b0) in (let TMP_51 
\def (CHead TMP_49 TMP_50 t0) in (let TMP_52 \def (CSort n) in (let TMP_53 
\def (Bind b) in (let TMP_54 \def (CHead TMP_52 TMP_53 t) in (getl TMP_47 
TMP_51 TMP_54))))))))))) in (let TMP_56 \def (Bind b0) in (let TMP_57 \def 
(clen c0) in (let TMP_58 \def (Bind b) in (let TMP_59 \def (CTail TMP_58 t 
c0) in (let TMP_60 \def (CSort x) in (let TMP_61 \def (Bind b) in (let TMP_62 
\def (CHead TMP_60 TMP_61 t) in (let TMP_63 \def (getl_head TMP_56 TMP_57 
TMP_59 TMP_62 H1 t0) in (ex_intro nat TMP_55 x TMP_63))))))))))) in (let 
TMP_81 \def (\lambda (f: F).(let TMP_73 \def (\lambda (n: nat).(let TMP_65 
\def (clen c0) in (let TMP_66 \def (Bind b) in (let TMP_67 \def (CTail TMP_66 
t c0) in (let TMP_68 \def (Flat f) in (let TMP_69 \def (CHead TMP_67 TMP_68 
t0) in (let TMP_70 \def (CSort n) in (let TMP_71 \def (Bind b) in (let TMP_72 
\def (CHead TMP_70 TMP_71 t) in (getl TMP_65 TMP_69 TMP_72)))))))))) in (let 
TMP_74 \def (Bind b) in (let TMP_75 \def (CTail TMP_74 t c0) in (let TMP_76 
\def (CSort x) in (let TMP_77 \def (Bind b) in (let TMP_78 \def (CHead TMP_76 
TMP_77 t) in (let TMP_79 \def (clen c0) in (let TMP_80 \def (getl_flat TMP_75 
TMP_78 TMP_79 H1 f t0) in (ex_intro nat TMP_73 x TMP_80)))))))))) in (K_ind 
TMP_45 TMP_64 TMP_81 k)))))) in (ex_ind nat TMP_25 TMP_35 TMP_82 H0)))))))))) 
in (C_ind TMP_8 TMP_18 TMP_83 c)))))).

theorem getl_gen_tail:
 \forall (k: K).(\forall (b: B).(\forall (u1: T).(\forall (u2: T).(\forall 
(c2: C).(\forall (c1: C).(\forall (i: nat).((getl i (CTail k u1 c1) (CHead c2 
(Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl i c1 (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: 
nat).(eq nat i (clen c1))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))))))))))))
\def
 \lambda (k: K).(\lambda (b: B).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(c2: C).(\lambda (c1: C).(let TMP_15 \def (\lambda (c: C).(\forall (i: 
nat).((getl i (CTail k u1 c) (CHead c2 (Bind b) u2)) \to (let TMP_2 \def 
(\lambda (e: C).(let TMP_1 \def (CTail k u1 e) in (eq C c2 TMP_1))) in (let 
TMP_5 \def (\lambda (e: C).(let TMP_3 \def (Bind b) in (let TMP_4 \def (CHead 
e TMP_3 u2) in (getl i c TMP_4)))) in (let TMP_6 \def (ex2 C TMP_2 TMP_5) in 
(let TMP_8 \def (\lambda (_: nat).(let TMP_7 \def (clen c) in (eq nat i 
TMP_7))) in (let TMP_10 \def (\lambda (_: nat).(let TMP_9 \def (Bind b) in 
(eq K k TMP_9))) in (let TMP_11 \def (\lambda (_: nat).(eq T u1 u2)) in (let 
TMP_13 \def (\lambda (n: nat).(let TMP_12 \def (CSort n) in (eq C c2 
TMP_12))) in (let TMP_14 \def (ex4 nat TMP_8 TMP_10 TMP_11 TMP_13) in (or 
TMP_6 TMP_14)))))))))))) in (let TMP_228 \def (\lambda (n: nat).(\lambda (i: 
nat).(let TMP_32 \def (\lambda (n0: nat).((getl n0 (CTail k u1 (CSort n)) 
(CHead c2 (Bind b) u2)) \to (let TMP_17 \def (\lambda (e: C).(let TMP_16 \def 
(CTail k u1 e) in (eq C c2 TMP_16))) in (let TMP_21 \def (\lambda (e: C).(let 
TMP_18 \def (CSort n) in (let TMP_19 \def (Bind b) in (let TMP_20 \def (CHead 
e TMP_19 u2) in (getl n0 TMP_18 TMP_20))))) in (let TMP_22 \def (ex2 C TMP_17 
TMP_21) in (let TMP_25 \def (\lambda (_: nat).(let TMP_23 \def (CSort n) in 
(let TMP_24 \def (clen TMP_23) in (eq nat n0 TMP_24)))) in (let TMP_27 \def 
(\lambda (_: nat).(let TMP_26 \def (Bind b) in (eq K k TMP_26))) in (let 
TMP_28 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_30 \def (\lambda (n1: 
nat).(let TMP_29 \def (CSort n1) in (eq C c2 TMP_29))) in (let TMP_31 \def 
(ex4 nat TMP_25 TMP_27 TMP_28 TMP_30) in (or TMP_22 TMP_31))))))))))) in (let 
TMP_202 \def (\lambda (H: (getl O (CHead (CSort n) k u1) (CHead c2 (Bind b) 
u2))).(let TMP_47 \def (\lambda (k0: K).((clear (CHead (CSort n) k0 u1) 
(CHead c2 (Bind b) u2)) \to (let TMP_34 \def (\lambda (e: C).(let TMP_33 \def 
(CTail k0 u1 e) in (eq C c2 TMP_33))) in (let TMP_38 \def (\lambda (e: 
C).(let TMP_35 \def (CSort n) in (let TMP_36 \def (Bind b) in (let TMP_37 
\def (CHead e TMP_36 u2) in (getl O TMP_35 TMP_37))))) in (let TMP_39 \def 
(ex2 C TMP_34 TMP_38) in (let TMP_40 \def (\lambda (_: nat).(eq nat O O)) in 
(let TMP_42 \def (\lambda (_: nat).(let TMP_41 \def (Bind b) in (eq K k0 
TMP_41))) in (let TMP_43 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_45 
\def (\lambda (n0: nat).(let TMP_44 \def (CSort n0) in (eq C c2 TMP_44))) in 
(let TMP_46 \def (ex4 nat TMP_40 TMP_42 TMP_43 TMP_45) in (or TMP_39 
TMP_46))))))))))) in (let TMP_172 \def (\lambda (b0: B).(\lambda (H0: (clear 
(CHead (CSort n) (Bind b0) u1) (CHead c2 (Bind b) u2))).(let TMP_48 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow c2 | (CHead c _ _) 
\Rightarrow c])) in (let TMP_49 \def (Bind b) in (let TMP_50 \def (CHead c2 
TMP_49 u2) in (let TMP_51 \def (CSort n) in (let TMP_52 \def (Bind b0) in 
(let TMP_53 \def (CHead TMP_51 TMP_52 u1) in (let TMP_54 \def (CSort n) in 
(let TMP_55 \def (Bind b) in (let TMP_56 \def (CHead c2 TMP_55 u2) in (let 
TMP_57 \def (clear_gen_bind b0 TMP_54 TMP_56 u1 H0) in (let H1 \def (f_equal 
C C TMP_48 TMP_50 TMP_53 TMP_57) in (let TMP_58 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow b | (CHead _ k0 _) \Rightarrow (match k0 with 
[(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let TMP_59 \def 
(Bind b) in (let TMP_60 \def (CHead c2 TMP_59 u2) in (let TMP_61 \def (CSort 
n) in (let TMP_62 \def (Bind b0) in (let TMP_63 \def (CHead TMP_61 TMP_62 u1) 
in (let TMP_64 \def (CSort n) in (let TMP_65 \def (Bind b) in (let TMP_66 
\def (CHead c2 TMP_65 u2) in (let TMP_67 \def (clear_gen_bind b0 TMP_64 
TMP_66 u1 H0) in (let H2 \def (f_equal C B TMP_58 TMP_60 TMP_63 TMP_67) in 
(let TMP_68 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u2 | 
(CHead _ _ t) \Rightarrow t])) in (let TMP_69 \def (Bind b) in (let TMP_70 
\def (CHead c2 TMP_69 u2) in (let TMP_71 \def (CSort n) in (let TMP_72 \def 
(Bind b0) in (let TMP_73 \def (CHead TMP_71 TMP_72 u1) in (let TMP_74 \def 
(CSort n) in (let TMP_75 \def (Bind b) in (let TMP_76 \def (CHead c2 TMP_75 
u2) in (let TMP_77 \def (clear_gen_bind b0 TMP_74 TMP_76 u1 H0) in (let H3 
\def (f_equal C T TMP_68 TMP_70 TMP_73 TMP_77) in (let TMP_170 \def (\lambda 
(H4: (eq B b b0)).(\lambda (H5: (eq C c2 (CSort n))).(let TMP_78 \def (CSort 
n) in (let TMP_95 \def (\lambda (c: C).(let TMP_81 \def (\lambda (e: C).(let 
TMP_79 \def (Bind b0) in (let TMP_80 \def (CTail TMP_79 u1 e) in (eq C c 
TMP_80)))) in (let TMP_85 \def (\lambda (e: C).(let TMP_82 \def (CSort n) in 
(let TMP_83 \def (Bind b) in (let TMP_84 \def (CHead e TMP_83 u2) in (getl O 
TMP_82 TMP_84))))) in (let TMP_86 \def (ex2 C TMP_81 TMP_85) in (let TMP_87 
\def (\lambda (_: nat).(eq nat O O)) in (let TMP_90 \def (\lambda (_: 
nat).(let TMP_88 \def (Bind b0) in (let TMP_89 \def (Bind b) in (eq K TMP_88 
TMP_89)))) in (let TMP_91 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_93 
\def (\lambda (n0: nat).(let TMP_92 \def (CSort n0) in (eq C c TMP_92))) in 
(let TMP_94 \def (ex4 nat TMP_87 TMP_90 TMP_91 TMP_93) in (or TMP_86 
TMP_94)))))))))) in (let TMP_114 \def (\lambda (t: T).(let TMP_99 \def 
(\lambda (e: C).(let TMP_96 \def (CSort n) in (let TMP_97 \def (Bind b0) in 
(let TMP_98 \def (CTail TMP_97 u1 e) in (eq C TMP_96 TMP_98))))) in (let 
TMP_103 \def (\lambda (e: C).(let TMP_100 \def (CSort n) in (let TMP_101 \def 
(Bind b) in (let TMP_102 \def (CHead e TMP_101 t) in (getl O TMP_100 
TMP_102))))) in (let TMP_104 \def (ex2 C TMP_99 TMP_103) in (let TMP_105 \def 
(\lambda (_: nat).(eq nat O O)) in (let TMP_108 \def (\lambda (_: nat).(let 
TMP_106 \def (Bind b0) in (let TMP_107 \def (Bind b) in (eq K TMP_106 
TMP_107)))) in (let TMP_109 \def (\lambda (_: nat).(eq T u1 t)) in (let 
TMP_112 \def (\lambda (n0: nat).(let TMP_110 \def (CSort n) in (let TMP_111 
\def (CSort n0) in (eq C TMP_110 TMP_111)))) in (let TMP_113 \def (ex4 nat 
TMP_105 TMP_108 TMP_109 TMP_112) in (or TMP_104 TMP_113)))))))))) in (let 
TMP_133 \def (\lambda (b1: B).(let TMP_118 \def (\lambda (e: C).(let TMP_115 
\def (CSort n) in (let TMP_116 \def (Bind b0) in (let TMP_117 \def (CTail 
TMP_116 u1 e) in (eq C TMP_115 TMP_117))))) in (let TMP_122 \def (\lambda (e: 
C).(let TMP_119 \def (CSort n) in (let TMP_120 \def (Bind b1) in (let TMP_121 
\def (CHead e TMP_120 u1) in (getl O TMP_119 TMP_121))))) in (let TMP_123 
\def (ex2 C TMP_118 TMP_122) in (let TMP_124 \def (\lambda (_: nat).(eq nat O 
O)) in (let TMP_127 \def (\lambda (_: nat).(let TMP_125 \def (Bind b0) in 
(let TMP_126 \def (Bind b1) in (eq K TMP_125 TMP_126)))) in (let TMP_128 \def 
(\lambda (_: nat).(eq T u1 u1)) in (let TMP_131 \def (\lambda (n0: nat).(let 
TMP_129 \def (CSort n) in (let TMP_130 \def (CSort n0) in (eq C TMP_129 
TMP_130)))) in (let TMP_132 \def (ex4 nat TMP_124 TMP_127 TMP_128 TMP_131) in 
(or TMP_123 TMP_132)))))))))) in (let TMP_137 \def (\lambda (e: C).(let 
TMP_134 \def (CSort n) in (let TMP_135 \def (Bind b0) in (let TMP_136 \def 
(CTail TMP_135 u1 e) in (eq C TMP_134 TMP_136))))) in (let TMP_141 \def 
(\lambda (e: C).(let TMP_138 \def (CSort n) in (let TMP_139 \def (Bind b0) in 
(let TMP_140 \def (CHead e TMP_139 u1) in (getl O TMP_138 TMP_140))))) in 
(let TMP_142 \def (ex2 C TMP_137 TMP_141) in (let TMP_143 \def (\lambda (_: 
nat).(eq nat O O)) in (let TMP_146 \def (\lambda (_: nat).(let TMP_144 \def 
(Bind b0) in (let TMP_145 \def (Bind b0) in (eq K TMP_144 TMP_145)))) in (let 
TMP_147 \def (\lambda (_: nat).(eq T u1 u1)) in (let TMP_150 \def (\lambda 
(n0: nat).(let TMP_148 \def (CSort n) in (let TMP_149 \def (CSort n0) in (eq 
C TMP_148 TMP_149)))) in (let TMP_151 \def (ex4 nat TMP_143 TMP_146 TMP_147 
TMP_150) in (let TMP_152 \def (\lambda (_: nat).(eq nat O O)) in (let TMP_155 
\def (\lambda (_: nat).(let TMP_153 \def (Bind b0) in (let TMP_154 \def (Bind 
b0) in (eq K TMP_153 TMP_154)))) in (let TMP_156 \def (\lambda (_: nat).(eq T 
u1 u1)) in (let TMP_159 \def (\lambda (n0: nat).(let TMP_157 \def (CSort n) 
in (let TMP_158 \def (CSort n0) in (eq C TMP_157 TMP_158)))) in (let TMP_160 
\def (refl_equal nat O) in (let TMP_161 \def (Bind b0) in (let TMP_162 \def 
(refl_equal K TMP_161) in (let TMP_163 \def (refl_equal T u1) in (let TMP_164 
\def (CSort n) in (let TMP_165 \def (refl_equal C TMP_164) in (let TMP_166 
\def (ex4_intro nat TMP_152 TMP_155 TMP_156 TMP_159 n TMP_160 TMP_162 TMP_163 
TMP_165) in (let TMP_167 \def (or_intror TMP_142 TMP_151 TMP_166) in (let 
TMP_168 \def (eq_ind_r B b0 TMP_133 TMP_167 b H4) in (let TMP_169 \def 
(eq_ind_r T u1 TMP_114 TMP_168 u2 H3) in (eq_ind_r C TMP_78 TMP_95 TMP_169 c2 
H5))))))))))))))))))))))))))))) in (let TMP_171 \def (TMP_170 H2) in (TMP_171 
H1)))))))))))))))))))))))))))))))))))))) in (let TMP_196 \def (\lambda (f: 
F).(\lambda (H0: (clear (CHead (CSort n) (Flat f) u1) (CHead c2 (Bind b) 
u2))).(let TMP_173 \def (Bind b) in (let TMP_174 \def (CHead c2 TMP_173 u2) 
in (let TMP_175 \def (CSort n) in (let TMP_176 \def (Bind b) in (let TMP_177 
\def (CHead c2 TMP_176 u2) in (let TMP_178 \def (clear_gen_flat f TMP_175 
TMP_177 u1 H0) in (let TMP_181 \def (\lambda (e: C).(let TMP_179 \def (Flat 
f) in (let TMP_180 \def (CTail TMP_179 u1 e) in (eq C c2 TMP_180)))) in (let 
TMP_185 \def (\lambda (e: C).(let TMP_182 \def (CSort n) in (let TMP_183 \def 
(Bind b) in (let TMP_184 \def (CHead e TMP_183 u2) in (getl O TMP_182 
TMP_184))))) in (let TMP_186 \def (ex2 C TMP_181 TMP_185) in (let TMP_187 
\def (\lambda (_: nat).(eq nat O O)) in (let TMP_190 \def (\lambda (_: 
nat).(let TMP_188 \def (Flat f) in (let TMP_189 \def (Bind b) in (eq K 
TMP_188 TMP_189)))) in (let TMP_191 \def (\lambda (_: nat).(eq T u1 u2)) in 
(let TMP_193 \def (\lambda (n0: nat).(let TMP_192 \def (CSort n0) in (eq C c2 
TMP_192))) in (let TMP_194 \def (ex4 nat TMP_187 TMP_190 TMP_191 TMP_193) in 
(let TMP_195 \def (or TMP_186 TMP_194) in (clear_gen_sort TMP_174 n TMP_178 
TMP_195)))))))))))))))))) in (let TMP_197 \def (CSort n) in (let TMP_198 \def 
(CHead TMP_197 k u1) in (let TMP_199 \def (Bind b) in (let TMP_200 \def 
(CHead c2 TMP_199 u2) in (let TMP_201 \def (getl_gen_O TMP_198 TMP_200 H) in 
(K_ind TMP_47 TMP_172 TMP_196 k TMP_201)))))))))) in (let TMP_227 \def 
(\lambda (n0: nat).(\lambda (_: (((getl n0 (CHead (CSort n) k u1) (CHead c2 
(Bind b) u2)) \to (or (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl n0 (CSort n) (CHead e (Bind b) u2)))) (ex4 nat (\lambda 
(_: nat).(eq nat n0 O)) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n1: nat).(eq C c2 (CSort n1)))))))).(\lambda 
(H0: (getl (S n0) (CHead (CSort n) k u1) (CHead c2 (Bind b) u2))).(let 
TMP_203 \def (r k n0) in (let TMP_204 \def (Bind b) in (let TMP_205 \def 
(CHead c2 TMP_204 u2) in (let TMP_206 \def (CSort n) in (let TMP_207 \def 
(Bind b) in (let TMP_208 \def (CHead c2 TMP_207 u2) in (let TMP_209 \def 
(getl_gen_S k TMP_206 TMP_208 u1 n0 H0) in (let TMP_211 \def (\lambda (e: 
C).(let TMP_210 \def (CTail k u1 e) in (eq C c2 TMP_210))) in (let TMP_216 
\def (\lambda (e: C).(let TMP_212 \def (S n0) in (let TMP_213 \def (CSort n) 
in (let TMP_214 \def (Bind b) in (let TMP_215 \def (CHead e TMP_214 u2) in 
(getl TMP_212 TMP_213 TMP_215)))))) in (let TMP_217 \def (ex2 C TMP_211 
TMP_216) in (let TMP_219 \def (\lambda (_: nat).(let TMP_218 \def (S n0) in 
(eq nat TMP_218 O))) in (let TMP_221 \def (\lambda (_: nat).(let TMP_220 \def 
(Bind b) in (eq K k TMP_220))) in (let TMP_222 \def (\lambda (_: nat).(eq T 
u1 u2)) in (let TMP_224 \def (\lambda (n1: nat).(let TMP_223 \def (CSort n1) 
in (eq C c2 TMP_223))) in (let TMP_225 \def (ex4 nat TMP_219 TMP_221 TMP_222 
TMP_224) in (let TMP_226 \def (or TMP_217 TMP_225) in (getl_gen_sort n 
TMP_203 TMP_205 TMP_209 TMP_226)))))))))))))))))))) in (nat_ind TMP_32 
TMP_202 TMP_227 i)))))) in (let TMP_1086 \def (\lambda (c: C).(\lambda (H: 
((\forall (i: nat).((getl i (CTail k u1 c) (CHead c2 (Bind b) u2)) \to (or 
(ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl i c 
(CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat i (clen c))) 
(\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda 
(n: nat).(eq C c2 (CSort n))))))))).(\lambda (k0: K).(\lambda (t: T).(\lambda 
(i: nat).(let TMP_245 \def (\lambda (n: nat).((getl n (CTail k u1 (CHead c k0 
t)) (CHead c2 (Bind b) u2)) \to (let TMP_230 \def (\lambda (e: C).(let 
TMP_229 \def (CTail k u1 e) in (eq C c2 TMP_229))) in (let TMP_234 \def 
(\lambda (e: C).(let TMP_231 \def (CHead c k0 t) in (let TMP_232 \def (Bind 
b) in (let TMP_233 \def (CHead e TMP_232 u2) in (getl n TMP_231 TMP_233))))) 
in (let TMP_235 \def (ex2 C TMP_230 TMP_234) in (let TMP_238 \def (\lambda 
(_: nat).(let TMP_236 \def (CHead c k0 t) in (let TMP_237 \def (clen TMP_236) 
in (eq nat n TMP_237)))) in (let TMP_240 \def (\lambda (_: nat).(let TMP_239 
\def (Bind b) in (eq K k TMP_239))) in (let TMP_241 \def (\lambda (_: 
nat).(eq T u1 u2)) in (let TMP_243 \def (\lambda (n0: nat).(let TMP_242 \def 
(CSort n0) in (eq C c2 TMP_242))) in (let TMP_244 \def (ex4 nat TMP_238 
TMP_240 TMP_241 TMP_243) in (or TMP_235 TMP_244))))))))))) in (let TMP_669 
\def (\lambda (H0: (getl O (CHead (CTail k u1 c) k0 t) (CHead c2 (Bind b) 
u2))).(let TMP_262 \def (\lambda (k1: K).((clear (CHead (CTail k u1 c) k1 t) 
(CHead c2 (Bind b) u2)) \to (let TMP_247 \def (\lambda (e: C).(let TMP_246 
\def (CTail k u1 e) in (eq C c2 TMP_246))) in (let TMP_251 \def (\lambda (e: 
C).(let TMP_248 \def (CHead c k1 t) in (let TMP_249 \def (Bind b) in (let 
TMP_250 \def (CHead e TMP_249 u2) in (getl O TMP_248 TMP_250))))) in (let 
TMP_252 \def (ex2 C TMP_247 TMP_251) in (let TMP_255 \def (\lambda (_: 
nat).(let TMP_253 \def (clen c) in (let TMP_254 \def (s k1 TMP_253) in (eq 
nat O TMP_254)))) in (let TMP_257 \def (\lambda (_: nat).(let TMP_256 \def 
(Bind b) in (eq K k TMP_256))) in (let TMP_258 \def (\lambda (_: nat).(eq T 
u1 u2)) in (let TMP_260 \def (\lambda (n: nat).(let TMP_259 \def (CSort n) in 
(eq C c2 TMP_259))) in (let TMP_261 \def (ex4 nat TMP_255 TMP_257 TMP_258 
TMP_260) in (or TMP_252 TMP_261))))))))))) in (let TMP_404 \def (\lambda (b0: 
B).(\lambda (H1: (clear (CHead (CTail k u1 c) (Bind b0) t) (CHead c2 (Bind b) 
u2))).(let TMP_263 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow 
c2 | (CHead c0 _ _) \Rightarrow c0])) in (let TMP_264 \def (Bind b) in (let 
TMP_265 \def (CHead c2 TMP_264 u2) in (let TMP_266 \def (CTail k u1 c) in 
(let TMP_267 \def (Bind b0) in (let TMP_268 \def (CHead TMP_266 TMP_267 t) in 
(let TMP_269 \def (CTail k u1 c) in (let TMP_270 \def (Bind b) in (let 
TMP_271 \def (CHead c2 TMP_270 u2) in (let TMP_272 \def (clear_gen_bind b0 
TMP_269 TMP_271 t H1) in (let H2 \def (f_equal C C TMP_263 TMP_265 TMP_268 
TMP_272) in (let TMP_273 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow b | (CHead _ k1 _) \Rightarrow (match k1 with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let TMP_274 \def (Bind b) in 
(let TMP_275 \def (CHead c2 TMP_274 u2) in (let TMP_276 \def (CTail k u1 c) 
in (let TMP_277 \def (Bind b0) in (let TMP_278 \def (CHead TMP_276 TMP_277 t) 
in (let TMP_279 \def (CTail k u1 c) in (let TMP_280 \def (Bind b) in (let 
TMP_281 \def (CHead c2 TMP_280 u2) in (let TMP_282 \def (clear_gen_bind b0 
TMP_279 TMP_281 t H1) in (let H3 \def (f_equal C B TMP_273 TMP_275 TMP_278 
TMP_282) in (let TMP_283 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u2 | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_284 \def (Bind 
b) in (let TMP_285 \def (CHead c2 TMP_284 u2) in (let TMP_286 \def (CTail k 
u1 c) in (let TMP_287 \def (Bind b0) in (let TMP_288 \def (CHead TMP_286 
TMP_287 t) in (let TMP_289 \def (CTail k u1 c) in (let TMP_290 \def (Bind b) 
in (let TMP_291 \def (CHead c2 TMP_290 u2) in (let TMP_292 \def 
(clear_gen_bind b0 TMP_289 TMP_291 t H1) in (let H4 \def (f_equal C T TMP_283 
TMP_285 TMP_288 TMP_292) in (let TMP_402 \def (\lambda (H5: (eq B b 
b0)).(\lambda (H6: (eq C c2 (CTail k u1 c))).(let TMP_311 \def (\lambda (t0: 
T).(let TMP_294 \def (\lambda (e: C).(let TMP_293 \def (CTail k u1 e) in (eq 
C c2 TMP_293))) in (let TMP_299 \def (\lambda (e: C).(let TMP_295 \def (Bind 
b0) in (let TMP_296 \def (CHead c TMP_295 t0) in (let TMP_297 \def (Bind b) 
in (let TMP_298 \def (CHead e TMP_297 u2) in (getl O TMP_296 TMP_298)))))) in 
(let TMP_300 \def (ex2 C TMP_294 TMP_299) in (let TMP_304 \def (\lambda (_: 
nat).(let TMP_301 \def (Bind b0) in (let TMP_302 \def (clen c) in (let 
TMP_303 \def (s TMP_301 TMP_302) in (eq nat O TMP_303))))) in (let TMP_306 
\def (\lambda (_: nat).(let TMP_305 \def (Bind b) in (eq K k TMP_305))) in 
(let TMP_307 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_309 \def 
(\lambda (n: nat).(let TMP_308 \def (CSort n) in (eq C c2 TMP_308))) in (let 
TMP_310 \def (ex4 nat TMP_304 TMP_306 TMP_307 TMP_309) in (or TMP_300 
TMP_310)))))))))) in (let TMP_330 \def (\lambda (b1: B).(let TMP_313 \def 
(\lambda (e: C).(let TMP_312 \def (CTail k u1 e) in (eq C c2 TMP_312))) in 
(let TMP_318 \def (\lambda (e: C).(let TMP_314 \def (Bind b1) in (let TMP_315 
\def (CHead c TMP_314 u2) in (let TMP_316 \def (Bind b) in (let TMP_317 \def 
(CHead e TMP_316 u2) in (getl O TMP_315 TMP_317)))))) in (let TMP_319 \def 
(ex2 C TMP_313 TMP_318) in (let TMP_323 \def (\lambda (_: nat).(let TMP_320 
\def (Bind b1) in (let TMP_321 \def (clen c) in (let TMP_322 \def (s TMP_320 
TMP_321) in (eq nat O TMP_322))))) in (let TMP_325 \def (\lambda (_: 
nat).(let TMP_324 \def (Bind b) in (eq K k TMP_324))) in (let TMP_326 \def 
(\lambda (_: nat).(eq T u1 u2)) in (let TMP_328 \def (\lambda (n: nat).(let 
TMP_327 \def (CSort n) in (eq C c2 TMP_327))) in (let TMP_329 \def (ex4 nat 
TMP_323 TMP_325 TMP_326 TMP_328) in (or TMP_319 TMP_329)))))))))) in (let 
TMP_345 \def (\lambda (c0: C).(\forall (i0: nat).((getl i0 (CTail k u1 c) 
(CHead c0 (Bind b) u2)) \to (let TMP_332 \def (\lambda (e: C).(let TMP_331 
\def (CTail k u1 e) in (eq C c0 TMP_331))) in (let TMP_335 \def (\lambda (e: 
C).(let TMP_333 \def (Bind b) in (let TMP_334 \def (CHead e TMP_333 u2) in 
(getl i0 c TMP_334)))) in (let TMP_336 \def (ex2 C TMP_332 TMP_335) in (let 
TMP_338 \def (\lambda (_: nat).(let TMP_337 \def (clen c) in (eq nat i0 
TMP_337))) in (let TMP_340 \def (\lambda (_: nat).(let TMP_339 \def (Bind b) 
in (eq K k TMP_339))) in (let TMP_341 \def (\lambda (_: nat).(eq T u1 u2)) in 
(let TMP_343 \def (\lambda (n: nat).(let TMP_342 \def (CSort n) in (eq C c0 
TMP_342))) in (let TMP_344 \def (ex4 nat TMP_338 TMP_340 TMP_341 TMP_343) in 
(or TMP_336 TMP_344)))))))))))) in (let TMP_346 \def (CTail k u1 c) in (let 
H7 \def (eq_ind C c2 TMP_345 H TMP_346 H6) in (let TMP_347 \def (CTail k u1 
c) in (let TMP_366 \def (\lambda (c0: C).(let TMP_349 \def (\lambda (e: 
C).(let TMP_348 \def (CTail k u1 e) in (eq C c0 TMP_348))) in (let TMP_354 
\def (\lambda (e: C).(let TMP_350 \def (Bind b) in (let TMP_351 \def (CHead c 
TMP_350 u2) in (let TMP_352 \def (Bind b) in (let TMP_353 \def (CHead e 
TMP_352 u2) in (getl O TMP_351 TMP_353)))))) in (let TMP_355 \def (ex2 C 
TMP_349 TMP_354) in (let TMP_359 \def (\lambda (_: nat).(let TMP_356 \def 
(Bind b) in (let TMP_357 \def (clen c) in (let TMP_358 \def (s TMP_356 
TMP_357) in (eq nat O TMP_358))))) in (let TMP_361 \def (\lambda (_: 
nat).(let TMP_360 \def (Bind b) in (eq K k TMP_360))) in (let TMP_362 \def 
(\lambda (_: nat).(eq T u1 u2)) in (let TMP_364 \def (\lambda (n: nat).(let 
TMP_363 \def (CSort n) in (eq C c0 TMP_363))) in (let TMP_365 \def (ex4 nat 
TMP_359 TMP_361 TMP_362 TMP_364) in (or TMP_355 TMP_365)))))))))) in (let 
TMP_369 \def (\lambda (e: C).(let TMP_367 \def (CTail k u1 c) in (let TMP_368 
\def (CTail k u1 e) in (eq C TMP_367 TMP_368)))) in (let TMP_374 \def 
(\lambda (e: C).(let TMP_370 \def (Bind b) in (let TMP_371 \def (CHead c 
TMP_370 u2) in (let TMP_372 \def (Bind b) in (let TMP_373 \def (CHead e 
TMP_372 u2) in (getl O TMP_371 TMP_373)))))) in (let TMP_375 \def (ex2 C 
TMP_369 TMP_374) in (let TMP_379 \def (\lambda (_: nat).(let TMP_376 \def 
(Bind b) in (let TMP_377 \def (clen c) in (let TMP_378 \def (s TMP_376 
TMP_377) in (eq nat O TMP_378))))) in (let TMP_381 \def (\lambda (_: 
nat).(let TMP_380 \def (Bind b) in (eq K k TMP_380))) in (let TMP_382 \def 
(\lambda (_: nat).(eq T u1 u2)) in (let TMP_385 \def (\lambda (n: nat).(let 
TMP_383 \def (CTail k u1 c) in (let TMP_384 \def (CSort n) in (eq C TMP_383 
TMP_384)))) in (let TMP_386 \def (ex4 nat TMP_379 TMP_381 TMP_382 TMP_385) in 
(let TMP_389 \def (\lambda (e: C).(let TMP_387 \def (CTail k u1 c) in (let 
TMP_388 \def (CTail k u1 e) in (eq C TMP_387 TMP_388)))) in (let TMP_394 \def 
(\lambda (e: C).(let TMP_390 \def (Bind b) in (let TMP_391 \def (CHead c 
TMP_390 u2) in (let TMP_392 \def (Bind b) in (let TMP_393 \def (CHead e 
TMP_392 u2) in (getl O TMP_391 TMP_393)))))) in (let TMP_395 \def (CTail k u1 
c) in (let TMP_396 \def (refl_equal C TMP_395) in (let TMP_397 \def 
(getl_refl b c u2) in (let TMP_398 \def (ex_intro2 C TMP_389 TMP_394 c 
TMP_396 TMP_397) in (let TMP_399 \def (or_introl TMP_375 TMP_386 TMP_398) in 
(let TMP_400 \def (eq_ind_r C TMP_347 TMP_366 TMP_399 c2 H6) in (let TMP_401 
\def (eq_ind B b TMP_330 TMP_400 b0 H5) in (eq_ind T u2 TMP_311 TMP_401 t 
H4))))))))))))))))))))))))))) in (let TMP_403 \def (TMP_402 H3) in (TMP_403 
H2)))))))))))))))))))))))))))))))))))))) in (let TMP_663 \def (\lambda (f: 
F).(\lambda (H1: (clear (CHead (CTail k u1 c) (Flat f) t) (CHead c2 (Bind b) 
u2))).(let TMP_405 \def (CTail k u1 c) in (let TMP_406 \def (Bind b) in (let 
TMP_407 \def (CHead c2 TMP_406 u2) in (let TMP_408 \def (CTail k u1 c) in 
(let TMP_409 \def (CTail k u1 c) in (let TMP_410 \def (drop_refl TMP_409) in 
(let TMP_411 \def (CTail k u1 c) in (let TMP_412 \def (Bind b) in (let 
TMP_413 \def (CHead c2 TMP_412 u2) in (let TMP_414 \def (clear_gen_flat f 
TMP_411 TMP_413 t H1) in (let TMP_415 \def (getl_intro O TMP_405 TMP_407 
TMP_408 TMP_410 TMP_414) in (let H2 \def (H O TMP_415) in (let TMP_417 \def 
(\lambda (e: C).(let TMP_416 \def (CTail k u1 e) in (eq C c2 TMP_416))) in 
(let TMP_420 \def (\lambda (e: C).(let TMP_418 \def (Bind b) in (let TMP_419 
\def (CHead e TMP_418 u2) in (getl O c TMP_419)))) in (let TMP_421 \def (ex2 
C TMP_417 TMP_420) in (let TMP_423 \def (\lambda (_: nat).(let TMP_422 \def 
(clen c) in (eq nat O TMP_422))) in (let TMP_425 \def (\lambda (_: nat).(let 
TMP_424 \def (Bind b) in (eq K k TMP_424))) in (let TMP_426 \def (\lambda (_: 
nat).(eq T u1 u2)) in (let TMP_428 \def (\lambda (n: nat).(let TMP_427 \def 
(CSort n) in (eq C c2 TMP_427))) in (let TMP_429 \def (ex4 nat TMP_423 
TMP_425 TMP_426 TMP_428) in (let TMP_431 \def (\lambda (e: C).(let TMP_430 
\def (CTail k u1 e) in (eq C c2 TMP_430))) in (let TMP_436 \def (\lambda (e: 
C).(let TMP_432 \def (Flat f) in (let TMP_433 \def (CHead c TMP_432 t) in 
(let TMP_434 \def (Bind b) in (let TMP_435 \def (CHead e TMP_434 u2) in (getl 
O TMP_433 TMP_435)))))) in (let TMP_437 \def (ex2 C TMP_431 TMP_436) in (let 
TMP_441 \def (\lambda (_: nat).(let TMP_438 \def (Flat f) in (let TMP_439 
\def (clen c) in (let TMP_440 \def (s TMP_438 TMP_439) in (eq nat O 
TMP_440))))) in (let TMP_443 \def (\lambda (_: nat).(let TMP_442 \def (Bind 
b) in (eq K k TMP_442))) in (let TMP_444 \def (\lambda (_: nat).(eq T u1 u2)) 
in (let TMP_446 \def (\lambda (n: nat).(let TMP_445 \def (CSort n) in (eq C 
c2 TMP_445))) in (let TMP_447 \def (ex4 nat TMP_441 TMP_443 TMP_444 TMP_446) 
in (let TMP_448 \def (or TMP_437 TMP_447) in (let TMP_529 \def (\lambda (H3: 
(ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl O c 
(CHead e (Bind b) u2))))).(let TMP_450 \def (\lambda (e: C).(let TMP_449 \def 
(CTail k u1 e) in (eq C c2 TMP_449))) in (let TMP_453 \def (\lambda (e: 
C).(let TMP_451 \def (Bind b) in (let TMP_452 \def (CHead e TMP_451 u2) in 
(getl O c TMP_452)))) in (let TMP_455 \def (\lambda (e: C).(let TMP_454 \def 
(CTail k u1 e) in (eq C c2 TMP_454))) in (let TMP_460 \def (\lambda (e: 
C).(let TMP_456 \def (Flat f) in (let TMP_457 \def (CHead c TMP_456 t) in 
(let TMP_458 \def (Bind b) in (let TMP_459 \def (CHead e TMP_458 u2) in (getl 
O TMP_457 TMP_459)))))) in (let TMP_461 \def (ex2 C TMP_455 TMP_460) in (let 
TMP_465 \def (\lambda (_: nat).(let TMP_462 \def (Flat f) in (let TMP_463 
\def (clen c) in (let TMP_464 \def (s TMP_462 TMP_463) in (eq nat O 
TMP_464))))) in (let TMP_467 \def (\lambda (_: nat).(let TMP_466 \def (Bind 
b) in (eq K k TMP_466))) in (let TMP_468 \def (\lambda (_: nat).(eq T u1 u2)) 
in (let TMP_470 \def (\lambda (n: nat).(let TMP_469 \def (CSort n) in (eq C 
c2 TMP_469))) in (let TMP_471 \def (ex4 nat TMP_465 TMP_467 TMP_468 TMP_470) 
in (let TMP_472 \def (or TMP_461 TMP_471) in (let TMP_528 \def (\lambda (x: 
C).(\lambda (H4: (eq C c2 (CTail k u1 x))).(\lambda (H5: (getl O c (CHead x 
(Bind b) u2))).(let TMP_473 \def (CTail k u1 x) in (let TMP_492 \def (\lambda 
(c0: C).(let TMP_475 \def (\lambda (e: C).(let TMP_474 \def (CTail k u1 e) in 
(eq C c0 TMP_474))) in (let TMP_480 \def (\lambda (e: C).(let TMP_476 \def 
(Flat f) in (let TMP_477 \def (CHead c TMP_476 t) in (let TMP_478 \def (Bind 
b) in (let TMP_479 \def (CHead e TMP_478 u2) in (getl O TMP_477 TMP_479)))))) 
in (let TMP_481 \def (ex2 C TMP_475 TMP_480) in (let TMP_485 \def (\lambda 
(_: nat).(let TMP_482 \def (Flat f) in (let TMP_483 \def (clen c) in (let 
TMP_484 \def (s TMP_482 TMP_483) in (eq nat O TMP_484))))) in (let TMP_487 
\def (\lambda (_: nat).(let TMP_486 \def (Bind b) in (eq K k TMP_486))) in 
(let TMP_488 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_490 \def 
(\lambda (n: nat).(let TMP_489 \def (CSort n) in (eq C c0 TMP_489))) in (let 
TMP_491 \def (ex4 nat TMP_485 TMP_487 TMP_488 TMP_490) in (or TMP_481 
TMP_491)))))))))) in (let TMP_495 \def (\lambda (e: C).(let TMP_493 \def 
(CTail k u1 x) in (let TMP_494 \def (CTail k u1 e) in (eq C TMP_493 
TMP_494)))) in (let TMP_500 \def (\lambda (e: C).(let TMP_496 \def (Flat f) 
in (let TMP_497 \def (CHead c TMP_496 t) in (let TMP_498 \def (Bind b) in 
(let TMP_499 \def (CHead e TMP_498 u2) in (getl O TMP_497 TMP_499)))))) in 
(let TMP_501 \def (ex2 C TMP_495 TMP_500) in (let TMP_505 \def (\lambda (_: 
nat).(let TMP_502 \def (Flat f) in (let TMP_503 \def (clen c) in (let TMP_504 
\def (s TMP_502 TMP_503) in (eq nat O TMP_504))))) in (let TMP_507 \def 
(\lambda (_: nat).(let TMP_506 \def (Bind b) in (eq K k TMP_506))) in (let 
TMP_508 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_511 \def (\lambda 
(n: nat).(let TMP_509 \def (CTail k u1 x) in (let TMP_510 \def (CSort n) in 
(eq C TMP_509 TMP_510)))) in (let TMP_512 \def (ex4 nat TMP_505 TMP_507 
TMP_508 TMP_511) in (let TMP_515 \def (\lambda (e: C).(let TMP_513 \def 
(CTail k u1 x) in (let TMP_514 \def (CTail k u1 e) in (eq C TMP_513 
TMP_514)))) in (let TMP_520 \def (\lambda (e: C).(let TMP_516 \def (Flat f) 
in (let TMP_517 \def (CHead c TMP_516 t) in (let TMP_518 \def (Bind b) in 
(let TMP_519 \def (CHead e TMP_518 u2) in (getl O TMP_517 TMP_519)))))) in 
(let TMP_521 \def (CTail k u1 x) in (let TMP_522 \def (refl_equal C TMP_521) 
in (let TMP_523 \def (Bind b) in (let TMP_524 \def (CHead x TMP_523 u2) in 
(let TMP_525 \def (getl_flat c TMP_524 O H5 f t) in (let TMP_526 \def 
(ex_intro2 C TMP_515 TMP_520 x TMP_522 TMP_525) in (let TMP_527 \def 
(or_introl TMP_501 TMP_512 TMP_526) in (eq_ind_r C TMP_473 TMP_492 TMP_527 c2 
H4))))))))))))))))))))))) in (ex2_ind C TMP_450 TMP_453 TMP_472 TMP_528 
H3)))))))))))))) in (let TMP_662 \def (\lambda (H3: (ex4 nat (\lambda (_: 
nat).(eq nat O (clen c))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: 
nat).(eq T u1 u2)) (\lambda (n: nat).(eq C c2 (CSort n))))).(let TMP_531 \def 
(\lambda (_: nat).(let TMP_530 \def (clen c) in (eq nat O TMP_530))) in (let 
TMP_533 \def (\lambda (_: nat).(let TMP_532 \def (Bind b) in (eq K k 
TMP_532))) in (let TMP_534 \def (\lambda (_: nat).(eq T u1 u2)) in (let 
TMP_536 \def (\lambda (n: nat).(let TMP_535 \def (CSort n) in (eq C c2 
TMP_535))) in (let TMP_538 \def (\lambda (e: C).(let TMP_537 \def (CTail k u1 
e) in (eq C c2 TMP_537))) in (let TMP_543 \def (\lambda (e: C).(let TMP_539 
\def (Flat f) in (let TMP_540 \def (CHead c TMP_539 t) in (let TMP_541 \def 
(Bind b) in (let TMP_542 \def (CHead e TMP_541 u2) in (getl O TMP_540 
TMP_542)))))) in (let TMP_544 \def (ex2 C TMP_538 TMP_543) in (let TMP_548 
\def (\lambda (_: nat).(let TMP_545 \def (Flat f) in (let TMP_546 \def (clen 
c) in (let TMP_547 \def (s TMP_545 TMP_546) in (eq nat O TMP_547))))) in (let 
TMP_550 \def (\lambda (_: nat).(let TMP_549 \def (Bind b) in (eq K k 
TMP_549))) in (let TMP_551 \def (\lambda (_: nat).(eq T u1 u2)) in (let 
TMP_553 \def (\lambda (n: nat).(let TMP_552 \def (CSort n) in (eq C c2 
TMP_552))) in (let TMP_554 \def (ex4 nat TMP_548 TMP_550 TMP_551 TMP_553) in 
(let TMP_555 \def (or TMP_544 TMP_554) in (let TMP_661 \def (\lambda (x0: 
nat).(\lambda (H4: (eq nat O (clen c))).(\lambda (H5: (eq K k (Bind 
b))).(\lambda (H6: (eq T u1 u2)).(\lambda (H7: (eq C c2 (CSort x0))).(let 
TMP_556 \def (CSort x0) in (let TMP_575 \def (\lambda (c0: C).(let TMP_558 
\def (\lambda (e: C).(let TMP_557 \def (CTail k u1 e) in (eq C c0 TMP_557))) 
in (let TMP_563 \def (\lambda (e: C).(let TMP_559 \def (Flat f) in (let 
TMP_560 \def (CHead c TMP_559 t) in (let TMP_561 \def (Bind b) in (let 
TMP_562 \def (CHead e TMP_561 u2) in (getl O TMP_560 TMP_562)))))) in (let 
TMP_564 \def (ex2 C TMP_558 TMP_563) in (let TMP_568 \def (\lambda (_: 
nat).(let TMP_565 \def (Flat f) in (let TMP_566 \def (clen c) in (let TMP_567 
\def (s TMP_565 TMP_566) in (eq nat O TMP_567))))) in (let TMP_570 \def 
(\lambda (_: nat).(let TMP_569 \def (Bind b) in (eq K k TMP_569))) in (let 
TMP_571 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_573 \def (\lambda 
(n: nat).(let TMP_572 \def (CSort n) in (eq C c0 TMP_572))) in (let TMP_574 
\def (ex4 nat TMP_568 TMP_570 TMP_571 TMP_573) in (or TMP_564 
TMP_574)))))))))) in (let TMP_596 \def (\lambda (t0: T).(let TMP_578 \def 
(\lambda (e: C).(let TMP_576 \def (CSort x0) in (let TMP_577 \def (CTail k u1 
e) in (eq C TMP_576 TMP_577)))) in (let TMP_583 \def (\lambda (e: C).(let 
TMP_579 \def (Flat f) in (let TMP_580 \def (CHead c TMP_579 t) in (let 
TMP_581 \def (Bind b) in (let TMP_582 \def (CHead e TMP_581 t0) in (getl O 
TMP_580 TMP_582)))))) in (let TMP_584 \def (ex2 C TMP_578 TMP_583) in (let 
TMP_588 \def (\lambda (_: nat).(let TMP_585 \def (Flat f) in (let TMP_586 
\def (clen c) in (let TMP_587 \def (s TMP_585 TMP_586) in (eq nat O 
TMP_587))))) in (let TMP_590 \def (\lambda (_: nat).(let TMP_589 \def (Bind 
b) in (eq K k TMP_589))) in (let TMP_591 \def (\lambda (_: nat).(eq T u1 t0)) 
in (let TMP_594 \def (\lambda (n: nat).(let TMP_592 \def (CSort x0) in (let 
TMP_593 \def (CSort n) in (eq C TMP_592 TMP_593)))) in (let TMP_595 \def (ex4 
nat TMP_588 TMP_590 TMP_591 TMP_594) in (or TMP_584 TMP_595)))))))))) in (let 
TMP_597 \def (Bind b) in (let TMP_618 \def (\lambda (k1: K).(let TMP_600 \def 
(\lambda (e: C).(let TMP_598 \def (CSort x0) in (let TMP_599 \def (CTail k1 
u1 e) in (eq C TMP_598 TMP_599)))) in (let TMP_605 \def (\lambda (e: C).(let 
TMP_601 \def (Flat f) in (let TMP_602 \def (CHead c TMP_601 t) in (let 
TMP_603 \def (Bind b) in (let TMP_604 \def (CHead e TMP_603 u1) in (getl O 
TMP_602 TMP_604)))))) in (let TMP_606 \def (ex2 C TMP_600 TMP_605) in (let 
TMP_610 \def (\lambda (_: nat).(let TMP_607 \def (Flat f) in (let TMP_608 
\def (clen c) in (let TMP_609 \def (s TMP_607 TMP_608) in (eq nat O 
TMP_609))))) in (let TMP_612 \def (\lambda (_: nat).(let TMP_611 \def (Bind 
b) in (eq K k1 TMP_611))) in (let TMP_613 \def (\lambda (_: nat).(eq T u1 
u1)) in (let TMP_616 \def (\lambda (n: nat).(let TMP_614 \def (CSort x0) in 
(let TMP_615 \def (CSort n) in (eq C TMP_614 TMP_615)))) in (let TMP_617 \def 
(ex4 nat TMP_610 TMP_612 TMP_613 TMP_616) in (or TMP_606 TMP_617)))))))))) in 
(let TMP_622 \def (\lambda (e: C).(let TMP_619 \def (CSort x0) in (let 
TMP_620 \def (Bind b) in (let TMP_621 \def (CTail TMP_620 u1 e) in (eq C 
TMP_619 TMP_621))))) in (let TMP_627 \def (\lambda (e: C).(let TMP_623 \def 
(Flat f) in (let TMP_624 \def (CHead c TMP_623 t) in (let TMP_625 \def (Bind 
b) in (let TMP_626 \def (CHead e TMP_625 u1) in (getl O TMP_624 TMP_626)))))) 
in (let TMP_628 \def (ex2 C TMP_622 TMP_627) in (let TMP_632 \def (\lambda 
(_: nat).(let TMP_629 \def (Flat f) in (let TMP_630 \def (clen c) in (let 
TMP_631 \def (s TMP_629 TMP_630) in (eq nat O TMP_631))))) in (let TMP_635 
\def (\lambda (_: nat).(let TMP_633 \def (Bind b) in (let TMP_634 \def (Bind 
b) in (eq K TMP_633 TMP_634)))) in (let TMP_636 \def (\lambda (_: nat).(eq T 
u1 u1)) in (let TMP_639 \def (\lambda (n: nat).(let TMP_637 \def (CSort x0) 
in (let TMP_638 \def (CSort n) in (eq C TMP_637 TMP_638)))) in (let TMP_640 
\def (ex4 nat TMP_632 TMP_635 TMP_636 TMP_639) in (let TMP_644 \def (\lambda 
(_: nat).(let TMP_641 \def (Flat f) in (let TMP_642 \def (clen c) in (let 
TMP_643 \def (s TMP_641 TMP_642) in (eq nat O TMP_643))))) in (let TMP_647 
\def (\lambda (_: nat).(let TMP_645 \def (Bind b) in (let TMP_646 \def (Bind 
b) in (eq K TMP_645 TMP_646)))) in (let TMP_648 \def (\lambda (_: nat).(eq T 
u1 u1)) in (let TMP_651 \def (\lambda (n: nat).(let TMP_649 \def (CSort x0) 
in (let TMP_650 \def (CSort n) in (eq C TMP_649 TMP_650)))) in (let TMP_652 
\def (Bind b) in (let TMP_653 \def (refl_equal K TMP_652) in (let TMP_654 
\def (refl_equal T u1) in (let TMP_655 \def (CSort x0) in (let TMP_656 \def 
(refl_equal C TMP_655) in (let TMP_657 \def (ex4_intro nat TMP_644 TMP_647 
TMP_648 TMP_651 x0 H4 TMP_653 TMP_654 TMP_656) in (let TMP_658 \def 
(or_intror TMP_628 TMP_640 TMP_657) in (let TMP_659 \def (eq_ind_r K TMP_597 
TMP_618 TMP_658 k H5) in (let TMP_660 \def (eq_ind T u1 TMP_596 TMP_659 u2 
H6) in (eq_ind_r C TMP_556 TMP_575 TMP_660 c2 
H7)))))))))))))))))))))))))))))))) in (ex4_ind nat TMP_531 TMP_533 TMP_534 
TMP_536 TMP_555 TMP_661 H3)))))))))))))))) in (or_ind TMP_421 TMP_429 TMP_448 
TMP_529 TMP_662 H2)))))))))))))))))))))))))))))))))) in (let TMP_664 \def 
(CTail k u1 c) in (let TMP_665 \def (CHead TMP_664 k0 t) in (let TMP_666 \def 
(Bind b) in (let TMP_667 \def (CHead c2 TMP_666 u2) in (let TMP_668 \def 
(getl_gen_O TMP_665 TMP_667 H0) in (K_ind TMP_262 TMP_404 TMP_663 k0 
TMP_668)))))))))) in (let TMP_1085 \def (\lambda (n: nat).(\lambda (H0: 
(((getl n (CHead (CTail k u1 c) k0 t) (CHead c2 (Bind b) u2)) \to (or (ex2 C 
(\lambda (e: C).(eq C c2 (CTail k u1 e))) (\lambda (e: C).(getl n (CHead c k0 
t) (CHead e (Bind b) u2)))) (ex4 nat (\lambda (_: nat).(eq nat n (s k0 (clen 
c)))) (\lambda (_: nat).(eq K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) 
(\lambda (n0: nat).(eq C c2 (CSort n0)))))))).(\lambda (H1: (getl (S n) 
(CHead (CTail k u1 c) k0 t) (CHead c2 (Bind b) u2))).(let TMP_670 \def (r k0 
n) in (let TMP_671 \def (CTail k u1 c) in (let TMP_672 \def (Bind b) in (let 
TMP_673 \def (CHead c2 TMP_672 u2) in (let TMP_674 \def (getl_gen_S k0 
TMP_671 TMP_673 t n H1) in (let H_x \def (H TMP_670 TMP_674) in (let H2 \def 
H_x in (let TMP_676 \def (\lambda (e: C).(let TMP_675 \def (CTail k u1 e) in 
(eq C c2 TMP_675))) in (let TMP_680 \def (\lambda (e: C).(let TMP_677 \def (r 
k0 n) in (let TMP_678 \def (Bind b) in (let TMP_679 \def (CHead e TMP_678 u2) 
in (getl TMP_677 c TMP_679))))) in (let TMP_681 \def (ex2 C TMP_676 TMP_680) 
in (let TMP_684 \def (\lambda (_: nat).(let TMP_682 \def (r k0 n) in (let 
TMP_683 \def (clen c) in (eq nat TMP_682 TMP_683)))) in (let TMP_686 \def 
(\lambda (_: nat).(let TMP_685 \def (Bind b) in (eq K k TMP_685))) in (let 
TMP_687 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_689 \def (\lambda 
(n0: nat).(let TMP_688 \def (CSort n0) in (eq C c2 TMP_688))) in (let TMP_690 
\def (ex4 nat TMP_684 TMP_686 TMP_687 TMP_689) in (let TMP_692 \def (\lambda 
(e: C).(let TMP_691 \def (CTail k u1 e) in (eq C c2 TMP_691))) in (let 
TMP_697 \def (\lambda (e: C).(let TMP_693 \def (S n) in (let TMP_694 \def 
(CHead c k0 t) in (let TMP_695 \def (Bind b) in (let TMP_696 \def (CHead e 
TMP_695 u2) in (getl TMP_693 TMP_694 TMP_696)))))) in (let TMP_698 \def (ex2 
C TMP_692 TMP_697) in (let TMP_702 \def (\lambda (_: nat).(let TMP_699 \def 
(S n) in (let TMP_700 \def (clen c) in (let TMP_701 \def (s k0 TMP_700) in 
(eq nat TMP_699 TMP_701))))) in (let TMP_704 \def (\lambda (_: nat).(let 
TMP_703 \def (Bind b) in (eq K k TMP_703))) in (let TMP_705 \def (\lambda (_: 
nat).(eq T u1 u2)) in (let TMP_707 \def (\lambda (n0: nat).(let TMP_706 \def 
(CSort n0) in (eq C c2 TMP_706))) in (let TMP_708 \def (ex4 nat TMP_702 
TMP_704 TMP_705 TMP_707) in (let TMP_709 \def (or TMP_698 TMP_708) in (let 
TMP_819 \def (\lambda (H3: (ex2 C (\lambda (e: C).(eq C c2 (CTail k u1 e))) 
(\lambda (e: C).(getl (r k0 n) c (CHead e (Bind b) u2))))).(let TMP_711 \def 
(\lambda (e: C).(let TMP_710 \def (CTail k u1 e) in (eq C c2 TMP_710))) in 
(let TMP_715 \def (\lambda (e: C).(let TMP_712 \def (r k0 n) in (let TMP_713 
\def (Bind b) in (let TMP_714 \def (CHead e TMP_713 u2) in (getl TMP_712 c 
TMP_714))))) in (let TMP_717 \def (\lambda (e: C).(let TMP_716 \def (CTail k 
u1 e) in (eq C c2 TMP_716))) in (let TMP_722 \def (\lambda (e: C).(let 
TMP_718 \def (S n) in (let TMP_719 \def (CHead c k0 t) in (let TMP_720 \def 
(Bind b) in (let TMP_721 \def (CHead e TMP_720 u2) in (getl TMP_718 TMP_719 
TMP_721)))))) in (let TMP_723 \def (ex2 C TMP_717 TMP_722) in (let TMP_727 
\def (\lambda (_: nat).(let TMP_724 \def (S n) in (let TMP_725 \def (clen c) 
in (let TMP_726 \def (s k0 TMP_725) in (eq nat TMP_724 TMP_726))))) in (let 
TMP_729 \def (\lambda (_: nat).(let TMP_728 \def (Bind b) in (eq K k 
TMP_728))) in (let TMP_730 \def (\lambda (_: nat).(eq T u1 u2)) in (let 
TMP_732 \def (\lambda (n0: nat).(let TMP_731 \def (CSort n0) in (eq C c2 
TMP_731))) in (let TMP_733 \def (ex4 nat TMP_727 TMP_729 TMP_730 TMP_732) in 
(let TMP_734 \def (or TMP_723 TMP_733) in (let TMP_818 \def (\lambda (x: 
C).(\lambda (H4: (eq C c2 (CTail k u1 x))).(\lambda (H5: (getl (r k0 n) c 
(CHead x (Bind b) u2))).(let TMP_739 \def (\lambda (c0: C).(let TMP_735 \def 
(r k0 n) in (let TMP_736 \def (CTail k u1 c) in (let TMP_737 \def (Bind b) in 
(let TMP_738 \def (CHead c0 TMP_737 u2) in (getl TMP_735 TMP_736 
TMP_738)))))) in (let TMP_740 \def (CTail k u1 c) in (let TMP_741 \def (Bind 
b) in (let TMP_742 \def (CHead c2 TMP_741 u2) in (let TMP_743 \def 
(getl_gen_S k0 TMP_740 TMP_742 t n H1) in (let TMP_744 \def (CTail k u1 x) in 
(let H6 \def (eq_ind C c2 TMP_739 TMP_743 TMP_744 H4) in (let TMP_761 \def 
(\lambda (c0: C).((getl n (CHead (CTail k u1 c) k0 t) (CHead c0 (Bind b) u2)) 
\to (let TMP_746 \def (\lambda (e: C).(let TMP_745 \def (CTail k u1 e) in (eq 
C c0 TMP_745))) in (let TMP_750 \def (\lambda (e: C).(let TMP_747 \def (CHead 
c k0 t) in (let TMP_748 \def (Bind b) in (let TMP_749 \def (CHead e TMP_748 
u2) in (getl n TMP_747 TMP_749))))) in (let TMP_751 \def (ex2 C TMP_746 
TMP_750) in (let TMP_754 \def (\lambda (_: nat).(let TMP_752 \def (clen c) in 
(let TMP_753 \def (s k0 TMP_752) in (eq nat n TMP_753)))) in (let TMP_756 
\def (\lambda (_: nat).(let TMP_755 \def (Bind b) in (eq K k TMP_755))) in 
(let TMP_757 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_759 \def 
(\lambda (n0: nat).(let TMP_758 \def (CSort n0) in (eq C c0 TMP_758))) in 
(let TMP_760 \def (ex4 nat TMP_754 TMP_756 TMP_757 TMP_759) in (or TMP_751 
TMP_760))))))))))) in (let TMP_762 \def (CTail k u1 x) in (let H7 \def 
(eq_ind C c2 TMP_761 H0 TMP_762 H4) in (let TMP_763 \def (CTail k u1 x) in 
(let TMP_782 \def (\lambda (c0: C).(let TMP_765 \def (\lambda (e: C).(let 
TMP_764 \def (CTail k u1 e) in (eq C c0 TMP_764))) in (let TMP_770 \def 
(\lambda (e: C).(let TMP_766 \def (S n) in (let TMP_767 \def (CHead c k0 t) 
in (let TMP_768 \def (Bind b) in (let TMP_769 \def (CHead e TMP_768 u2) in 
(getl TMP_766 TMP_767 TMP_769)))))) in (let TMP_771 \def (ex2 C TMP_765 
TMP_770) in (let TMP_775 \def (\lambda (_: nat).(let TMP_772 \def (S n) in 
(let TMP_773 \def (clen c) in (let TMP_774 \def (s k0 TMP_773) in (eq nat 
TMP_772 TMP_774))))) in (let TMP_777 \def (\lambda (_: nat).(let TMP_776 \def 
(Bind b) in (eq K k TMP_776))) in (let TMP_778 \def (\lambda (_: nat).(eq T 
u1 u2)) in (let TMP_780 \def (\lambda (n0: nat).(let TMP_779 \def (CSort n0) 
in (eq C c0 TMP_779))) in (let TMP_781 \def (ex4 nat TMP_775 TMP_777 TMP_778 
TMP_780) in (or TMP_771 TMP_781)))))))))) in (let TMP_785 \def (\lambda (e: 
C).(let TMP_783 \def (CTail k u1 x) in (let TMP_784 \def (CTail k u1 e) in 
(eq C TMP_783 TMP_784)))) in (let TMP_790 \def (\lambda (e: C).(let TMP_786 
\def (S n) in (let TMP_787 \def (CHead c k0 t) in (let TMP_788 \def (Bind b) 
in (let TMP_789 \def (CHead e TMP_788 u2) in (getl TMP_786 TMP_787 
TMP_789)))))) in (let TMP_791 \def (ex2 C TMP_785 TMP_790) in (let TMP_795 
\def (\lambda (_: nat).(let TMP_792 \def (S n) in (let TMP_793 \def (clen c) 
in (let TMP_794 \def (s k0 TMP_793) in (eq nat TMP_792 TMP_794))))) in (let 
TMP_797 \def (\lambda (_: nat).(let TMP_796 \def (Bind b) in (eq K k 
TMP_796))) in (let TMP_798 \def (\lambda (_: nat).(eq T u1 u2)) in (let 
TMP_801 \def (\lambda (n0: nat).(let TMP_799 \def (CTail k u1 x) in (let 
TMP_800 \def (CSort n0) in (eq C TMP_799 TMP_800)))) in (let TMP_802 \def 
(ex4 nat TMP_795 TMP_797 TMP_798 TMP_801) in (let TMP_805 \def (\lambda (e: 
C).(let TMP_803 \def (CTail k u1 x) in (let TMP_804 \def (CTail k u1 e) in 
(eq C TMP_803 TMP_804)))) in (let TMP_810 \def (\lambda (e: C).(let TMP_806 
\def (S n) in (let TMP_807 \def (CHead c k0 t) in (let TMP_808 \def (Bind b) 
in (let TMP_809 \def (CHead e TMP_808 u2) in (getl TMP_806 TMP_807 
TMP_809)))))) in (let TMP_811 \def (CTail k u1 x) in (let TMP_812 \def 
(refl_equal C TMP_811) in (let TMP_813 \def (Bind b) in (let TMP_814 \def 
(CHead x TMP_813 u2) in (let TMP_815 \def (getl_head k0 n c TMP_814 H5 t) in 
(let TMP_816 \def (ex_intro2 C TMP_805 TMP_810 x TMP_812 TMP_815) in (let 
TMP_817 \def (or_introl TMP_791 TMP_802 TMP_816) in (eq_ind_r C TMP_763 
TMP_782 TMP_817 c2 H4))))))))))))))))))))))))))))))))) in (ex2_ind C TMP_711 
TMP_715 TMP_734 TMP_818 H3)))))))))))))) in (let TMP_1084 \def (\lambda (H3: 
(ex4 nat (\lambda (_: nat).(eq nat (r k0 n) (clen c))) (\lambda (_: nat).(eq 
K k (Bind b))) (\lambda (_: nat).(eq T u1 u2)) (\lambda (n0: nat).(eq C c2 
(CSort n0))))).(let TMP_822 \def (\lambda (_: nat).(let TMP_820 \def (r k0 n) 
in (let TMP_821 \def (clen c) in (eq nat TMP_820 TMP_821)))) in (let TMP_824 
\def (\lambda (_: nat).(let TMP_823 \def (Bind b) in (eq K k TMP_823))) in 
(let TMP_825 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_827 \def 
(\lambda (n0: nat).(let TMP_826 \def (CSort n0) in (eq C c2 TMP_826))) in 
(let TMP_829 \def (\lambda (e: C).(let TMP_828 \def (CTail k u1 e) in (eq C 
c2 TMP_828))) in (let TMP_834 \def (\lambda (e: C).(let TMP_830 \def (S n) in 
(let TMP_831 \def (CHead c k0 t) in (let TMP_832 \def (Bind b) in (let 
TMP_833 \def (CHead e TMP_832 u2) in (getl TMP_830 TMP_831 TMP_833)))))) in 
(let TMP_835 \def (ex2 C TMP_829 TMP_834) in (let TMP_839 \def (\lambda (_: 
nat).(let TMP_836 \def (S n) in (let TMP_837 \def (clen c) in (let TMP_838 
\def (s k0 TMP_837) in (eq nat TMP_836 TMP_838))))) in (let TMP_841 \def 
(\lambda (_: nat).(let TMP_840 \def (Bind b) in (eq K k TMP_840))) in (let 
TMP_842 \def (\lambda (_: nat).(eq T u1 u2)) in (let TMP_844 \def (\lambda 
(n0: nat).(let TMP_843 \def (CSort n0) in (eq C c2 TMP_843))) in (let TMP_845 
\def (ex4 nat TMP_839 TMP_841 TMP_842 TMP_844) in (let TMP_846 \def (or 
TMP_835 TMP_845) in (let TMP_1083 \def (\lambda (x0: nat).(\lambda (H4: (eq 
nat (r k0 n) (clen c))).(\lambda (H5: (eq K k (Bind b))).(\lambda (H6: (eq T 
u1 u2)).(\lambda (H7: (eq C c2 (CSort x0))).(let TMP_851 \def (\lambda (c0: 
C).(let TMP_847 \def (r k0 n) in (let TMP_848 \def (CTail k u1 c) in (let 
TMP_849 \def (Bind b) in (let TMP_850 \def (CHead c0 TMP_849 u2) in (getl 
TMP_847 TMP_848 TMP_850)))))) in (let TMP_852 \def (CTail k u1 c) in (let 
TMP_853 \def (Bind b) in (let TMP_854 \def (CHead c2 TMP_853 u2) in (let 
TMP_855 \def (getl_gen_S k0 TMP_852 TMP_854 t n H1) in (let TMP_856 \def 
(CSort x0) in (let H8 \def (eq_ind C c2 TMP_851 TMP_855 TMP_856 H7) in (let 
TMP_873 \def (\lambda (c0: C).((getl n (CHead (CTail k u1 c) k0 t) (CHead c0 
(Bind b) u2)) \to (let TMP_858 \def (\lambda (e: C).(let TMP_857 \def (CTail 
k u1 e) in (eq C c0 TMP_857))) in (let TMP_862 \def (\lambda (e: C).(let 
TMP_859 \def (CHead c k0 t) in (let TMP_860 \def (Bind b) in (let TMP_861 
\def (CHead e TMP_860 u2) in (getl n TMP_859 TMP_861))))) in (let TMP_863 
\def (ex2 C TMP_858 TMP_862) in (let TMP_866 \def (\lambda (_: nat).(let 
TMP_864 \def (clen c) in (let TMP_865 \def (s k0 TMP_864) in (eq nat n 
TMP_865)))) in (let TMP_868 \def (\lambda (_: nat).(let TMP_867 \def (Bind b) 
in (eq K k TMP_867))) in (let TMP_869 \def (\lambda (_: nat).(eq T u1 u2)) in 
(let TMP_871 \def (\lambda (n0: nat).(let TMP_870 \def (CSort n0) in (eq C c0 
TMP_870))) in (let TMP_872 \def (ex4 nat TMP_866 TMP_868 TMP_869 TMP_871) in 
(or TMP_863 TMP_872))))))))))) in (let TMP_874 \def (CSort x0) in (let H9 
\def (eq_ind C c2 TMP_873 H0 TMP_874 H7) in (let TMP_875 \def (CSort x0) in 
(let TMP_894 \def (\lambda (c0: C).(let TMP_877 \def (\lambda (e: C).(let 
TMP_876 \def (CTail k u1 e) in (eq C c0 TMP_876))) in (let TMP_882 \def 
(\lambda (e: C).(let TMP_878 \def (S n) in (let TMP_879 \def (CHead c k0 t) 
in (let TMP_880 \def (Bind b) in (let TMP_881 \def (CHead e TMP_880 u2) in 
(getl TMP_878 TMP_879 TMP_881)))))) in (let TMP_883 \def (ex2 C TMP_877 
TMP_882) in (let TMP_887 \def (\lambda (_: nat).(let TMP_884 \def (S n) in 
(let TMP_885 \def (clen c) in (let TMP_886 \def (s k0 TMP_885) in (eq nat 
TMP_884 TMP_886))))) in (let TMP_889 \def (\lambda (_: nat).(let TMP_888 \def 
(Bind b) in (eq K k TMP_888))) in (let TMP_890 \def (\lambda (_: nat).(eq T 
u1 u2)) in (let TMP_892 \def (\lambda (n0: nat).(let TMP_891 \def (CSort n0) 
in (eq C c0 TMP_891))) in (let TMP_893 \def (ex4 nat TMP_887 TMP_889 TMP_890 
TMP_892) in (or TMP_883 TMP_893)))))))))) in (let TMP_913 \def (\lambda (t0: 
T).((getl n (CHead (CTail k u1 c) k0 t) (CHead (CSort x0) (Bind b) t0)) \to 
(let TMP_897 \def (\lambda (e: C).(let TMP_895 \def (CSort x0) in (let 
TMP_896 \def (CTail k u1 e) in (eq C TMP_895 TMP_896)))) in (let TMP_901 \def 
(\lambda (e: C).(let TMP_898 \def (CHead c k0 t) in (let TMP_899 \def (Bind 
b) in (let TMP_900 \def (CHead e TMP_899 t0) in (getl n TMP_898 TMP_900))))) 
in (let TMP_902 \def (ex2 C TMP_897 TMP_901) in (let TMP_905 \def (\lambda 
(_: nat).(let TMP_903 \def (clen c) in (let TMP_904 \def (s k0 TMP_903) in 
(eq nat n TMP_904)))) in (let TMP_907 \def (\lambda (_: nat).(let TMP_906 
\def (Bind b) in (eq K k TMP_906))) in (let TMP_908 \def (\lambda (_: 
nat).(eq T u1 t0)) in (let TMP_911 \def (\lambda (n0: nat).(let TMP_909 \def 
(CSort x0) in (let TMP_910 \def (CSort n0) in (eq C TMP_909 TMP_910)))) in 
(let TMP_912 \def (ex4 nat TMP_905 TMP_907 TMP_908 TMP_911) in (or TMP_902 
TMP_912))))))))))) in (let H10 \def (eq_ind_r T u2 TMP_913 H9 u1 H6) in (let 
TMP_919 \def (\lambda (t0: T).(let TMP_914 \def (r k0 n) in (let TMP_915 \def 
(CTail k u1 c) in (let TMP_916 \def (CSort x0) in (let TMP_917 \def (Bind b) 
in (let TMP_918 \def (CHead TMP_916 TMP_917 t0) in (getl TMP_914 TMP_915 
TMP_918))))))) in (let H11 \def (eq_ind_r T u2 TMP_919 H8 u1 H6) in (let 
TMP_940 \def (\lambda (t0: T).(let TMP_922 \def (\lambda (e: C).(let TMP_920 
\def (CSort x0) in (let TMP_921 \def (CTail k u1 e) in (eq C TMP_920 
TMP_921)))) in (let TMP_927 \def (\lambda (e: C).(let TMP_923 \def (S n) in 
(let TMP_924 \def (CHead c k0 t) in (let TMP_925 \def (Bind b) in (let 
TMP_926 \def (CHead e TMP_925 t0) in (getl TMP_923 TMP_924 TMP_926)))))) in 
(let TMP_928 \def (ex2 C TMP_922 TMP_927) in (let TMP_932 \def (\lambda (_: 
nat).(let TMP_929 \def (S n) in (let TMP_930 \def (clen c) in (let TMP_931 
\def (s k0 TMP_930) in (eq nat TMP_929 TMP_931))))) in (let TMP_934 \def 
(\lambda (_: nat).(let TMP_933 \def (Bind b) in (eq K k TMP_933))) in (let 
TMP_935 \def (\lambda (_: nat).(eq T u1 t0)) in (let TMP_938 \def (\lambda 
(n0: nat).(let TMP_936 \def (CSort x0) in (let TMP_937 \def (CSort n0) in (eq 
C TMP_936 TMP_937)))) in (let TMP_939 \def (ex4 nat TMP_932 TMP_934 TMP_935 
TMP_938) in (or TMP_928 TMP_939)))))))))) in (let TMP_959 \def (\lambda (k1: 
K).((getl n (CHead (CTail k1 u1 c) k0 t) (CHead (CSort x0) (Bind b) u1)) \to 
(let TMP_943 \def (\lambda (e: C).(let TMP_941 \def (CSort x0) in (let 
TMP_942 \def (CTail k1 u1 e) in (eq C TMP_941 TMP_942)))) in (let TMP_947 
\def (\lambda (e: C).(let TMP_944 \def (CHead c k0 t) in (let TMP_945 \def 
(Bind b) in (let TMP_946 \def (CHead e TMP_945 u1) in (getl n TMP_944 
TMP_946))))) in (let TMP_948 \def (ex2 C TMP_943 TMP_947) in (let TMP_951 
\def (\lambda (_: nat).(let TMP_949 \def (clen c) in (let TMP_950 \def (s k0 
TMP_949) in (eq nat n TMP_950)))) in (let TMP_953 \def (\lambda (_: nat).(let 
TMP_952 \def (Bind b) in (eq K k1 TMP_952))) in (let TMP_954 \def (\lambda 
(_: nat).(eq T u1 u1)) in (let TMP_957 \def (\lambda (n0: nat).(let TMP_955 
\def (CSort x0) in (let TMP_956 \def (CSort n0) in (eq C TMP_955 TMP_956)))) 
in (let TMP_958 \def (ex4 nat TMP_951 TMP_953 TMP_954 TMP_957) in (or TMP_948 
TMP_958))))))))))) in (let TMP_960 \def (Bind b) in (let H12 \def (eq_ind K k 
TMP_959 H10 TMP_960 H5) in (let TMP_966 \def (\lambda (k1: K).(let TMP_961 
\def (r k0 n) in (let TMP_962 \def (CTail k1 u1 c) in (let TMP_963 \def 
(CSort x0) in (let TMP_964 \def (Bind b) in (let TMP_965 \def (CHead TMP_963 
TMP_964 u1) in (getl TMP_961 TMP_962 TMP_965))))))) in (let TMP_967 \def 
(Bind b) in (let H13 \def (eq_ind K k TMP_966 H11 TMP_967 H5) in (let TMP_968 
\def (Bind b) in (let TMP_989 \def (\lambda (k1: K).(let TMP_971 \def 
(\lambda (e: C).(let TMP_969 \def (CSort x0) in (let TMP_970 \def (CTail k1 
u1 e) in (eq C TMP_969 TMP_970)))) in (let TMP_976 \def (\lambda (e: C).(let 
TMP_972 \def (S n) in (let TMP_973 \def (CHead c k0 t) in (let TMP_974 \def 
(Bind b) in (let TMP_975 \def (CHead e TMP_974 u1) in (getl TMP_972 TMP_973 
TMP_975)))))) in (let TMP_977 \def (ex2 C TMP_971 TMP_976) in (let TMP_981 
\def (\lambda (_: nat).(let TMP_978 \def (S n) in (let TMP_979 \def (clen c) 
in (let TMP_980 \def (s k0 TMP_979) in (eq nat TMP_978 TMP_980))))) in (let 
TMP_983 \def (\lambda (_: nat).(let TMP_982 \def (Bind b) in (eq K k1 
TMP_982))) in (let TMP_984 \def (\lambda (_: nat).(eq T u1 u1)) in (let 
TMP_987 \def (\lambda (n0: nat).(let TMP_985 \def (CSort x0) in (let TMP_986 
\def (CSort n0) in (eq C TMP_985 TMP_986)))) in (let TMP_988 \def (ex4 nat 
TMP_981 TMP_983 TMP_984 TMP_987) in (or TMP_977 TMP_988)))))))))) in (let 
TMP_990 \def (r k0 n) in (let TMP_1012 \def (\lambda (n0: nat).(let TMP_994 
\def (\lambda (e: C).(let TMP_991 \def (CSort x0) in (let TMP_992 \def (Bind 
b) in (let TMP_993 \def (CTail TMP_992 u1 e) in (eq C TMP_991 TMP_993))))) in 
(let TMP_999 \def (\lambda (e: C).(let TMP_995 \def (S n) in (let TMP_996 
\def (CHead c k0 t) in (let TMP_997 \def (Bind b) in (let TMP_998 \def (CHead 
e TMP_997 u1) in (getl TMP_995 TMP_996 TMP_998)))))) in (let TMP_1000 \def 
(ex2 C TMP_994 TMP_999) in (let TMP_1003 \def (\lambda (_: nat).(let TMP_1001 
\def (S n) in (let TMP_1002 \def (s k0 n0) in (eq nat TMP_1001 TMP_1002)))) 
in (let TMP_1006 \def (\lambda (_: nat).(let TMP_1004 \def (Bind b) in (let 
TMP_1005 \def (Bind b) in (eq K TMP_1004 TMP_1005)))) in (let TMP_1007 \def 
(\lambda (_: nat).(eq T u1 u1)) in (let TMP_1010 \def (\lambda (n1: nat).(let 
TMP_1008 \def (CSort x0) in (let TMP_1009 \def (CSort n1) in (eq C TMP_1008 
TMP_1009)))) in (let TMP_1011 \def (ex4 nat TMP_1003 TMP_1006 TMP_1007 
TMP_1010) in (or TMP_1000 TMP_1011)))))))))) in (let TMP_1013 \def (S n) in 
(let TMP_1034 \def (\lambda (n0: nat).(let TMP_1017 \def (\lambda (e: C).(let 
TMP_1014 \def (CSort x0) in (let TMP_1015 \def (Bind b) in (let TMP_1016 \def 
(CTail TMP_1015 u1 e) in (eq C TMP_1014 TMP_1016))))) in (let TMP_1022 \def 
(\lambda (e: C).(let TMP_1018 \def (S n) in (let TMP_1019 \def (CHead c k0 t) 
in (let TMP_1020 \def (Bind b) in (let TMP_1021 \def (CHead e TMP_1020 u1) in 
(getl TMP_1018 TMP_1019 TMP_1021)))))) in (let TMP_1023 \def (ex2 C TMP_1017 
TMP_1022) in (let TMP_1025 \def (\lambda (_: nat).(let TMP_1024 \def (S n) in 
(eq nat TMP_1024 n0))) in (let TMP_1028 \def (\lambda (_: nat).(let TMP_1026 
\def (Bind b) in (let TMP_1027 \def (Bind b) in (eq K TMP_1026 TMP_1027)))) 
in (let TMP_1029 \def (\lambda (_: nat).(eq T u1 u1)) in (let TMP_1032 \def 
(\lambda (n1: nat).(let TMP_1030 \def (CSort x0) in (let TMP_1031 \def (CSort 
n1) in (eq C TMP_1030 TMP_1031)))) in (let TMP_1033 \def (ex4 nat TMP_1025 
TMP_1028 TMP_1029 TMP_1032) in (or TMP_1023 TMP_1033)))))))))) in (let 
TMP_1038 \def (\lambda (e: C).(let TMP_1035 \def (CSort x0) in (let TMP_1036 
\def (Bind b) in (let TMP_1037 \def (CTail TMP_1036 u1 e) in (eq C TMP_1035 
TMP_1037))))) in (let TMP_1043 \def (\lambda (e: C).(let TMP_1039 \def (S n) 
in (let TMP_1040 \def (CHead c k0 t) in (let TMP_1041 \def (Bind b) in (let 
TMP_1042 \def (CHead e TMP_1041 u1) in (getl TMP_1039 TMP_1040 TMP_1042)))))) 
in (let TMP_1044 \def (ex2 C TMP_1038 TMP_1043) in (let TMP_1047 \def 
(\lambda (_: nat).(let TMP_1045 \def (S n) in (let TMP_1046 \def (S n) in (eq 
nat TMP_1045 TMP_1046)))) in (let TMP_1050 \def (\lambda (_: nat).(let 
TMP_1048 \def (Bind b) in (let TMP_1049 \def (Bind b) in (eq K TMP_1048 
TMP_1049)))) in (let TMP_1051 \def (\lambda (_: nat).(eq T u1 u1)) in (let 
TMP_1054 \def (\lambda (n0: nat).(let TMP_1052 \def (CSort x0) in (let 
TMP_1053 \def (CSort n0) in (eq C TMP_1052 TMP_1053)))) in (let TMP_1055 \def 
(ex4 nat TMP_1047 TMP_1050 TMP_1051 TMP_1054) in (let TMP_1058 \def (\lambda 
(_: nat).(let TMP_1056 \def (S n) in (let TMP_1057 \def (S n) in (eq nat 
TMP_1056 TMP_1057)))) in (let TMP_1061 \def (\lambda (_: nat).(let TMP_1059 
\def (Bind b) in (let TMP_1060 \def (Bind b) in (eq K TMP_1059 TMP_1060)))) 
in (let TMP_1062 \def (\lambda (_: nat).(eq T u1 u1)) in (let TMP_1065 \def 
(\lambda (n0: nat).(let TMP_1063 \def (CSort x0) in (let TMP_1064 \def (CSort 
n0) in (eq C TMP_1063 TMP_1064)))) in (let TMP_1066 \def (S n) in (let 
TMP_1067 \def (refl_equal nat TMP_1066) in (let TMP_1068 \def (Bind b) in 
(let TMP_1069 \def (refl_equal K TMP_1068) in (let TMP_1070 \def (refl_equal 
T u1) in (let TMP_1071 \def (CSort x0) in (let TMP_1072 \def (refl_equal C 
TMP_1071) in (let TMP_1073 \def (ex4_intro nat TMP_1058 TMP_1061 TMP_1062 
TMP_1065 x0 TMP_1067 TMP_1069 TMP_1070 TMP_1072) in (let TMP_1074 \def 
(or_intror TMP_1044 TMP_1055 TMP_1073) in (let TMP_1075 \def (r k0 n) in (let 
TMP_1076 \def (s k0 TMP_1075) in (let TMP_1077 \def (s_r k0 n) in (let 
TMP_1078 \def (eq_ind_r nat TMP_1013 TMP_1034 TMP_1074 TMP_1076 TMP_1077) in 
(let TMP_1079 \def (clen c) in (let TMP_1080 \def (eq_ind nat TMP_990 
TMP_1012 TMP_1078 TMP_1079 H4) in (let TMP_1081 \def (eq_ind_r K TMP_968 
TMP_989 TMP_1080 k H5) in (let TMP_1082 \def (eq_ind T u1 TMP_940 TMP_1081 u2 
H6) in (eq_ind_r C TMP_875 TMP_894 TMP_1082 c2 
H7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex4_ind nat TMP_822 TMP_824 TMP_825 TMP_827 TMP_846 TMP_1083 
H3)))))))))))))))) in (or_ind TMP_681 TMP_690 TMP_709 TMP_819 TMP_1084 
H2)))))))))))))))))))))))))))))) in (nat_ind TMP_245 TMP_669 TMP_1085 
i))))))))) in (C_ind TMP_15 TMP_228 TMP_1086 c1))))))))).

