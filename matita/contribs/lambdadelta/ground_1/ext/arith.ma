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

include "ground_1/preamble.ma".

theorem nat_dec:
 \forall (n1: nat).(\forall (n2: nat).(or (eq nat n1 n2) ((eq nat n1 n2) \to 
(\forall (P: Prop).P))))
\def
 \lambda (n1: nat).(let TMP_81 \def (\lambda (n: nat).(\forall (n2: nat).(let 
TMP_80 \def (eq nat n n2) in (let TMP_79 \def ((eq nat n n2) \to (\forall (P: 
Prop).P)) in (or TMP_80 TMP_79))))) in (let TMP_78 \def (\lambda (n2: 
nat).(let TMP_77 \def (\lambda (n: nat).(let TMP_76 \def (eq nat O n) in (let 
TMP_75 \def ((eq nat O n) \to (\forall (P: Prop).P)) in (or TMP_76 TMP_75)))) 
in (let TMP_73 \def (eq nat O O) in (let TMP_72 \def ((eq nat O O) \to 
(\forall (P: Prop).P)) in (let TMP_71 \def (refl_equal nat O) in (let TMP_74 
\def (or_introl TMP_73 TMP_72 TMP_71) in (let TMP_70 \def (\lambda (n: 
nat).(\lambda (_: (or (eq nat O n) ((eq nat O n) \to (\forall (P: 
Prop).P)))).(let TMP_68 \def (S n) in (let TMP_69 \def (eq nat O TMP_68) in 
(let TMP_67 \def ((eq nat O (S n)) \to (\forall (P: Prop).P)) in (let TMP_66 
\def (\lambda (H0: (eq nat O (S n))).(\lambda (P: Prop).(let TMP_65 \def 
(\lambda (ee: nat).(match ee in nat with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_64 \def (S n) in (let H1 \def (eq_ind nat O 
TMP_65 I TMP_64 H0) in (False_ind P H1)))))) in (or_intror TMP_69 TMP_67 
TMP_66))))))) in (nat_ind TMP_77 TMP_74 TMP_70 n2)))))))) in (let TMP_63 \def 
(\lambda (n: nat).(\lambda (H: ((\forall (n2: nat).(or (eq nat n n2) ((eq nat 
n n2) \to (\forall (P: Prop).P)))))).(\lambda (n2: nat).(let TMP_62 \def 
(\lambda (n0: nat).(let TMP_60 \def (S n) in (let TMP_61 \def (eq nat TMP_60 
n0) in (let TMP_59 \def ((eq nat (S n) n0) \to (\forall (P: Prop).P)) in (or 
TMP_61 TMP_59))))) in (let TMP_56 \def (S n) in (let TMP_57 \def (eq nat 
TMP_56 O) in (let TMP_55 \def ((eq nat (S n) O) \to (\forall (P: Prop).P)) in 
(let TMP_54 \def (\lambda (H0: (eq nat (S n) O)).(\lambda (P: Prop).(let 
TMP_53 \def (S n) in (let TMP_52 \def (\lambda (ee: nat).(match ee in nat 
with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H1 \def (eq_ind 
nat TMP_53 TMP_52 I O H0) in (False_ind P H1)))))) in (let TMP_58 \def 
(or_intror TMP_57 TMP_55 TMP_54) in (let TMP_51 \def (\lambda (n0: 
nat).(\lambda (H0: (or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: 
Prop).P)))).(let TMP_50 \def (eq nat n n0) in (let TMP_49 \def ((eq nat n n0) 
\to (\forall (P: Prop).P)) in (let TMP_46 \def (S n) in (let TMP_45 \def (S 
n0) in (let TMP_47 \def (eq nat TMP_46 TMP_45) in (let TMP_44 \def ((eq nat 
(S n) (S n0)) \to (\forall (P: Prop).P)) in (let TMP_48 \def (or TMP_47 
TMP_44) in (let TMP_43 \def (\lambda (H1: (eq nat n n0)).(let TMP_30 \def 
(\lambda (n3: nat).(let TMP_28 \def (S n) in (let TMP_29 \def (eq nat TMP_28 
n3) in (let TMP_27 \def ((eq nat (S n) n3) \to (\forall (P: Prop).P)) in (or 
TMP_29 TMP_27))))) in (let H2 \def (eq_ind_r nat n0 TMP_30 H0 n H1) in (let 
TMP_42 \def (\lambda (n3: nat).(let TMP_40 \def (S n) in (let TMP_39 \def (S 
n3) in (let TMP_41 \def (eq nat TMP_40 TMP_39) in (let TMP_38 \def ((eq nat 
(S n) (S n3)) \to (\forall (P: Prop).P)) in (or TMP_41 TMP_38)))))) in (let 
TMP_35 \def (S n) in (let TMP_34 \def (S n) in (let TMP_36 \def (eq nat 
TMP_35 TMP_34) in (let TMP_33 \def ((eq nat (S n) (S n)) \to (\forall (P: 
Prop).P)) in (let TMP_31 \def (S n) in (let TMP_32 \def (refl_equal nat 
TMP_31) in (let TMP_37 \def (or_introl TMP_36 TMP_33 TMP_32) in (eq_ind nat n 
TMP_42 TMP_37 n0 H1)))))))))))) in (let TMP_26 \def (\lambda (H1: (((eq nat n 
n0) \to (\forall (P: Prop).P)))).(let TMP_24 \def (S n) in (let TMP_23 \def 
(S n0) in (let TMP_25 \def (eq nat TMP_24 TMP_23) in (let TMP_22 \def ((eq 
nat (S n) (S n0)) \to (\forall (P: Prop).P)) in (let TMP_21 \def (\lambda 
(H2: (eq nat (S n) (S n0))).(\lambda (P: Prop).(let TMP_14 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow n | (S n3) \Rightarrow n3])) in (let 
TMP_13 \def (S n) in (let TMP_12 \def (S n0) in (let H3 \def (f_equal nat nat 
TMP_14 TMP_13 TMP_12 H2) in (let TMP_15 \def (\lambda (n3: nat).((eq nat n 
n3) \to (\forall (P0: Prop).P0))) in (let H4 \def (eq_ind_r nat n0 TMP_15 H1 
n H3) in (let TMP_19 \def (\lambda (n3: nat).(let TMP_17 \def (S n) in (let 
TMP_18 \def (eq nat TMP_17 n3) in (let TMP_16 \def ((eq nat (S n) n3) \to 
(\forall (P0: Prop).P0)) in (or TMP_18 TMP_16))))) in (let H5 \def (eq_ind_r 
nat n0 TMP_19 H0 n H3) in (let TMP_20 \def (refl_equal nat n) in (H4 TMP_20 
P)))))))))))) in (or_intror TMP_25 TMP_22 TMP_21))))))) in (let TMP_11 \def 
(H n0) in (or_ind TMP_50 TMP_49 TMP_48 TMP_43 TMP_26 TMP_11))))))))))))) in 
(nat_ind TMP_62 TMP_58 TMP_51 n2))))))))))) in (nat_ind TMP_81 TMP_78 TMP_63 
n1)))).

theorem simpl_plus_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus m n) 
(plus p n)) \to (eq nat m p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat 
(plus m n) (plus p n))).(let TMP_92 \def (plus m n) in (let TMP_91 \def 
(\lambda (n0: nat).(let TMP_90 \def (plus n p) in (eq nat n0 TMP_90))) in 
(let TMP_88 \def (plus p n) in (let TMP_87 \def (\lambda (n0: nat).(let 
TMP_86 \def (plus n p) in (eq nat n0 TMP_86))) in (let TMP_85 \def (plus_sym 
p n) in (let TMP_84 \def (plus m n) in (let TMP_89 \def (eq_ind_r nat TMP_88 
TMP_87 TMP_85 TMP_84 H) in (let TMP_83 \def (plus n m) in (let TMP_82 \def 
(plus_sym n m) in (let TMP_93 \def (eq_ind_r nat TMP_92 TMP_91 TMP_89 TMP_83 
TMP_82) in (simpl_plus_l n m p TMP_93)))))))))))))).

theorem minus_Sx_Sy:
 \forall (x: nat).(\forall (y: nat).(eq nat (minus (S x) (S y)) (minus x y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_94 \def (minus x y) in 
(refl_equal nat TMP_94))).

theorem minus_plus_r:
 \forall (m: nat).(\forall (n: nat).(eq nat (minus (plus m n) n) m))
\def
 \lambda (m: nat).(\lambda (n: nat).(let TMP_100 \def (plus n m) in (let 
TMP_99 \def (\lambda (n0: nat).(let TMP_98 \def (minus n0 n) in (eq nat 
TMP_98 m))) in (let TMP_97 \def (minus_plus n m) in (let TMP_96 \def (plus m 
n) in (let TMP_95 \def (plus_sym m n) in (eq_ind_r nat TMP_100 TMP_99 TMP_97 
TMP_96 TMP_95))))))).

theorem plus_permute_2_in_3:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).(eq nat (plus (plus x 
y) z) (plus (plus x z) y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(let TMP_127 \def (plus 
y z) in (let TMP_128 \def (plus x TMP_127) in (let TMP_126 \def (\lambda (n: 
nat).(let TMP_124 \def (plus x z) in (let TMP_125 \def (plus TMP_124 y) in 
(eq nat n TMP_125)))) in (let TMP_122 \def (plus z y) in (let TMP_121 \def 
(\lambda (n: nat).(let TMP_120 \def (plus x n) in (let TMP_118 \def (plus x 
z) in (let TMP_119 \def (plus TMP_118 y) in (eq nat TMP_120 TMP_119))))) in 
(let TMP_115 \def (plus x z) in (let TMP_116 \def (plus TMP_115 y) in (let 
TMP_114 \def (\lambda (n: nat).(let TMP_112 \def (plus x z) in (let TMP_113 
\def (plus TMP_112 y) in (eq nat n TMP_113)))) in (let TMP_109 \def (plus x 
z) in (let TMP_110 \def (plus TMP_109 y) in (let TMP_111 \def (refl_equal nat 
TMP_110) in (let TMP_107 \def (plus z y) in (let TMP_108 \def (plus x 
TMP_107) in (let TMP_106 \def (plus_assoc_r x z y) in (let TMP_117 \def 
(eq_ind nat TMP_116 TMP_114 TMP_111 TMP_108 TMP_106) in (let TMP_105 \def 
(plus y z) in (let TMP_104 \def (plus_sym y z) in (let TMP_123 \def (eq_ind_r 
nat TMP_122 TMP_121 TMP_117 TMP_105 TMP_104) in (let TMP_102 \def (plus x y) 
in (let TMP_103 \def (plus TMP_102 z) in (let TMP_101 \def (plus_assoc_r x y 
z) in (eq_ind_r nat TMP_128 TMP_126 TMP_123 TMP_103 
TMP_101)))))))))))))))))))))))).

theorem plus_permute_2_in_3_assoc:
 \forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq nat (plus (plus n 
h) k) (plus n (plus k h)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(let TMP_147 \def (plus 
n k) in (let TMP_148 \def (plus TMP_147 h) in (let TMP_146 \def (\lambda (n0: 
nat).(let TMP_144 \def (plus k h) in (let TMP_145 \def (plus n TMP_144) in 
(eq nat n0 TMP_145)))) in (let TMP_141 \def (plus n k) in (let TMP_142 \def 
(plus TMP_141 h) in (let TMP_140 \def (\lambda (n0: nat).(let TMP_138 \def 
(plus n k) in (let TMP_139 \def (plus TMP_138 h) in (eq nat TMP_139 n0)))) in 
(let TMP_135 \def (plus n k) in (let TMP_136 \def (plus TMP_135 h) in (let 
TMP_137 \def (refl_equal nat TMP_136) in (let TMP_133 \def (plus k h) in (let 
TMP_134 \def (plus n TMP_133) in (let TMP_132 \def (plus_assoc_l n k h) in 
(let TMP_143 \def (eq_ind_r nat TMP_142 TMP_140 TMP_137 TMP_134 TMP_132) in 
(let TMP_130 \def (plus n h) in (let TMP_131 \def (plus TMP_130 k) in (let 
TMP_129 \def (plus_permute_2_in_3 n h k) in (eq_ind_r nat TMP_148 TMP_146 
TMP_143 TMP_131 TMP_129))))))))))))))))))).

theorem plus_O:
 \forall (x: nat).(\forall (y: nat).((eq nat (plus x y) O) \to (land (eq nat 
x O) (eq nat y O))))
\def
 \lambda (x: nat).(let TMP_164 \def (\lambda (n: nat).(\forall (y: nat).((eq 
nat (plus n y) O) \to (let TMP_163 \def (eq nat n O) in (let TMP_162 \def (eq 
nat y O) in (land TMP_163 TMP_162)))))) in (let TMP_161 \def (\lambda (y: 
nat).(\lambda (H: (eq nat (plus O y) O)).(let TMP_160 \def (eq nat O O) in 
(let TMP_159 \def (eq nat y O) in (let TMP_158 \def (refl_equal nat O) in 
(conj TMP_160 TMP_159 TMP_158 H)))))) in (let TMP_157 \def (\lambda (n: 
nat).(\lambda (_: ((\forall (y: nat).((eq nat (plus n y) O) \to (land (eq nat 
n O) (eq nat y O)))))).(\lambda (y: nat).(\lambda (H0: (eq nat (plus (S n) y) 
O)).(let H1 \def (match H0 in eq with [refl_equal \Rightarrow (\lambda (H1: 
(eq nat (plus (S n) y) O)).(let TMP_150 \def (S n) in (let TMP_151 \def (plus 
TMP_150 y) in (let TMP_149 \def (\lambda (e: nat).(match e in nat with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H2 \def (eq_ind nat 
TMP_151 TMP_149 I O H1) in (let TMP_153 \def (S n) in (let TMP_154 \def (eq 
nat TMP_153 O) in (let TMP_152 \def (eq nat y O) in (let TMP_155 \def (land 
TMP_154 TMP_152) in (False_ind TMP_155 H2))))))))))]) in (let TMP_156 \def 
(refl_equal nat O) in (H1 TMP_156))))))) in (nat_ind TMP_164 TMP_161 TMP_157 
x)))).

theorem minus_Sx_SO:
 \forall (x: nat).(eq nat (minus (S x) (S O)) x)
\def
 \lambda (x: nat).(let TMP_168 \def (\lambda (n: nat).(eq nat n x)) in (let 
TMP_167 \def (refl_equal nat x) in (let TMP_166 \def (minus x O) in (let 
TMP_165 \def (minus_n_O x) in (eq_ind nat x TMP_168 TMP_167 TMP_166 
TMP_165))))).

theorem nat_dec_neg:
 \forall (i: nat).(\forall (j: nat).(or (not (eq nat i j)) (eq nat i j)))
\def
 \lambda (i: nat).(let TMP_236 \def (\lambda (n: nat).(\forall (j: nat).(let 
TMP_234 \def (eq nat n j) in (let TMP_235 \def (not TMP_234) in (let TMP_233 
\def (eq nat n j) in (or TMP_235 TMP_233)))))) in (let TMP_232 \def (\lambda 
(j: nat).(let TMP_231 \def (\lambda (n: nat).(let TMP_229 \def (eq nat O n) 
in (let TMP_230 \def (not TMP_229) in (let TMP_228 \def (eq nat O n) in (or 
TMP_230 TMP_228))))) in (let TMP_225 \def (eq nat O O) in (let TMP_226 \def 
(not TMP_225) in (let TMP_224 \def (eq nat O O) in (let TMP_223 \def 
(refl_equal nat O) in (let TMP_227 \def (or_intror TMP_226 TMP_224 TMP_223) 
in (let TMP_222 \def (\lambda (n: nat).(\lambda (_: (or (not (eq nat O n)) 
(eq nat O n))).(let TMP_219 \def (S n) in (let TMP_220 \def (eq nat O 
TMP_219) in (let TMP_221 \def (not TMP_220) in (let TMP_217 \def (S n) in 
(let TMP_218 \def (eq nat O TMP_217) in (let TMP_216 \def (O_S n) in 
(or_introl TMP_221 TMP_218 TMP_216))))))))) in (nat_ind TMP_231 TMP_227 
TMP_222 j))))))))) in (let TMP_215 \def (\lambda (n: nat).(\lambda (H: 
((\forall (j: nat).(or (not (eq nat n j)) (eq nat n j))))).(\lambda (j: 
nat).(let TMP_214 \def (\lambda (n0: nat).(let TMP_211 \def (S n) in (let 
TMP_212 \def (eq nat TMP_211 n0) in (let TMP_213 \def (not TMP_212) in (let 
TMP_209 \def (S n) in (let TMP_210 \def (eq nat TMP_209 n0) in (or TMP_213 
TMP_210))))))) in (let TMP_205 \def (S n) in (let TMP_206 \def (eq nat 
TMP_205 O) in (let TMP_207 \def (not TMP_206) in (let TMP_203 \def (S n) in 
(let TMP_204 \def (eq nat TMP_203 O) in (let TMP_201 \def (S n) in (let 
TMP_200 \def (O_S n) in (let TMP_202 \def (sym_not_eq nat O TMP_201 TMP_200) 
in (let TMP_208 \def (or_introl TMP_207 TMP_204 TMP_202) in (let TMP_199 \def 
(\lambda (n0: nat).(\lambda (_: (or (not (eq nat (S n) n0)) (eq nat (S n) 
n0))).(let TMP_197 \def (eq nat n n0) in (let TMP_198 \def (not TMP_197) in 
(let TMP_196 \def (eq nat n n0) in (let TMP_192 \def (S n) in (let TMP_191 
\def (S n0) in (let TMP_193 \def (eq nat TMP_192 TMP_191) in (let TMP_194 
\def (not TMP_193) in (let TMP_189 \def (S n) in (let TMP_188 \def (S n0) in 
(let TMP_190 \def (eq nat TMP_189 TMP_188) in (let TMP_195 \def (or TMP_194 
TMP_190) in (let TMP_187 \def (\lambda (H1: (not (eq nat n n0))).(let TMP_184 
\def (S n) in (let TMP_183 \def (S n0) in (let TMP_185 \def (eq nat TMP_184 
TMP_183) in (let TMP_186 \def (not TMP_185) in (let TMP_181 \def (S n) in 
(let TMP_180 \def (S n0) in (let TMP_182 \def (eq nat TMP_181 TMP_180) in 
(let TMP_179 \def (not_eq_S n n0 H1) in (or_introl TMP_186 TMP_182 
TMP_179)))))))))) in (let TMP_178 \def (\lambda (H1: (eq nat n n0)).(let 
TMP_175 \def (S n) in (let TMP_174 \def (S n0) in (let TMP_176 \def (eq nat 
TMP_175 TMP_174) in (let TMP_177 \def (not TMP_176) in (let TMP_172 \def (S 
n) in (let TMP_171 \def (S n0) in (let TMP_173 \def (eq nat TMP_172 TMP_171) 
in (let TMP_170 \def (f_equal nat nat S n n0 H1) in (or_intror TMP_177 
TMP_173 TMP_170)))))))))) in (let TMP_169 \def (H n0) in (or_ind TMP_198 
TMP_196 TMP_195 TMP_187 TMP_178 TMP_169))))))))))))))))) in (nat_ind TMP_214 
TMP_208 TMP_199 j))))))))))))))) in (nat_ind TMP_236 TMP_232 TMP_215 i)))).

theorem neq_eq_e:
 \forall (i: nat).(\forall (j: nat).(\forall (P: Prop).((((not (eq nat i j)) 
\to P)) \to ((((eq nat i j) \to P)) \to P))))
\def
 \lambda (i: nat).(\lambda (j: nat).(\lambda (P: Prop).(\lambda (H: (((not 
(eq nat i j)) \to P))).(\lambda (H0: (((eq nat i j) \to P))).(let o \def 
(nat_dec_neg i j) in (let TMP_238 \def (eq nat i j) in (let TMP_239 \def (not 
TMP_238) in (let TMP_237 \def (eq nat i j) in (or_ind TMP_239 TMP_237 P H H0 
o))))))))).

theorem le_false:
 \forall (m: nat).(\forall (n: nat).(\forall (P: Prop).((le m n) \to ((le (S 
n) m) \to P))))
\def
 \lambda (m: nat).(let TMP_262 \def (\lambda (n: nat).(\forall (n0: 
nat).(\forall (P: Prop).((le n n0) \to ((le (S n0) n) \to P))))) in (let 
TMP_261 \def (\lambda (n: nat).(\lambda (P: Prop).(\lambda (_: (le O 
n)).(\lambda (H0: (le (S n) O)).(let H1 \def (match H0 in le with [le_n 
\Rightarrow (\lambda (H1: (eq nat (S n) O)).(let TMP_259 \def (S n) in (let 
TMP_258 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow False | (S 
_) \Rightarrow True])) in (let H2 \def (eq_ind nat TMP_259 TMP_258 I O H1) in 
(False_ind P H2))))) | (le_S m0 H1) \Rightarrow (\lambda (H2: (eq nat (S m0) 
O)).(let TMP_255 \def (S m0) in (let TMP_254 \def (\lambda (e: nat).(match e 
in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H3 \def 
(eq_ind nat TMP_255 TMP_254 I O H2) in (let TMP_256 \def ((le (S n) m0) \to 
P) in (let TMP_257 \def (False_ind TMP_256 H3) in (TMP_257 H1)))))))]) in 
(let TMP_260 \def (refl_equal nat O) in (H1 TMP_260))))))) in (let TMP_253 
\def (\lambda (n: nat).(\lambda (H: ((\forall (n0: nat).(\forall (P: 
Prop).((le n n0) \to ((le (S n0) n) \to P)))))).(\lambda (n0: nat).(let 
TMP_252 \def (\lambda (n1: nat).(\forall (P: Prop).((le (S n) n1) \to ((le (S 
n1) (S n)) \to P)))) in (let TMP_251 \def (\lambda (P: Prop).(\lambda (H0: 
(le (S n) O)).(\lambda (_: (le (S O) (S n))).(let H2 \def (match H0 in le 
with [le_n \Rightarrow (\lambda (H2: (eq nat (S n) O)).(let TMP_249 \def (S 
n) in (let TMP_248 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow 
False | (S _) \Rightarrow True])) in (let H3 \def (eq_ind nat TMP_249 TMP_248 
I O H2) in (False_ind P H3))))) | (le_S m0 H2) \Rightarrow (\lambda (H3: (eq 
nat (S m0) O)).(let TMP_245 \def (S m0) in (let TMP_244 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H4 \def (eq_ind nat TMP_245 TMP_244 I O H3) in (let TMP_246 \def ((le (S 
n) m0) \to P) in (let TMP_247 \def (False_ind TMP_246 H4) in (TMP_247 
H2)))))))]) in (let TMP_250 \def (refl_equal nat O) in (H2 TMP_250)))))) in 
(let TMP_243 \def (\lambda (n1: nat).(\lambda (_: ((\forall (P: Prop).((le (S 
n) n1) \to ((le (S n1) (S n)) \to P))))).(\lambda (P: Prop).(\lambda (H1: (le 
(S n) (S n1))).(\lambda (H2: (le (S (S n1)) (S n))).(let TMP_242 \def (le_S_n 
n n1 H1) in (let TMP_240 \def (S n1) in (let TMP_241 \def (le_S_n TMP_240 n 
H2) in (H n1 P TMP_242 TMP_241))))))))) in (nat_ind TMP_252 TMP_251 TMP_243 
n0))))))) in (nat_ind TMP_262 TMP_261 TMP_253 m)))).

theorem le_Sx_x:
 \forall (x: nat).((le (S x) x) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) x)).(\lambda (P: Prop).(let H0 \def 
le_Sn_n in (let TMP_263 \def (H0 x H) in (False_ind P TMP_263))))).

theorem le_n_pred:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (pred n) (pred m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_272 \def 
(\lambda (n0: nat).(let TMP_271 \def (pred n) in (let TMP_270 \def (pred n0) 
in (le TMP_271 TMP_270)))) in (let TMP_268 \def (pred n) in (let TMP_269 \def 
(le_n TMP_268) in (let TMP_267 \def (\lambda (m0: nat).(\lambda (_: (le n 
m0)).(\lambda (H1: (le (pred n) (pred m0))).(let TMP_266 \def (pred n) in 
(let TMP_265 \def (pred m0) in (let TMP_264 \def (le_pred_n m0) in (le_trans 
TMP_266 TMP_265 m0 H1 TMP_264))))))) in (le_ind n TMP_272 TMP_269 TMP_267 m 
H))))))).

theorem minus_le:
 \forall (x: nat).(\forall (y: nat).(le (minus x y) x))
\def
 \lambda (x: nat).(let TMP_285 \def (\lambda (n: nat).(\forall (y: nat).(let 
TMP_284 \def (minus n y) in (le TMP_284 n)))) in (let TMP_283 \def (\lambda 
(_: nat).(le_O_n O)) in (let TMP_282 \def (\lambda (n: nat).(\lambda (H: 
((\forall (y: nat).(le (minus n y) n)))).(\lambda (y: nat).(let TMP_281 \def 
(\lambda (n0: nat).(let TMP_279 \def (S n) in (let TMP_280 \def (minus 
TMP_279 n0) in (let TMP_278 \def (S n) in (le TMP_280 TMP_278))))) in (let 
TMP_276 \def (S n) in (let TMP_277 \def (le_n TMP_276) in (let TMP_275 \def 
(\lambda (n0: nat).(\lambda (_: (le (match n0 with [O \Rightarrow (S n) | (S 
l) \Rightarrow (minus n l)]) (S n))).(let TMP_274 \def (minus n n0) in (let 
TMP_273 \def (H n0) in (le_S TMP_274 n TMP_273))))) in (nat_ind TMP_281 
TMP_277 TMP_275 y)))))))) in (nat_ind TMP_285 TMP_283 TMP_282 x)))).

theorem le_plus_minus_sym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus (minus m n) 
n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_292 \def 
(minus m n) in (let TMP_293 \def (plus n TMP_292) in (let TMP_291 \def 
(\lambda (n0: nat).(eq nat m n0)) in (let TMP_290 \def (le_plus_minus n m H) 
in (let TMP_288 \def (minus m n) in (let TMP_289 \def (plus TMP_288 n) in 
(let TMP_286 \def (minus m n) in (let TMP_287 \def (plus_sym TMP_286 n) in 
(eq_ind_r nat TMP_293 TMP_291 TMP_290 TMP_289 TMP_287))))))))))).

theorem le_minus_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (\forall (z: nat).((le y z) 
\to (le (minus y x) (minus z x))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (z: 
nat).(\lambda (H0: (le y z)).(let TMP_308 \def (minus y x) in (let TMP_307 
\def (minus z x) in (let TMP_305 \def (\lambda (n: nat).(let TMP_303 \def 
(minus z x) in (let TMP_304 \def (plus x TMP_303) in (le n TMP_304)))) in 
(let TMP_301 \def (\lambda (n: nat).(le y n)) in (let TMP_299 \def (minus z 
x) in (let TMP_300 \def (plus x TMP_299) in (let TMP_297 \def (le_trans x y z 
H H0) in (let TMP_298 \def (le_plus_minus_r x z TMP_297) in (let TMP_302 \def 
(eq_ind_r nat z TMP_301 H0 TMP_300 TMP_298) in (let TMP_295 \def (minus y x) 
in (let TMP_296 \def (plus x TMP_295) in (let TMP_294 \def (le_plus_minus_r x 
y H) in (let TMP_306 \def (eq_ind_r nat y TMP_305 TMP_302 TMP_296 TMP_294) in 
(simpl_le_plus_l x TMP_308 TMP_307 TMP_306)))))))))))))))))).

theorem le_minus_plus:
 \forall (z: nat).(\forall (x: nat).((le z x) \to (\forall (y: nat).(eq nat 
(minus (plus x y) z) (plus (minus x z) y)))))
\def
 \lambda (z: nat).(let TMP_368 \def (\lambda (n: nat).(\forall (x: nat).((le 
n x) \to (\forall (y: nat).(let TMP_366 \def (plus x y) in (let TMP_367 \def 
(minus TMP_366 n) in (let TMP_364 \def (minus x n) in (let TMP_365 \def (plus 
TMP_364 y) in (eq nat TMP_367 TMP_365))))))))) in (let TMP_363 \def (\lambda 
(x: nat).(\lambda (H: (le O x)).(let H0 \def (match H in le with [le_n 
\Rightarrow (\lambda (H0: (eq nat O x)).(let TMP_361 \def (\lambda (n: 
nat).(\forall (y: nat).(let TMP_359 \def (plus n y) in (let TMP_360 \def 
(minus TMP_359 O) in (let TMP_357 \def (minus n O) in (let TMP_358 \def (plus 
TMP_357 y) in (eq nat TMP_360 TMP_358))))))) in (let TMP_356 \def (\lambda 
(y: nat).(let TMP_354 \def (minus O O) in (let TMP_355 \def (plus TMP_354 y) 
in (let TMP_352 \def (plus O y) in (let TMP_353 \def (minus TMP_352 O) in 
(let TMP_350 \def (plus O y) in (let TMP_351 \def (minus_n_O TMP_350) in 
(sym_eq nat TMP_355 TMP_353 TMP_351)))))))) in (eq_ind nat O TMP_361 TMP_356 
x H0)))) | (le_S m H0) \Rightarrow (\lambda (H1: (eq nat (S m) x)).(let 
TMP_349 \def (S m) in (let TMP_348 \def (\lambda (n: nat).((le O m) \to 
(\forall (y: nat).(let TMP_346 \def (plus n y) in (let TMP_347 \def (minus 
TMP_346 O) in (let TMP_344 \def (minus n O) in (let TMP_345 \def (plus 
TMP_344 y) in (eq nat TMP_347 TMP_345)))))))) in (let TMP_343 \def (\lambda 
(_: (le O m)).(\lambda (y: nat).(let TMP_340 \def (S m) in (let TMP_341 \def 
(minus TMP_340 O) in (let TMP_342 \def (plus TMP_341 y) in (refl_equal nat 
TMP_342)))))) in (eq_ind nat TMP_349 TMP_348 TMP_343 x H1 H0)))))]) in (let 
TMP_362 \def (refl_equal nat x) in (H0 TMP_362))))) in (let TMP_339 \def 
(\lambda (z0: nat).(\lambda (H: ((\forall (x: nat).((le z0 x) \to (\forall 
(y: nat).(eq nat (minus (plus x y) z0) (plus (minus x z0) y))))))).(\lambda 
(x: nat).(let TMP_338 \def (\lambda (n: nat).((le (S z0) n) \to (\forall (y: 
nat).(let TMP_336 \def (plus n y) in (let TMP_335 \def (S z0) in (let TMP_337 
\def (minus TMP_336 TMP_335) in (let TMP_332 \def (S z0) in (let TMP_333 \def 
(minus n TMP_332) in (let TMP_334 \def (plus TMP_333 y) in (eq nat TMP_337 
TMP_334)))))))))) in (let TMP_331 \def (\lambda (H0: (le (S z0) O)).(\lambda 
(y: nat).(let H1 \def (match H0 in le with [le_n \Rightarrow (\lambda (H1: 
(eq nat (S z0) O)).(let TMP_322 \def (S z0) in (let TMP_321 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H2 \def (eq_ind nat TMP_322 TMP_321 I O H1) in (let TMP_327 \def (plus O 
y) in (let TMP_326 \def (S z0) in (let TMP_328 \def (minus TMP_327 TMP_326) 
in (let TMP_323 \def (S z0) in (let TMP_324 \def (minus O TMP_323) in (let 
TMP_325 \def (plus TMP_324 y) in (let TMP_329 \def (eq nat TMP_328 TMP_325) 
in (False_ind TMP_329 H2)))))))))))) | (le_S m H1) \Rightarrow (\lambda (H2: 
(eq nat (S m) O)).(let TMP_312 \def (S m) in (let TMP_311 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H3 \def (eq_ind nat TMP_312 TMP_311 I O H2) in (let TMP_319 \def ((le (S 
z0) m) \to (let TMP_317 \def (plus O y) in (let TMP_316 \def (S z0) in (let 
TMP_318 \def (minus TMP_317 TMP_316) in (let TMP_313 \def (S z0) in (let 
TMP_314 \def (minus O TMP_313) in (let TMP_315 \def (plus TMP_314 y) in (eq 
nat TMP_318 TMP_315)))))))) in (let TMP_320 \def (False_ind TMP_319 H3) in 
(TMP_320 H1)))))))]) in (let TMP_330 \def (refl_equal nat O) in (H1 
TMP_330))))) in (let TMP_310 \def (\lambda (n: nat).(\lambda (_: (((le (S z0) 
n) \to (\forall (y: nat).(eq nat (minus (plus n y) (S z0)) (plus (minus n (S 
z0)) y)))))).(\lambda (H1: (le (S z0) (S n))).(\lambda (y: nat).(let TMP_309 
\def (le_S_n z0 n H1) in (H n TMP_309 y)))))) in (nat_ind TMP_338 TMP_331 
TMP_310 x))))))) in (nat_ind TMP_368 TMP_363 TMP_339 z)))).

theorem le_minus:
 \forall (x: nat).(\forall (z: nat).(\forall (y: nat).((le (plus x y) z) \to 
(le x (minus z y)))))
\def
 \lambda (x: nat).(\lambda (z: nat).(\lambda (y: nat).(\lambda (H: (le (plus 
x y) z)).(let TMP_375 \def (plus x y) in (let TMP_376 \def (minus TMP_375 y) 
in (let TMP_374 \def (\lambda (n: nat).(let TMP_373 \def (minus z y) in (le n 
TMP_373))) in (let TMP_371 \def (plus x y) in (let TMP_370 \def (le_plus_r x 
y) in (let TMP_372 \def (le_minus_minus y TMP_371 TMP_370 z H) in (let 
TMP_369 \def (minus_plus_r x y) in (eq_ind nat TMP_376 TMP_374 TMP_372 x 
TMP_369))))))))))).

theorem le_trans_plus_r:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).((le (plus x y) z) \to 
(le y z))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(\lambda (H: (le (plus 
x y) z)).(let TMP_378 \def (plus x y) in (let TMP_377 \def (le_plus_r x y) in 
(le_trans y TMP_378 z TMP_377 H)))))).

theorem lt_x_O:
 \forall (x: nat).((lt x O) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) O)).(\lambda (P: Prop).(let TMP_379 
\def (S x) in (let H_y \def (le_n_O_eq TMP_379 H) in (let TMP_381 \def 
(\lambda (ee: nat).(match ee in nat with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_380 \def (S x) in (let H0 \def (eq_ind nat O 
TMP_381 I TMP_380 H_y) in (False_ind P H0)))))))).

theorem le_gen_S:
 \forall (m: nat).(\forall (x: nat).((le (S m) x) \to (ex2 nat (\lambda (n: 
nat).(eq nat x (S n))) (\lambda (n: nat).(le m n)))))
\def
 \lambda (m: nat).(\lambda (x: nat).(\lambda (H: (le (S m) x)).(let H0 \def 
(match H in le with [le_n \Rightarrow (\lambda (H0: (eq nat (S m) x)).(let 
TMP_409 \def (S m) in (let TMP_408 \def (\lambda (n: nat).(let TMP_407 \def 
(\lambda (n0: nat).(let TMP_406 \def (S n0) in (eq nat n TMP_406))) in (let 
TMP_405 \def (\lambda (n0: nat).(le m n0)) in (ex2 nat TMP_407 TMP_405)))) in 
(let TMP_403 \def (\lambda (n: nat).(let TMP_402 \def (S m) in (let TMP_401 
\def (S n) in (eq nat TMP_402 TMP_401)))) in (let TMP_400 \def (\lambda (n: 
nat).(le m n)) in (let TMP_398 \def (S m) in (let TMP_399 \def (refl_equal 
nat TMP_398) in (let TMP_397 \def (le_n m) in (let TMP_404 \def (ex_intro2 
nat TMP_403 TMP_400 m TMP_399 TMP_397) in (eq_ind nat TMP_409 TMP_408 TMP_404 
x H0)))))))))) | (le_S m0 H0) \Rightarrow (\lambda (H1: (eq nat (S m0) 
x)).(let TMP_396 \def (S m0) in (let TMP_395 \def (\lambda (n: nat).((le (S 
m) m0) \to (let TMP_394 \def (\lambda (n0: nat).(let TMP_393 \def (S n0) in 
(eq nat n TMP_393))) in (let TMP_392 \def (\lambda (n0: nat).(le m n0)) in 
(ex2 nat TMP_394 TMP_392))))) in (let TMP_391 \def (\lambda (H2: (le (S m) 
m0)).(let TMP_390 \def (\lambda (n: nat).(let TMP_389 \def (S m0) in (let 
TMP_388 \def (S n) in (eq nat TMP_389 TMP_388)))) in (let TMP_387 \def 
(\lambda (n: nat).(le m n)) in (let TMP_385 \def (S m0) in (let TMP_386 \def 
(refl_equal nat TMP_385) in (let TMP_382 \def (S m) in (let TMP_383 \def 
(le_S TMP_382 m0 H2) in (let TMP_384 \def (le_S_n m m0 TMP_383) in (ex_intro2 
nat TMP_390 TMP_387 m0 TMP_386 TMP_384))))))))) in (eq_ind nat TMP_396 
TMP_395 TMP_391 x H1 H0)))))]) in (let TMP_410 \def (refl_equal nat x) in (H0 
TMP_410))))).

theorem lt_x_plus_x_Sy:
 \forall (x: nat).(\forall (y: nat).(lt x (plus x (S y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_427 \def (S y) in (let TMP_428 
\def (plus TMP_427 x) in (let TMP_426 \def (\lambda (n: nat).(lt x n)) in 
(let TMP_424 \def (S x) in (let TMP_422 \def (plus y x) in (let TMP_423 \def 
(S TMP_422) in (let TMP_420 \def (S x) in (let TMP_418 \def (plus y x) in 
(let TMP_419 \def (S TMP_418) in (let TMP_416 \def (plus y x) in (let TMP_415 
\def (le_plus_r y x) in (let TMP_417 \def (le_n_S x TMP_416 TMP_415) in (let 
TMP_421 \def (le_n_S TMP_420 TMP_419 TMP_417) in (let TMP_425 \def (le_S_n 
TMP_424 TMP_423 TMP_421) in (let TMP_413 \def (S y) in (let TMP_414 \def 
(plus x TMP_413) in (let TMP_411 \def (S y) in (let TMP_412 \def (plus_sym x 
TMP_411) in (eq_ind_r nat TMP_428 TMP_426 TMP_425 TMP_414 
TMP_412)))))))))))))))))))).

theorem simpl_lt_plus_r:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((lt (plus n p) (plus m 
p)) \to (lt n m))))
\def
 \lambda (p: nat).(\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (plus 
n p) (plus m p))).(let TMP_433 \def (plus n p) in (let TMP_432 \def (\lambda 
(n0: nat).(let TMP_431 \def (plus m p) in (lt n0 TMP_431))) in (let TMP_430 
\def (plus p n) in (let TMP_429 \def (plus_sym n p) in (let H0 \def (eq_ind 
nat TMP_433 TMP_432 H TMP_430 TMP_429) in (let TMP_438 \def (plus m p) in 
(let TMP_437 \def (\lambda (n0: nat).(let TMP_436 \def (plus p n) in (lt 
TMP_436 n0))) in (let TMP_435 \def (plus p m) in (let TMP_434 \def (plus_sym 
m p) in (let H1 \def (eq_ind nat TMP_438 TMP_437 H0 TMP_435 TMP_434) in 
(simpl_lt_plus_l n m p H1)))))))))))))).

theorem minus_x_Sy:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq nat (minus x y) (S 
(minus x (S y))))))
\def
 \lambda (x: nat).(let TMP_478 \def (\lambda (n: nat).(\forall (y: nat).((lt 
y n) \to (let TMP_477 \def (minus n y) in (let TMP_474 \def (S y) in (let 
TMP_475 \def (minus n TMP_474) in (let TMP_476 \def (S TMP_475) in (eq nat 
TMP_477 TMP_476)))))))) in (let TMP_473 \def (\lambda (y: nat).(\lambda (H: 
(lt y O)).(let H0 \def (match H in le with [le_n \Rightarrow (\lambda (H0: 
(eq nat (S y) O)).(let TMP_466 \def (S y) in (let TMP_465 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H1 \def (eq_ind nat TMP_466 TMP_465 I O H0) in (let TMP_470 \def (minus 
O y) in (let TMP_467 \def (S y) in (let TMP_468 \def (minus O TMP_467) in 
(let TMP_469 \def (S TMP_468) in (let TMP_471 \def (eq nat TMP_470 TMP_469) 
in (False_ind TMP_471 H1)))))))))) | (le_S m H0) \Rightarrow (\lambda (H1: 
(eq nat (S m) O)).(let TMP_458 \def (S m) in (let TMP_457 \def (\lambda (e: 
nat).(match e in nat with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H2 \def (eq_ind nat TMP_458 TMP_457 I O H1) in (let TMP_463 \def ((le (S 
y) m) \to (let TMP_462 \def (minus O y) in (let TMP_459 \def (S y) in (let 
TMP_460 \def (minus O TMP_459) in (let TMP_461 \def (S TMP_460) in (eq nat 
TMP_462 TMP_461)))))) in (let TMP_464 \def (False_ind TMP_463 H2) in (TMP_464 
H0)))))))]) in (let TMP_472 \def (refl_equal nat O) in (H0 TMP_472))))) in 
(let TMP_456 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y n) 
\to (eq nat (minus n y) (S (minus n (S y)))))))).(\lambda (y: nat).(let 
TMP_455 \def (\lambda (n0: nat).((lt n0 (S n)) \to (let TMP_453 \def (S n) in 
(let TMP_454 \def (minus TMP_453 n0) in (let TMP_450 \def (S n) in (let 
TMP_449 \def (S n0) in (let TMP_451 \def (minus TMP_450 TMP_449) in (let 
TMP_452 \def (S TMP_451) in (eq nat TMP_454 TMP_452))))))))) in (let TMP_448 
\def (\lambda (_: (lt O (S n))).(let TMP_447 \def (\lambda (n0: nat).(let 
TMP_446 \def (S n) in (let TMP_445 \def (S n0) in (eq nat TMP_446 TMP_445)))) 
in (let TMP_443 \def (S n) in (let TMP_444 \def (refl_equal nat TMP_443) in 
(let TMP_442 \def (minus n O) in (let TMP_441 \def (minus_n_O n) in (eq_ind 
nat n TMP_447 TMP_444 TMP_442 TMP_441))))))) in (let TMP_440 \def (\lambda 
(n0: nat).(\lambda (_: (((lt n0 (S n)) \to (eq nat (minus (S n) n0) (S (minus 
(S n) (S n0))))))).(\lambda (H1: (lt (S n0) (S n))).(let TMP_439 \def (S n0) 
in (let H2 \def (le_S_n TMP_439 n H1) in (H n0 H2)))))) in (nat_ind TMP_455 
TMP_448 TMP_440 y))))))) in (nat_ind TMP_478 TMP_473 TMP_456 x)))).

theorem lt_plus_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus x (minus 
y (S x)))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_479 \def 
(S x) in (le_plus_minus TMP_479 y H)))).

theorem lt_plus_minus_r:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus (minus y 
(S x)) x)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_489 \def 
(S x) in (let TMP_490 \def (minus y TMP_489) in (let TMP_491 \def (plus x 
TMP_490) in (let TMP_488 \def (\lambda (n: nat).(let TMP_487 \def (S n) in 
(eq nat y TMP_487))) in (let TMP_486 \def (lt_plus_minus x y H) in (let 
TMP_483 \def (S x) in (let TMP_484 \def (minus y TMP_483) in (let TMP_485 
\def (plus TMP_484 x) in (let TMP_480 \def (S x) in (let TMP_481 \def (minus 
y TMP_480) in (let TMP_482 \def (plus_sym TMP_481 x) in (eq_ind_r nat TMP_491 
TMP_488 TMP_486 TMP_485 TMP_482)))))))))))))).

theorem minus_x_SO:
 \forall (x: nat).((lt O x) \to (eq nat x (S (minus x (S O)))))
\def
 \lambda (x: nat).(\lambda (H: (lt O x)).(let TMP_502 \def (minus x O) in 
(let TMP_501 \def (\lambda (n: nat).(eq nat x n)) in (let TMP_499 \def 
(\lambda (n: nat).(eq nat x n)) in (let TMP_498 \def (refl_equal nat x) in 
(let TMP_497 \def (minus x O) in (let TMP_496 \def (minus_n_O x) in (let 
TMP_500 \def (eq_ind nat x TMP_499 TMP_498 TMP_497 TMP_496) in (let TMP_493 
\def (S O) in (let TMP_494 \def (minus x TMP_493) in (let TMP_495 \def (S 
TMP_494) in (let TMP_492 \def (minus_x_Sy x O H) in (eq_ind nat TMP_502 
TMP_501 TMP_500 TMP_495 TMP_492))))))))))))).

theorem le_x_pred_y:
 \forall (y: nat).(\forall (x: nat).((lt x y) \to (le x (pred y))))
\def
 \lambda (y: nat).(let TMP_514 \def (\lambda (n: nat).(\forall (x: nat).((lt 
x n) \to (let TMP_513 \def (pred n) in (le x TMP_513))))) in (let TMP_512 
\def (\lambda (x: nat).(\lambda (H: (lt x O)).(let H0 \def (match H in le 
with [le_n \Rightarrow (\lambda (H0: (eq nat (S x) O)).(let TMP_509 \def (S 
x) in (let TMP_508 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow 
False | (S _) \Rightarrow True])) in (let H1 \def (eq_ind nat TMP_509 TMP_508 
I O H0) in (let TMP_510 \def (le x O) in (False_ind TMP_510 H1)))))) | (le_S 
m H0) \Rightarrow (\lambda (H1: (eq nat (S m) O)).(let TMP_505 \def (S m) in 
(let TMP_504 \def (\lambda (e: nat).(match e in nat with [O \Rightarrow False 
| (S _) \Rightarrow True])) in (let H2 \def (eq_ind nat TMP_505 TMP_504 I O 
H1) in (let TMP_506 \def ((le (S x) m) \to (le x O)) in (let TMP_507 \def 
(False_ind TMP_506 H2) in (TMP_507 H0)))))))]) in (let TMP_511 \def 
(refl_equal nat O) in (H0 TMP_511))))) in (let TMP_503 \def (\lambda (n: 
nat).(\lambda (_: ((\forall (x: nat).((lt x n) \to (le x (pred 
n)))))).(\lambda (x: nat).(\lambda (H0: (lt x (S n))).(le_S_n x n H0))))) in 
(nat_ind TMP_514 TMP_512 TMP_503 y)))).

theorem lt_le_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (le x (minus y (S O)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_523 \def 
(S O) in (let TMP_520 \def (S O) in (let TMP_521 \def (plus TMP_520 x) in 
(let TMP_519 \def (\lambda (n: nat).(le n y)) in (let TMP_517 \def (S O) in 
(let TMP_518 \def (plus x TMP_517) in (let TMP_515 \def (S O) in (let TMP_516 
\def (plus_sym x TMP_515) in (let TMP_522 \def (eq_ind_r nat TMP_521 TMP_519 
H TMP_518 TMP_516) in (le_minus x y TMP_523 TMP_522)))))))))))).

theorem lt_le_e:
 \forall (n: nat).(\forall (d: nat).(\forall (P: Prop).((((lt n d) \to P)) 
\to ((((le d n) \to P)) \to P))))
\def
 \lambda (n: nat).(\lambda (d: nat).(\lambda (P: Prop).(\lambda (H: (((lt n 
d) \to P))).(\lambda (H0: (((le d n) \to P))).(let H1 \def (le_or_lt d n) in 
(let TMP_525 \def (le d n) in (let TMP_524 \def (lt n d) in (or_ind TMP_525 
TMP_524 P H0 H H1)))))))).

theorem lt_eq_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((le x y) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (le x 
y)).(let TMP_528 \def (lt x y) in (let TMP_527 \def (eq nat x y) in (let 
TMP_526 \def (le_lt_or_eq x y H1) in (or_ind TMP_528 TMP_527 P H H0 
TMP_526))))))))).

theorem lt_eq_gt_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((((lt y x) \to P)) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (((lt y x) 
\to P))).(let TMP_531 \def (\lambda (H2: (le y x)).(let TMP_530 \def (\lambda 
(H3: (eq nat y x)).(let TMP_529 \def (sym_eq nat y x H3) in (H0 TMP_529))) in 
(lt_eq_e y x P H1 TMP_530 H2))) in (lt_le_e x y P H TMP_531))))))).

theorem lt_gen_xS:
 \forall (x: nat).(\forall (n: nat).((lt x (S n)) \to (or (eq nat x O) (ex2 
nat (\lambda (m: nat).(eq nat x (S m))) (\lambda (m: nat).(lt m n))))))
\def
 \lambda (x: nat).(let TMP_561 \def (\lambda (n: nat).(\forall (n0: nat).((lt 
n (S n0)) \to (let TMP_560 \def (eq nat n O) in (let TMP_558 \def (\lambda 
(m: nat).(let TMP_557 \def (S m) in (eq nat n TMP_557))) in (let TMP_556 \def 
(\lambda (m: nat).(lt m n0)) in (let TMP_559 \def (ex2 nat TMP_558 TMP_556) 
in (or TMP_560 TMP_559)))))))) in (let TMP_555 \def (\lambda (n: 
nat).(\lambda (_: (lt O (S n))).(let TMP_554 \def (eq nat O O) in (let 
TMP_552 \def (\lambda (m: nat).(let TMP_551 \def (S m) in (eq nat O 
TMP_551))) in (let TMP_550 \def (\lambda (m: nat).(lt m n)) in (let TMP_553 
\def (ex2 nat TMP_552 TMP_550) in (let TMP_549 \def (refl_equal nat O) in 
(or_introl TMP_554 TMP_553 TMP_549)))))))) in (let TMP_548 \def (\lambda (n: 
nat).(\lambda (_: ((\forall (n0: nat).((lt n (S n0)) \to (or (eq nat n O) 
(ex2 nat (\lambda (m: nat).(eq nat n (S m))) (\lambda (m: nat).(lt m 
n0)))))))).(\lambda (n0: nat).(\lambda (H0: (lt (S n) (S n0))).(let TMP_546 
\def (S n) in (let TMP_547 \def (eq nat TMP_546 O) in (let TMP_544 \def 
(\lambda (m: nat).(let TMP_543 \def (S n) in (let TMP_542 \def (S m) in (eq 
nat TMP_543 TMP_542)))) in (let TMP_541 \def (\lambda (m: nat).(lt m n0)) in 
(let TMP_545 \def (ex2 nat TMP_544 TMP_541) in (let TMP_539 \def (\lambda (m: 
nat).(let TMP_538 \def (S n) in (let TMP_537 \def (S m) in (eq nat TMP_538 
TMP_537)))) in (let TMP_536 \def (\lambda (m: nat).(lt m n0)) in (let TMP_534 
\def (S n) in (let TMP_535 \def (refl_equal nat TMP_534) in (let TMP_532 \def 
(S n) in (let TMP_533 \def (le_S_n TMP_532 n0 H0) in (let TMP_540 \def 
(ex_intro2 nat TMP_539 TMP_536 n TMP_535 TMP_533) in (or_intror TMP_547 
TMP_545 TMP_540))))))))))))))))) in (nat_ind TMP_561 TMP_555 TMP_548 x)))).

theorem le_lt_false:
 \forall (x: nat).(\forall (y: nat).((le x y) \to ((lt y x) \to (\forall (P: 
Prop).P))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (H0: (lt 
y x)).(\lambda (P: Prop).(let TMP_562 \def (le_not_lt x y H H0) in (False_ind 
P TMP_562)))))).

theorem lt_neq:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (not (eq nat x y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(\lambda (H0: (eq 
nat x y)).(let TMP_563 \def (\lambda (n: nat).(lt n y)) in (let H1 \def 
(eq_ind nat x TMP_563 H y H0) in (lt_n_n y H1)))))).

theorem arith0:
 \forall (h2: nat).(\forall (d2: nat).(\forall (n: nat).((le (plus d2 h2) n) 
\to (\forall (h1: nat).(le (plus d2 h1) (minus (plus n h1) h2))))))
\def
 \lambda (h2: nat).(\lambda (d2: nat).(\lambda (n: nat).(\lambda (H: (le 
(plus d2 h2) n)).(\lambda (h1: nat).(let TMP_602 \def (plus d2 h1) in (let 
TMP_603 \def (plus h2 TMP_602) in (let TMP_604 \def (minus TMP_603 h2) in 
(let TMP_601 \def (\lambda (n0: nat).(let TMP_599 \def (plus n h1) in (let 
TMP_600 \def (minus TMP_599 h2) in (le n0 TMP_600)))) in (let TMP_596 \def 
(plus d2 h1) in (let TMP_597 \def (plus h2 TMP_596) in (let TMP_594 \def 
(plus d2 h1) in (let TMP_595 \def (le_plus_l h2 TMP_594) in (let TMP_593 \def 
(plus n h1) in (let TMP_590 \def (plus h2 d2) in (let TMP_591 \def (plus 
TMP_590 h1) in (let TMP_589 \def (\lambda (n0: nat).(let TMP_588 \def (plus n 
h1) in (le n0 TMP_588))) in (let TMP_586 \def (plus d2 h2) in (let TMP_585 
\def (\lambda (n0: nat).(let TMP_584 \def (plus n0 h1) in (let TMP_583 \def 
(plus n h1) in (le TMP_584 TMP_583)))) in (let TMP_580 \def (plus d2 h2) in 
(let TMP_581 \def (plus TMP_580 h1) in (let TMP_579 \def (plus n h1) in (let 
TMP_576 \def (plus d2 h2) in (let TMP_577 \def (plus TMP_576 h1) in (let 
TMP_575 \def (plus n h1) in (let TMP_573 \def (plus d2 h2) in (let TMP_572 
\def (le_n h1) in (let TMP_574 \def (le_plus_plus TMP_573 n h1 h1 H TMP_572) 
in (let TMP_578 \def (le_n_S TMP_577 TMP_575 TMP_574) in (let TMP_582 \def 
(le_S_n TMP_581 TMP_579 TMP_578) in (let TMP_571 \def (plus h2 d2) in (let 
TMP_570 \def (plus_sym h2 d2) in (let TMP_587 \def (eq_ind_r nat TMP_586 
TMP_585 TMP_582 TMP_571 TMP_570) in (let TMP_568 \def (plus d2 h1) in (let 
TMP_569 \def (plus h2 TMP_568) in (let TMP_567 \def (plus_assoc_l h2 d2 h1) 
in (let TMP_592 \def (eq_ind_r nat TMP_591 TMP_589 TMP_587 TMP_569 TMP_567) 
in (let TMP_598 \def (le_minus_minus h2 TMP_597 TMP_595 TMP_593 TMP_592) in 
(let TMP_566 \def (plus d2 h1) in (let TMP_564 \def (plus d2 h1) in (let 
TMP_565 \def (minus_plus h2 TMP_564) in (eq_ind nat TMP_604 TMP_601 TMP_598 
TMP_566 TMP_565))))))))))))))))))))))))))))))))))))))))).

theorem O_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq nat (minus x y) O)))
\def
 \lambda (x: nat).(let TMP_624 \def (\lambda (n: nat).(\forall (y: nat).((le 
n y) \to (let TMP_623 \def (minus n y) in (eq nat TMP_623 O))))) in (let 
TMP_622 \def (\lambda (y: nat).(\lambda (_: (le O y)).(refl_equal nat O))) in 
(let TMP_621 \def (\lambda (x0: nat).(\lambda (H: ((\forall (y: nat).((le x0 
y) \to (eq nat (minus x0 y) O))))).(\lambda (y: nat).(let TMP_620 \def 
(\lambda (n: nat).((le (S x0) n) \to (let TMP_619 \def (match n with [O 
\Rightarrow (S x0) | (S l) \Rightarrow (minus x0 l)]) in (eq nat TMP_619 
O)))) in (let TMP_618 \def (\lambda (H0: (le (S x0) O)).(let TMP_617 \def 
(\lambda (n: nat).(let TMP_616 \def (S n) in (eq nat O TMP_616))) in (let 
TMP_615 \def (\lambda (n: nat).(le x0 n)) in (let TMP_613 \def (S x0) in (let 
TMP_614 \def (eq nat TMP_613 O) in (let TMP_612 \def (\lambda (x1: 
nat).(\lambda (H1: (eq nat O (S x1))).(\lambda (_: (le x0 x1)).(let TMP_609 
\def (\lambda (ee: nat).(match ee in nat with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_608 \def (S x1) in (let H3 \def (eq_ind nat 
O TMP_609 I TMP_608 H1) in (let TMP_610 \def (S x0) in (let TMP_611 \def (eq 
nat TMP_610 O) in (False_ind TMP_611 H3))))))))) in (let TMP_607 \def 
(le_gen_S x0 O H0) in (ex2_ind nat TMP_617 TMP_615 TMP_614 TMP_612 
TMP_607)))))))) in (let TMP_606 \def (\lambda (n: nat).(\lambda (_: (((le (S 
x0) n) \to (eq nat (match n with [O \Rightarrow (S x0) | (S l) \Rightarrow 
(minus x0 l)]) O)))).(\lambda (H1: (le (S x0) (S n))).(let TMP_605 \def 
(le_S_n x0 n H1) in (H n TMP_605))))) in (nat_ind TMP_620 TMP_618 TMP_606 
y))))))) in (nat_ind TMP_624 TMP_622 TMP_621 x)))).

theorem minus_minus:
 \forall (z: nat).(\forall (x: nat).(\forall (y: nat).((le z x) \to ((le z y) 
\to ((eq nat (minus x z) (minus y z)) \to (eq nat x y))))))
\def
 \lambda (z: nat).(let TMP_664 \def (\lambda (n: nat).(\forall (x: 
nat).(\forall (y: nat).((le n x) \to ((le n y) \to ((eq nat (minus x n) 
(minus y n)) \to (eq nat x y))))))) in (let TMP_663 \def (\lambda (x: 
nat).(\lambda (y: nat).(\lambda (_: (le O x)).(\lambda (_: (le O y)).(\lambda 
(H1: (eq nat (minus x O) (minus y O))).(let TMP_659 \def (minus x O) in (let 
TMP_658 \def (\lambda (n: nat).(let TMP_657 \def (minus y O) in (eq nat n 
TMP_657))) in (let TMP_656 \def (minus_n_O x) in (let H2 \def (eq_ind_r nat 
TMP_659 TMP_658 H1 x TMP_656) in (let TMP_662 \def (minus y O) in (let 
TMP_661 \def (\lambda (n: nat).(eq nat x n)) in (let TMP_660 \def (minus_n_O 
y) in (let H3 \def (eq_ind_r nat TMP_662 TMP_661 H2 y TMP_660) in 
H3))))))))))))) in (let TMP_655 \def (\lambda (z0: nat).(\lambda (IH: 
((\forall (x: nat).(\forall (y: nat).((le z0 x) \to ((le z0 y) \to ((eq nat 
(minus x z0) (minus y z0)) \to (eq nat x y)))))))).(\lambda (x: nat).(let 
TMP_654 \def (\lambda (n: nat).(\forall (y: nat).((le (S z0) n) \to ((le (S 
z0) y) \to ((eq nat (minus n (S z0)) (minus y (S z0))) \to (eq nat n y)))))) 
in (let TMP_653 \def (\lambda (y: nat).(\lambda (H: (le (S z0) O)).(\lambda 
(_: (le (S z0) y)).(\lambda (_: (eq nat (minus O (S z0)) (minus y (S 
z0)))).(let TMP_652 \def (\lambda (n: nat).(let TMP_651 \def (S n) in (eq nat 
O TMP_651))) in (let TMP_650 \def (\lambda (n: nat).(le z0 n)) in (let 
TMP_649 \def (eq nat O y) in (let TMP_648 \def (\lambda (x0: nat).(\lambda 
(H2: (eq nat O (S x0))).(\lambda (_: (le z0 x0)).(let TMP_646 \def (\lambda 
(ee: nat).(match ee in nat with [O \Rightarrow True | (S _) \Rightarrow 
False])) in (let TMP_645 \def (S x0) in (let H4 \def (eq_ind nat O TMP_646 I 
TMP_645 H2) in (let TMP_647 \def (eq nat O y) in (False_ind TMP_647 
H4)))))))) in (let TMP_644 \def (le_gen_S z0 O H) in (ex2_ind nat TMP_652 
TMP_650 TMP_649 TMP_648 TMP_644)))))))))) in (let TMP_643 \def (\lambda (x0: 
nat).(\lambda (_: ((\forall (y: nat).((le (S z0) x0) \to ((le (S z0) y) \to 
((eq nat (minus x0 (S z0)) (minus y (S z0))) \to (eq nat x0 y))))))).(\lambda 
(y: nat).(let TMP_642 \def (\lambda (n: nat).((le (S z0) (S x0)) \to ((le (S 
z0) n) \to ((eq nat (minus (S x0) (S z0)) (minus n (S z0))) \to (let TMP_641 
\def (S x0) in (eq nat TMP_641 n)))))) in (let TMP_640 \def (\lambda (H: (le 
(S z0) (S x0))).(\lambda (H0: (le (S z0) O)).(\lambda (_: (eq nat (minus (S 
x0) (S z0)) (minus O (S z0)))).(let H_y \def (le_S_n z0 x0 H) in (let TMP_639 
\def (\lambda (n: nat).(let TMP_638 \def (S n) in (eq nat O TMP_638))) in 
(let TMP_637 \def (\lambda (n: nat).(le z0 n)) in (let TMP_635 \def (S x0) in 
(let TMP_636 \def (eq nat TMP_635 O) in (let TMP_634 \def (\lambda (x1: 
nat).(\lambda (H2: (eq nat O (S x1))).(\lambda (_: (le z0 x1)).(let TMP_631 
\def (\lambda (ee: nat).(match ee in nat with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_630 \def (S x1) in (let H4 \def (eq_ind nat 
O TMP_631 I TMP_630 H2) in (let TMP_632 \def (S x0) in (let TMP_633 \def (eq 
nat TMP_632 O) in (False_ind TMP_633 H4))))))))) in (let TMP_629 \def 
(le_gen_S z0 O H0) in (ex2_ind nat TMP_639 TMP_637 TMP_636 TMP_634 
TMP_629))))))))))) in (let TMP_628 \def (\lambda (y0: nat).(\lambda (_: (((le 
(S z0) (S x0)) \to ((le (S z0) y0) \to ((eq nat (minus (S x0) (S z0)) (minus 
y0 (S z0))) \to (eq nat (S x0) y0)))))).(\lambda (H: (le (S z0) (S 
x0))).(\lambda (H0: (le (S z0) (S y0))).(\lambda (H1: (eq nat (minus (S x0) 
(S z0)) (minus (S y0) (S z0)))).(let TMP_626 \def (le_S_n z0 x0 H) in (let 
TMP_625 \def (le_S_n z0 y0 H0) in (let TMP_627 \def (IH x0 y0 TMP_626 TMP_625 
H1) in (f_equal nat nat S x0 y0 TMP_627))))))))) in (nat_ind TMP_642 TMP_640 
TMP_628 y))))))) in (nat_ind TMP_654 TMP_653 TMP_643 x))))))) in (nat_ind 
TMP_664 TMP_663 TMP_655 z)))).

theorem plus_plus:
 \forall (z: nat).(\forall (x1: nat).(\forall (x2: nat).(\forall (y1: 
nat).(\forall (y2: nat).((le x1 z) \to ((le x2 z) \to ((eq nat (plus (minus z 
x1) y1) (plus (minus z x2) y2)) \to (eq nat (plus x1 y2) (plus x2 y1)))))))))
\def
 \lambda (z: nat).(let TMP_755 \def (\lambda (n: nat).(\forall (x1: 
nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 n) \to 
((le x2 n) \to ((eq nat (plus (minus n x1) y1) (plus (minus n x2) y2)) \to 
(let TMP_754 \def (plus x1 y2) in (let TMP_753 \def (plus x2 y1) in (eq nat 
TMP_754 TMP_753))))))))))) in (let TMP_752 \def (\lambda (x1: nat).(\lambda 
(x2: nat).(\lambda (y1: nat).(\lambda (y2: nat).(\lambda (H: (le x1 
O)).(\lambda (H0: (le x2 O)).(\lambda (H1: (eq nat y1 y2)).(let TMP_751 \def 
(\lambda (n: nat).(let TMP_750 \def (plus x1 n) in (let TMP_749 \def (plus x2 
y1) in (eq nat TMP_750 TMP_749)))) in (let H_y \def (le_n_O_eq x2 H0) in (let 
TMP_747 \def (\lambda (n: nat).(let TMP_746 \def (plus x1 y1) in (let TMP_745 
\def (plus n y1) in (eq nat TMP_746 TMP_745)))) in (let H_y0 \def (le_n_O_eq 
x1 H) in (let TMP_743 \def (\lambda (n: nat).(let TMP_742 \def (plus n y1) in 
(let TMP_741 \def (plus O y1) in (eq nat TMP_742 TMP_741)))) in (let TMP_739 
\def (plus O y1) in (let TMP_740 \def (refl_equal nat TMP_739) in (let 
TMP_744 \def (eq_ind nat O TMP_743 TMP_740 x1 H_y0) in (let TMP_748 \def 
(eq_ind nat O TMP_747 TMP_744 x2 H_y) in (eq_ind nat y1 TMP_751 TMP_748 y2 
H1))))))))))))))))) in (let TMP_738 \def (\lambda (z0: nat).(\lambda (IH: 
((\forall (x1: nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: 
nat).((le x1 z0) \to ((le x2 z0) \to ((eq nat (plus (minus z0 x1) y1) (plus 
(minus z0 x2) y2)) \to (eq nat (plus x1 y2) (plus x2 y1))))))))))).(\lambda 
(x1: nat).(let TMP_737 \def (\lambda (n: nat).(\forall (x2: nat).(\forall 
(y1: nat).(\forall (y2: nat).((le n (S z0)) \to ((le x2 (S z0)) \to ((eq nat 
(plus (minus (S z0) n) y1) (plus (minus (S z0) x2) y2)) \to (let TMP_736 \def 
(plus n y2) in (let TMP_735 \def (plus x2 y1) in (eq nat TMP_736 
TMP_735)))))))))) in (let TMP_734 \def (\lambda (x2: nat).(let TMP_733 \def 
(\lambda (n: nat).(\forall (y1: nat).(\forall (y2: nat).((le O (S z0)) \to 
((le n (S z0)) \to ((eq nat (plus (minus (S z0) O) y1) (plus (minus (S z0) n) 
y2)) \to (let TMP_732 \def (plus O y2) in (let TMP_731 \def (plus n y1) in 
(eq nat TMP_732 TMP_731))))))))) in (let TMP_730 \def (\lambda (y1: 
nat).(\lambda (y2: nat).(\lambda (_: (le O (S z0))).(\lambda (_: (le O (S 
z0))).(\lambda (H1: (eq nat (S (plus z0 y1)) (S (plus z0 y2)))).(let H_y \def 
(IH O O) in (let TMP_724 \def (minus z0 O) in (let TMP_723 \def (\lambda (n: 
nat).(\forall (y3: nat).(\forall (y4: nat).((le O z0) \to ((le O z0) \to ((eq 
nat (plus n y3) (plus n y4)) \to (eq nat y4 y3))))))) in (let TMP_722 \def 
(minus_n_O z0) in (let H2 \def (eq_ind_r nat TMP_724 TMP_723 H_y z0 TMP_722) 
in (let TMP_729 \def (le_O_n z0) in (let TMP_728 \def (le_O_n z0) in (let 
TMP_726 \def (plus z0 y1) in (let TMP_725 \def (plus z0 y2) in (let TMP_727 
\def (eq_add_S TMP_726 TMP_725 H1) in (H2 y1 y2 TMP_729 TMP_728 
TMP_727)))))))))))))))) in (let TMP_721 \def (\lambda (x3: nat).(\lambda (_: 
((\forall (y1: nat).(\forall (y2: nat).((le O (S z0)) \to ((le x3 (S z0)) \to 
((eq nat (S (plus z0 y1)) (plus (match x3 with [O \Rightarrow (S z0) | (S l) 
\Rightarrow (minus z0 l)]) y2)) \to (eq nat y2 (plus x3 y1))))))))).(\lambda 
(y1: nat).(\lambda (y2: nat).(\lambda (_: (le O (S z0))).(\lambda (H0: (le (S 
x3) (S z0))).(\lambda (H1: (eq nat (S (plus z0 y1)) (plus (minus z0 x3) 
y2))).(let TMP_699 \def (S y1) in (let H_y \def (IH O x3 TMP_699) in (let 
TMP_704 \def (minus z0 O) in (let TMP_703 \def (\lambda (n: nat).(\forall 
(y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat (plus n (S y1)) (plus 
(minus z0 x3) y3)) \to (let TMP_701 \def (S y1) in (let TMP_702 \def (plus x3 
TMP_701) in (eq nat y3 TMP_702)))))))) in (let TMP_700 \def (minus_n_O z0) in 
(let H2 \def (eq_ind_r nat TMP_704 TMP_703 H_y z0 TMP_700) in (let TMP_711 
\def (S y1) in (let TMP_712 \def (plus z0 TMP_711) in (let TMP_710 \def 
(\lambda (n: nat).(\forall (y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat 
n (plus (minus z0 x3) y3)) \to (let TMP_708 \def (S y1) in (let TMP_709 \def 
(plus x3 TMP_708) in (eq nat y3 TMP_709)))))))) in (let TMP_706 \def (plus z0 
y1) in (let TMP_707 \def (S TMP_706) in (let TMP_705 \def (plus_n_Sm z0 y1) 
in (let H3 \def (eq_ind_r nat TMP_712 TMP_710 H2 TMP_707 TMP_705) in (let 
TMP_717 \def (S y1) in (let TMP_718 \def (plus x3 TMP_717) in (let TMP_716 
\def (\lambda (n: nat).(\forall (y3: nat).((le O z0) \to ((le x3 z0) \to ((eq 
nat (S (plus z0 y1)) (plus (minus z0 x3) y3)) \to (eq nat y3 n)))))) in (let 
TMP_714 \def (plus x3 y1) in (let TMP_715 \def (S TMP_714) in (let TMP_713 
\def (plus_n_Sm x3 y1) in (let H4 \def (eq_ind_r nat TMP_718 TMP_716 H3 
TMP_715 TMP_713) in (let TMP_720 \def (le_O_n z0) in (let TMP_719 \def 
(le_S_n x3 z0 H0) in (H4 y2 TMP_720 TMP_719 H1)))))))))))))))))))))))))))))) 
in (nat_ind TMP_733 TMP_730 TMP_721 x2))))) in (let TMP_698 \def (\lambda 
(x2: nat).(\lambda (_: ((\forall (x3: nat).(\forall (y1: nat).(\forall (y2: 
nat).((le x2 (S z0)) \to ((le x3 (S z0)) \to ((eq nat (plus (minus (S z0) x2) 
y1) (plus (minus (S z0) x3) y2)) \to (eq nat (plus x2 y2) (plus x3 
y1)))))))))).(\lambda (x3: nat).(let TMP_697 \def (\lambda (n: nat).(\forall 
(y1: nat).(\forall (y2: nat).((le (S x2) (S z0)) \to ((le n (S z0)) \to ((eq 
nat (plus (minus (S z0) (S x2)) y1) (plus (minus (S z0) n) y2)) \to (let 
TMP_695 \def (S x2) in (let TMP_696 \def (plus TMP_695 y2) in (let TMP_694 
\def (plus n y1) in (eq nat TMP_696 TMP_694)))))))))) in (let TMP_693 \def 
(\lambda (y1: nat).(\lambda (y2: nat).(\lambda (H: (le (S x2) (S 
z0))).(\lambda (_: (le O (S z0))).(\lambda (H1: (eq nat (plus (minus z0 x2) 
y1) (S (plus z0 y2)))).(let TMP_671 \def (S y2) in (let H_y \def (IH x2 O y1 
TMP_671) in (let TMP_676 \def (minus z0 O) in (let TMP_675 \def (\lambda (n: 
nat).((le x2 z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) (plus n 
(S y2))) \to (let TMP_673 \def (S y2) in (let TMP_674 \def (plus x2 TMP_673) 
in (eq nat TMP_674 y1))))))) in (let TMP_672 \def (minus_n_O z0) in (let H2 
\def (eq_ind_r nat TMP_676 TMP_675 H_y z0 TMP_672) in (let TMP_683 \def (S 
y2) in (let TMP_684 \def (plus z0 TMP_683) in (let TMP_682 \def (\lambda (n: 
nat).((le x2 z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) n) \to 
(let TMP_680 \def (S y2) in (let TMP_681 \def (plus x2 TMP_680) in (eq nat 
TMP_681 y1))))))) in (let TMP_678 \def (plus z0 y2) in (let TMP_679 \def (S 
TMP_678) in (let TMP_677 \def (plus_n_Sm z0 y2) in (let H3 \def (eq_ind_r nat 
TMP_684 TMP_682 H2 TMP_679 TMP_677) in (let TMP_689 \def (S y2) in (let 
TMP_690 \def (plus x2 TMP_689) in (let TMP_688 \def (\lambda (n: nat).((le x2 
z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) (S (plus z0 y2))) \to 
(eq nat n y1))))) in (let TMP_686 \def (plus x2 y2) in (let TMP_687 \def (S 
TMP_686) in (let TMP_685 \def (plus_n_Sm x2 y2) in (let H4 \def (eq_ind_r nat 
TMP_690 TMP_688 H3 TMP_687 TMP_685) in (let TMP_692 \def (le_S_n x2 z0 H) in 
(let TMP_691 \def (le_O_n z0) in (H4 TMP_692 TMP_691 
H1)))))))))))))))))))))))))))) in (let TMP_670 \def (\lambda (x4: 
nat).(\lambda (_: ((\forall (y1: nat).(\forall (y2: nat).((le (S x2) (S z0)) 
\to ((le x4 (S z0)) \to ((eq nat (plus (minus z0 x2) y1) (plus (match x4 with 
[O \Rightarrow (S z0) | (S l) \Rightarrow (minus z0 l)]) y2)) \to (eq nat (S 
(plus x2 y2)) (plus x4 y1))))))))).(\lambda (y1: nat).(\lambda (y2: 
nat).(\lambda (H: (le (S x2) (S z0))).(\lambda (H0: (le (S x4) (S 
z0))).(\lambda (H1: (eq nat (plus (minus z0 x2) y1) (plus (minus z0 x4) 
y2))).(let TMP_669 \def (plus x2 y2) in (let TMP_668 \def (plus x4 y1) in 
(let TMP_666 \def (le_S_n x2 z0 H) in (let TMP_665 \def (le_S_n x4 z0 H0) in 
(let TMP_667 \def (IH x2 x4 y1 y2 TMP_666 TMP_665 H1) in (f_equal nat nat S 
TMP_669 TMP_668 TMP_667))))))))))))) in (nat_ind TMP_697 TMP_693 TMP_670 
x3))))))) in (nat_ind TMP_737 TMP_734 TMP_698 x1))))))) in (nat_ind TMP_755 
TMP_752 TMP_738 z)))).

theorem le_S_minus:
 \forall (d: nat).(\forall (h: nat).(\forall (n: nat).((le (plus d h) n) \to 
(le d (S (minus n h))))))
\def
 \lambda (d: nat).(\lambda (h: nat).(\lambda (n: nat).(\lambda (H: (le (plus 
d h) n)).(let TMP_757 \def (plus d h) in (let TMP_756 \def (le_plus_l d h) in 
(let H0 \def (le_trans d TMP_757 n TMP_756 H) in (let TMP_764 \def (\lambda 
(n0: nat).(le d n0)) in (let TMP_762 \def (minus n h) in (let TMP_763 \def 
(plus TMP_762 h) in (let TMP_759 \def (plus d h) in (let TMP_758 \def 
(le_plus_r d h) in (let TMP_760 \def (le_trans h TMP_759 n TMP_758 H) in (let 
TMP_761 \def (le_plus_minus_sym h n TMP_760) in (let H1 \def (eq_ind nat n 
TMP_764 H0 TMP_763 TMP_761) in (let TMP_766 \def (minus n h) in (let TMP_765 
\def (le_minus d n h H) in (le_S d TMP_766 TMP_765))))))))))))))))).

theorem lt_x_pred_y:
 \forall (x: nat).(\forall (y: nat).((lt x (pred y)) \to (lt (S x) y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_772 \def (\lambda (n: nat).((lt 
x (pred n)) \to (let TMP_771 \def (S x) in (lt TMP_771 n)))) in (let TMP_770 
\def (\lambda (H: (lt x O)).(let TMP_768 \def (S x) in (let TMP_769 \def (lt 
TMP_768 O) in (lt_x_O x H TMP_769)))) in (let TMP_767 \def (\lambda (n: 
nat).(\lambda (_: (((lt x (pred n)) \to (lt (S x) n)))).(\lambda (H0: (lt x 
n)).(lt_n_S x n H0)))) in (nat_ind TMP_772 TMP_770 TMP_767 y))))).

