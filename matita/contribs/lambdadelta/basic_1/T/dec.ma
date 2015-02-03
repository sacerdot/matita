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

include "basic_1/T/fwd.ma".

theorem terms_props__bind_dec:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) ((eq B b1 b2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (b1: B).(let TMP_61 \def (\lambda (b: B).(\forall (b2: B).(let 
TMP_60 \def (eq B b b2) in (let TMP_59 \def ((eq B b b2) \to (\forall (P: 
Prop).P)) in (or TMP_60 TMP_59))))) in (let TMP_58 \def (\lambda (b2: B).(let 
TMP_57 \def (\lambda (b: B).(let TMP_56 \def (eq B Abbr b) in (let TMP_55 
\def ((eq B Abbr b) \to (\forall (P: Prop).P)) in (or TMP_56 TMP_55)))) in 
(let TMP_53 \def (eq B Abbr Abbr) in (let TMP_52 \def ((eq B Abbr Abbr) \to 
(\forall (P: Prop).P)) in (let TMP_51 \def (refl_equal B Abbr) in (let TMP_54 
\def (or_introl TMP_53 TMP_52 TMP_51) in (let TMP_49 \def (eq B Abbr Abst) in 
(let TMP_48 \def ((eq B Abbr Abst) \to (\forall (P: Prop).P)) in (let TMP_47 
\def (\lambda (H: (eq B Abbr Abst)).(\lambda (P: Prop).(let TMP_46 \def 
(\lambda (ee: B).(match ee in B with [Abbr \Rightarrow True | Abst 
\Rightarrow False | Void \Rightarrow False])) in (let H0 \def (eq_ind B Abbr 
TMP_46 I Abst H) in (False_ind P H0))))) in (let TMP_50 \def (or_intror 
TMP_49 TMP_48 TMP_47) in (let TMP_44 \def (eq B Abbr Void) in (let TMP_43 
\def ((eq B Abbr Void) \to (\forall (P: Prop).P)) in (let TMP_42 \def 
(\lambda (H: (eq B Abbr Void)).(\lambda (P: Prop).(let TMP_41 \def (\lambda 
(ee: B).(match ee in B with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False])) in (let H0 \def (eq_ind B Abbr TMP_41 I Void H) in 
(False_ind P H0))))) in (let TMP_45 \def (or_intror TMP_44 TMP_43 TMP_42) in 
(B_ind TMP_57 TMP_54 TMP_50 TMP_45 b2))))))))))))))) in (let TMP_40 \def 
(\lambda (b2: B).(let TMP_39 \def (\lambda (b: B).(let TMP_38 \def (eq B Abst 
b) in (let TMP_37 \def ((eq B Abst b) \to (\forall (P: Prop).P)) in (or 
TMP_38 TMP_37)))) in (let TMP_35 \def (eq B Abst Abbr) in (let TMP_34 \def 
((eq B Abst Abbr) \to (\forall (P: Prop).P)) in (let TMP_33 \def (\lambda (H: 
(eq B Abst Abbr)).(\lambda (P: Prop).(let TMP_32 \def (\lambda (ee: B).(match 
ee in B with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False])) in (let H0 \def (eq_ind B Abst TMP_32 I Abbr H) in 
(False_ind P H0))))) in (let TMP_36 \def (or_intror TMP_35 TMP_34 TMP_33) in 
(let TMP_30 \def (eq B Abst Abst) in (let TMP_29 \def ((eq B Abst Abst) \to 
(\forall (P: Prop).P)) in (let TMP_28 \def (refl_equal B Abst) in (let TMP_31 
\def (or_introl TMP_30 TMP_29 TMP_28) in (let TMP_26 \def (eq B Abst Void) in 
(let TMP_25 \def ((eq B Abst Void) \to (\forall (P: Prop).P)) in (let TMP_24 
\def (\lambda (H: (eq B Abst Void)).(\lambda (P: Prop).(let TMP_23 \def 
(\lambda (ee: B).(match ee in B with [Abbr \Rightarrow False | Abst 
\Rightarrow True | Void \Rightarrow False])) in (let H0 \def (eq_ind B Abst 
TMP_23 I Void H) in (False_ind P H0))))) in (let TMP_27 \def (or_intror 
TMP_26 TMP_25 TMP_24) in (B_ind TMP_39 TMP_36 TMP_31 TMP_27 b2))))))))))))))) 
in (let TMP_22 \def (\lambda (b2: B).(let TMP_21 \def (\lambda (b: B).(let 
TMP_20 \def (eq B Void b) in (let TMP_19 \def ((eq B Void b) \to (\forall (P: 
Prop).P)) in (or TMP_20 TMP_19)))) in (let TMP_17 \def (eq B Void Abbr) in 
(let TMP_16 \def ((eq B Void Abbr) \to (\forall (P: Prop).P)) in (let TMP_15 
\def (\lambda (H: (eq B Void Abbr)).(\lambda (P: Prop).(let TMP_14 \def 
(\lambda (ee: B).(match ee in B with [Abbr \Rightarrow False | Abst 
\Rightarrow False | Void \Rightarrow True])) in (let H0 \def (eq_ind B Void 
TMP_14 I Abbr H) in (False_ind P H0))))) in (let TMP_18 \def (or_intror 
TMP_17 TMP_16 TMP_15) in (let TMP_12 \def (eq B Void Abst) in (let TMP_11 
\def ((eq B Void Abst) \to (\forall (P: Prop).P)) in (let TMP_10 \def 
(\lambda (H: (eq B Void Abst)).(\lambda (P: Prop).(let TMP_9 \def (\lambda 
(ee: B).(match ee in B with [Abbr \Rightarrow False | Abst \Rightarrow False 
| Void \Rightarrow True])) in (let H0 \def (eq_ind B Void TMP_9 I Abst H) in 
(False_ind P H0))))) in (let TMP_13 \def (or_intror TMP_12 TMP_11 TMP_10) in 
(let TMP_7 \def (eq B Void Void) in (let TMP_6 \def ((eq B Void Void) \to 
(\forall (P: Prop).P)) in (let TMP_5 \def (refl_equal B Void) in (let TMP_8 
\def (or_introl TMP_7 TMP_6 TMP_5) in (B_ind TMP_21 TMP_18 TMP_13 TMP_8 
b2))))))))))))))) in (B_ind TMP_61 TMP_58 TMP_40 TMP_22 b1))))).

theorem bind_dec_not:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) (not (eq B b1 b2))))
\def
 \lambda (b1: B).(\lambda (b2: B).(let H_x \def (terms_props__bind_dec b1 b2) 
in (let H \def H_x in (let TMP_73 \def (eq B b1 b2) in (let TMP_72 \def ((eq 
B b1 b2) \to (\forall (P: Prop).P)) in (let TMP_70 \def (eq B b1 b2) in (let 
TMP_69 \def ((eq B b1 b2) \to False) in (let TMP_71 \def (or TMP_70 TMP_69) 
in (let TMP_68 \def (\lambda (H0: (eq B b1 b2)).(let TMP_67 \def (eq B b1 b2) 
in (let TMP_66 \def ((eq B b1 b2) \to False) in (or_introl TMP_67 TMP_66 
H0)))) in (let TMP_65 \def (\lambda (H0: (((eq B b1 b2) \to (\forall (P: 
Prop).P)))).(let TMP_64 \def (eq B b1 b2) in (let TMP_63 \def ((eq B b1 b2) 
\to False) in (let TMP_62 \def (\lambda (H1: (eq B b1 b2)).(H0 H1 False)) in 
(or_intror TMP_64 TMP_63 TMP_62))))) in (or_ind TMP_73 TMP_72 TMP_71 TMP_68 
TMP_65 H))))))))))).

theorem terms_props__flat_dec:
 \forall (f1: F).(\forall (f2: F).(or (eq F f1 f2) ((eq F f1 f2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (f1: F).(let TMP_102 \def (\lambda (f: F).(\forall (f2: F).(let 
TMP_101 \def (eq F f f2) in (let TMP_100 \def ((eq F f f2) \to (\forall (P: 
Prop).P)) in (or TMP_101 TMP_100))))) in (let TMP_99 \def (\lambda (f2: 
F).(let TMP_98 \def (\lambda (f: F).(let TMP_97 \def (eq F Appl f) in (let 
TMP_96 \def ((eq F Appl f) \to (\forall (P: Prop).P)) in (or TMP_97 
TMP_96)))) in (let TMP_94 \def (eq F Appl Appl) in (let TMP_93 \def ((eq F 
Appl Appl) \to (\forall (P: Prop).P)) in (let TMP_92 \def (refl_equal F Appl) 
in (let TMP_95 \def (or_introl TMP_94 TMP_93 TMP_92) in (let TMP_90 \def (eq 
F Appl Cast) in (let TMP_89 \def ((eq F Appl Cast) \to (\forall (P: Prop).P)) 
in (let TMP_88 \def (\lambda (H: (eq F Appl Cast)).(\lambda (P: Prop).(let 
TMP_87 \def (\lambda (ee: F).(match ee in F with [Appl \Rightarrow True | 
Cast \Rightarrow False])) in (let H0 \def (eq_ind F Appl TMP_87 I Cast H) in 
(False_ind P H0))))) in (let TMP_91 \def (or_intror TMP_90 TMP_89 TMP_88) in 
(F_ind TMP_98 TMP_95 TMP_91 f2))))))))))) in (let TMP_86 \def (\lambda (f2: 
F).(let TMP_85 \def (\lambda (f: F).(let TMP_84 \def (eq F Cast f) in (let 
TMP_83 \def ((eq F Cast f) \to (\forall (P: Prop).P)) in (or TMP_84 
TMP_83)))) in (let TMP_81 \def (eq F Cast Appl) in (let TMP_80 \def ((eq F 
Cast Appl) \to (\forall (P: Prop).P)) in (let TMP_79 \def (\lambda (H: (eq F 
Cast Appl)).(\lambda (P: Prop).(let TMP_78 \def (\lambda (ee: F).(match ee in 
F with [Appl \Rightarrow False | Cast \Rightarrow True])) in (let H0 \def 
(eq_ind F Cast TMP_78 I Appl H) in (False_ind P H0))))) in (let TMP_82 \def 
(or_intror TMP_81 TMP_80 TMP_79) in (let TMP_76 \def (eq F Cast Cast) in (let 
TMP_75 \def ((eq F Cast Cast) \to (\forall (P: Prop).P)) in (let TMP_74 \def 
(refl_equal F Cast) in (let TMP_77 \def (or_introl TMP_76 TMP_75 TMP_74) in 
(F_ind TMP_85 TMP_82 TMP_77 f2))))))))))) in (F_ind TMP_102 TMP_99 TMP_86 
f1)))).

theorem terms_props__kind_dec:
 \forall (k1: K).(\forall (k2: K).(or (eq K k1 k2) ((eq K k1 k2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (k1: K).(let TMP_197 \def (\lambda (k: K).(\forall (k2: K).(let 
TMP_196 \def (eq K k k2) in (let TMP_195 \def ((eq K k k2) \to (\forall (P: 
Prop).P)) in (or TMP_196 TMP_195))))) in (let TMP_194 \def (\lambda (b: 
B).(\lambda (k2: K).(let TMP_193 \def (\lambda (k: K).(let TMP_191 \def (Bind 
b) in (let TMP_192 \def (eq K TMP_191 k) in (let TMP_190 \def ((eq K (Bind b) 
k) \to (\forall (P: Prop).P)) in (or TMP_192 TMP_190))))) in (let TMP_189 
\def (\lambda (b0: B).(let H_x \def (terms_props__bind_dec b b0) in (let H 
\def H_x in (let TMP_188 \def (eq B b b0) in (let TMP_187 \def ((eq B b b0) 
\to (\forall (P: Prop).P)) in (let TMP_184 \def (Bind b) in (let TMP_183 \def 
(Bind b0) in (let TMP_185 \def (eq K TMP_184 TMP_183) in (let TMP_182 \def 
((eq K (Bind b) (Bind b0)) \to (\forall (P: Prop).P)) in (let TMP_186 \def 
(or TMP_185 TMP_182) in (let TMP_181 \def (\lambda (H0: (eq B b b0)).(let 
TMP_180 \def (\lambda (b1: B).(let TMP_178 \def (Bind b) in (let TMP_177 \def 
(Bind b1) in (let TMP_179 \def (eq K TMP_178 TMP_177) in (let TMP_176 \def 
((eq K (Bind b) (Bind b1)) \to (\forall (P: Prop).P)) in (or TMP_179 
TMP_176)))))) in (let TMP_173 \def (Bind b) in (let TMP_172 \def (Bind b) in 
(let TMP_174 \def (eq K TMP_173 TMP_172) in (let TMP_171 \def ((eq K (Bind b) 
(Bind b)) \to (\forall (P: Prop).P)) in (let TMP_169 \def (Bind b) in (let 
TMP_170 \def (refl_equal K TMP_169) in (let TMP_175 \def (or_introl TMP_174 
TMP_171 TMP_170) in (eq_ind B b TMP_180 TMP_175 b0 H0)))))))))) in (let 
TMP_168 \def (\lambda (H0: (((eq B b b0) \to (\forall (P: Prop).P)))).(let 
TMP_166 \def (Bind b) in (let TMP_165 \def (Bind b0) in (let TMP_167 \def (eq 
K TMP_166 TMP_165) in (let TMP_164 \def ((eq K (Bind b) (Bind b0)) \to 
(\forall (P: Prop).P)) in (let TMP_163 \def (\lambda (H1: (eq K (Bind b) 
(Bind b0))).(\lambda (P: Prop).(let TMP_160 \def (\lambda (e: K).(match e in 
K with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])) in (let TMP_159 
\def (Bind b) in (let TMP_158 \def (Bind b0) in (let H2 \def (f_equal K B 
TMP_160 TMP_159 TMP_158 H1) in (let TMP_161 \def (\lambda (b1: B).((eq B b 
b1) \to (\forall (P0: Prop).P0))) in (let H3 \def (eq_ind_r B b0 TMP_161 H0 b 
H2) in (let TMP_162 \def (refl_equal B b) in (H3 TMP_162 P)))))))))) in 
(or_intror TMP_167 TMP_164 TMP_163))))))) in (or_ind TMP_188 TMP_187 TMP_186 
TMP_181 TMP_168 H))))))))))))) in (let TMP_157 \def (\lambda (f: F).(let 
TMP_155 \def (Bind b) in (let TMP_154 \def (Flat f) in (let TMP_156 \def (eq 
K TMP_155 TMP_154) in (let TMP_153 \def ((eq K (Bind b) (Flat f)) \to 
(\forall (P: Prop).P)) in (let TMP_152 \def (\lambda (H: (eq K (Bind b) (Flat 
f))).(\lambda (P: Prop).(let TMP_151 \def (Bind b) in (let TMP_150 \def 
(\lambda (ee: K).(match ee in K with [(Bind _) \Rightarrow True | (Flat _) 
\Rightarrow False])) in (let TMP_149 \def (Flat f) in (let H0 \def (eq_ind K 
TMP_151 TMP_150 I TMP_149 H) in (False_ind P H0))))))) in (or_intror TMP_156 
TMP_153 TMP_152))))))) in (K_ind TMP_193 TMP_189 TMP_157 k2)))))) in (let 
TMP_148 \def (\lambda (f: F).(\lambda (k2: K).(let TMP_147 \def (\lambda (k: 
K).(let TMP_145 \def (Flat f) in (let TMP_146 \def (eq K TMP_145 k) in (let 
TMP_144 \def ((eq K (Flat f) k) \to (\forall (P: Prop).P)) in (or TMP_146 
TMP_144))))) in (let TMP_143 \def (\lambda (b: B).(let TMP_141 \def (Flat f) 
in (let TMP_140 \def (Bind b) in (let TMP_142 \def (eq K TMP_141 TMP_140) in 
(let TMP_139 \def ((eq K (Flat f) (Bind b)) \to (\forall (P: Prop).P)) in 
(let TMP_138 \def (\lambda (H: (eq K (Flat f) (Bind b))).(\lambda (P: 
Prop).(let TMP_137 \def (Flat f) in (let TMP_136 \def (\lambda (ee: K).(match 
ee in K with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])) in 
(let TMP_135 \def (Bind b) in (let H0 \def (eq_ind K TMP_137 TMP_136 I 
TMP_135 H) in (False_ind P H0))))))) in (or_intror TMP_142 TMP_139 
TMP_138))))))) in (let TMP_134 \def (\lambda (f0: F).(let H_x \def 
(terms_props__flat_dec f f0) in (let H \def H_x in (let TMP_133 \def (eq F f 
f0) in (let TMP_132 \def ((eq F f f0) \to (\forall (P: Prop).P)) in (let 
TMP_129 \def (Flat f) in (let TMP_128 \def (Flat f0) in (let TMP_130 \def (eq 
K TMP_129 TMP_128) in (let TMP_127 \def ((eq K (Flat f) (Flat f0)) \to 
(\forall (P: Prop).P)) in (let TMP_131 \def (or TMP_130 TMP_127) in (let 
TMP_126 \def (\lambda (H0: (eq F f f0)).(let TMP_125 \def (\lambda (f1: 
F).(let TMP_123 \def (Flat f) in (let TMP_122 \def (Flat f1) in (let TMP_124 
\def (eq K TMP_123 TMP_122) in (let TMP_121 \def ((eq K (Flat f) (Flat f1)) 
\to (\forall (P: Prop).P)) in (or TMP_124 TMP_121)))))) in (let TMP_118 \def 
(Flat f) in (let TMP_117 \def (Flat f) in (let TMP_119 \def (eq K TMP_118 
TMP_117) in (let TMP_116 \def ((eq K (Flat f) (Flat f)) \to (\forall (P: 
Prop).P)) in (let TMP_114 \def (Flat f) in (let TMP_115 \def (refl_equal K 
TMP_114) in (let TMP_120 \def (or_introl TMP_119 TMP_116 TMP_115) in (eq_ind 
F f TMP_125 TMP_120 f0 H0)))))))))) in (let TMP_113 \def (\lambda (H0: (((eq 
F f f0) \to (\forall (P: Prop).P)))).(let TMP_111 \def (Flat f) in (let 
TMP_110 \def (Flat f0) in (let TMP_112 \def (eq K TMP_111 TMP_110) in (let 
TMP_109 \def ((eq K (Flat f) (Flat f0)) \to (\forall (P: Prop).P)) in (let 
TMP_108 \def (\lambda (H1: (eq K (Flat f) (Flat f0))).(\lambda (P: Prop).(let 
TMP_105 \def (\lambda (e: K).(match e in K with [(Bind _) \Rightarrow f | 
(Flat f1) \Rightarrow f1])) in (let TMP_104 \def (Flat f) in (let TMP_103 
\def (Flat f0) in (let H2 \def (f_equal K F TMP_105 TMP_104 TMP_103 H1) in 
(let TMP_106 \def (\lambda (f1: F).((eq F f f1) \to (\forall (P0: Prop).P0))) 
in (let H3 \def (eq_ind_r F f0 TMP_106 H0 f H2) in (let TMP_107 \def 
(refl_equal F f) in (H3 TMP_107 P)))))))))) in (or_intror TMP_112 TMP_109 
TMP_108))))))) in (or_ind TMP_133 TMP_132 TMP_131 TMP_126 TMP_113 
H))))))))))))) in (K_ind TMP_147 TMP_143 TMP_134 k2)))))) in (K_ind TMP_197 
TMP_194 TMP_148 k1)))).

theorem term_dec:
 \forall (t1: T).(\forall (t2: T).(or (eq T t1 t2) ((eq T t1 t2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (t1: T).(let TMP_447 \def (\lambda (t: T).(\forall (t2: T).(let 
TMP_446 \def (eq T t t2) in (let TMP_445 \def ((eq T t t2) \to (\forall (P: 
Prop).P)) in (or TMP_446 TMP_445))))) in (let TMP_444 \def (\lambda (n: 
nat).(\lambda (t2: T).(let TMP_443 \def (\lambda (t: T).(let TMP_441 \def 
(TSort n) in (let TMP_442 \def (eq T TMP_441 t) in (let TMP_440 \def ((eq T 
(TSort n) t) \to (\forall (P: Prop).P)) in (or TMP_442 TMP_440))))) in (let 
TMP_439 \def (\lambda (n0: nat).(let H_x \def (nat_dec n n0) in (let H \def 
H_x in (let TMP_438 \def (eq nat n n0) in (let TMP_437 \def ((eq nat n n0) 
\to (\forall (P: Prop).P)) in (let TMP_434 \def (TSort n) in (let TMP_433 
\def (TSort n0) in (let TMP_435 \def (eq T TMP_434 TMP_433) in (let TMP_432 
\def ((eq T (TSort n) (TSort n0)) \to (\forall (P: Prop).P)) in (let TMP_436 
\def (or TMP_435 TMP_432) in (let TMP_431 \def (\lambda (H0: (eq nat n 
n0)).(let TMP_430 \def (\lambda (n1: nat).(let TMP_428 \def (TSort n) in (let 
TMP_427 \def (TSort n1) in (let TMP_429 \def (eq T TMP_428 TMP_427) in (let 
TMP_426 \def ((eq T (TSort n) (TSort n1)) \to (\forall (P: Prop).P)) in (or 
TMP_429 TMP_426)))))) in (let TMP_423 \def (TSort n) in (let TMP_422 \def 
(TSort n) in (let TMP_424 \def (eq T TMP_423 TMP_422) in (let TMP_421 \def 
((eq T (TSort n) (TSort n)) \to (\forall (P: Prop).P)) in (let TMP_419 \def 
(TSort n) in (let TMP_420 \def (refl_equal T TMP_419) in (let TMP_425 \def 
(or_introl TMP_424 TMP_421 TMP_420) in (eq_ind nat n TMP_430 TMP_425 n0 
H0)))))))))) in (let TMP_418 \def (\lambda (H0: (((eq nat n n0) \to (\forall 
(P: Prop).P)))).(let TMP_416 \def (TSort n) in (let TMP_415 \def (TSort n0) 
in (let TMP_417 \def (eq T TMP_416 TMP_415) in (let TMP_414 \def ((eq T 
(TSort n) (TSort n0)) \to (\forall (P: Prop).P)) in (let TMP_413 \def 
(\lambda (H1: (eq T (TSort n) (TSort n0))).(\lambda (P: Prop).(let TMP_410 
\def (\lambda (e: T).(match e in T with [(TSort n1) \Rightarrow n1 | (TLRef 
_) \Rightarrow n | (THead _ _ _) \Rightarrow n])) in (let TMP_409 \def (TSort 
n) in (let TMP_408 \def (TSort n0) in (let H2 \def (f_equal T nat TMP_410 
TMP_409 TMP_408 H1) in (let TMP_411 \def (\lambda (n1: nat).((eq nat n n1) 
\to (\forall (P0: Prop).P0))) in (let H3 \def (eq_ind_r nat n0 TMP_411 H0 n 
H2) in (let TMP_412 \def (refl_equal nat n) in (H3 TMP_412 P)))))))))) in 
(or_intror TMP_417 TMP_414 TMP_413))))))) in (or_ind TMP_438 TMP_437 TMP_436 
TMP_431 TMP_418 H))))))))))))) in (let TMP_407 \def (\lambda (n0: nat).(let 
TMP_405 \def (TSort n) in (let TMP_404 \def (TLRef n0) in (let TMP_406 \def 
(eq T TMP_405 TMP_404) in (let TMP_403 \def ((eq T (TSort n) (TLRef n0)) \to 
(\forall (P: Prop).P)) in (let TMP_402 \def (\lambda (H: (eq T (TSort n) 
(TLRef n0))).(\lambda (P: Prop).(let TMP_401 \def (TSort n) in (let TMP_400 
\def (\lambda (ee: T).(match ee in T with [(TSort _) \Rightarrow True | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let 
TMP_399 \def (TLRef n0) in (let H0 \def (eq_ind T TMP_401 TMP_400 I TMP_399 
H) in (False_ind P H0))))))) in (or_intror TMP_406 TMP_403 TMP_402))))))) in 
(let TMP_398 \def (\lambda (k: K).(\lambda (t: T).(\lambda (_: (or (eq T 
(TSort n) t) ((eq T (TSort n) t) \to (\forall (P: Prop).P)))).(\lambda (t0: 
T).(\lambda (_: (or (eq T (TSort n) t0) ((eq T (TSort n) t0) \to (\forall (P: 
Prop).P)))).(let TMP_396 \def (TSort n) in (let TMP_395 \def (THead k t t0) 
in (let TMP_397 \def (eq T TMP_396 TMP_395) in (let TMP_394 \def ((eq T 
(TSort n) (THead k t t0)) \to (\forall (P: Prop).P)) in (let TMP_393 \def 
(\lambda (H1: (eq T (TSort n) (THead k t t0))).(\lambda (P: Prop).(let 
TMP_392 \def (TSort n) in (let TMP_391 \def (\lambda (ee: T).(match ee in T 
with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow False])) in (let TMP_390 \def (THead k t t0) in (let H2 \def 
(eq_ind T TMP_392 TMP_391 I TMP_390 H1) in (False_ind P H2))))))) in 
(or_intror TMP_397 TMP_394 TMP_393))))))))))) in (T_ind TMP_443 TMP_439 
TMP_407 TMP_398 t2))))))) in (let TMP_389 \def (\lambda (n: nat).(\lambda 
(t2: T).(let TMP_388 \def (\lambda (t: T).(let TMP_386 \def (TLRef n) in (let 
TMP_387 \def (eq T TMP_386 t) in (let TMP_385 \def ((eq T (TLRef n) t) \to 
(\forall (P: Prop).P)) in (or TMP_387 TMP_385))))) in (let TMP_384 \def 
(\lambda (n0: nat).(let TMP_382 \def (TLRef n) in (let TMP_381 \def (TSort 
n0) in (let TMP_383 \def (eq T TMP_382 TMP_381) in (let TMP_380 \def ((eq T 
(TLRef n) (TSort n0)) \to (\forall (P: Prop).P)) in (let TMP_379 \def 
(\lambda (H: (eq T (TLRef n) (TSort n0))).(\lambda (P: Prop).(let TMP_378 
\def (TLRef n) in (let TMP_377 \def (\lambda (ee: T).(match ee in T with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) in (let TMP_376 \def (TSort n0) in (let H0 \def (eq_ind 
T TMP_378 TMP_377 I TMP_376 H) in (False_ind P H0))))))) in (or_intror 
TMP_383 TMP_380 TMP_379))))))) in (let TMP_375 \def (\lambda (n0: nat).(let 
H_x \def (nat_dec n n0) in (let H \def H_x in (let TMP_374 \def (eq nat n n0) 
in (let TMP_373 \def ((eq nat n n0) \to (\forall (P: Prop).P)) in (let 
TMP_370 \def (TLRef n) in (let TMP_369 \def (TLRef n0) in (let TMP_371 \def 
(eq T TMP_370 TMP_369) in (let TMP_368 \def ((eq T (TLRef n) (TLRef n0)) \to 
(\forall (P: Prop).P)) in (let TMP_372 \def (or TMP_371 TMP_368) in (let 
TMP_367 \def (\lambda (H0: (eq nat n n0)).(let TMP_366 \def (\lambda (n1: 
nat).(let TMP_364 \def (TLRef n) in (let TMP_363 \def (TLRef n1) in (let 
TMP_365 \def (eq T TMP_364 TMP_363) in (let TMP_362 \def ((eq T (TLRef n) 
(TLRef n1)) \to (\forall (P: Prop).P)) in (or TMP_365 TMP_362)))))) in (let 
TMP_359 \def (TLRef n) in (let TMP_358 \def (TLRef n) in (let TMP_360 \def 
(eq T TMP_359 TMP_358) in (let TMP_357 \def ((eq T (TLRef n) (TLRef n)) \to 
(\forall (P: Prop).P)) in (let TMP_355 \def (TLRef n) in (let TMP_356 \def 
(refl_equal T TMP_355) in (let TMP_361 \def (or_introl TMP_360 TMP_357 
TMP_356) in (eq_ind nat n TMP_366 TMP_361 n0 H0)))))))))) in (let TMP_354 
\def (\lambda (H0: (((eq nat n n0) \to (\forall (P: Prop).P)))).(let TMP_352 
\def (TLRef n) in (let TMP_351 \def (TLRef n0) in (let TMP_353 \def (eq T 
TMP_352 TMP_351) in (let TMP_350 \def ((eq T (TLRef n) (TLRef n0)) \to 
(\forall (P: Prop).P)) in (let TMP_349 \def (\lambda (H1: (eq T (TLRef n) 
(TLRef n0))).(\lambda (P: Prop).(let TMP_346 \def (\lambda (e: T).(match e in 
T with [(TSort _) \Rightarrow n | (TLRef n1) \Rightarrow n1 | (THead _ _ _) 
\Rightarrow n])) in (let TMP_345 \def (TLRef n) in (let TMP_344 \def (TLRef 
n0) in (let H2 \def (f_equal T nat TMP_346 TMP_345 TMP_344 H1) in (let 
TMP_347 \def (\lambda (n1: nat).((eq nat n n1) \to (\forall (P0: Prop).P0))) 
in (let H3 \def (eq_ind_r nat n0 TMP_347 H0 n H2) in (let TMP_348 \def 
(refl_equal nat n) in (H3 TMP_348 P)))))))))) in (or_intror TMP_353 TMP_350 
TMP_349))))))) in (or_ind TMP_374 TMP_373 TMP_372 TMP_367 TMP_354 
H))))))))))))) in (let TMP_343 \def (\lambda (k: K).(\lambda (t: T).(\lambda 
(_: (or (eq T (TLRef n) t) ((eq T (TLRef n) t) \to (\forall (P: 
Prop).P)))).(\lambda (t0: T).(\lambda (_: (or (eq T (TLRef n) t0) ((eq T 
(TLRef n) t0) \to (\forall (P: Prop).P)))).(let TMP_341 \def (TLRef n) in 
(let TMP_340 \def (THead k t t0) in (let TMP_342 \def (eq T TMP_341 TMP_340) 
in (let TMP_339 \def ((eq T (TLRef n) (THead k t t0)) \to (\forall (P: 
Prop).P)) in (let TMP_338 \def (\lambda (H1: (eq T (TLRef n) (THead k t 
t0))).(\lambda (P: Prop).(let TMP_337 \def (TLRef n) in (let TMP_336 \def 
(\lambda (ee: T).(match ee in T with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let TMP_335 \def 
(THead k t t0) in (let H2 \def (eq_ind T TMP_337 TMP_336 I TMP_335 H1) in 
(False_ind P H2))))))) in (or_intror TMP_342 TMP_339 TMP_338))))))))))) in 
(T_ind TMP_388 TMP_384 TMP_375 TMP_343 t2))))))) in (let TMP_334 \def 
(\lambda (k: K).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).(or (eq T t 
t2) ((eq T t t2) \to (\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda 
(H0: ((\forall (t2: T).(or (eq T t0 t2) ((eq T t0 t2) \to (\forall (P: 
Prop).P)))))).(\lambda (t2: T).(let TMP_333 \def (\lambda (t3: T).(let 
TMP_331 \def (THead k t t0) in (let TMP_332 \def (eq T TMP_331 t3) in (let 
TMP_330 \def ((eq T (THead k t t0) t3) \to (\forall (P: Prop).P)) in (or 
TMP_332 TMP_330))))) in (let TMP_329 \def (\lambda (n: nat).(let TMP_327 \def 
(THead k t t0) in (let TMP_326 \def (TSort n) in (let TMP_328 \def (eq T 
TMP_327 TMP_326) in (let TMP_325 \def ((eq T (THead k t t0) (TSort n)) \to 
(\forall (P: Prop).P)) in (let TMP_324 \def (\lambda (H1: (eq T (THead k t 
t0) (TSort n))).(\lambda (P: Prop).(let TMP_323 \def (THead k t t0) in (let 
TMP_322 \def (\lambda (ee: T).(match ee in T with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_321 \def (TSort n) in (let H2 \def (eq_ind T TMP_323 TMP_322 I 
TMP_321 H1) in (False_ind P H2))))))) in (or_intror TMP_328 TMP_325 
TMP_324))))))) in (let TMP_320 \def (\lambda (n: nat).(let TMP_318 \def 
(THead k t t0) in (let TMP_317 \def (TLRef n) in (let TMP_319 \def (eq T 
TMP_318 TMP_317) in (let TMP_316 \def ((eq T (THead k t t0) (TLRef n)) \to 
(\forall (P: Prop).P)) in (let TMP_315 \def (\lambda (H1: (eq T (THead k t 
t0) (TLRef n))).(\lambda (P: Prop).(let TMP_314 \def (THead k t t0) in (let 
TMP_313 \def (\lambda (ee: T).(match ee in T with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_312 \def (TLRef n) in (let H2 \def (eq_ind T TMP_314 TMP_313 I 
TMP_312 H1) in (False_ind P H2))))))) in (or_intror TMP_319 TMP_316 
TMP_315))))))) in (let TMP_311 \def (\lambda (k0: K).(\lambda (t3: 
T).(\lambda (H1: (or (eq T (THead k t t0) t3) ((eq T (THead k t t0) t3) \to 
(\forall (P: Prop).P)))).(\lambda (t4: T).(\lambda (H2: (or (eq T (THead k t 
t0) t4) ((eq T (THead k t t0) t4) \to (\forall (P: Prop).P)))).(let H_x \def 
(H t3) in (let H3 \def H_x in (let TMP_310 \def (eq T t t3) in (let TMP_309 
\def ((eq T t t3) \to (\forall (P: Prop).P)) in (let TMP_306 \def (THead k t 
t0) in (let TMP_305 \def (THead k0 t3 t4) in (let TMP_307 \def (eq T TMP_306 
TMP_305) in (let TMP_304 \def ((eq T (THead k t t0) (THead k0 t3 t4)) \to 
(\forall (P: Prop).P)) in (let TMP_308 \def (or TMP_307 TMP_304) in (let 
TMP_303 \def (\lambda (H4: (eq T t t3)).(let TMP_228 \def (\lambda (t5: 
T).(let TMP_226 \def (THead k t t0) in (let TMP_227 \def (eq T TMP_226 t5) in 
(let TMP_225 \def ((eq T (THead k t t0) t5) \to (\forall (P: Prop).P)) in (or 
TMP_227 TMP_225))))) in (let H5 \def (eq_ind_r T t3 TMP_228 H1 t H4) in (let 
TMP_302 \def (\lambda (t5: T).(let TMP_300 \def (THead k t t0) in (let 
TMP_299 \def (THead k0 t5 t4) in (let TMP_301 \def (eq T TMP_300 TMP_299) in 
(let TMP_298 \def ((eq T (THead k t t0) (THead k0 t5 t4)) \to (\forall (P: 
Prop).P)) in (or TMP_301 TMP_298)))))) in (let H_x0 \def (H0 t4) in (let H6 
\def H_x0 in (let TMP_296 \def (eq T t0 t4) in (let TMP_295 \def ((eq T t0 
t4) \to (\forall (P: Prop).P)) in (let TMP_292 \def (THead k t t0) in (let 
TMP_291 \def (THead k0 t t4) in (let TMP_293 \def (eq T TMP_292 TMP_291) in 
(let TMP_290 \def ((eq T (THead k t t0) (THead k0 t t4)) \to (\forall (P: 
Prop).P)) in (let TMP_294 \def (or TMP_293 TMP_290) in (let TMP_289 \def 
(\lambda (H7: (eq T t0 t4)).(let TMP_251 \def (\lambda (t5: T).(let TMP_249 
\def (THead k t t0) in (let TMP_250 \def (eq T TMP_249 t5) in (let TMP_248 
\def ((eq T (THead k t t0) t5) \to (\forall (P: Prop).P)) in (or TMP_250 
TMP_248))))) in (let H8 \def (eq_ind_r T t4 TMP_251 H2 t0 H7) in (let TMP_288 
\def (\lambda (t5: T).(let TMP_286 \def (THead k t t0) in (let TMP_285 \def 
(THead k0 t t5) in (let TMP_287 \def (eq T TMP_286 TMP_285) in (let TMP_284 
\def ((eq T (THead k t t0) (THead k0 t t5)) \to (\forall (P: Prop).P)) in (or 
TMP_287 TMP_284)))))) in (let H_x1 \def (terms_props__kind_dec k k0) in (let 
H9 \def H_x1 in (let TMP_282 \def (eq K k k0) in (let TMP_281 \def ((eq K k 
k0) \to (\forall (P: Prop).P)) in (let TMP_278 \def (THead k t t0) in (let 
TMP_277 \def (THead k0 t t0) in (let TMP_279 \def (eq T TMP_278 TMP_277) in 
(let TMP_276 \def ((eq T (THead k t t0) (THead k0 t t0)) \to (\forall (P: 
Prop).P)) in (let TMP_280 \def (or TMP_279 TMP_276) in (let TMP_275 \def 
(\lambda (H10: (eq K k k0)).(let TMP_274 \def (\lambda (k1: K).(let TMP_272 
\def (THead k t t0) in (let TMP_271 \def (THead k1 t t0) in (let TMP_273 \def 
(eq T TMP_272 TMP_271) in (let TMP_270 \def ((eq T (THead k t t0) (THead k1 t 
t0)) \to (\forall (P: Prop).P)) in (or TMP_273 TMP_270)))))) in (let TMP_267 
\def (THead k t t0) in (let TMP_266 \def (THead k t t0) in (let TMP_268 \def 
(eq T TMP_267 TMP_266) in (let TMP_265 \def ((eq T (THead k t t0) (THead k t 
t0)) \to (\forall (P: Prop).P)) in (let TMP_263 \def (THead k t t0) in (let 
TMP_264 \def (refl_equal T TMP_263) in (let TMP_269 \def (or_introl TMP_268 
TMP_265 TMP_264) in (eq_ind K k TMP_274 TMP_269 k0 H10)))))))))) in (let 
TMP_262 \def (\lambda (H10: (((eq K k k0) \to (\forall (P: Prop).P)))).(let 
TMP_260 \def (THead k t t0) in (let TMP_259 \def (THead k0 t t0) in (let 
TMP_261 \def (eq T TMP_260 TMP_259) in (let TMP_258 \def ((eq T (THead k t 
t0) (THead k0 t t0)) \to (\forall (P: Prop).P)) in (let TMP_257 \def (\lambda 
(H11: (eq T (THead k t t0) (THead k0 t t0))).(\lambda (P: Prop).(let TMP_254 
\def (\lambda (e: T).(match e in T with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) in (let TMP_253 \def (THead 
k t t0) in (let TMP_252 \def (THead k0 t t0) in (let H12 \def (f_equal T K 
TMP_254 TMP_253 TMP_252 H11) in (let TMP_255 \def (\lambda (k1: K).((eq K k 
k1) \to (\forall (P0: Prop).P0))) in (let H13 \def (eq_ind_r K k0 TMP_255 H10 
k H12) in (let TMP_256 \def (refl_equal K k) in (H13 TMP_256 P)))))))))) in 
(or_intror TMP_261 TMP_258 TMP_257))))))) in (let TMP_283 \def (or_ind 
TMP_282 TMP_281 TMP_280 TMP_275 TMP_262 H9) in (eq_ind T t0 TMP_288 TMP_283 
t4 H7))))))))))))))))) in (let TMP_247 \def (\lambda (H7: (((eq T t0 t4) \to 
(\forall (P: Prop).P)))).(let TMP_245 \def (THead k t t0) in (let TMP_244 
\def (THead k0 t t4) in (let TMP_246 \def (eq T TMP_245 TMP_244) in (let 
TMP_243 \def ((eq T (THead k t t0) (THead k0 t t4)) \to (\forall (P: 
Prop).P)) in (let TMP_242 \def (\lambda (H8: (eq T (THead k t t0) (THead k0 t 
t4))).(\lambda (P: Prop).(let TMP_231 \def (\lambda (e: T).(match e in T with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) 
\Rightarrow k1])) in (let TMP_230 \def (THead k t t0) in (let TMP_229 \def 
(THead k0 t t4) in (let H9 \def (f_equal T K TMP_231 TMP_230 TMP_229 H8) in 
(let TMP_234 \def (\lambda (e: T).(match e in T with [(TSort _) \Rightarrow 
t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t5) \Rightarrow t5])) in (let 
TMP_233 \def (THead k t t0) in (let TMP_232 \def (THead k0 t t4) in (let H10 
\def (f_equal T T TMP_234 TMP_233 TMP_232 H8) in (let TMP_241 \def (\lambda 
(_: (eq K k k0)).(let TMP_235 \def (\lambda (t5: T).((eq T t0 t5) \to 
(\forall (P0: Prop).P0))) in (let H12 \def (eq_ind_r T t4 TMP_235 H7 t0 H10) 
in (let TMP_239 \def (\lambda (t5: T).(let TMP_237 \def (THead k t t0) in 
(let TMP_238 \def (eq T TMP_237 t5) in (let TMP_236 \def ((eq T (THead k t 
t0) t5) \to (\forall (P0: Prop).P0)) in (or TMP_238 TMP_236))))) in (let H13 
\def (eq_ind_r T t4 TMP_239 H2 t0 H10) in (let TMP_240 \def (refl_equal T t0) 
in (H12 TMP_240 P))))))) in (TMP_241 H9)))))))))))) in (or_intror TMP_246 
TMP_243 TMP_242))))))) in (let TMP_297 \def (or_ind TMP_296 TMP_295 TMP_294 
TMP_289 TMP_247 H6) in (eq_ind T t TMP_302 TMP_297 t3 H4))))))))))))))))) in 
(let TMP_224 \def (\lambda (H4: (((eq T t t3) \to (\forall (P: 
Prop).P)))).(let TMP_222 \def (THead k t t0) in (let TMP_221 \def (THead k0 
t3 t4) in (let TMP_223 \def (eq T TMP_222 TMP_221) in (let TMP_220 \def ((eq 
T (THead k t t0) (THead k0 t3 t4)) \to (\forall (P: Prop).P)) in (let TMP_219 
\def (\lambda (H5: (eq T (THead k t t0) (THead k0 t3 t4))).(\lambda (P: 
Prop).(let TMP_200 \def (\lambda (e: T).(match e in T with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) \Rightarrow k1])) in 
(let TMP_199 \def (THead k t t0) in (let TMP_198 \def (THead k0 t3 t4) in 
(let H6 \def (f_equal T K TMP_200 TMP_199 TMP_198 H5) in (let TMP_203 \def 
(\lambda (e: T).(match e in T with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ t5 _) \Rightarrow t5])) in (let TMP_202 \def (THead 
k t t0) in (let TMP_201 \def (THead k0 t3 t4) in (let H7 \def (f_equal T T 
TMP_203 TMP_202 TMP_201 H5) in (let TMP_206 \def (\lambda (e: T).(match e in 
T with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t5) 
\Rightarrow t5])) in (let TMP_205 \def (THead k t t0) in (let TMP_204 \def 
(THead k0 t3 t4) in (let H8 \def (f_equal T T TMP_206 TMP_205 TMP_204 H5) in 
(let TMP_217 \def (\lambda (H9: (eq T t t3)).(\lambda (_: (eq K k k0)).(let 
TMP_210 \def (\lambda (t5: T).(let TMP_208 \def (THead k t t0) in (let 
TMP_209 \def (eq T TMP_208 t5) in (let TMP_207 \def ((eq T (THead k t t0) t5) 
\to (\forall (P0: Prop).P0)) in (or TMP_209 TMP_207))))) in (let H11 \def 
(eq_ind_r T t4 TMP_210 H2 t0 H8) in (let TMP_211 \def (\lambda (t5: T).((eq T 
t t5) \to (\forall (P0: Prop).P0))) in (let H12 \def (eq_ind_r T t3 TMP_211 
H4 t H9) in (let TMP_215 \def (\lambda (t5: T).(let TMP_213 \def (THead k t 
t0) in (let TMP_214 \def (eq T TMP_213 t5) in (let TMP_212 \def ((eq T (THead 
k t t0) t5) \to (\forall (P0: Prop).P0)) in (or TMP_214 TMP_212))))) in (let 
H13 \def (eq_ind_r T t3 TMP_215 H1 t H9) in (let TMP_216 \def (refl_equal T 
t) in (H12 TMP_216 P)))))))))) in (let TMP_218 \def (TMP_217 H7) in (TMP_218 
H6))))))))))))))))) in (or_intror TMP_223 TMP_220 TMP_219))))))) in (or_ind 
TMP_310 TMP_309 TMP_308 TMP_303 TMP_224 H3))))))))))))))))) in (T_ind TMP_333 
TMP_329 TMP_320 TMP_311 t2))))))))))) in (T_ind TMP_447 TMP_444 TMP_389 
TMP_334 t1))))).

theorem binder_dec:
 \forall (t: T).(or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T t (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall 
(u: T).((eq T t (THead (Bind b) w u)) \to (\forall (P: Prop).P))))))
\def
 \lambda (t: T).(let TMP_516 \def (\lambda (t0: T).(let TMP_514 \def (\lambda 
(b: B).(\lambda (w: T).(\lambda (u: T).(let TMP_512 \def (Bind b) in (let 
TMP_513 \def (THead TMP_512 w u) in (eq T t0 TMP_513)))))) in (let TMP_515 
\def (ex_3 B T T TMP_514) in (let TMP_511 \def (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))) in (or TMP_515 TMP_511))))) in (let TMP_510 \def (\lambda (n: 
nat).(let TMP_508 \def (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(let 
TMP_507 \def (TSort n) in (let TMP_505 \def (Bind b) in (let TMP_506 \def 
(THead TMP_505 w u) in (eq T TMP_507 TMP_506))))))) in (let TMP_509 \def 
(ex_3 B T T TMP_508) in (let TMP_504 \def (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T (TSort n) (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))) in (let TMP_503 \def (\lambda (b: B).(\lambda (w: T).(\lambda 
(u: T).(\lambda (H: (eq T (TSort n) (THead (Bind b) w u))).(\lambda (P: 
Prop).(let TMP_502 \def (TSort n) in (let TMP_501 \def (\lambda (ee: 
T).(match ee in T with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow 
False | (THead _ _ _) \Rightarrow False])) in (let TMP_499 \def (Bind b) in 
(let TMP_500 \def (THead TMP_499 w u) in (let H0 \def (eq_ind T TMP_502 
TMP_501 I TMP_500 H) in (False_ind P H0))))))))))) in (or_intror TMP_509 
TMP_504 TMP_503)))))) in (let TMP_498 \def (\lambda (n: nat).(let TMP_496 
\def (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(let TMP_495 \def (TLRef 
n) in (let TMP_493 \def (Bind b) in (let TMP_494 \def (THead TMP_493 w u) in 
(eq T TMP_495 TMP_494))))))) in (let TMP_497 \def (ex_3 B T T TMP_496) in 
(let TMP_492 \def (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T 
(TLRef n) (THead (Bind b) w u)) \to (\forall (P: Prop).P))))) in (let TMP_491 
\def (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(\lambda (H: (eq T 
(TLRef n) (THead (Bind b) w u))).(\lambda (P: Prop).(let TMP_490 \def (TLRef 
n) in (let TMP_489 \def (\lambda (ee: T).(match ee in T with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) in (let TMP_487 \def (Bind b) in (let TMP_488 \def (THead TMP_487 w 
u) in (let H0 \def (eq_ind T TMP_490 TMP_489 I TMP_488 H) in (False_ind P 
H0))))))))))) in (or_intror TMP_497 TMP_492 TMP_491)))))) in (let TMP_486 
\def (\lambda (k: K).(let TMP_485 \def (\lambda (k0: K).(\forall (t0: T).((or 
(ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead 
(Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t0 
(THead (Bind b) w u)) \to (\forall (P: Prop).P)))))) \to (\forall (t1: 
T).((or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t1 
(THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: 
T).((eq T t1 (THead (Bind b) w u)) \to (\forall (P: Prop).P)))))) \to (let 
TMP_483 \def (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(let TMP_482 
\def (THead k0 t0 t1) in (let TMP_480 \def (Bind b) in (let TMP_481 \def 
(THead TMP_480 w u) in (eq T TMP_482 TMP_481))))))) in (let TMP_484 \def 
(ex_3 B T T TMP_483) in (let TMP_479 \def (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T (THead k0 t0 t1) (THead (Bind b) w u)) \to (\forall 
(P: Prop).P))))) in (or TMP_484 TMP_479))))))))) in (let TMP_478 \def 
(\lambda (b: B).(\lambda (t0: T).(\lambda (_: (or (ex_3 B T T (\lambda (b0: 
B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind b0) w u)))))) 
(\forall (b0: B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead (Bind b0) w 
u)) \to (\forall (P: Prop).P))))))).(\lambda (t1: T).(\lambda (_: (or (ex_3 B 
T T (\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind 
b0) w u)))))) (\forall (b0: B).(\forall (w: T).(\forall (u: T).((eq T t1 
(THead (Bind b0) w u)) \to (\forall (P: Prop).P))))))).(let TMP_476 \def 
(\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(let TMP_474 \def (Bind b) 
in (let TMP_475 \def (THead TMP_474 t0 t1) in (let TMP_472 \def (Bind b0) in 
(let TMP_473 \def (THead TMP_472 w u) in (eq T TMP_475 TMP_473)))))))) in 
(let TMP_477 \def (ex_3 B T T TMP_476) in (let TMP_471 \def (\forall (b0: 
B).(\forall (w: T).(\forall (u: T).((eq T (THead (Bind b) t0 t1) (THead (Bind 
b0) w u)) \to (\forall (P: Prop).P))))) in (let TMP_469 \def (\lambda (b0: 
B).(\lambda (w: T).(\lambda (u: T).(let TMP_467 \def (Bind b) in (let TMP_468 
\def (THead TMP_467 t0 t1) in (let TMP_465 \def (Bind b0) in (let TMP_466 
\def (THead TMP_465 w u) in (eq T TMP_468 TMP_466)))))))) in (let TMP_462 
\def (Bind b) in (let TMP_463 \def (THead TMP_462 t0 t1) in (let TMP_464 \def 
(refl_equal T TMP_463) in (let TMP_470 \def (ex_3_intro B T T TMP_469 b t0 t1 
TMP_464) in (or_introl TMP_477 TMP_471 TMP_470)))))))))))))) in (let TMP_461 
\def (\lambda (f: F).(\lambda (t0: T).(\lambda (_: (or (ex_3 B T T (\lambda 
(b: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w u)))))) 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead (Bind b) w 
u)) \to (\forall (P: Prop).P))))))).(\lambda (t1: T).(\lambda (_: (or (ex_3 B 
T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind b) 
w u)))))) (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead 
(Bind b) w u)) \to (\forall (P: Prop).P))))))).(let TMP_459 \def (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(let TMP_457 \def (Flat f) in (let TMP_458 
\def (THead TMP_457 t0 t1) in (let TMP_455 \def (Bind b) in (let TMP_456 \def 
(THead TMP_455 w u) in (eq T TMP_458 TMP_456)))))))) in (let TMP_460 \def 
(ex_3 B T T TMP_459) in (let TMP_454 \def (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T (THead (Flat f) t0 t1) (THead (Bind b) w u)) \to 
(\forall (P: Prop).P))))) in (let TMP_453 \def (\lambda (b: B).(\lambda (w: 
T).(\lambda (u: T).(\lambda (H1: (eq T (THead (Flat f) t0 t1) (THead (Bind b) 
w u))).(\lambda (P: Prop).(let TMP_451 \def (Flat f) in (let TMP_452 \def 
(THead TMP_451 t0 t1) in (let TMP_450 \def (\lambda (ee: T).(match ee in T 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ 
_) \Rightarrow (match k0 in K with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) in (let TMP_448 \def (Bind b) in (let TMP_449 \def 
(THead TMP_448 w u) in (let H2 \def (eq_ind T TMP_452 TMP_450 I TMP_449 H1) 
in (False_ind P H2)))))))))))) in (or_intror TMP_460 TMP_454 
TMP_453)))))))))) in (K_ind TMP_485 TMP_478 TMP_461 k))))) in (T_ind TMP_516 
TMP_510 TMP_498 TMP_486 t))))).

theorem abst_dec:
 \forall (u: T).(\forall (v: T).(or (ex T (\lambda (t: T).(eq T u (THead 
(Bind Abst) v t)))) (\forall (t: T).((eq T u (THead (Bind Abst) v t)) \to 
(\forall (P: Prop).P)))))
\def
 \lambda (u: T).(let TMP_646 \def (\lambda (t: T).(\forall (v: T).(let 
TMP_644 \def (\lambda (t0: T).(let TMP_642 \def (Bind Abst) in (let TMP_643 
\def (THead TMP_642 v t0) in (eq T t TMP_643)))) in (let TMP_645 \def (ex T 
TMP_644) in (let TMP_641 \def (\forall (t0: T).((eq T t (THead (Bind Abst) v 
t0)) \to (\forall (P: Prop).P))) in (or TMP_645 TMP_641)))))) in (let TMP_640 
\def (\lambda (n: nat).(\lambda (v: T).(let TMP_638 \def (\lambda (t: T).(let 
TMP_637 \def (TSort n) in (let TMP_635 \def (Bind Abst) in (let TMP_636 \def 
(THead TMP_635 v t) in (eq T TMP_637 TMP_636))))) in (let TMP_639 \def (ex T 
TMP_638) in (let TMP_634 \def (\forall (t: T).((eq T (TSort n) (THead (Bind 
Abst) v t)) \to (\forall (P: Prop).P))) in (let TMP_633 \def (\lambda (t: 
T).(\lambda (H: (eq T (TSort n) (THead (Bind Abst) v t))).(\lambda (P: 
Prop).(let TMP_632 \def (TSort n) in (let TMP_631 \def (\lambda (ee: 
T).(match ee in T with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow 
False | (THead _ _ _) \Rightarrow False])) in (let TMP_629 \def (Bind Abst) 
in (let TMP_630 \def (THead TMP_629 v t) in (let H0 \def (eq_ind T TMP_632 
TMP_631 I TMP_630 H) in (False_ind P H0))))))))) in (or_intror TMP_639 
TMP_634 TMP_633))))))) in (let TMP_628 \def (\lambda (n: nat).(\lambda (v: 
T).(let TMP_626 \def (\lambda (t: T).(let TMP_625 \def (TLRef n) in (let 
TMP_623 \def (Bind Abst) in (let TMP_624 \def (THead TMP_623 v t) in (eq T 
TMP_625 TMP_624))))) in (let TMP_627 \def (ex T TMP_626) in (let TMP_622 \def 
(\forall (t: T).((eq T (TLRef n) (THead (Bind Abst) v t)) \to (\forall (P: 
Prop).P))) in (let TMP_621 \def (\lambda (t: T).(\lambda (H: (eq T (TLRef n) 
(THead (Bind Abst) v t))).(\lambda (P: Prop).(let TMP_620 \def (TLRef n) in 
(let TMP_619 \def (\lambda (ee: T).(match ee in T with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) in 
(let TMP_617 \def (Bind Abst) in (let TMP_618 \def (THead TMP_617 v t) in 
(let H0 \def (eq_ind T TMP_620 TMP_619 I TMP_618 H) in (False_ind P 
H0))))))))) in (or_intror TMP_627 TMP_622 TMP_621))))))) in (let TMP_616 \def 
(\lambda (k: K).(\lambda (t: T).(\lambda (_: ((\forall (v: T).(or (ex T 
(\lambda (t0: T).(eq T t (THead (Bind Abst) v t0)))) (\forall (t0: T).((eq T 
t (THead (Bind Abst) v t0)) \to (\forall (P: Prop).P))))))).(\lambda (t0: 
T).(\lambda (_: ((\forall (v: T).(or (ex T (\lambda (t1: T).(eq T t0 (THead 
(Bind Abst) v t1)))) (\forall (t1: T).((eq T t0 (THead (Bind Abst) v t1)) \to 
(\forall (P: Prop).P))))))).(\lambda (v: T).(let TMP_517 \def (Bind Abst) in 
(let H_x \def (terms_props__kind_dec k TMP_517) in (let H1 \def H_x in (let 
TMP_614 \def (Bind Abst) in (let TMP_615 \def (eq K k TMP_614) in (let 
TMP_613 \def ((eq K k (Bind Abst)) \to (\forall (P: Prop).P)) in (let TMP_610 
\def (\lambda (t1: T).(let TMP_609 \def (THead k t t0) in (let TMP_607 \def 
(Bind Abst) in (let TMP_608 \def (THead TMP_607 v t1) in (eq T TMP_609 
TMP_608))))) in (let TMP_611 \def (ex T TMP_610) in (let TMP_606 \def 
(\forall (t1: T).((eq T (THead k t t0) (THead (Bind Abst) v t1)) \to (\forall 
(P: Prop).P))) in (let TMP_612 \def (or TMP_611 TMP_606) in (let TMP_605 \def 
(\lambda (H2: (eq K k (Bind Abst))).(let TMP_604 \def (Bind Abst) in (let 
TMP_603 \def (\lambda (k0: K).(let TMP_601 \def (\lambda (t1: T).(let TMP_600 
\def (THead k0 t t0) in (let TMP_598 \def (Bind Abst) in (let TMP_599 \def 
(THead TMP_598 v t1) in (eq T TMP_600 TMP_599))))) in (let TMP_602 \def (ex T 
TMP_601) in (let TMP_597 \def (\forall (t1: T).((eq T (THead k0 t t0) (THead 
(Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (or TMP_602 TMP_597))))) in 
(let H_x0 \def (term_dec t v) in (let H3 \def H_x0 in (let TMP_595 \def (eq T 
t v) in (let TMP_594 \def ((eq T t v) \to (\forall (P: Prop).P)) in (let 
TMP_591 \def (\lambda (t1: T).(let TMP_589 \def (Bind Abst) in (let TMP_590 
\def (THead TMP_589 t t0) in (let TMP_587 \def (Bind Abst) in (let TMP_588 
\def (THead TMP_587 v t1) in (eq T TMP_590 TMP_588)))))) in (let TMP_592 \def 
(ex T TMP_591) in (let TMP_586 \def (\forall (t1: T).((eq T (THead (Bind 
Abst) t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (let 
TMP_593 \def (or TMP_592 TMP_586) in (let TMP_585 \def (\lambda (H4: (eq T t 
v)).(let TMP_584 \def (\lambda (t1: T).(let TMP_582 \def (\lambda (t2: 
T).(let TMP_580 \def (Bind Abst) in (let TMP_581 \def (THead TMP_580 t t0) in 
(let TMP_578 \def (Bind Abst) in (let TMP_579 \def (THead TMP_578 t1 t2) in 
(eq T TMP_581 TMP_579)))))) in (let TMP_583 \def (ex T TMP_582) in (let 
TMP_577 \def (\forall (t2: T).((eq T (THead (Bind Abst) t t0) (THead (Bind 
Abst) t1 t2)) \to (\forall (P: Prop).P))) in (or TMP_583 TMP_577))))) in (let 
TMP_574 \def (\lambda (t1: T).(let TMP_572 \def (Bind Abst) in (let TMP_573 
\def (THead TMP_572 t t0) in (let TMP_570 \def (Bind Abst) in (let TMP_571 
\def (THead TMP_570 t t1) in (eq T TMP_573 TMP_571)))))) in (let TMP_575 \def 
(ex T TMP_574) in (let TMP_569 \def (\forall (t1: T).((eq T (THead (Bind 
Abst) t t0) (THead (Bind Abst) t t1)) \to (\forall (P: Prop).P))) in (let 
TMP_567 \def (\lambda (t1: T).(let TMP_565 \def (Bind Abst) in (let TMP_566 
\def (THead TMP_565 t t0) in (let TMP_563 \def (Bind Abst) in (let TMP_564 
\def (THead TMP_563 t t1) in (eq T TMP_566 TMP_564)))))) in (let TMP_560 \def 
(Bind Abst) in (let TMP_561 \def (THead TMP_560 t t0) in (let TMP_562 \def 
(refl_equal T TMP_561) in (let TMP_568 \def (ex_intro T TMP_567 t0 TMP_562) 
in (let TMP_576 \def (or_introl TMP_575 TMP_569 TMP_568) in (eq_ind T t 
TMP_584 TMP_576 v H4)))))))))))) in (let TMP_559 \def (\lambda (H4: (((eq T t 
v) \to (\forall (P: Prop).P)))).(let TMP_557 \def (\lambda (t1: T).(let 
TMP_555 \def (Bind Abst) in (let TMP_556 \def (THead TMP_555 t t0) in (let 
TMP_553 \def (Bind Abst) in (let TMP_554 \def (THead TMP_553 v t1) in (eq T 
TMP_556 TMP_554)))))) in (let TMP_558 \def (ex T TMP_557) in (let TMP_552 
\def (\forall (t1: T).((eq T (THead (Bind Abst) t t0) (THead (Bind Abst) v 
t1)) \to (\forall (P: Prop).P))) in (let TMP_551 \def (\lambda (t1: 
T).(\lambda (H5: (eq T (THead (Bind Abst) t t0) (THead (Bind Abst) v 
t1))).(\lambda (P: Prop).(let TMP_544 \def (\lambda (e: T).(match e in T with 
[(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ t2 _) 
\Rightarrow t2])) in (let TMP_542 \def (Bind Abst) in (let TMP_543 \def 
(THead TMP_542 t t0) in (let TMP_540 \def (Bind Abst) in (let TMP_541 \def 
(THead TMP_540 v t1) in (let H6 \def (f_equal T T TMP_544 TMP_543 TMP_541 H5) 
in (let TMP_549 \def (\lambda (e: T).(match e in T with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) 
in (let TMP_547 \def (Bind Abst) in (let TMP_548 \def (THead TMP_547 t t0) in 
(let TMP_545 \def (Bind Abst) in (let TMP_546 \def (THead TMP_545 v t1) in 
(let H7 \def (f_equal T T TMP_549 TMP_548 TMP_546 H5) in (let TMP_550 \def 
(\lambda (H8: (eq T t v)).(H4 H8 P)) in (TMP_550 H6))))))))))))))))) in 
(or_intror TMP_558 TMP_552 TMP_551)))))) in (let TMP_596 \def (or_ind TMP_595 
TMP_594 TMP_593 TMP_585 TMP_559 H3) in (eq_ind_r K TMP_604 TMP_603 TMP_596 k 
H2))))))))))))))) in (let TMP_539 \def (\lambda (H2: (((eq K k (Bind Abst)) 
\to (\forall (P: Prop).P)))).(let TMP_537 \def (\lambda (t1: T).(let TMP_536 
\def (THead k t t0) in (let TMP_534 \def (Bind Abst) in (let TMP_535 \def 
(THead TMP_534 v t1) in (eq T TMP_536 TMP_535))))) in (let TMP_538 \def (ex T 
TMP_537) in (let TMP_533 \def (\forall (t1: T).((eq T (THead k t t0) (THead 
(Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (let TMP_532 \def (\lambda 
(t1: T).(\lambda (H3: (eq T (THead k t t0) (THead (Bind Abst) v 
t1))).(\lambda (P: Prop).(let TMP_521 \def (\lambda (e: T).(match e in T with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) in (let TMP_520 \def (THead k t t0) in (let TMP_518 \def 
(Bind Abst) in (let TMP_519 \def (THead TMP_518 v t1) in (let H4 \def 
(f_equal T K TMP_521 TMP_520 TMP_519 H3) in (let TMP_525 \def (\lambda (e: 
T).(match e in T with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | 
(THead _ t2 _) \Rightarrow t2])) in (let TMP_524 \def (THead k t t0) in (let 
TMP_522 \def (Bind Abst) in (let TMP_523 \def (THead TMP_522 v t1) in (let H5 
\def (f_equal T T TMP_525 TMP_524 TMP_523 H3) in (let TMP_529 \def (\lambda 
(e: T).(match e in T with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow 
t0 | (THead _ _ t2) \Rightarrow t2])) in (let TMP_528 \def (THead k t t0) in 
(let TMP_526 \def (Bind Abst) in (let TMP_527 \def (THead TMP_526 v t1) in 
(let H6 \def (f_equal T T TMP_529 TMP_528 TMP_527 H3) in (let TMP_530 \def 
(\lambda (_: (eq T t v)).(\lambda (H8: (eq K k (Bind Abst))).(H2 H8 P))) in 
(let TMP_531 \def (TMP_530 H5) in (TMP_531 H4))))))))))))))))))))) in 
(or_intror TMP_538 TMP_533 TMP_532)))))) in (or_ind TMP_615 TMP_613 TMP_612 
TMP_605 TMP_539 H1))))))))))))))))))) in (T_ind TMP_646 TMP_640 TMP_628 
TMP_616 u))))).

