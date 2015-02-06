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

include "basic_1/lift/props.ma".

theorem lift_gen_sort:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).(\forall (t: T).((eq T 
(TSort n) (lift h d t)) \to (eq T t (TSort n))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (t: T).(let 
TMP_2 \def (\lambda (t0: T).((eq T (TSort n) (lift h d t0)) \to (let TMP_1 
\def (TSort n) in (eq T t0 TMP_1)))) in (let TMP_5 \def (\lambda (n0: 
nat).(\lambda (H: (eq T (TSort n) (lift h d (TSort n0)))).(let TMP_3 \def 
(TSort n) in (let TMP_4 \def (TSort n0) in (sym_eq T TMP_3 TMP_4 H))))) in 
(let TMP_49 \def (\lambda (n0: nat).(\lambda (H: (eq T (TSort n) (lift h d 
(TLRef n0)))).(let TMP_6 \def (TLRef n0) in (let TMP_7 \def (TSort n) in (let 
TMP_8 \def (eq T TMP_6 TMP_7) in (let TMP_27 \def (\lambda (_: (lt n0 
d)).(let TMP_9 \def (TLRef n0) in (let TMP_10 \def (lift h d TMP_9) in (let 
TMP_12 \def (\lambda (t0: T).(let TMP_11 \def (TSort n) in (eq T TMP_11 t0))) 
in (let TMP_13 \def (TLRef n0) in (let TMP_14 \def (TSort n) in (let TMP_15 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let TMP_16 \def 
(TLRef n0) in (let TMP_17 \def (lift h d TMP_16) in (let H1 \def (eq_ind T 
TMP_14 TMP_15 I TMP_17 H) in (let TMP_18 \def (lt n0 d) in (let TMP_19 \def 
(False_ind TMP_18 H1) in (let TMP_20 \def (lift_lref_lt n0 h d TMP_19) in 
(let H1 \def (eq_ind T TMP_10 TMP_12 H TMP_13 TMP_20) in (let TMP_21 \def 
(TSort n) in (let TMP_22 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) in (let TMP_23 \def (TLRef n0) in (let H2 \def (eq_ind T TMP_21 
TMP_22 I TMP_23 H1) in (let TMP_24 \def (TLRef n0) in (let TMP_25 \def (TSort 
n) in (let TMP_26 \def (eq T TMP_24 TMP_25) in (False_ind TMP_26 
H2)))))))))))))))))))))) in (let TMP_48 \def (\lambda (_: (le d n0)).(let 
TMP_28 \def (TLRef n0) in (let TMP_29 \def (lift h d TMP_28) in (let TMP_31 
\def (\lambda (t0: T).(let TMP_30 \def (TSort n) in (eq T TMP_30 t0))) in 
(let TMP_32 \def (plus n0 h) in (let TMP_33 \def (TLRef TMP_32) in (let 
TMP_34 \def (TSort n) in (let TMP_35 \def (\lambda (ee: T).(match ee with 
[(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow False])) in (let TMP_36 \def (TLRef n0) in (let TMP_37 \def (lift 
h d TMP_36) in (let H1 \def (eq_ind T TMP_34 TMP_35 I TMP_37 H) in (let 
TMP_38 \def (le d n0) in (let TMP_39 \def (False_ind TMP_38 H1) in (let 
TMP_40 \def (lift_lref_ge n0 h d TMP_39) in (let H1 \def (eq_ind T TMP_29 
TMP_31 H TMP_33 TMP_40) in (let TMP_41 \def (TSort n) in (let TMP_42 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let TMP_43 \def 
(plus n0 h) in (let TMP_44 \def (TLRef TMP_43) in (let H2 \def (eq_ind T 
TMP_41 TMP_42 I TMP_44 H1) in (let TMP_45 \def (TLRef n0) in (let TMP_46 \def 
(TSort n) in (let TMP_47 \def (eq T TMP_45 TMP_46) in (False_ind TMP_47 
H2)))))))))))))))))))))))) in (lt_le_e n0 d TMP_8 TMP_27 TMP_48)))))))) in 
(let TMP_68 \def (\lambda (k: K).(\lambda (t0: T).(\lambda (_: (((eq T (TSort 
n) (lift h d t0)) \to (eq T t0 (TSort n))))).(\lambda (t1: T).(\lambda (_: 
(((eq T (TSort n) (lift h d t1)) \to (eq T t1 (TSort n))))).(\lambda (H1: (eq 
T (TSort n) (lift h d (THead k t0 t1)))).(let TMP_50 \def (THead k t0 t1) in 
(let TMP_51 \def (lift h d TMP_50) in (let TMP_53 \def (\lambda (t2: T).(let 
TMP_52 \def (TSort n) in (eq T TMP_52 t2))) in (let TMP_54 \def (lift h d t0) 
in (let TMP_55 \def (s k d) in (let TMP_56 \def (lift h TMP_55 t1) in (let 
TMP_57 \def (THead k TMP_54 TMP_56) in (let TMP_58 \def (lift_head k t0 t1 h 
d) in (let H2 \def (eq_ind T TMP_51 TMP_53 H1 TMP_57 TMP_58) in (let TMP_59 
\def (TSort n) in (let TMP_60 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) in (let TMP_61 \def (lift h d t0) in (let TMP_62 \def (s k d) in 
(let TMP_63 \def (lift h TMP_62 t1) in (let TMP_64 \def (THead k TMP_61 
TMP_63) in (let H3 \def (eq_ind T TMP_59 TMP_60 I TMP_64 H2) in (let TMP_65 
\def (THead k t0 t1) in (let TMP_66 \def (TSort n) in (let TMP_67 \def (eq T 
TMP_65 TMP_66) in (False_ind TMP_67 H3)))))))))))))))))))))))))) in (T_ind 
TMP_2 TMP_5 TMP_49 TMP_68 t)))))))).

theorem lift_gen_lref:
 \forall (t: T).(\forall (d: nat).(\forall (h: nat).(\forall (i: nat).((eq T 
(TLRef i) (lift h d t)) \to (or (land (lt i d) (eq T t (TLRef i))) (land (le 
(plus d h) i) (eq T t (TLRef (minus i h)))))))))
\def
 \lambda (t: T).(let TMP_11 \def (\lambda (t0: T).(\forall (d: nat).(\forall 
(h: nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t0)) \to (let TMP_1 
\def (lt i d) in (let TMP_2 \def (TLRef i) in (let TMP_3 \def (eq T t0 TMP_2) 
in (let TMP_4 \def (land TMP_1 TMP_3) in (let TMP_5 \def (plus d h) in (let 
TMP_6 \def (le TMP_5 i) in (let TMP_7 \def (minus i h) in (let TMP_8 \def 
(TLRef TMP_7) in (let TMP_9 \def (eq T t0 TMP_8) in (let TMP_10 \def (land 
TMP_6 TMP_9) in (or TMP_4 TMP_10)))))))))))))))) in (let TMP_34 \def (\lambda 
(n: nat).(\lambda (d: nat).(\lambda (h: nat).(\lambda (i: nat).(\lambda (H: 
(eq T (TLRef i) (lift h d (TSort n)))).(let TMP_12 \def (TSort n) in (let 
TMP_13 \def (lift h d TMP_12) in (let TMP_15 \def (\lambda (t0: T).(let 
TMP_14 \def (TLRef i) in (eq T TMP_14 t0))) in (let TMP_16 \def (TSort n) in 
(let TMP_17 \def (lift_sort n h d) in (let H0 \def (eq_ind T TMP_13 TMP_15 H 
TMP_16 TMP_17) in (let TMP_18 \def (TLRef i) in (let TMP_19 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
True | (THead _ _ _) \Rightarrow False])) in (let TMP_20 \def (TSort n) in 
(let H1 \def (eq_ind T TMP_18 TMP_19 I TMP_20 H0) in (let TMP_21 \def (lt i 
d) in (let TMP_22 \def (TSort n) in (let TMP_23 \def (TLRef i) in (let TMP_24 
\def (eq T TMP_22 TMP_23) in (let TMP_25 \def (land TMP_21 TMP_24) in (let 
TMP_26 \def (plus d h) in (let TMP_27 \def (le TMP_26 i) in (let TMP_28 \def 
(TSort n) in (let TMP_29 \def (minus i h) in (let TMP_30 \def (TLRef TMP_29) 
in (let TMP_31 \def (eq T TMP_28 TMP_30) in (let TMP_32 \def (land TMP_27 
TMP_31) in (let TMP_33 \def (or TMP_25 TMP_32) in (False_ind TMP_33 
H1))))))))))))))))))))))))))))) in (let TMP_162 \def (\lambda (n: 
nat).(\lambda (d: nat).(\lambda (h: nat).(\lambda (i: nat).(\lambda (H: (eq T 
(TLRef i) (lift h d (TLRef n)))).(let TMP_35 \def (lt i d) in (let TMP_36 
\def (TLRef n) in (let TMP_37 \def (TLRef i) in (let TMP_38 \def (eq T TMP_36 
TMP_37) in (let TMP_39 \def (land TMP_35 TMP_38) in (let TMP_40 \def (plus d 
h) in (let TMP_41 \def (le TMP_40 i) in (let TMP_42 \def (TLRef n) in (let 
TMP_43 \def (minus i h) in (let TMP_44 \def (TLRef TMP_43) in (let TMP_45 
\def (eq T TMP_42 TMP_44) in (let TMP_46 \def (land TMP_41 TMP_45) in (let 
TMP_47 \def (or TMP_39 TMP_46) in (let TMP_90 \def (\lambda (H0: (lt n 
d)).(let TMP_48 \def (TLRef n) in (let TMP_49 \def (lift h d TMP_48) in (let 
TMP_51 \def (\lambda (t0: T).(let TMP_50 \def (TLRef i) in (eq T TMP_50 t0))) 
in (let TMP_52 \def (TLRef n) in (let TMP_53 \def (lift_lref_lt n h d H0) in 
(let H1 \def (eq_ind T TMP_49 TMP_51 H TMP_52 TMP_53) in (let TMP_54 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) in (let TMP_55 \def (TLRef i) 
in (let TMP_56 \def (TLRef n) in (let H2 \def (f_equal T nat TMP_54 TMP_55 
TMP_56 H1) in (let TMP_69 \def (\lambda (n0: nat).(let TMP_57 \def (lt n0 d) 
in (let TMP_58 \def (TLRef n) in (let TMP_59 \def (TLRef n0) in (let TMP_60 
\def (eq T TMP_58 TMP_59) in (let TMP_61 \def (land TMP_57 TMP_60) in (let 
TMP_62 \def (plus d h) in (let TMP_63 \def (le TMP_62 n0) in (let TMP_64 \def 
(TLRef n) in (let TMP_65 \def (minus n0 h) in (let TMP_66 \def (TLRef TMP_65) 
in (let TMP_67 \def (eq T TMP_64 TMP_66) in (let TMP_68 \def (land TMP_63 
TMP_67) in (or TMP_61 TMP_68)))))))))))))) in (let TMP_70 \def (lt n d) in 
(let TMP_71 \def (TLRef n) in (let TMP_72 \def (TLRef n) in (let TMP_73 \def 
(eq T TMP_71 TMP_72) in (let TMP_74 \def (land TMP_70 TMP_73) in (let TMP_75 
\def (plus d h) in (let TMP_76 \def (le TMP_75 n) in (let TMP_77 \def (TLRef 
n) in (let TMP_78 \def (minus n h) in (let TMP_79 \def (TLRef TMP_78) in (let 
TMP_80 \def (eq T TMP_77 TMP_79) in (let TMP_81 \def (land TMP_76 TMP_80) in 
(let TMP_82 \def (lt n d) in (let TMP_83 \def (TLRef n) in (let TMP_84 \def 
(TLRef n) in (let TMP_85 \def (eq T TMP_83 TMP_84) in (let TMP_86 \def (TLRef 
n) in (let TMP_87 \def (refl_equal T TMP_86) in (let TMP_88 \def (conj TMP_82 
TMP_85 H0 TMP_87) in (let TMP_89 \def (or_introl TMP_74 TMP_81 TMP_88) in 
(eq_ind_r nat n TMP_69 TMP_89 i H2))))))))))))))))))))))))))))))))) in (let 
TMP_161 \def (\lambda (H0: (le d n)).(let TMP_91 \def (TLRef n) in (let 
TMP_92 \def (lift h d TMP_91) in (let TMP_94 \def (\lambda (t0: T).(let 
TMP_93 \def (TLRef i) in (eq T TMP_93 t0))) in (let TMP_95 \def (plus n h) in 
(let TMP_96 \def (TLRef TMP_95) in (let TMP_97 \def (lift_lref_ge n h d H0) 
in (let H1 \def (eq_ind T TMP_92 TMP_94 H TMP_96 TMP_97) in (let TMP_98 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) in (let TMP_99 \def (TLRef i) 
in (let TMP_100 \def (plus n h) in (let TMP_101 \def (TLRef TMP_100) in (let 
H2 \def (f_equal T nat TMP_98 TMP_99 TMP_101 H1) in (let TMP_102 \def (plus n 
h) in (let TMP_115 \def (\lambda (n0: nat).(let TMP_103 \def (lt n0 d) in 
(let TMP_104 \def (TLRef n) in (let TMP_105 \def (TLRef n0) in (let TMP_106 
\def (eq T TMP_104 TMP_105) in (let TMP_107 \def (land TMP_103 TMP_106) in 
(let TMP_108 \def (plus d h) in (let TMP_109 \def (le TMP_108 n0) in (let 
TMP_110 \def (TLRef n) in (let TMP_111 \def (minus n0 h) in (let TMP_112 \def 
(TLRef TMP_111) in (let TMP_113 \def (eq T TMP_110 TMP_112) in (let TMP_114 
\def (land TMP_109 TMP_113) in (or TMP_107 TMP_114)))))))))))))) in (let 
TMP_130 \def (\lambda (n0: nat).(let TMP_116 \def (plus n h) in (let TMP_117 
\def (lt TMP_116 d) in (let TMP_118 \def (TLRef n) in (let TMP_119 \def (plus 
n h) in (let TMP_120 \def (TLRef TMP_119) in (let TMP_121 \def (eq T TMP_118 
TMP_120) in (let TMP_122 \def (land TMP_117 TMP_121) in (let TMP_123 \def 
(plus d h) in (let TMP_124 \def (plus n h) in (let TMP_125 \def (le TMP_123 
TMP_124) in (let TMP_126 \def (TLRef n) in (let TMP_127 \def (TLRef n0) in 
(let TMP_128 \def (eq T TMP_126 TMP_127) in (let TMP_129 \def (land TMP_125 
TMP_128) in (or TMP_122 TMP_129)))))))))))))))) in (let TMP_131 \def (plus n 
h) in (let TMP_132 \def (lt TMP_131 d) in (let TMP_133 \def (TLRef n) in (let 
TMP_134 \def (plus n h) in (let TMP_135 \def (TLRef TMP_134) in (let TMP_136 
\def (eq T TMP_133 TMP_135) in (let TMP_137 \def (land TMP_132 TMP_136) in 
(let TMP_138 \def (plus d h) in (let TMP_139 \def (plus n h) in (let TMP_140 
\def (le TMP_138 TMP_139) in (let TMP_141 \def (TLRef n) in (let TMP_142 \def 
(TLRef n) in (let TMP_143 \def (eq T TMP_141 TMP_142) in (let TMP_144 \def 
(land TMP_140 TMP_143) in (let TMP_145 \def (plus d h) in (let TMP_146 \def 
(plus n h) in (let TMP_147 \def (le TMP_145 TMP_146) in (let TMP_148 \def 
(TLRef n) in (let TMP_149 \def (TLRef n) in (let TMP_150 \def (eq T TMP_148 
TMP_149) in (let TMP_151 \def (le_n h) in (let TMP_152 \def (le_plus_plus d n 
h h H0 TMP_151) in (let TMP_153 \def (TLRef n) in (let TMP_154 \def 
(refl_equal T TMP_153) in (let TMP_155 \def (conj TMP_147 TMP_150 TMP_152 
TMP_154) in (let TMP_156 \def (or_intror TMP_137 TMP_144 TMP_155) in (let 
TMP_157 \def (plus n h) in (let TMP_158 \def (minus TMP_157 h) in (let 
TMP_159 \def (minus_plus_r n h) in (let TMP_160 \def (eq_ind_r nat n TMP_130 
TMP_156 TMP_158 TMP_159) in (eq_ind_r nat TMP_102 TMP_115 TMP_160 i 
H2))))))))))))))))))))))))))))))))))))))))))))))) in (lt_le_e n d TMP_47 
TMP_90 TMP_161))))))))))))))))))))) in (let TMP_191 \def (\lambda (k: 
K).(\lambda (t0: T).(\lambda (_: ((\forall (d: nat).(\forall (h: 
nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t0)) \to (or (land (lt i d) 
(eq T t0 (TLRef i))) (land (le (plus d h) i) (eq T t0 (TLRef (minus i 
h))))))))))).(\lambda (t1: T).(\lambda (_: ((\forall (d: nat).(\forall (h: 
nat).(\forall (i: nat).((eq T (TLRef i) (lift h d t1)) \to (or (land (lt i d) 
(eq T t1 (TLRef i))) (land (le (plus d h) i) (eq T t1 (TLRef (minus i 
h))))))))))).(\lambda (d: nat).(\lambda (h: nat).(\lambda (i: nat).(\lambda 
(H1: (eq T (TLRef i) (lift h d (THead k t0 t1)))).(let TMP_163 \def (THead k 
t0 t1) in (let TMP_164 \def (lift h d TMP_163) in (let TMP_166 \def (\lambda 
(t2: T).(let TMP_165 \def (TLRef i) in (eq T TMP_165 t2))) in (let TMP_167 
\def (lift h d t0) in (let TMP_168 \def (s k d) in (let TMP_169 \def (lift h 
TMP_168 t1) in (let TMP_170 \def (THead k TMP_167 TMP_169) in (let TMP_171 
\def (lift_head k t0 t1 h d) in (let H2 \def (eq_ind T TMP_164 TMP_166 H1 
TMP_170 TMP_171) in (let TMP_172 \def (TLRef i) in (let TMP_173 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
True | (THead _ _ _) \Rightarrow False])) in (let TMP_174 \def (lift h d t0) 
in (let TMP_175 \def (s k d) in (let TMP_176 \def (lift h TMP_175 t1) in (let 
TMP_177 \def (THead k TMP_174 TMP_176) in (let H3 \def (eq_ind T TMP_172 
TMP_173 I TMP_177 H2) in (let TMP_178 \def (lt i d) in (let TMP_179 \def 
(THead k t0 t1) in (let TMP_180 \def (TLRef i) in (let TMP_181 \def (eq T 
TMP_179 TMP_180) in (let TMP_182 \def (land TMP_178 TMP_181) in (let TMP_183 
\def (plus d h) in (let TMP_184 \def (le TMP_183 i) in (let TMP_185 \def 
(THead k t0 t1) in (let TMP_186 \def (minus i h) in (let TMP_187 \def (TLRef 
TMP_186) in (let TMP_188 \def (eq T TMP_185 TMP_187) in (let TMP_189 \def 
(land TMP_184 TMP_188) in (let TMP_190 \def (or TMP_182 TMP_189) in 
(False_ind TMP_190 H3))))))))))))))))))))))))))))))))))))))) in (T_ind TMP_11 
TMP_34 TMP_162 TMP_191 t))))).

theorem lift_gen_lref_lt:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((lt n d) \to (\forall 
(t: T).((eq T (TLRef n) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (lt n 
d)).(\lambda (t: T).(\lambda (H0: (eq T (TLRef n) (lift h d t))).(let H_x 
\def (lift_gen_lref t d h n H0) in (let H1 \def H_x in (let TMP_1 \def (lt n 
d) in (let TMP_2 \def (TLRef n) in (let TMP_3 \def (eq T t TMP_2) in (let 
TMP_4 \def (land TMP_1 TMP_3) in (let TMP_5 \def (plus d h) in (let TMP_6 
\def (le TMP_5 n) in (let TMP_7 \def (minus n h) in (let TMP_8 \def (TLRef 
TMP_7) in (let TMP_9 \def (eq T t TMP_8) in (let TMP_10 \def (land TMP_6 
TMP_9) in (let TMP_11 \def (TLRef n) in (let TMP_12 \def (eq T t TMP_11) in 
(let TMP_24 \def (\lambda (H2: (land (lt n d) (eq T t (TLRef n)))).(let 
TMP_13 \def (lt n d) in (let TMP_14 \def (TLRef n) in (let TMP_15 \def (eq T 
t TMP_14) in (let TMP_16 \def (TLRef n) in (let TMP_17 \def (eq T t TMP_16) 
in (let TMP_23 \def (\lambda (_: (lt n d)).(\lambda (H4: (eq T t (TLRef 
n))).(let TMP_18 \def (TLRef n) in (let TMP_20 \def (\lambda (t0: T).(let 
TMP_19 \def (TLRef n) in (eq T t0 TMP_19))) in (let TMP_21 \def (TLRef n) in 
(let TMP_22 \def (refl_equal T TMP_21) in (eq_ind_r T TMP_18 TMP_20 TMP_22 t 
H4))))))) in (land_ind TMP_13 TMP_15 TMP_17 TMP_23 H2)))))))) in (let TMP_47 
\def (\lambda (H2: (land (le (plus d h) n) (eq T t (TLRef (minus n 
h))))).(let TMP_25 \def (plus d h) in (let TMP_26 \def (le TMP_25 n) in (let 
TMP_27 \def (minus n h) in (let TMP_28 \def (TLRef TMP_27) in (let TMP_29 
\def (eq T t TMP_28) in (let TMP_30 \def (TLRef n) in (let TMP_31 \def (eq T 
t TMP_30) in (let TMP_46 \def (\lambda (H3: (le (plus d h) n)).(\lambda (H4: 
(eq T t (TLRef (minus n h)))).(let TMP_32 \def (minus n h) in (let TMP_33 
\def (TLRef TMP_32) in (let TMP_35 \def (\lambda (t0: T).(let TMP_34 \def 
(TLRef n) in (eq T t0 TMP_34))) in (let TMP_36 \def (plus d h) in (let TMP_37 
\def (minus n h) in (let TMP_38 \def (TLRef TMP_37) in (let TMP_39 \def 
(TLRef n) in (let TMP_40 \def (eq T TMP_38 TMP_39) in (let TMP_41 \def (plus 
d h) in (let TMP_42 \def (S n) in (let TMP_43 \def (le_plus_trans TMP_42 d h 
H) in (let TMP_44 \def (lt_le_S n TMP_41 TMP_43) in (let TMP_45 \def 
(le_false TMP_36 n TMP_40 H3 TMP_44) in (eq_ind_r T TMP_33 TMP_35 TMP_45 t 
H4)))))))))))))))) in (land_ind TMP_26 TMP_29 TMP_31 TMP_46 H2)))))))))) in 
(or_ind TMP_4 TMP_10 TMP_12 TMP_24 TMP_47 H1)))))))))))))))))))))).

theorem lift_gen_lref_false:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to ((lt n 
(plus d h)) \to (\forall (t: T).((eq T (TLRef n) (lift h d t)) \to (\forall 
(P: Prop).P)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (H0: (lt n (plus d h))).(\lambda (t: T).(\lambda (H1: (eq T 
(TLRef n) (lift h d t))).(\lambda (P: Prop).(let H_x \def (lift_gen_lref t d 
h n H1) in (let H2 \def H_x in (let TMP_1 \def (lt n d) in (let TMP_2 \def 
(TLRef n) in (let TMP_3 \def (eq T t TMP_2) in (let TMP_4 \def (land TMP_1 
TMP_3) in (let TMP_5 \def (plus d h) in (let TMP_6 \def (le TMP_5 n) in (let 
TMP_7 \def (minus n h) in (let TMP_8 \def (TLRef TMP_7) in (let TMP_9 \def 
(eq T t TMP_8) in (let TMP_10 \def (land TMP_6 TMP_9) in (let TMP_15 \def 
(\lambda (H3: (land (lt n d) (eq T t (TLRef n)))).(let TMP_11 \def (lt n d) 
in (let TMP_12 \def (TLRef n) in (let TMP_13 \def (eq T t TMP_12) in (let 
TMP_14 \def (\lambda (H4: (lt n d)).(\lambda (_: (eq T t (TLRef 
n))).(le_false d n P H H4))) in (land_ind TMP_11 TMP_13 P TMP_14 H3)))))) in 
(let TMP_23 \def (\lambda (H3: (land (le (plus d h) n) (eq T t (TLRef (minus 
n h))))).(let TMP_16 \def (plus d h) in (let TMP_17 \def (le TMP_16 n) in 
(let TMP_18 \def (minus n h) in (let TMP_19 \def (TLRef TMP_18) in (let 
TMP_20 \def (eq T t TMP_19) in (let TMP_22 \def (\lambda (H4: (le (plus d h) 
n)).(\lambda (_: (eq T t (TLRef (minus n h)))).(let TMP_21 \def (plus d h) in 
(le_false TMP_21 n P H4 H0)))) in (land_ind TMP_17 TMP_20 P TMP_22 H3)))))))) 
in (or_ind TMP_4 TMP_10 P TMP_15 TMP_23 H2)))))))))))))))))))))).

theorem lift_gen_lref_ge:
 \forall (h: nat).(\forall (d: nat).(\forall (n: nat).((le d n) \to (\forall 
(t: T).((eq T (TLRef (plus n h)) (lift h d t)) \to (eq T t (TLRef n)))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (n: nat).(\lambda (H: (le d 
n)).(\lambda (t: T).(\lambda (H0: (eq T (TLRef (plus n h)) (lift h d 
t))).(let TMP_1 \def (plus n h) in (let H_x \def (lift_gen_lref t d h TMP_1 
H0) in (let H1 \def H_x in (let TMP_2 \def (plus n h) in (let TMP_3 \def (lt 
TMP_2 d) in (let TMP_4 \def (plus n h) in (let TMP_5 \def (TLRef TMP_4) in 
(let TMP_6 \def (eq T t TMP_5) in (let TMP_7 \def (land TMP_3 TMP_6) in (let 
TMP_8 \def (plus d h) in (let TMP_9 \def (plus n h) in (let TMP_10 \def (le 
TMP_8 TMP_9) in (let TMP_11 \def (plus n h) in (let TMP_12 \def (minus TMP_11 
h) in (let TMP_13 \def (TLRef TMP_12) in (let TMP_14 \def (eq T t TMP_13) in 
(let TMP_15 \def (land TMP_10 TMP_14) in (let TMP_16 \def (TLRef n) in (let 
TMP_17 \def (eq T t TMP_16) in (let TMP_41 \def (\lambda (H2: (land (lt (plus 
n h) d) (eq T t (TLRef (plus n h))))).(let TMP_18 \def (plus n h) in (let 
TMP_19 \def (lt TMP_18 d) in (let TMP_20 \def (plus n h) in (let TMP_21 \def 
(TLRef TMP_20) in (let TMP_22 \def (eq T t TMP_21) in (let TMP_23 \def (TLRef 
n) in (let TMP_24 \def (eq T t TMP_23) in (let TMP_40 \def (\lambda (H3: (lt 
(plus n h) d)).(\lambda (H4: (eq T t (TLRef (plus n h)))).(let TMP_25 \def 
(plus n h) in (let TMP_26 \def (TLRef TMP_25) in (let TMP_28 \def (\lambda 
(t0: T).(let TMP_27 \def (TLRef n) in (eq T t0 TMP_27))) in (let TMP_29 \def 
(plus n h) in (let TMP_30 \def (TLRef TMP_29) in (let TMP_31 \def (TLRef n) 
in (let TMP_32 \def (eq T TMP_30 TMP_31) in (let TMP_33 \def (plus n h) in 
(let TMP_34 \def (plus d h) in (let TMP_35 \def (le_plus_l d h) in (let 
TMP_36 \def (lt_le_trans TMP_33 d TMP_34 H3 TMP_35) in (let TMP_37 \def 
(simpl_lt_plus_r h n d TMP_36) in (let TMP_38 \def (lt_le_S n d TMP_37) in 
(let TMP_39 \def (le_false d n TMP_32 H TMP_38) in (eq_ind_r T TMP_26 TMP_28 
TMP_39 t H4))))))))))))))))) in (land_ind TMP_19 TMP_22 TMP_24 TMP_40 
H2)))))))))) in (let TMP_61 \def (\lambda (H2: (land (le (plus d h) (plus n 
h)) (eq T t (TLRef (minus (plus n h) h))))).(let TMP_42 \def (plus d h) in 
(let TMP_43 \def (plus n h) in (let TMP_44 \def (le TMP_42 TMP_43) in (let 
TMP_45 \def (plus n h) in (let TMP_46 \def (minus TMP_45 h) in (let TMP_47 
\def (TLRef TMP_46) in (let TMP_48 \def (eq T t TMP_47) in (let TMP_49 \def 
(TLRef n) in (let TMP_50 \def (eq T t TMP_49) in (let TMP_60 \def (\lambda 
(_: (le (plus d h) (plus n h))).(\lambda (H4: (eq T t (TLRef (minus (plus n 
h) h)))).(let TMP_51 \def (plus n h) in (let TMP_52 \def (minus TMP_51 h) in 
(let TMP_53 \def (TLRef TMP_52) in (let TMP_55 \def (\lambda (t0: T).(let 
TMP_54 \def (TLRef n) in (eq T t0 TMP_54))) in (let TMP_56 \def (plus n h) in 
(let TMP_57 \def (minus TMP_56 h) in (let TMP_58 \def (minus_plus_r n h) in 
(let TMP_59 \def (f_equal nat T TLRef TMP_57 n TMP_58) in (eq_ind_r T TMP_53 
TMP_55 TMP_59 t H4))))))))))) in (land_ind TMP_44 TMP_48 TMP_50 TMP_60 
H2)))))))))))) in (or_ind TMP_7 TMP_15 TMP_17 TMP_41 TMP_61 
H1))))))))))))))))))))))))))).

theorem lift_gen_head:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead k u t) (lift h d x)) \to (ex3_2 T T 
(\lambda (y: T).(\lambda (z: T).(eq T x (THead k y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (s k d) z)))))))))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(let TMP_8 
\def (\lambda (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (THead k u 
t) (lift h d t0)) \to (let TMP_2 \def (\lambda (y: T).(\lambda (z: T).(let 
TMP_1 \def (THead k y z) in (eq T t0 TMP_1)))) in (let TMP_4 \def (\lambda 
(y: T).(\lambda (_: T).(let TMP_3 \def (lift h d y) in (eq T u TMP_3)))) in 
(let TMP_7 \def (\lambda (_: T).(\lambda (z: T).(let TMP_5 \def (s k d) in 
(let TMP_6 \def (lift h TMP_5 z) in (eq T t TMP_6))))) in (ex3_2 T T TMP_2 
TMP_4 TMP_7)))))))) in (let TMP_27 \def (\lambda (n: nat).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k u t) (lift h d (TSort 
n)))).(let TMP_9 \def (TSort n) in (let TMP_10 \def (lift h d TMP_9) in (let 
TMP_12 \def (\lambda (t0: T).(let TMP_11 \def (THead k u t) in (eq T TMP_11 
t0))) in (let TMP_13 \def (TSort n) in (let TMP_14 \def (lift_sort n h d) in 
(let H0 \def (eq_ind T TMP_10 TMP_12 H TMP_13 TMP_14) in (let TMP_15 \def 
(THead k u t) in (let TMP_16 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) in (let TMP_17 \def (TSort n) in (let H1 \def (eq_ind T TMP_15 TMP_16 
I TMP_17 H0) in (let TMP_20 \def (\lambda (y: T).(\lambda (z: T).(let TMP_18 
\def (TSort n) in (let TMP_19 \def (THead k y z) in (eq T TMP_18 TMP_19))))) 
in (let TMP_22 \def (\lambda (y: T).(\lambda (_: T).(let TMP_21 \def (lift h 
d y) in (eq T u TMP_21)))) in (let TMP_25 \def (\lambda (_: T).(\lambda (z: 
T).(let TMP_23 \def (s k d) in (let TMP_24 \def (lift h TMP_23 z) in (eq T t 
TMP_24))))) in (let TMP_26 \def (ex3_2 T T TMP_20 TMP_22 TMP_25) in 
(False_ind TMP_26 H1))))))))))))))))))) in (let TMP_77 \def (\lambda (n: 
nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (THead k u t) 
(lift h d (TLRef n)))).(let TMP_30 \def (\lambda (y: T).(\lambda (z: T).(let 
TMP_28 \def (TLRef n) in (let TMP_29 \def (THead k y z) in (eq T TMP_28 
TMP_29))))) in (let TMP_32 \def (\lambda (y: T).(\lambda (_: T).(let TMP_31 
\def (lift h d y) in (eq T u TMP_31)))) in (let TMP_35 \def (\lambda (_: 
T).(\lambda (z: T).(let TMP_33 \def (s k d) in (let TMP_34 \def (lift h 
TMP_33 z) in (eq T t TMP_34))))) in (let TMP_36 \def (ex3_2 T T TMP_30 TMP_32 
TMP_35) in (let TMP_55 \def (\lambda (H0: (lt n d)).(let TMP_37 \def (TLRef 
n) in (let TMP_38 \def (lift h d TMP_37) in (let TMP_40 \def (\lambda (t0: 
T).(let TMP_39 \def (THead k u t) in (eq T TMP_39 t0))) in (let TMP_41 \def 
(TLRef n) in (let TMP_42 \def (lift_lref_lt n h d H0) in (let H1 \def (eq_ind 
T TMP_38 TMP_40 H TMP_41 TMP_42) in (let TMP_43 \def (THead k u t) in (let 
TMP_44 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let 
TMP_45 \def (TLRef n) in (let H2 \def (eq_ind T TMP_43 TMP_44 I TMP_45 H1) in 
(let TMP_48 \def (\lambda (y: T).(\lambda (z: T).(let TMP_46 \def (TLRef n) 
in (let TMP_47 \def (THead k y z) in (eq T TMP_46 TMP_47))))) in (let TMP_50 
\def (\lambda (y: T).(\lambda (_: T).(let TMP_49 \def (lift h d y) in (eq T u 
TMP_49)))) in (let TMP_53 \def (\lambda (_: T).(\lambda (z: T).(let TMP_51 
\def (s k d) in (let TMP_52 \def (lift h TMP_51 z) in (eq T t TMP_52))))) in 
(let TMP_54 \def (ex3_2 T T TMP_48 TMP_50 TMP_53) in (False_ind TMP_54 
H2)))))))))))))))) in (let TMP_76 \def (\lambda (H0: (le d n)).(let TMP_56 
\def (TLRef n) in (let TMP_57 \def (lift h d TMP_56) in (let TMP_59 \def 
(\lambda (t0: T).(let TMP_58 \def (THead k u t) in (eq T TMP_58 t0))) in (let 
TMP_60 \def (plus n h) in (let TMP_61 \def (TLRef TMP_60) in (let TMP_62 \def 
(lift_lref_ge n h d H0) in (let H1 \def (eq_ind T TMP_57 TMP_59 H TMP_61 
TMP_62) in (let TMP_63 \def (THead k u t) in (let TMP_64 \def (\lambda (ee: 
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) in (let TMP_65 \def (plus n h) in (let 
TMP_66 \def (TLRef TMP_65) in (let H2 \def (eq_ind T TMP_63 TMP_64 I TMP_66 
H1) in (let TMP_69 \def (\lambda (y: T).(\lambda (z: T).(let TMP_67 \def 
(TLRef n) in (let TMP_68 \def (THead k y z) in (eq T TMP_67 TMP_68))))) in 
(let TMP_71 \def (\lambda (y: T).(\lambda (_: T).(let TMP_70 \def (lift h d 
y) in (eq T u TMP_70)))) in (let TMP_74 \def (\lambda (_: T).(\lambda (z: 
T).(let TMP_72 \def (s k d) in (let TMP_73 \def (lift h TMP_72 z) in (eq T t 
TMP_73))))) in (let TMP_75 \def (ex3_2 T T TMP_69 TMP_71 TMP_74) in 
(False_ind TMP_75 H2)))))))))))))))))) in (lt_le_e n d TMP_36 TMP_55 
TMP_76))))))))))) in (let TMP_205 \def (\lambda (k0: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) 
(lift h d t0)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t0 (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))))))).(\lambda (t1: 
T).(\lambda (H0: ((\forall (h: nat).(\forall (d: nat).((eq T (THead k u t) 
(lift h d t1)) \to (ex3_2 T T (\lambda (y: T).(\lambda (z: T).(eq T t1 (THead 
k y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t (lift h (s k d) z)))))))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq T (THead k u t) (lift h d (THead k0 
t0 t1)))).(let TMP_78 \def (THead k0 t0 t1) in (let TMP_79 \def (lift h d 
TMP_78) in (let TMP_81 \def (\lambda (t2: T).(let TMP_80 \def (THead k u t) 
in (eq T TMP_80 t2))) in (let TMP_82 \def (lift h d t0) in (let TMP_83 \def 
(s k0 d) in (let TMP_84 \def (lift h TMP_83 t1) in (let TMP_85 \def (THead k0 
TMP_82 TMP_84) in (let TMP_86 \def (lift_head k0 t0 t1 h d) in (let H2 \def 
(eq_ind T TMP_79 TMP_81 H1 TMP_85 TMP_86) in (let TMP_87 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead 
k1 _ _) \Rightarrow k1])) in (let TMP_88 \def (THead k u t) in (let TMP_89 
\def (lift h d t0) in (let TMP_90 \def (s k0 d) in (let TMP_91 \def (lift h 
TMP_90 t1) in (let TMP_92 \def (THead k0 TMP_89 TMP_91) in (let H3 \def 
(f_equal T K TMP_87 TMP_88 TMP_92 H2) in (let TMP_93 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead 
_ t2 _) \Rightarrow t2])) in (let TMP_94 \def (THead k u t) in (let TMP_95 
\def (lift h d t0) in (let TMP_96 \def (s k0 d) in (let TMP_97 \def (lift h 
TMP_96 t1) in (let TMP_98 \def (THead k0 TMP_95 TMP_97) in (let H4 \def 
(f_equal T T TMP_93 TMP_94 TMP_98 H2) in (let TMP_99 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead 
_ _ t2) \Rightarrow t2])) in (let TMP_100 \def (THead k u t) in (let TMP_101 
\def (lift h d t0) in (let TMP_102 \def (s k0 d) in (let TMP_103 \def (lift h 
TMP_102 t1) in (let TMP_104 \def (THead k0 TMP_101 TMP_103) in (let H5 \def 
(f_equal T T TMP_99 TMP_100 TMP_104 H2) in (let TMP_203 \def (\lambda (H6: 
(eq T u (lift h d t0))).(\lambda (H7: (eq K k k0)).(let TMP_107 \def (\lambda 
(k1: K).(let TMP_105 \def (s k1 d) in (let TMP_106 \def (lift h TMP_105 t1) 
in (eq T t TMP_106)))) in (let H8 \def (eq_ind_r K k0 TMP_107 H5 k H7) in 
(let TMP_116 \def (\lambda (k1: K).(let TMP_110 \def (\lambda (y: T).(\lambda 
(z: T).(let TMP_108 \def (THead k1 t0 t1) in (let TMP_109 \def (THead k y z) 
in (eq T TMP_108 TMP_109))))) in (let TMP_112 \def (\lambda (y: T).(\lambda 
(_: T).(let TMP_111 \def (lift h d y) in (eq T u TMP_111)))) in (let TMP_115 
\def (\lambda (_: T).(\lambda (z: T).(let TMP_113 \def (s k d) in (let 
TMP_114 \def (lift h TMP_113 z) in (eq T t TMP_114))))) in (ex3_2 T T TMP_110 
TMP_112 TMP_115))))) in (let TMP_124 \def (\lambda (t2: T).(\forall (h0: 
nat).(\forall (d0: nat).((eq T (THead k u t2) (lift h0 d0 t1)) \to (let 
TMP_118 \def (\lambda (y: T).(\lambda (z: T).(let TMP_117 \def (THead k y z) 
in (eq T t1 TMP_117)))) in (let TMP_120 \def (\lambda (y: T).(\lambda (_: 
T).(let TMP_119 \def (lift h0 d0 y) in (eq T u TMP_119)))) in (let TMP_123 
\def (\lambda (_: T).(\lambda (z: T).(let TMP_121 \def (s k d0) in (let 
TMP_122 \def (lift h0 TMP_121 z) in (eq T t2 TMP_122))))) in (ex3_2 T T 
TMP_118 TMP_120 TMP_123)))))))) in (let TMP_125 \def (s k d) in (let TMP_126 
\def (lift h TMP_125 t1) in (let H9 \def (eq_ind T t TMP_124 H0 TMP_126 H8) 
in (let TMP_134 \def (\lambda (t2: T).(\forall (h0: nat).(\forall (d0: 
nat).((eq T (THead k u t2) (lift h0 d0 t0)) \to (let TMP_128 \def (\lambda 
(y: T).(\lambda (z: T).(let TMP_127 \def (THead k y z) in (eq T t0 
TMP_127)))) in (let TMP_130 \def (\lambda (y: T).(\lambda (_: T).(let TMP_129 
\def (lift h0 d0 y) in (eq T u TMP_129)))) in (let TMP_133 \def (\lambda (_: 
T).(\lambda (z: T).(let TMP_131 \def (s k d0) in (let TMP_132 \def (lift h0 
TMP_131 z) in (eq T t2 TMP_132))))) in (ex3_2 T T TMP_128 TMP_130 
TMP_133)))))))) in (let TMP_135 \def (s k d) in (let TMP_136 \def (lift h 
TMP_135 t1) in (let H10 \def (eq_ind T t TMP_134 H TMP_136 H8) in (let 
TMP_137 \def (s k d) in (let TMP_138 \def (lift h TMP_137 t1) in (let TMP_147 
\def (\lambda (t2: T).(let TMP_141 \def (\lambda (y: T).(\lambda (z: T).(let 
TMP_139 \def (THead k t0 t1) in (let TMP_140 \def (THead k y z) in (eq T 
TMP_139 TMP_140))))) in (let TMP_143 \def (\lambda (y: T).(\lambda (_: 
T).(let TMP_142 \def (lift h d y) in (eq T u TMP_142)))) in (let TMP_146 \def 
(\lambda (_: T).(\lambda (z: T).(let TMP_144 \def (s k d) in (let TMP_145 
\def (lift h TMP_144 z) in (eq T t2 TMP_145))))) in (ex3_2 T T TMP_141 
TMP_143 TMP_146))))) in (let TMP_157 \def (\lambda (t2: T).(\forall (h0: 
nat).(\forall (d0: nat).((eq T (THead k t2 (lift h (s k d) t1)) (lift h0 d0 
t0)) \to (let TMP_149 \def (\lambda (y: T).(\lambda (z: T).(let TMP_148 \def 
(THead k y z) in (eq T t0 TMP_148)))) in (let TMP_151 \def (\lambda (y: 
T).(\lambda (_: T).(let TMP_150 \def (lift h0 d0 y) in (eq T t2 TMP_150)))) 
in (let TMP_156 \def (\lambda (_: T).(\lambda (z: T).(let TMP_152 \def (s k 
d) in (let TMP_153 \def (lift h TMP_152 t1) in (let TMP_154 \def (s k d0) in 
(let TMP_155 \def (lift h0 TMP_154 z) in (eq T TMP_153 TMP_155))))))) in 
(ex3_2 T T TMP_149 TMP_151 TMP_156)))))))) in (let TMP_158 \def (lift h d t0) 
in (let H11 \def (eq_ind T u TMP_157 H10 TMP_158 H6) in (let TMP_168 \def 
(\lambda (t2: T).(\forall (h0: nat).(\forall (d0: nat).((eq T (THead k t2 
(lift h (s k d) t1)) (lift h0 d0 t1)) \to (let TMP_160 \def (\lambda (y: 
T).(\lambda (z: T).(let TMP_159 \def (THead k y z) in (eq T t1 TMP_159)))) in 
(let TMP_162 \def (\lambda (y: T).(\lambda (_: T).(let TMP_161 \def (lift h0 
d0 y) in (eq T t2 TMP_161)))) in (let TMP_167 \def (\lambda (_: T).(\lambda 
(z: T).(let TMP_163 \def (s k d) in (let TMP_164 \def (lift h TMP_163 t1) in 
(let TMP_165 \def (s k d0) in (let TMP_166 \def (lift h0 TMP_165 z) in (eq T 
TMP_164 TMP_166))))))) in (ex3_2 T T TMP_160 TMP_162 TMP_167)))))))) in (let 
TMP_169 \def (lift h d t0) in (let H12 \def (eq_ind T u TMP_168 H9 TMP_169 
H6) in (let TMP_170 \def (lift h d t0) in (let TMP_181 \def (\lambda (t2: 
T).(let TMP_173 \def (\lambda (y: T).(\lambda (z: T).(let TMP_171 \def (THead 
k t0 t1) in (let TMP_172 \def (THead k y z) in (eq T TMP_171 TMP_172))))) in 
(let TMP_175 \def (\lambda (y: T).(\lambda (_: T).(let TMP_174 \def (lift h d 
y) in (eq T t2 TMP_174)))) in (let TMP_180 \def (\lambda (_: T).(\lambda (z: 
T).(let TMP_176 \def (s k d) in (let TMP_177 \def (lift h TMP_176 t1) in (let 
TMP_178 \def (s k d) in (let TMP_179 \def (lift h TMP_178 z) in (eq T TMP_177 
TMP_179))))))) in (ex3_2 T T TMP_173 TMP_175 TMP_180))))) in (let TMP_184 
\def (\lambda (y: T).(\lambda (z: T).(let TMP_182 \def (THead k t0 t1) in 
(let TMP_183 \def (THead k y z) in (eq T TMP_182 TMP_183))))) in (let TMP_187 
\def (\lambda (y: T).(\lambda (_: T).(let TMP_185 \def (lift h d t0) in (let 
TMP_186 \def (lift h d y) in (eq T TMP_185 TMP_186))))) in (let TMP_192 \def 
(\lambda (_: T).(\lambda (z: T).(let TMP_188 \def (s k d) in (let TMP_189 
\def (lift h TMP_188 t1) in (let TMP_190 \def (s k d) in (let TMP_191 \def 
(lift h TMP_190 z) in (eq T TMP_189 TMP_191))))))) in (let TMP_193 \def 
(THead k t0 t1) in (let TMP_194 \def (refl_equal T TMP_193) in (let TMP_195 
\def (lift h d t0) in (let TMP_196 \def (refl_equal T TMP_195) in (let 
TMP_197 \def (s k d) in (let TMP_198 \def (lift h TMP_197 t1) in (let TMP_199 
\def (refl_equal T TMP_198) in (let TMP_200 \def (ex3_2_intro T T TMP_184 
TMP_187 TMP_192 t0 t1 TMP_194 TMP_196 TMP_199) in (let TMP_201 \def (eq_ind_r 
T TMP_170 TMP_181 TMP_200 u H6) in (let TMP_202 \def (eq_ind_r T TMP_138 
TMP_147 TMP_201 t H8) in (eq_ind K k TMP_116 TMP_202 k0 
H7)))))))))))))))))))))))))))))))))))))) in (let TMP_204 \def (TMP_203 H4) in 
(TMP_204 H3))))))))))))))))))))))))))))))))))))))))) in (T_ind TMP_8 TMP_27 
TMP_77 TMP_205 x)))))))).

theorem lift_gen_bind:
 \forall (b: B).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Bind b) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Bind b) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h (S d) z)))))))))))
\def
 \lambda (b: B).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u t) (lift h d 
x))).(let TMP_1 \def (Bind b) in (let H_x \def (lift_gen_head TMP_1 u t x h d 
H) in (let H0 \def H_x in (let TMP_4 \def (\lambda (y: T).(\lambda (z: 
T).(let TMP_2 \def (Bind b) in (let TMP_3 \def (THead TMP_2 y z) in (eq T x 
TMP_3))))) in (let TMP_6 \def (\lambda (y: T).(\lambda (_: T).(let TMP_5 \def 
(lift h d y) in (eq T u TMP_5)))) in (let TMP_9 \def (\lambda (_: T).(\lambda 
(z: T).(let TMP_7 \def (S d) in (let TMP_8 \def (lift h TMP_7 z) in (eq T t 
TMP_8))))) in (let TMP_12 \def (\lambda (y: T).(\lambda (z: T).(let TMP_10 
\def (Bind b) in (let TMP_11 \def (THead TMP_10 y z) in (eq T x TMP_11))))) 
in (let TMP_14 \def (\lambda (y: T).(\lambda (_: T).(let TMP_13 \def (lift h 
d y) in (eq T u TMP_13)))) in (let TMP_17 \def (\lambda (_: T).(\lambda (z: 
T).(let TMP_15 \def (S d) in (let TMP_16 \def (lift h TMP_15 z) in (eq T t 
TMP_16))))) in (let TMP_18 \def (ex3_2 T T TMP_12 TMP_14 TMP_17) in (let 
TMP_81 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T x (THead 
(Bind b) x0 x1))).(\lambda (H2: (eq T u (lift h d x0))).(\lambda (H3: (eq T t 
(lift h (S d) x1))).(let TMP_19 \def (Bind b) in (let TMP_20 \def (THead 
TMP_19 x0 x1) in (let TMP_29 \def (\lambda (t0: T).(let TMP_23 \def (\lambda 
(y: T).(\lambda (z: T).(let TMP_21 \def (Bind b) in (let TMP_22 \def (THead 
TMP_21 y z) in (eq T t0 TMP_22))))) in (let TMP_25 \def (\lambda (y: 
T).(\lambda (_: T).(let TMP_24 \def (lift h d y) in (eq T u TMP_24)))) in 
(let TMP_28 \def (\lambda (_: T).(\lambda (z: T).(let TMP_26 \def (S d) in 
(let TMP_27 \def (lift h TMP_26 z) in (eq T t TMP_27))))) in (ex3_2 T T 
TMP_23 TMP_25 TMP_28))))) in (let TMP_30 \def (S d) in (let TMP_31 \def (lift 
h TMP_30 x1) in (let TMP_42 \def (\lambda (t0: T).(let TMP_36 \def (\lambda 
(y: T).(\lambda (z: T).(let TMP_32 \def (Bind b) in (let TMP_33 \def (THead 
TMP_32 x0 x1) in (let TMP_34 \def (Bind b) in (let TMP_35 \def (THead TMP_34 
y z) in (eq T TMP_33 TMP_35))))))) in (let TMP_38 \def (\lambda (y: 
T).(\lambda (_: T).(let TMP_37 \def (lift h d y) in (eq T u TMP_37)))) in 
(let TMP_41 \def (\lambda (_: T).(\lambda (z: T).(let TMP_39 \def (S d) in 
(let TMP_40 \def (lift h TMP_39 z) in (eq T t0 TMP_40))))) in (ex3_2 T T 
TMP_36 TMP_38 TMP_41))))) in (let TMP_43 \def (lift h d x0) in (let TMP_56 
\def (\lambda (t0: T).(let TMP_48 \def (\lambda (y: T).(\lambda (z: T).(let 
TMP_44 \def (Bind b) in (let TMP_45 \def (THead TMP_44 x0 x1) in (let TMP_46 
\def (Bind b) in (let TMP_47 \def (THead TMP_46 y z) in (eq T TMP_45 
TMP_47))))))) in (let TMP_50 \def (\lambda (y: T).(\lambda (_: T).(let TMP_49 
\def (lift h d y) in (eq T t0 TMP_49)))) in (let TMP_55 \def (\lambda (_: 
T).(\lambda (z: T).(let TMP_51 \def (S d) in (let TMP_52 \def (lift h TMP_51 
x1) in (let TMP_53 \def (S d) in (let TMP_54 \def (lift h TMP_53 z) in (eq T 
TMP_52 TMP_54))))))) in (ex3_2 T T TMP_48 TMP_50 TMP_55))))) in (let TMP_61 
\def (\lambda (y: T).(\lambda (z: T).(let TMP_57 \def (Bind b) in (let TMP_58 
\def (THead TMP_57 x0 x1) in (let TMP_59 \def (Bind b) in (let TMP_60 \def 
(THead TMP_59 y z) in (eq T TMP_58 TMP_60))))))) in (let TMP_64 \def (\lambda 
(y: T).(\lambda (_: T).(let TMP_62 \def (lift h d x0) in (let TMP_63 \def 
(lift h d y) in (eq T TMP_62 TMP_63))))) in (let TMP_69 \def (\lambda (_: 
T).(\lambda (z: T).(let TMP_65 \def (S d) in (let TMP_66 \def (lift h TMP_65 
x1) in (let TMP_67 \def (S d) in (let TMP_68 \def (lift h TMP_67 z) in (eq T 
TMP_66 TMP_68))))))) in (let TMP_70 \def (Bind b) in (let TMP_71 \def (THead 
TMP_70 x0 x1) in (let TMP_72 \def (refl_equal T TMP_71) in (let TMP_73 \def 
(lift h d x0) in (let TMP_74 \def (refl_equal T TMP_73) in (let TMP_75 \def 
(S d) in (let TMP_76 \def (lift h TMP_75 x1) in (let TMP_77 \def (refl_equal 
T TMP_76) in (let TMP_78 \def (ex3_2_intro T T TMP_61 TMP_64 TMP_69 x0 x1 
TMP_72 TMP_74 TMP_77) in (let TMP_79 \def (eq_ind_r T TMP_43 TMP_56 TMP_78 u 
H2) in (let TMP_80 \def (eq_ind_r T TMP_31 TMP_42 TMP_79 t H3) in (eq_ind_r T 
TMP_20 TMP_29 TMP_80 x H1)))))))))))))))))))))))))))) in (ex3_2_ind T T TMP_4 
TMP_6 TMP_9 TMP_18 TMP_81 H0)))))))))))))))))).

theorem lift_gen_flat:
 \forall (f: F).(\forall (u: T).(\forall (t: T).(\forall (x: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (THead (Flat f) u t) (lift h d x)) \to (ex3_2 T 
T (\lambda (y: T).(\lambda (z: T).(eq T x (THead (Flat f) y z)))) (\lambda 
(y: T).(\lambda (_: T).(eq T u (lift h d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t (lift h d z)))))))))))
\def
 \lambda (f: F).(\lambda (u: T).(\lambda (t: T).(\lambda (x: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (THead (Flat f) u t) (lift h d 
x))).(let TMP_1 \def (Flat f) in (let H_x \def (lift_gen_head TMP_1 u t x h d 
H) in (let H0 \def H_x in (let TMP_4 \def (\lambda (y: T).(\lambda (z: 
T).(let TMP_2 \def (Flat f) in (let TMP_3 \def (THead TMP_2 y z) in (eq T x 
TMP_3))))) in (let TMP_6 \def (\lambda (y: T).(\lambda (_: T).(let TMP_5 \def 
(lift h d y) in (eq T u TMP_5)))) in (let TMP_8 \def (\lambda (_: T).(\lambda 
(z: T).(let TMP_7 \def (lift h d z) in (eq T t TMP_7)))) in (let TMP_11 \def 
(\lambda (y: T).(\lambda (z: T).(let TMP_9 \def (Flat f) in (let TMP_10 \def 
(THead TMP_9 y z) in (eq T x TMP_10))))) in (let TMP_13 \def (\lambda (y: 
T).(\lambda (_: T).(let TMP_12 \def (lift h d y) in (eq T u TMP_12)))) in 
(let TMP_15 \def (\lambda (_: T).(\lambda (z: T).(let TMP_14 \def (lift h d 
z) in (eq T t TMP_14)))) in (let TMP_16 \def (ex3_2 T T TMP_11 TMP_13 TMP_15) 
in (let TMP_71 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H1: (eq T x 
(THead (Flat f) x0 x1))).(\lambda (H2: (eq T u (lift h d x0))).(\lambda (H3: 
(eq T t (lift h d x1))).(let TMP_17 \def (Flat f) in (let TMP_18 \def (THead 
TMP_17 x0 x1) in (let TMP_26 \def (\lambda (t0: T).(let TMP_21 \def (\lambda 
(y: T).(\lambda (z: T).(let TMP_19 \def (Flat f) in (let TMP_20 \def (THead 
TMP_19 y z) in (eq T t0 TMP_20))))) in (let TMP_23 \def (\lambda (y: 
T).(\lambda (_: T).(let TMP_22 \def (lift h d y) in (eq T u TMP_22)))) in 
(let TMP_25 \def (\lambda (_: T).(\lambda (z: T).(let TMP_24 \def (lift h d 
z) in (eq T t TMP_24)))) in (ex3_2 T T TMP_21 TMP_23 TMP_25))))) in (let 
TMP_27 \def (lift h d x1) in (let TMP_37 \def (\lambda (t0: T).(let TMP_32 
\def (\lambda (y: T).(\lambda (z: T).(let TMP_28 \def (Flat f) in (let TMP_29 
\def (THead TMP_28 x0 x1) in (let TMP_30 \def (Flat f) in (let TMP_31 \def 
(THead TMP_30 y z) in (eq T TMP_29 TMP_31))))))) in (let TMP_34 \def (\lambda 
(y: T).(\lambda (_: T).(let TMP_33 \def (lift h d y) in (eq T u TMP_33)))) in 
(let TMP_36 \def (\lambda (_: T).(\lambda (z: T).(let TMP_35 \def (lift h d 
z) in (eq T t0 TMP_35)))) in (ex3_2 T T TMP_32 TMP_34 TMP_36))))) in (let 
TMP_38 \def (lift h d x0) in (let TMP_49 \def (\lambda (t0: T).(let TMP_43 
\def (\lambda (y: T).(\lambda (z: T).(let TMP_39 \def (Flat f) in (let TMP_40 
\def (THead TMP_39 x0 x1) in (let TMP_41 \def (Flat f) in (let TMP_42 \def 
(THead TMP_41 y z) in (eq T TMP_40 TMP_42))))))) in (let TMP_45 \def (\lambda 
(y: T).(\lambda (_: T).(let TMP_44 \def (lift h d y) in (eq T t0 TMP_44)))) 
in (let TMP_48 \def (\lambda (_: T).(\lambda (z: T).(let TMP_46 \def (lift h 
d x1) in (let TMP_47 \def (lift h d z) in (eq T TMP_46 TMP_47))))) in (ex3_2 
T T TMP_43 TMP_45 TMP_48))))) in (let TMP_54 \def (\lambda (y: T).(\lambda 
(z: T).(let TMP_50 \def (Flat f) in (let TMP_51 \def (THead TMP_50 x0 x1) in 
(let TMP_52 \def (Flat f) in (let TMP_53 \def (THead TMP_52 y z) in (eq T 
TMP_51 TMP_53))))))) in (let TMP_57 \def (\lambda (y: T).(\lambda (_: T).(let 
TMP_55 \def (lift h d x0) in (let TMP_56 \def (lift h d y) in (eq T TMP_55 
TMP_56))))) in (let TMP_60 \def (\lambda (_: T).(\lambda (z: T).(let TMP_58 
\def (lift h d x1) in (let TMP_59 \def (lift h d z) in (eq T TMP_58 
TMP_59))))) in (let TMP_61 \def (Flat f) in (let TMP_62 \def (THead TMP_61 x0 
x1) in (let TMP_63 \def (refl_equal T TMP_62) in (let TMP_64 \def (lift h d 
x0) in (let TMP_65 \def (refl_equal T TMP_64) in (let TMP_66 \def (lift h d 
x1) in (let TMP_67 \def (refl_equal T TMP_66) in (let TMP_68 \def 
(ex3_2_intro T T TMP_54 TMP_57 TMP_60 x0 x1 TMP_63 TMP_65 TMP_67) in (let 
TMP_69 \def (eq_ind_r T TMP_38 TMP_49 TMP_68 u H2) in (let TMP_70 \def 
(eq_ind_r T TMP_27 TMP_37 TMP_69 t H3) in (eq_ind_r T TMP_18 TMP_26 TMP_70 x 
H1)))))))))))))))))))))))))) in (ex3_2_ind T T TMP_4 TMP_6 TMP_8 TMP_16 
TMP_71 H0)))))))))))))))))).

theorem lift_inj:
 \forall (x: T).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((eq T 
(lift h d x) (lift h d t)) \to (eq T x t)))))
\def
 \lambda (x: T).(let TMP_1 \def (\lambda (t: T).(\forall (t0: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to (eq T t 
t0)))))) in (let TMP_10 \def (\lambda (n: nat).(\lambda (t: T).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H: (eq T (lift h d (TSort n)) (lift h d 
t))).(let TMP_2 \def (TSort n) in (let TMP_3 \def (lift h d TMP_2) in (let 
TMP_5 \def (\lambda (t0: T).(let TMP_4 \def (lift h d t) in (eq T t0 TMP_4))) 
in (let TMP_6 \def (TSort n) in (let TMP_7 \def (lift_sort n h d) in (let H0 
\def (eq_ind T TMP_3 TMP_5 H TMP_6 TMP_7) in (let TMP_8 \def (TSort n) in 
(let TMP_9 \def (lift_gen_sort h d n t H0) in (sym_eq T t TMP_8 
TMP_9)))))))))))))) in (let TMP_34 \def (\lambda (n: nat).(\lambda (t: 
T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (eq T (lift h d (TLRef 
n)) (lift h d t))).(let TMP_11 \def (TLRef n) in (let TMP_12 \def (eq T 
TMP_11 t) in (let TMP_23 \def (\lambda (H0: (lt n d)).(let TMP_13 \def (TLRef 
n) in (let TMP_14 \def (lift h d TMP_13) in (let TMP_16 \def (\lambda (t0: 
T).(let TMP_15 \def (lift h d t) in (eq T t0 TMP_15))) in (let TMP_17 \def 
(TLRef n) in (let TMP_18 \def (lift_lref_lt n h d H0) in (let H1 \def (eq_ind 
T TMP_14 TMP_16 H TMP_17 TMP_18) in (let TMP_19 \def (TLRef n) in (let TMP_20 
\def (le_n d) in (let TMP_21 \def (lt_le_trans n d d H0 TMP_20) in (let 
TMP_22 \def (lift_gen_lref_lt h d n TMP_21 t H1) in (sym_eq T t TMP_19 
TMP_22)))))))))))) in (let TMP_33 \def (\lambda (H0: (le d n)).(let TMP_24 
\def (TLRef n) in (let TMP_25 \def (lift h d TMP_24) in (let TMP_27 \def 
(\lambda (t0: T).(let TMP_26 \def (lift h d t) in (eq T t0 TMP_26))) in (let 
TMP_28 \def (plus n h) in (let TMP_29 \def (TLRef TMP_28) in (let TMP_30 \def 
(lift_lref_ge n h d H0) in (let H1 \def (eq_ind T TMP_25 TMP_27 H TMP_29 
TMP_30) in (let TMP_31 \def (TLRef n) in (let TMP_32 \def (lift_gen_lref_ge h 
d n H0 t H1) in (sym_eq T t TMP_31 TMP_32))))))))))) in (lt_le_e n d TMP_12 
TMP_23 TMP_33)))))))))) in (let TMP_140 \def (\lambda (k: K).(let TMP_36 \def 
(\lambda (k0: K).(\forall (t: T).(((\forall (t0: T).(\forall (h: 
nat).(\forall (d: nat).((eq T (lift h d t) (lift h d t0)) \to (eq T t 
t0)))))) \to (\forall (t0: T).(((\forall (t1: T).(\forall (h: nat).(\forall 
(d: nat).((eq T (lift h d t0) (lift h d t1)) \to (eq T t0 t1)))))) \to 
(\forall (t1: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d (THead 
k0 t t0)) (lift h d t1)) \to (let TMP_35 \def (THead k0 t t0) in (eq T TMP_35 
t1))))))))))) in (let TMP_90 \def (\lambda (b: B).(\lambda (t: T).(\lambda 
(H: ((\forall (t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) 
(lift h d t0)) \to (eq T t t0))))))).(\lambda (t0: T).(\lambda (H0: ((\forall 
(t1: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d 
t1)) \to (eq T t0 t1))))))).(\lambda (t1: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H1: (eq T (lift h d (THead (Bind b) t t0)) (lift h d 
t1))).(let TMP_37 \def (Bind b) in (let TMP_38 \def (THead TMP_37 t t0) in 
(let TMP_39 \def (lift h d TMP_38) in (let TMP_41 \def (\lambda (t2: T).(let 
TMP_40 \def (lift h d t1) in (eq T t2 TMP_40))) in (let TMP_42 \def (Bind b) 
in (let TMP_43 \def (lift h d t) in (let TMP_44 \def (S d) in (let TMP_45 
\def (lift h TMP_44 t0) in (let TMP_46 \def (THead TMP_42 TMP_43 TMP_45) in 
(let TMP_47 \def (lift_bind b t t0 h d) in (let H2 \def (eq_ind T TMP_39 
TMP_41 H1 TMP_46 TMP_47) in (let TMP_50 \def (\lambda (y: T).(\lambda (z: 
T).(let TMP_48 \def (Bind b) in (let TMP_49 \def (THead TMP_48 y z) in (eq T 
t1 TMP_49))))) in (let TMP_53 \def (\lambda (y: T).(\lambda (_: T).(let 
TMP_51 \def (lift h d t) in (let TMP_52 \def (lift h d y) in (eq T TMP_51 
TMP_52))))) in (let TMP_58 \def (\lambda (_: T).(\lambda (z: T).(let TMP_54 
\def (S d) in (let TMP_55 \def (lift h TMP_54 t0) in (let TMP_56 \def (S d) 
in (let TMP_57 \def (lift h TMP_56 z) in (eq T TMP_55 TMP_57))))))) in (let 
TMP_59 \def (Bind b) in (let TMP_60 \def (THead TMP_59 t t0) in (let TMP_61 
\def (eq T TMP_60 t1) in (let TMP_85 \def (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H3: (eq T t1 (THead (Bind b) x0 x1))).(\lambda (H4: (eq T (lift 
h d t) (lift h d x0))).(\lambda (H5: (eq T (lift h (S d) t0) (lift h (S d) 
x1))).(let TMP_62 \def (Bind b) in (let TMP_63 \def (THead TMP_62 x0 x1) in 
(let TMP_66 \def (\lambda (t2: T).(let TMP_64 \def (Bind b) in (let TMP_65 
\def (THead TMP_64 t t0) in (eq T TMP_65 t2)))) in (let TMP_67 \def (Bind b) 
in (let TMP_68 \def (THead TMP_67 x0 x1) in (let TMP_69 \def (Bind b) in (let 
TMP_70 \def (THead TMP_69 t t0) in (let TMP_71 \def (Bind b) in (let TMP_72 
\def (THead TMP_71 t t0) in (let TMP_73 \def (Bind b) in (let TMP_74 \def 
(THead TMP_73 x0 x1) in (let TMP_75 \def (Bind b) in (let TMP_76 \def (Bind 
b) in (let TMP_77 \def (Bind b) in (let TMP_78 \def (refl_equal K TMP_77) in 
(let TMP_79 \def (H x0 h d H4) in (let TMP_80 \def (S d) in (let TMP_81 \def 
(H0 x1 h TMP_80 H5) in (let TMP_82 \def (f_equal3 K T T T THead TMP_75 TMP_76 
t x0 t0 x1 TMP_78 TMP_79 TMP_81) in (let TMP_83 \def (sym_eq T TMP_72 TMP_74 
TMP_82) in (let TMP_84 \def (sym_eq T TMP_68 TMP_70 TMP_83) in (eq_ind_r T 
TMP_63 TMP_66 TMP_84 t1 H3))))))))))))))))))))))))))) in (let TMP_86 \def 
(lift h d t) in (let TMP_87 \def (S d) in (let TMP_88 \def (lift h TMP_87 t0) 
in (let TMP_89 \def (lift_gen_bind b TMP_86 TMP_88 t1 h d H2) in (ex3_2_ind T 
T TMP_50 TMP_53 TMP_58 TMP_61 TMP_85 TMP_89)))))))))))))))))))))))))))))))) 
in (let TMP_139 \def (\lambda (f: F).(\lambda (t: T).(\lambda (H: ((\forall 
(t0: T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t) (lift h d 
t0)) \to (eq T t t0))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (t1: 
T).(\forall (h: nat).(\forall (d: nat).((eq T (lift h d t0) (lift h d t1)) 
\to (eq T t0 t1))))))).(\lambda (t1: T).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H1: (eq T (lift h d (THead (Flat f) t t0)) (lift h d 
t1))).(let TMP_91 \def (Flat f) in (let TMP_92 \def (THead TMP_91 t t0) in 
(let TMP_93 \def (lift h d TMP_92) in (let TMP_95 \def (\lambda (t2: T).(let 
TMP_94 \def (lift h d t1) in (eq T t2 TMP_94))) in (let TMP_96 \def (Flat f) 
in (let TMP_97 \def (lift h d t) in (let TMP_98 \def (lift h d t0) in (let 
TMP_99 \def (THead TMP_96 TMP_97 TMP_98) in (let TMP_100 \def (lift_flat f t 
t0 h d) in (let H2 \def (eq_ind T TMP_93 TMP_95 H1 TMP_99 TMP_100) in (let 
TMP_103 \def (\lambda (y: T).(\lambda (z: T).(let TMP_101 \def (Flat f) in 
(let TMP_102 \def (THead TMP_101 y z) in (eq T t1 TMP_102))))) in (let 
TMP_106 \def (\lambda (y: T).(\lambda (_: T).(let TMP_104 \def (lift h d t) 
in (let TMP_105 \def (lift h d y) in (eq T TMP_104 TMP_105))))) in (let 
TMP_109 \def (\lambda (_: T).(\lambda (z: T).(let TMP_107 \def (lift h d t0) 
in (let TMP_108 \def (lift h d z) in (eq T TMP_107 TMP_108))))) in (let 
TMP_110 \def (Flat f) in (let TMP_111 \def (THead TMP_110 t t0) in (let 
TMP_112 \def (eq T TMP_111 t1) in (let TMP_135 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H3: (eq T t1 (THead (Flat f) x0 x1))).(\lambda (H4: (eq T 
(lift h d t) (lift h d x0))).(\lambda (H5: (eq T (lift h d t0) (lift h d 
x1))).(let TMP_113 \def (Flat f) in (let TMP_114 \def (THead TMP_113 x0 x1) 
in (let TMP_117 \def (\lambda (t2: T).(let TMP_115 \def (Flat f) in (let 
TMP_116 \def (THead TMP_115 t t0) in (eq T TMP_116 t2)))) in (let TMP_118 
\def (Flat f) in (let TMP_119 \def (THead TMP_118 x0 x1) in (let TMP_120 \def 
(Flat f) in (let TMP_121 \def (THead TMP_120 t t0) in (let TMP_122 \def (Flat 
f) in (let TMP_123 \def (THead TMP_122 t t0) in (let TMP_124 \def (Flat f) in 
(let TMP_125 \def (THead TMP_124 x0 x1) in (let TMP_126 \def (Flat f) in (let 
TMP_127 \def (Flat f) in (let TMP_128 \def (Flat f) in (let TMP_129 \def 
(refl_equal K TMP_128) in (let TMP_130 \def (H x0 h d H4) in (let TMP_131 
\def (H0 x1 h d H5) in (let TMP_132 \def (f_equal3 K T T T THead TMP_126 
TMP_127 t x0 t0 x1 TMP_129 TMP_130 TMP_131) in (let TMP_133 \def (sym_eq T 
TMP_123 TMP_125 TMP_132) in (let TMP_134 \def (sym_eq T TMP_119 TMP_121 
TMP_133) in (eq_ind_r T TMP_114 TMP_117 TMP_134 t1 
H3)))))))))))))))))))))))))) in (let TMP_136 \def (lift h d t) in (let 
TMP_137 \def (lift h d t0) in (let TMP_138 \def (lift_gen_flat f TMP_136 
TMP_137 t1 h d H2) in (ex3_2_ind T T TMP_103 TMP_106 TMP_109 TMP_112 TMP_135 
TMP_138)))))))))))))))))))))))))))))) in (K_ind TMP_36 TMP_90 TMP_139 k))))) 
in (T_ind TMP_1 TMP_10 TMP_34 TMP_140 x))))).

theorem lift_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h1: nat).(\forall (h2: 
nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to ((eq T (lift h1 d1 
t1) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h1 d1 
t2))) (\lambda (t2: T).(eq T t1 (lift h2 d2 t2)))))))))))
\def
 \lambda (t1: T).(let TMP_5 \def (\lambda (t: T).(\forall (x: T).(\forall 
(h1: nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 
d2) \to ((eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x)) \to (let TMP_2 \def 
(\lambda (t2: T).(let TMP_1 \def (lift h1 d1 t2) in (eq T x TMP_1))) in (let 
TMP_4 \def (\lambda (t2: T).(let TMP_3 \def (lift h2 d2 t2) in (eq T t 
TMP_3))) in (ex2 T TMP_2 TMP_4))))))))))) in (let TMP_48 \def (\lambda (n: 
nat).(\lambda (x: T).(\lambda (h1: nat).(\lambda (h2: nat).(\lambda (d1: 
nat).(\lambda (d2: nat).(\lambda (_: (le d1 d2)).(\lambda (H0: (eq T (lift h1 
d1 (TSort n)) (lift h2 (plus d2 h1) x))).(let TMP_6 \def (TSort n) in (let 
TMP_7 \def (lift h1 d1 TMP_6) in (let TMP_10 \def (\lambda (t: T).(let TMP_8 
\def (plus d2 h1) in (let TMP_9 \def (lift h2 TMP_8 x) in (eq T t TMP_9)))) 
in (let TMP_11 \def (TSort n) in (let TMP_12 \def (lift_sort n h1 d1) in (let 
H1 \def (eq_ind T TMP_7 TMP_10 H0 TMP_11 TMP_12) in (let TMP_13 \def (TSort 
n) in (let TMP_19 \def (\lambda (t: T).(let TMP_15 \def (\lambda (t2: T).(let 
TMP_14 \def (lift h1 d1 t2) in (eq T t TMP_14))) in (let TMP_18 \def (\lambda 
(t2: T).(let TMP_16 \def (TSort n) in (let TMP_17 \def (lift h2 d2 t2) in (eq 
T TMP_16 TMP_17)))) in (ex2 T TMP_15 TMP_18)))) in (let TMP_22 \def (\lambda 
(t2: T).(let TMP_20 \def (TSort n) in (let TMP_21 \def (lift h1 d1 t2) in (eq 
T TMP_20 TMP_21)))) in (let TMP_25 \def (\lambda (t2: T).(let TMP_23 \def 
(TSort n) in (let TMP_24 \def (lift h2 d2 t2) in (eq T TMP_23 TMP_24)))) in 
(let TMP_26 \def (TSort n) in (let TMP_27 \def (TSort n) in (let TMP_29 \def 
(\lambda (t: T).(let TMP_28 \def (TSort n) in (eq T TMP_28 t))) in (let 
TMP_30 \def (TSort n) in (let TMP_31 \def (refl_equal T TMP_30) in (let 
TMP_32 \def (TSort n) in (let TMP_33 \def (lift h1 d1 TMP_32) in (let TMP_34 
\def (lift_sort n h1 d1) in (let TMP_35 \def (eq_ind_r T TMP_27 TMP_29 TMP_31 
TMP_33 TMP_34) in (let TMP_36 \def (TSort n) in (let TMP_38 \def (\lambda (t: 
T).(let TMP_37 \def (TSort n) in (eq T TMP_37 t))) in (let TMP_39 \def (TSort 
n) in (let TMP_40 \def (refl_equal T TMP_39) in (let TMP_41 \def (TSort n) in 
(let TMP_42 \def (lift h2 d2 TMP_41) in (let TMP_43 \def (lift_sort n h2 d2) 
in (let TMP_44 \def (eq_ind_r T TMP_36 TMP_38 TMP_40 TMP_42 TMP_43) in (let 
TMP_45 \def (ex_intro2 T TMP_22 TMP_25 TMP_26 TMP_35 TMP_44) in (let TMP_46 
\def (plus d2 h1) in (let TMP_47 \def (lift_gen_sort h2 TMP_46 n x H1) in 
(eq_ind_r T TMP_13 TMP_19 TMP_45 x 
TMP_47))))))))))))))))))))))))))))))))))))))) in (let TMP_325 \def (\lambda 
(n: nat).(\lambda (x: T).(\lambda (h1: nat).(\lambda (h2: nat).(\lambda (d1: 
nat).(\lambda (d2: nat).(\lambda (H: (le d1 d2)).(\lambda (H0: (eq T (lift h1 
d1 (TLRef n)) (lift h2 (plus d2 h1) x))).(let TMP_50 \def (\lambda (t2: 
T).(let TMP_49 \def (lift h1 d1 t2) in (eq T x TMP_49))) in (let TMP_53 \def 
(\lambda (t2: T).(let TMP_51 \def (TLRef n) in (let TMP_52 \def (lift h2 d2 
t2) in (eq T TMP_51 TMP_52)))) in (let TMP_54 \def (ex2 T TMP_50 TMP_53) in 
(let TMP_101 \def (\lambda (H1: (lt n d1)).(let TMP_55 \def (TLRef n) in (let 
TMP_56 \def (lift h1 d1 TMP_55) in (let TMP_59 \def (\lambda (t: T).(let 
TMP_57 \def (plus d2 h1) in (let TMP_58 \def (lift h2 TMP_57 x) in (eq T t 
TMP_58)))) in (let TMP_60 \def (TLRef n) in (let TMP_61 \def (lift_lref_lt n 
h1 d1 H1) in (let H2 \def (eq_ind T TMP_56 TMP_59 H0 TMP_60 TMP_61) in (let 
TMP_62 \def (TLRef n) in (let TMP_68 \def (\lambda (t: T).(let TMP_64 \def 
(\lambda (t2: T).(let TMP_63 \def (lift h1 d1 t2) in (eq T t TMP_63))) in 
(let TMP_67 \def (\lambda (t2: T).(let TMP_65 \def (TLRef n) in (let TMP_66 
\def (lift h2 d2 t2) in (eq T TMP_65 TMP_66)))) in (ex2 T TMP_64 TMP_67)))) 
in (let TMP_71 \def (\lambda (t2: T).(let TMP_69 \def (TLRef n) in (let 
TMP_70 \def (lift h1 d1 t2) in (eq T TMP_69 TMP_70)))) in (let TMP_74 \def 
(\lambda (t2: T).(let TMP_72 \def (TLRef n) in (let TMP_73 \def (lift h2 d2 
t2) in (eq T TMP_72 TMP_73)))) in (let TMP_75 \def (TLRef n) in (let TMP_76 
\def (TLRef n) in (let TMP_78 \def (\lambda (t: T).(let TMP_77 \def (TLRef n) 
in (eq T TMP_77 t))) in (let TMP_79 \def (TLRef n) in (let TMP_80 \def 
(refl_equal T TMP_79) in (let TMP_81 \def (TLRef n) in (let TMP_82 \def (lift 
h1 d1 TMP_81) in (let TMP_83 \def (lift_lref_lt n h1 d1 H1) in (let TMP_84 
\def (eq_ind_r T TMP_76 TMP_78 TMP_80 TMP_82 TMP_83) in (let TMP_85 \def 
(TLRef n) in (let TMP_87 \def (\lambda (t: T).(let TMP_86 \def (TLRef n) in 
(eq T TMP_86 t))) in (let TMP_88 \def (TLRef n) in (let TMP_89 \def 
(refl_equal T TMP_88) in (let TMP_90 \def (TLRef n) in (let TMP_91 \def (lift 
h2 d2 TMP_90) in (let TMP_92 \def (lt_le_trans n d1 d2 H1 H) in (let TMP_93 
\def (lift_lref_lt n h2 d2 TMP_92) in (let TMP_94 \def (eq_ind_r T TMP_85 
TMP_87 TMP_89 TMP_91 TMP_93) in (let TMP_95 \def (ex_intro2 T TMP_71 TMP_74 
TMP_75 TMP_84 TMP_94) in (let TMP_96 \def (plus d2 h1) in (let TMP_97 \def 
(plus d2 h1) in (let TMP_98 \def (le_plus_trans d1 d2 h1 H) in (let TMP_99 
\def (lt_le_trans n d1 TMP_97 H1 TMP_98) in (let TMP_100 \def 
(lift_gen_lref_lt h2 TMP_96 n TMP_99 x H2) in (eq_ind_r T TMP_62 TMP_68 
TMP_95 x TMP_100)))))))))))))))))))))))))))))))))))) in (let TMP_324 \def 
(\lambda (H1: (le d1 n)).(let TMP_102 \def (TLRef n) in (let TMP_103 \def 
(lift h1 d1 TMP_102) in (let TMP_106 \def (\lambda (t: T).(let TMP_104 \def 
(plus d2 h1) in (let TMP_105 \def (lift h2 TMP_104 x) in (eq T t TMP_105)))) 
in (let TMP_107 \def (plus n h1) in (let TMP_108 \def (TLRef TMP_107) in (let 
TMP_109 \def (lift_lref_ge n h1 d1 H1) in (let H2 \def (eq_ind T TMP_103 
TMP_106 H0 TMP_108 TMP_109) in (let TMP_111 \def (\lambda (t2: T).(let 
TMP_110 \def (lift h1 d1 t2) in (eq T x TMP_110))) in (let TMP_114 \def 
(\lambda (t2: T).(let TMP_112 \def (TLRef n) in (let TMP_113 \def (lift h2 d2 
t2) in (eq T TMP_112 TMP_113)))) in (let TMP_115 \def (ex2 T TMP_111 TMP_114) 
in (let TMP_158 \def (\lambda (H3: (lt n d2)).(let TMP_116 \def (plus n h1) 
in (let TMP_117 \def (TLRef TMP_116) in (let TMP_123 \def (\lambda (t: 
T).(let TMP_119 \def (\lambda (t2: T).(let TMP_118 \def (lift h1 d1 t2) in 
(eq T t TMP_118))) in (let TMP_122 \def (\lambda (t2: T).(let TMP_120 \def 
(TLRef n) in (let TMP_121 \def (lift h2 d2 t2) in (eq T TMP_120 TMP_121)))) 
in (ex2 T TMP_119 TMP_122)))) in (let TMP_127 \def (\lambda (t2: T).(let 
TMP_124 \def (plus n h1) in (let TMP_125 \def (TLRef TMP_124) in (let TMP_126 
\def (lift h1 d1 t2) in (eq T TMP_125 TMP_126))))) in (let TMP_130 \def 
(\lambda (t2: T).(let TMP_128 \def (TLRef n) in (let TMP_129 \def (lift h2 d2 
t2) in (eq T TMP_128 TMP_129)))) in (let TMP_131 \def (TLRef n) in (let 
TMP_132 \def (plus n h1) in (let TMP_133 \def (TLRef TMP_132) in (let TMP_136 
\def (\lambda (t: T).(let TMP_134 \def (plus n h1) in (let TMP_135 \def 
(TLRef TMP_134) in (eq T TMP_135 t)))) in (let TMP_137 \def (plus n h1) in 
(let TMP_138 \def (TLRef TMP_137) in (let TMP_139 \def (refl_equal T TMP_138) 
in (let TMP_140 \def (TLRef n) in (let TMP_141 \def (lift h1 d1 TMP_140) in 
(let TMP_142 \def (lift_lref_ge n h1 d1 H1) in (let TMP_143 \def (eq_ind_r T 
TMP_133 TMP_136 TMP_139 TMP_141 TMP_142) in (let TMP_144 \def (TLRef n) in 
(let TMP_146 \def (\lambda (t: T).(let TMP_145 \def (TLRef n) in (eq T 
TMP_145 t))) in (let TMP_147 \def (TLRef n) in (let TMP_148 \def (refl_equal 
T TMP_147) in (let TMP_149 \def (TLRef n) in (let TMP_150 \def (lift h2 d2 
TMP_149) in (let TMP_151 \def (lift_lref_lt n h2 d2 H3) in (let TMP_152 \def 
(eq_ind_r T TMP_144 TMP_146 TMP_148 TMP_150 TMP_151) in (let TMP_153 \def 
(ex_intro2 T TMP_127 TMP_130 TMP_131 TMP_143 TMP_152) in (let TMP_154 \def 
(plus d2 h1) in (let TMP_155 \def (plus n h1) in (let TMP_156 \def (lt_reg_r 
n d2 h1 H3) in (let TMP_157 \def (lift_gen_lref_lt h2 TMP_154 TMP_155 TMP_156 
x H2) in (eq_ind_r T TMP_117 TMP_123 TMP_153 x 
TMP_157))))))))))))))))))))))))))))))) in (let TMP_323 \def (\lambda (H3: (le 
d2 n)).(let TMP_159 \def (plus d2 h2) in (let TMP_161 \def (\lambda (t2: 
T).(let TMP_160 \def (lift h1 d1 t2) in (eq T x TMP_160))) in (let TMP_164 
\def (\lambda (t2: T).(let TMP_162 \def (TLRef n) in (let TMP_163 \def (lift 
h2 d2 t2) in (eq T TMP_162 TMP_163)))) in (let TMP_165 \def (ex2 T TMP_161 
TMP_164) in (let TMP_186 \def (\lambda (H4: (lt n (plus d2 h2))).(let TMP_166 
\def (plus d2 h1) in (let TMP_167 \def (plus n h1) in (let TMP_168 \def (le_n 
h1) in (let TMP_169 \def (le_plus_plus d2 n h1 h1 H3 TMP_168) in (let TMP_170 
\def (plus d2 h2) in (let TMP_171 \def (plus TMP_170 h1) in (let TMP_173 \def 
(\lambda (n0: nat).(let TMP_172 \def (plus n h1) in (lt TMP_172 n0))) in (let 
TMP_174 \def (plus d2 h2) in (let TMP_175 \def (lt_reg_r n TMP_174 h1 H4) in 
(let TMP_176 \def (plus d2 h1) in (let TMP_177 \def (plus TMP_176 h2) in (let 
TMP_178 \def (plus_permute_2_in_3 d2 h1 h2) in (let TMP_179 \def (eq_ind_r 
nat TMP_171 TMP_173 TMP_175 TMP_177 TMP_178) in (let TMP_181 \def (\lambda 
(t2: T).(let TMP_180 \def (lift h1 d1 t2) in (eq T x TMP_180))) in (let 
TMP_184 \def (\lambda (t2: T).(let TMP_182 \def (TLRef n) in (let TMP_183 
\def (lift h2 d2 t2) in (eq T TMP_182 TMP_183)))) in (let TMP_185 \def (ex2 T 
TMP_181 TMP_184) in (lift_gen_lref_false h2 TMP_166 TMP_167 TMP_169 TMP_179 x 
H2 TMP_185)))))))))))))))))) in (let TMP_322 \def (\lambda (H4: (le (plus d2 
h2) n)).(let TMP_187 \def (plus n h1) in (let TMP_191 \def (\lambda (n0: 
nat).(let TMP_188 \def (TLRef n0) in (let TMP_189 \def (plus d2 h1) in (let 
TMP_190 \def (lift h2 TMP_189 x) in (eq T TMP_188 TMP_190))))) in (let 
TMP_192 \def (plus n h1) in (let TMP_193 \def (minus TMP_192 h2) in (let 
TMP_194 \def (plus TMP_193 h2) in (let TMP_195 \def (plus n h1) in (let 
TMP_196 \def (plus d2 h2) in (let TMP_197 \def (le_plus_r d2 h2) in (let 
TMP_198 \def (le_trans h2 TMP_196 n TMP_197 H4) in (let TMP_199 \def 
(le_plus_trans h2 n h1 TMP_198) in (let TMP_200 \def (le_plus_minus_sym h2 
TMP_195 TMP_199) in (let H5 \def (eq_ind nat TMP_187 TMP_191 H2 TMP_194 
TMP_200) in (let TMP_201 \def (plus n h1) in (let TMP_202 \def (minus TMP_201 
h2) in (let TMP_203 \def (TLRef TMP_202) in (let TMP_209 \def (\lambda (t: 
T).(let TMP_205 \def (\lambda (t2: T).(let TMP_204 \def (lift h1 d1 t2) in 
(eq T t TMP_204))) in (let TMP_208 \def (\lambda (t2: T).(let TMP_206 \def 
(TLRef n) in (let TMP_207 \def (lift h2 d2 t2) in (eq T TMP_206 TMP_207)))) 
in (ex2 T TMP_205 TMP_208)))) in (let TMP_214 \def (\lambda (t2: T).(let 
TMP_210 \def (plus n h1) in (let TMP_211 \def (minus TMP_210 h2) in (let 
TMP_212 \def (TLRef TMP_211) in (let TMP_213 \def (lift h1 d1 t2) in (eq T 
TMP_212 TMP_213)))))) in (let TMP_217 \def (\lambda (t2: T).(let TMP_215 \def 
(TLRef n) in (let TMP_216 \def (lift h2 d2 t2) in (eq T TMP_215 TMP_216)))) 
in (let TMP_218 \def (minus n h2) in (let TMP_219 \def (TLRef TMP_218) in 
(let TMP_220 \def (minus n h2) in (let TMP_221 \def (plus TMP_220 h1) in (let 
TMP_226 \def (\lambda (n0: nat).(let TMP_222 \def (TLRef n0) in (let TMP_223 
\def (minus n h2) in (let TMP_224 \def (TLRef TMP_223) in (let TMP_225 \def 
(lift h1 d1 TMP_224) in (eq T TMP_222 TMP_225)))))) in (let TMP_227 \def 
(minus n h2) in (let TMP_228 \def (plus TMP_227 h1) in (let TMP_229 \def 
(TLRef TMP_228) in (let TMP_233 \def (\lambda (t: T).(let TMP_230 \def (minus 
n h2) in (let TMP_231 \def (plus TMP_230 h1) in (let TMP_232 \def (TLRef 
TMP_231) in (eq T TMP_232 t))))) in (let TMP_234 \def (minus n h2) in (let 
TMP_235 \def (plus TMP_234 h1) in (let TMP_236 \def (TLRef TMP_235) in (let 
TMP_237 \def (refl_equal T TMP_236) in (let TMP_238 \def (minus n h2) in (let 
TMP_239 \def (TLRef TMP_238) in (let TMP_240 \def (lift h1 d1 TMP_239) in 
(let TMP_241 \def (minus n h2) in (let TMP_242 \def (minus n h2) in (let 
TMP_243 \def (le_minus d2 n h2 H4) in (let TMP_244 \def (le_trans d1 d2 
TMP_242 H TMP_243) in (let TMP_245 \def (lift_lref_ge TMP_241 h1 d1 TMP_244) 
in (let TMP_246 \def (eq_ind_r T TMP_229 TMP_233 TMP_237 TMP_240 TMP_245) in 
(let TMP_247 \def (plus n h1) in (let TMP_248 \def (minus TMP_247 h2) in (let 
TMP_249 \def (plus d2 h2) in (let TMP_250 \def (le_plus_r d2 h2) in (let 
TMP_251 \def (le_trans h2 TMP_249 n TMP_250 H4) in (let TMP_252 \def 
(le_minus_plus h2 n TMP_251 h1) in (let TMP_253 \def (eq_ind_r nat TMP_221 
TMP_226 TMP_246 TMP_248 TMP_252) in (let TMP_254 \def (minus n h2) in (let 
TMP_255 \def (plus TMP_254 h2) in (let TMP_260 \def (\lambda (n0: nat).(let 
TMP_256 \def (TLRef n0) in (let TMP_257 \def (minus n0 h2) in (let TMP_258 
\def (TLRef TMP_257) in (let TMP_259 \def (lift h2 d2 TMP_258) in (eq T 
TMP_256 TMP_259)))))) in (let TMP_261 \def (minus n h2) in (let TMP_262 \def 
(plus TMP_261 h2) in (let TMP_263 \def (minus TMP_262 h2) in (let TMP_264 
\def (plus TMP_263 h2) in (let TMP_265 \def (TLRef TMP_264) in (let TMP_269 
\def (\lambda (t: T).(let TMP_266 \def (minus n h2) in (let TMP_267 \def 
(plus TMP_266 h2) in (let TMP_268 \def (TLRef TMP_267) in (eq T TMP_268 
t))))) in (let TMP_270 \def (minus n h2) in (let TMP_271 \def (plus TMP_270 
h2) in (let TMP_272 \def (minus TMP_271 h2) in (let TMP_273 \def (plus 
TMP_272 h2) in (let TMP_274 \def (TLRef TMP_273) in (let TMP_275 \def (minus 
n h2) in (let TMP_276 \def (plus TMP_275 h2) in (let TMP_277 \def (TLRef 
TMP_276) in (let TMP_278 \def (minus n h2) in (let TMP_279 \def (plus TMP_278 
h2) in (let TMP_280 \def (minus TMP_279 h2) in (let TMP_281 \def (plus 
TMP_280 h2) in (let TMP_282 \def (minus n h2) in (let TMP_283 \def (plus 
TMP_282 h2) in (let TMP_284 \def (minus n h2) in (let TMP_285 \def (plus 
TMP_284 h2) in (let TMP_286 \def (minus TMP_285 h2) in (let TMP_287 \def 
(minus n h2) in (let TMP_288 \def (minus n h2) in (let TMP_289 \def 
(minus_plus_r TMP_288 h2) in (let TMP_290 \def (refl_equal nat h2) in (let 
TMP_291 \def (f_equal2 nat nat nat plus TMP_286 TMP_287 h2 h2 TMP_289 
TMP_290) in (let TMP_292 \def (f_equal nat T TLRef TMP_281 TMP_283 TMP_291) 
in (let TMP_293 \def (sym_eq T TMP_274 TMP_277 TMP_292) in (let TMP_294 \def 
(minus n h2) in (let TMP_295 \def (plus TMP_294 h2) in (let TMP_296 \def 
(minus TMP_295 h2) in (let TMP_297 \def (TLRef TMP_296) in (let TMP_298 \def 
(lift h2 d2 TMP_297) in (let TMP_299 \def (minus n h2) in (let TMP_300 \def 
(plus TMP_299 h2) in (let TMP_301 \def (minus TMP_300 h2) in (let TMP_302 
\def (minus n h2) in (let TMP_303 \def (plus TMP_302 h2) in (let TMP_304 \def 
(minus n h2) in (let TMP_305 \def (le_minus d2 n h2 H4) in (let TMP_306 \def 
(le_n h2) in (let TMP_307 \def (le_plus_plus d2 TMP_304 h2 h2 TMP_305 
TMP_306) in (let TMP_308 \def (le_minus d2 TMP_303 h2 TMP_307) in (let 
TMP_309 \def (lift_lref_ge TMP_301 h2 d2 TMP_308) in (let TMP_310 \def 
(eq_ind_r T TMP_265 TMP_269 TMP_293 TMP_298 TMP_309) in (let TMP_311 \def 
(plus d2 h2) in (let TMP_312 \def (le_plus_r d2 h2) in (let TMP_313 \def 
(le_trans h2 TMP_311 n TMP_312 H4) in (let TMP_314 \def (le_plus_minus_sym h2 
n TMP_313) in (let TMP_315 \def (eq_ind_r nat TMP_255 TMP_260 TMP_310 n 
TMP_314) in (let TMP_316 \def (ex_intro2 T TMP_214 TMP_217 TMP_219 TMP_253 
TMP_315) in (let TMP_317 \def (plus d2 h1) in (let TMP_318 \def (plus n h1) 
in (let TMP_319 \def (minus TMP_318 h2) in (let TMP_320 \def (arith0 h2 d2 n 
H4 h1) in (let TMP_321 \def (lift_gen_lref_ge h2 TMP_317 TMP_319 TMP_320 x 
H5) in (eq_ind_r T TMP_203 TMP_209 TMP_316 x 
TMP_321)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))) in (lt_le_e n TMP_159 TMP_165 TMP_186 
TMP_322)))))))) in (lt_le_e n d2 TMP_115 TMP_158 TMP_323)))))))))))))) in 
(lt_le_e n d1 TMP_54 TMP_101 TMP_324)))))))))))))) in (let TMP_720 \def 
(\lambda (k: K).(\lambda (t: T).(\lambda (H: ((\forall (x: T).(\forall (h1: 
nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to 
((eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: 
T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t (lift h2 d2 
t2))))))))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (x: T).(\forall (h1: 
nat).(\forall (h2: nat).(\forall (d1: nat).(\forall (d2: nat).((le d1 d2) \to 
((eq T (lift h1 d1 t0) (lift h2 (plus d2 h1) x)) \to (ex2 T (\lambda (t2: 
T).(eq T x (lift h1 d1 t2))) (\lambda (t2: T).(eq T t0 (lift h2 d2 
t2))))))))))))).(\lambda (x: T).(\lambda (h1: nat).(\lambda (h2: 
nat).(\lambda (d1: nat).(\lambda (d2: nat).(\lambda (H1: (le d1 d2)).(\lambda 
(H2: (eq T (lift h1 d1 (THead k t t0)) (lift h2 (plus d2 h1) x))).(let 
TMP_331 \def (\lambda (k0: K).((eq T (lift h1 d1 (THead k0 t t0)) (lift h2 
(plus d2 h1) x)) \to (let TMP_327 \def (\lambda (t2: T).(let TMP_326 \def 
(lift h1 d1 t2) in (eq T x TMP_326))) in (let TMP_330 \def (\lambda (t2: 
T).(let TMP_328 \def (THead k0 t t0) in (let TMP_329 \def (lift h2 d2 t2) in 
(eq T TMP_328 TMP_329)))) in (ex2 T TMP_327 TMP_330))))) in (let TMP_540 \def 
(\lambda (b: B).(\lambda (H3: (eq T (lift h1 d1 (THead (Bind b) t t0)) (lift 
h2 (plus d2 h1) x))).(let TMP_332 \def (Bind b) in (let TMP_333 \def (THead 
TMP_332 t t0) in (let TMP_334 \def (lift h1 d1 TMP_333) in (let TMP_337 \def 
(\lambda (t2: T).(let TMP_335 \def (plus d2 h1) in (let TMP_336 \def (lift h2 
TMP_335 x) in (eq T t2 TMP_336)))) in (let TMP_338 \def (Bind b) in (let 
TMP_339 \def (lift h1 d1 t) in (let TMP_340 \def (S d1) in (let TMP_341 \def 
(lift h1 TMP_340 t0) in (let TMP_342 \def (THead TMP_338 TMP_339 TMP_341) in 
(let TMP_343 \def (lift_bind b t t0 h1 d1) in (let H4 \def (eq_ind T TMP_334 
TMP_337 H3 TMP_342 TMP_343) in (let TMP_346 \def (\lambda (y: T).(\lambda (z: 
T).(let TMP_344 \def (Bind b) in (let TMP_345 \def (THead TMP_344 y z) in (eq 
T x TMP_345))))) in (let TMP_350 \def (\lambda (y: T).(\lambda (_: T).(let 
TMP_347 \def (lift h1 d1 t) in (let TMP_348 \def (plus d2 h1) in (let TMP_349 
\def (lift h2 TMP_348 y) in (eq T TMP_347 TMP_349)))))) in (let TMP_356 \def 
(\lambda (_: T).(\lambda (z: T).(let TMP_351 \def (S d1) in (let TMP_352 \def 
(lift h1 TMP_351 t0) in (let TMP_353 \def (plus d2 h1) in (let TMP_354 \def 
(S TMP_353) in (let TMP_355 \def (lift h2 TMP_354 z) in (eq T TMP_352 
TMP_355)))))))) in (let TMP_358 \def (\lambda (t2: T).(let TMP_357 \def (lift 
h1 d1 t2) in (eq T x TMP_357))) in (let TMP_362 \def (\lambda (t2: T).(let 
TMP_359 \def (Bind b) in (let TMP_360 \def (THead TMP_359 t t0) in (let 
TMP_361 \def (lift h2 d2 t2) in (eq T TMP_360 TMP_361))))) in (let TMP_363 
\def (ex2 T TMP_358 TMP_362) in (let TMP_534 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H5: (eq T x (THead (Bind b) x0 x1))).(\lambda (H6: (eq T 
(lift h1 d1 t) (lift h2 (plus d2 h1) x0))).(\lambda (H7: (eq T (lift h1 (S 
d1) t0) (lift h2 (S (plus d2 h1)) x1))).(let TMP_364 \def (Bind b) in (let 
TMP_365 \def (THead TMP_364 x0 x1) in (let TMP_372 \def (\lambda (t2: T).(let 
TMP_367 \def (\lambda (t3: T).(let TMP_366 \def (lift h1 d1 t3) in (eq T t2 
TMP_366))) in (let TMP_371 \def (\lambda (t3: T).(let TMP_368 \def (Bind b) 
in (let TMP_369 \def (THead TMP_368 t t0) in (let TMP_370 \def (lift h2 d2 
t3) in (eq T TMP_369 TMP_370))))) in (ex2 T TMP_367 TMP_371)))) in (let 
TMP_374 \def (\lambda (t2: T).(let TMP_373 \def (lift h1 d1 t2) in (eq T x0 
TMP_373))) in (let TMP_376 \def (\lambda (t2: T).(let TMP_375 \def (lift h2 
d2 t2) in (eq T t TMP_375))) in (let TMP_380 \def (\lambda (t2: T).(let 
TMP_377 \def (Bind b) in (let TMP_378 \def (THead TMP_377 x0 x1) in (let 
TMP_379 \def (lift h1 d1 t2) in (eq T TMP_378 TMP_379))))) in (let TMP_384 
\def (\lambda (t2: T).(let TMP_381 \def (Bind b) in (let TMP_382 \def (THead 
TMP_381 t t0) in (let TMP_383 \def (lift h2 d2 t2) in (eq T TMP_382 
TMP_383))))) in (let TMP_385 \def (ex2 T TMP_380 TMP_384) in (let TMP_531 
\def (\lambda (x2: T).(\lambda (H8: (eq T x0 (lift h1 d1 x2))).(\lambda (H9: 
(eq T t (lift h2 d2 x2))).(let TMP_386 \def (lift h1 d1 x2) in (let TMP_395 
\def (\lambda (t2: T).(let TMP_390 \def (\lambda (t3: T).(let TMP_387 \def 
(Bind b) in (let TMP_388 \def (THead TMP_387 t2 x1) in (let TMP_389 \def 
(lift h1 d1 t3) in (eq T TMP_388 TMP_389))))) in (let TMP_394 \def (\lambda 
(t3: T).(let TMP_391 \def (Bind b) in (let TMP_392 \def (THead TMP_391 t t0) 
in (let TMP_393 \def (lift h2 d2 t3) in (eq T TMP_392 TMP_393))))) in (ex2 T 
TMP_390 TMP_394)))) in (let TMP_396 \def (lift h2 d2 x2) in (let TMP_406 \def 
(\lambda (t2: T).(let TMP_401 \def (\lambda (t3: T).(let TMP_397 \def (Bind 
b) in (let TMP_398 \def (lift h1 d1 x2) in (let TMP_399 \def (THead TMP_397 
TMP_398 x1) in (let TMP_400 \def (lift h1 d1 t3) in (eq T TMP_399 
TMP_400)))))) in (let TMP_405 \def (\lambda (t3: T).(let TMP_402 \def (Bind 
b) in (let TMP_403 \def (THead TMP_402 t2 t0) in (let TMP_404 \def (lift h2 
d2 t3) in (eq T TMP_403 TMP_404))))) in (ex2 T TMP_401 TMP_405)))) in (let 
TMP_407 \def (S d2) in (let TMP_408 \def (plus TMP_407 h1) in (let H10 \def 
(refl_equal nat TMP_408) in (let TMP_409 \def (plus d2 h1) in (let TMP_410 
\def (S TMP_409) in (let TMP_414 \def (\lambda (n: nat).(let TMP_411 \def (S 
d1) in (let TMP_412 \def (lift h1 TMP_411 t0) in (let TMP_413 \def (lift h2 n 
x1) in (eq T TMP_412 TMP_413))))) in (let TMP_415 \def (S d2) in (let TMP_416 
\def (plus TMP_415 h1) in (let H11 \def (eq_ind nat TMP_410 TMP_414 H7 
TMP_416 H10) in (let TMP_419 \def (\lambda (t2: T).(let TMP_417 \def (S d1) 
in (let TMP_418 \def (lift h1 TMP_417 t2) in (eq T x1 TMP_418)))) in (let 
TMP_422 \def (\lambda (t2: T).(let TMP_420 \def (S d2) in (let TMP_421 \def 
(lift h2 TMP_420 t2) in (eq T t0 TMP_421)))) in (let TMP_427 \def (\lambda 
(t2: T).(let TMP_423 \def (Bind b) in (let TMP_424 \def (lift h1 d1 x2) in 
(let TMP_425 \def (THead TMP_423 TMP_424 x1) in (let TMP_426 \def (lift h1 d1 
t2) in (eq T TMP_425 TMP_426)))))) in (let TMP_432 \def (\lambda (t2: T).(let 
TMP_428 \def (Bind b) in (let TMP_429 \def (lift h2 d2 x2) in (let TMP_430 
\def (THead TMP_428 TMP_429 t0) in (let TMP_431 \def (lift h2 d2 t2) in (eq T 
TMP_430 TMP_431)))))) in (let TMP_433 \def (ex2 T TMP_427 TMP_432) in (let 
TMP_524 \def (\lambda (x3: T).(\lambda (H12: (eq T x1 (lift h1 (S d1) 
x3))).(\lambda (H13: (eq T t0 (lift h2 (S d2) x3))).(let TMP_434 \def (S d1) 
in (let TMP_435 \def (lift h1 TMP_434 x3) in (let TMP_446 \def (\lambda (t2: 
T).(let TMP_440 \def (\lambda (t3: T).(let TMP_436 \def (Bind b) in (let 
TMP_437 \def (lift h1 d1 x2) in (let TMP_438 \def (THead TMP_436 TMP_437 t2) 
in (let TMP_439 \def (lift h1 d1 t3) in (eq T TMP_438 TMP_439)))))) in (let 
TMP_445 \def (\lambda (t3: T).(let TMP_441 \def (Bind b) in (let TMP_442 \def 
(lift h2 d2 x2) in (let TMP_443 \def (THead TMP_441 TMP_442 t0) in (let 
TMP_444 \def (lift h2 d2 t3) in (eq T TMP_443 TMP_444)))))) in (ex2 T TMP_440 
TMP_445)))) in (let TMP_447 \def (S d2) in (let TMP_448 \def (lift h2 TMP_447 
x3) in (let TMP_461 \def (\lambda (t2: T).(let TMP_455 \def (\lambda (t3: 
T).(let TMP_449 \def (Bind b) in (let TMP_450 \def (lift h1 d1 x2) in (let 
TMP_451 \def (S d1) in (let TMP_452 \def (lift h1 TMP_451 x3) in (let TMP_453 
\def (THead TMP_449 TMP_450 TMP_452) in (let TMP_454 \def (lift h1 d1 t3) in 
(eq T TMP_453 TMP_454)))))))) in (let TMP_460 \def (\lambda (t3: T).(let 
TMP_456 \def (Bind b) in (let TMP_457 \def (lift h2 d2 x2) in (let TMP_458 
\def (THead TMP_456 TMP_457 t2) in (let TMP_459 \def (lift h2 d2 t3) in (eq T 
TMP_458 TMP_459)))))) in (ex2 T TMP_455 TMP_460)))) in (let TMP_468 \def 
(\lambda (t2: T).(let TMP_462 \def (Bind b) in (let TMP_463 \def (lift h1 d1 
x2) in (let TMP_464 \def (S d1) in (let TMP_465 \def (lift h1 TMP_464 x3) in 
(let TMP_466 \def (THead TMP_462 TMP_463 TMP_465) in (let TMP_467 \def (lift 
h1 d1 t2) in (eq T TMP_466 TMP_467)))))))) in (let TMP_475 \def (\lambda (t2: 
T).(let TMP_469 \def (Bind b) in (let TMP_470 \def (lift h2 d2 x2) in (let 
TMP_471 \def (S d2) in (let TMP_472 \def (lift h2 TMP_471 x3) in (let TMP_473 
\def (THead TMP_469 TMP_470 TMP_472) in (let TMP_474 \def (lift h2 d2 t2) in 
(eq T TMP_473 TMP_474)))))))) in (let TMP_476 \def (Bind b) in (let TMP_477 
\def (THead TMP_476 x2 x3) in (let TMP_478 \def (Bind b) in (let TMP_479 \def 
(lift h1 d1 x2) in (let TMP_480 \def (S d1) in (let TMP_481 \def (lift h1 
TMP_480 x3) in (let TMP_482 \def (THead TMP_478 TMP_479 TMP_481) in (let 
TMP_488 \def (\lambda (t2: T).(let TMP_483 \def (Bind b) in (let TMP_484 \def 
(lift h1 d1 x2) in (let TMP_485 \def (S d1) in (let TMP_486 \def (lift h1 
TMP_485 x3) in (let TMP_487 \def (THead TMP_483 TMP_484 TMP_486) in (eq T 
TMP_487 t2))))))) in (let TMP_489 \def (Bind b) in (let TMP_490 \def (lift h1 
d1 x2) in (let TMP_491 \def (S d1) in (let TMP_492 \def (lift h1 TMP_491 x3) 
in (let TMP_493 \def (THead TMP_489 TMP_490 TMP_492) in (let TMP_494 \def 
(refl_equal T TMP_493) in (let TMP_495 \def (Bind b) in (let TMP_496 \def 
(THead TMP_495 x2 x3) in (let TMP_497 \def (lift h1 d1 TMP_496) in (let 
TMP_498 \def (lift_bind b x2 x3 h1 d1) in (let TMP_499 \def (eq_ind_r T 
TMP_482 TMP_488 TMP_494 TMP_497 TMP_498) in (let TMP_500 \def (Bind b) in 
(let TMP_501 \def (lift h2 d2 x2) in (let TMP_502 \def (S d2) in (let TMP_503 
\def (lift h2 TMP_502 x3) in (let TMP_504 \def (THead TMP_500 TMP_501 
TMP_503) in (let TMP_510 \def (\lambda (t2: T).(let TMP_505 \def (Bind b) in 
(let TMP_506 \def (lift h2 d2 x2) in (let TMP_507 \def (S d2) in (let TMP_508 
\def (lift h2 TMP_507 x3) in (let TMP_509 \def (THead TMP_505 TMP_506 
TMP_508) in (eq T TMP_509 t2))))))) in (let TMP_511 \def (Bind b) in (let 
TMP_512 \def (lift h2 d2 x2) in (let TMP_513 \def (S d2) in (let TMP_514 \def 
(lift h2 TMP_513 x3) in (let TMP_515 \def (THead TMP_511 TMP_512 TMP_514) in 
(let TMP_516 \def (refl_equal T TMP_515) in (let TMP_517 \def (Bind b) in 
(let TMP_518 \def (THead TMP_517 x2 x3) in (let TMP_519 \def (lift h2 d2 
TMP_518) in (let TMP_520 \def (lift_bind b x2 x3 h2 d2) in (let TMP_521 \def 
(eq_ind_r T TMP_504 TMP_510 TMP_516 TMP_519 TMP_520) in (let TMP_522 \def 
(ex_intro2 T TMP_468 TMP_475 TMP_477 TMP_499 TMP_521) in (let TMP_523 \def 
(eq_ind_r T TMP_448 TMP_461 TMP_522 t0 H13) in (eq_ind_r T TMP_435 TMP_446 
TMP_523 x1 H12)))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_525 \def (S d1) in (let TMP_526 \def (S d2) in (let TMP_527 \def (le_n_S 
d1 d2 H1) in (let TMP_528 \def (H0 x1 h1 h2 TMP_525 TMP_526 TMP_527 H11) in 
(let TMP_529 \def (ex2_ind T TMP_419 TMP_422 TMP_433 TMP_524 TMP_528) in (let 
TMP_530 \def (eq_ind_r T TMP_396 TMP_406 TMP_529 t H9) in (eq_ind_r T TMP_386 
TMP_395 TMP_530 x0 H8))))))))))))))))))))))))))))) in (let TMP_532 \def (H x0 
h1 h2 d1 d2 H1 H6) in (let TMP_533 \def (ex2_ind T TMP_374 TMP_376 TMP_385 
TMP_531 TMP_532) in (eq_ind_r T TMP_365 TMP_372 TMP_533 x H5))))))))))))))))) 
in (let TMP_535 \def (lift h1 d1 t) in (let TMP_536 \def (S d1) in (let 
TMP_537 \def (lift h1 TMP_536 t0) in (let TMP_538 \def (plus d2 h1) in (let 
TMP_539 \def (lift_gen_bind b TMP_535 TMP_537 x h2 TMP_538 H4) in (ex3_2_ind 
T T TMP_346 TMP_350 TMP_356 TMP_363 TMP_534 TMP_539)))))))))))))))))))))))))) 
in (let TMP_719 \def (\lambda (f: F).(\lambda (H3: (eq T (lift h1 d1 (THead 
(Flat f) t t0)) (lift h2 (plus d2 h1) x))).(let TMP_541 \def (Flat f) in (let 
TMP_542 \def (THead TMP_541 t t0) in (let TMP_543 \def (lift h1 d1 TMP_542) 
in (let TMP_546 \def (\lambda (t2: T).(let TMP_544 \def (plus d2 h1) in (let 
TMP_545 \def (lift h2 TMP_544 x) in (eq T t2 TMP_545)))) in (let TMP_547 \def 
(Flat f) in (let TMP_548 \def (lift h1 d1 t) in (let TMP_549 \def (lift h1 d1 
t0) in (let TMP_550 \def (THead TMP_547 TMP_548 TMP_549) in (let TMP_551 \def 
(lift_flat f t t0 h1 d1) in (let H4 \def (eq_ind T TMP_543 TMP_546 H3 TMP_550 
TMP_551) in (let TMP_554 \def (\lambda (y: T).(\lambda (z: T).(let TMP_552 
\def (Flat f) in (let TMP_553 \def (THead TMP_552 y z) in (eq T x 
TMP_553))))) in (let TMP_558 \def (\lambda (y: T).(\lambda (_: T).(let 
TMP_555 \def (lift h1 d1 t) in (let TMP_556 \def (plus d2 h1) in (let TMP_557 
\def (lift h2 TMP_556 y) in (eq T TMP_555 TMP_557)))))) in (let TMP_562 \def 
(\lambda (_: T).(\lambda (z: T).(let TMP_559 \def (lift h1 d1 t0) in (let 
TMP_560 \def (plus d2 h1) in (let TMP_561 \def (lift h2 TMP_560 z) in (eq T 
TMP_559 TMP_561)))))) in (let TMP_564 \def (\lambda (t2: T).(let TMP_563 \def 
(lift h1 d1 t2) in (eq T x TMP_563))) in (let TMP_568 \def (\lambda (t2: 
T).(let TMP_565 \def (Flat f) in (let TMP_566 \def (THead TMP_565 t t0) in 
(let TMP_567 \def (lift h2 d2 t2) in (eq T TMP_566 TMP_567))))) in (let 
TMP_569 \def (ex2 T TMP_564 TMP_568) in (let TMP_714 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H5: (eq T x (THead (Flat f) x0 x1))).(\lambda 
(H6: (eq T (lift h1 d1 t) (lift h2 (plus d2 h1) x0))).(\lambda (H7: (eq T 
(lift h1 d1 t0) (lift h2 (plus d2 h1) x1))).(let TMP_570 \def (Flat f) in 
(let TMP_571 \def (THead TMP_570 x0 x1) in (let TMP_578 \def (\lambda (t2: 
T).(let TMP_573 \def (\lambda (t3: T).(let TMP_572 \def (lift h1 d1 t3) in 
(eq T t2 TMP_572))) in (let TMP_577 \def (\lambda (t3: T).(let TMP_574 \def 
(Flat f) in (let TMP_575 \def (THead TMP_574 t t0) in (let TMP_576 \def (lift 
h2 d2 t3) in (eq T TMP_575 TMP_576))))) in (ex2 T TMP_573 TMP_577)))) in (let 
TMP_580 \def (\lambda (t2: T).(let TMP_579 \def (lift h1 d1 t2) in (eq T x0 
TMP_579))) in (let TMP_582 \def (\lambda (t2: T).(let TMP_581 \def (lift h2 
d2 t2) in (eq T t TMP_581))) in (let TMP_586 \def (\lambda (t2: T).(let 
TMP_583 \def (Flat f) in (let TMP_584 \def (THead TMP_583 x0 x1) in (let 
TMP_585 \def (lift h1 d1 t2) in (eq T TMP_584 TMP_585))))) in (let TMP_590 
\def (\lambda (t2: T).(let TMP_587 \def (Flat f) in (let TMP_588 \def (THead 
TMP_587 t t0) in (let TMP_589 \def (lift h2 d2 t2) in (eq T TMP_588 
TMP_589))))) in (let TMP_591 \def (ex2 T TMP_586 TMP_590) in (let TMP_711 
\def (\lambda (x2: T).(\lambda (H8: (eq T x0 (lift h1 d1 x2))).(\lambda (H9: 
(eq T t (lift h2 d2 x2))).(let TMP_592 \def (lift h1 d1 x2) in (let TMP_601 
\def (\lambda (t2: T).(let TMP_596 \def (\lambda (t3: T).(let TMP_593 \def 
(Flat f) in (let TMP_594 \def (THead TMP_593 t2 x1) in (let TMP_595 \def 
(lift h1 d1 t3) in (eq T TMP_594 TMP_595))))) in (let TMP_600 \def (\lambda 
(t3: T).(let TMP_597 \def (Flat f) in (let TMP_598 \def (THead TMP_597 t t0) 
in (let TMP_599 \def (lift h2 d2 t3) in (eq T TMP_598 TMP_599))))) in (ex2 T 
TMP_596 TMP_600)))) in (let TMP_602 \def (lift h2 d2 x2) in (let TMP_612 \def 
(\lambda (t2: T).(let TMP_607 \def (\lambda (t3: T).(let TMP_603 \def (Flat 
f) in (let TMP_604 \def (lift h1 d1 x2) in (let TMP_605 \def (THead TMP_603 
TMP_604 x1) in (let TMP_606 \def (lift h1 d1 t3) in (eq T TMP_605 
TMP_606)))))) in (let TMP_611 \def (\lambda (t3: T).(let TMP_608 \def (Flat 
f) in (let TMP_609 \def (THead TMP_608 t2 t0) in (let TMP_610 \def (lift h2 
d2 t3) in (eq T TMP_609 TMP_610))))) in (ex2 T TMP_607 TMP_611)))) in (let 
TMP_614 \def (\lambda (t2: T).(let TMP_613 \def (lift h1 d1 t2) in (eq T x1 
TMP_613))) in (let TMP_616 \def (\lambda (t2: T).(let TMP_615 \def (lift h2 
d2 t2) in (eq T t0 TMP_615))) in (let TMP_621 \def (\lambda (t2: T).(let 
TMP_617 \def (Flat f) in (let TMP_618 \def (lift h1 d1 x2) in (let TMP_619 
\def (THead TMP_617 TMP_618 x1) in (let TMP_620 \def (lift h1 d1 t2) in (eq T 
TMP_619 TMP_620)))))) in (let TMP_626 \def (\lambda (t2: T).(let TMP_622 \def 
(Flat f) in (let TMP_623 \def (lift h2 d2 x2) in (let TMP_624 \def (THead 
TMP_622 TMP_623 t0) in (let TMP_625 \def (lift h2 d2 t2) in (eq T TMP_624 
TMP_625)))))) in (let TMP_627 \def (ex2 T TMP_621 TMP_626) in (let TMP_707 
\def (\lambda (x3: T).(\lambda (H10: (eq T x1 (lift h1 d1 x3))).(\lambda 
(H11: (eq T t0 (lift h2 d2 x3))).(let TMP_628 \def (lift h1 d1 x3) in (let 
TMP_639 \def (\lambda (t2: T).(let TMP_633 \def (\lambda (t3: T).(let TMP_629 
\def (Flat f) in (let TMP_630 \def (lift h1 d1 x2) in (let TMP_631 \def 
(THead TMP_629 TMP_630 t2) in (let TMP_632 \def (lift h1 d1 t3) in (eq T 
TMP_631 TMP_632)))))) in (let TMP_638 \def (\lambda (t3: T).(let TMP_634 \def 
(Flat f) in (let TMP_635 \def (lift h2 d2 x2) in (let TMP_636 \def (THead 
TMP_634 TMP_635 t0) in (let TMP_637 \def (lift h2 d2 t3) in (eq T TMP_636 
TMP_637)))))) in (ex2 T TMP_633 TMP_638)))) in (let TMP_640 \def (lift h2 d2 
x3) in (let TMP_652 \def (\lambda (t2: T).(let TMP_646 \def (\lambda (t3: 
T).(let TMP_641 \def (Flat f) in (let TMP_642 \def (lift h1 d1 x2) in (let 
TMP_643 \def (lift h1 d1 x3) in (let TMP_644 \def (THead TMP_641 TMP_642 
TMP_643) in (let TMP_645 \def (lift h1 d1 t3) in (eq T TMP_644 TMP_645))))))) 
in (let TMP_651 \def (\lambda (t3: T).(let TMP_647 \def (Flat f) in (let 
TMP_648 \def (lift h2 d2 x2) in (let TMP_649 \def (THead TMP_647 TMP_648 t2) 
in (let TMP_650 \def (lift h2 d2 t3) in (eq T TMP_649 TMP_650)))))) in (ex2 T 
TMP_646 TMP_651)))) in (let TMP_658 \def (\lambda (t2: T).(let TMP_653 \def 
(Flat f) in (let TMP_654 \def (lift h1 d1 x2) in (let TMP_655 \def (lift h1 
d1 x3) in (let TMP_656 \def (THead TMP_653 TMP_654 TMP_655) in (let TMP_657 
\def (lift h1 d1 t2) in (eq T TMP_656 TMP_657))))))) in (let TMP_664 \def 
(\lambda (t2: T).(let TMP_659 \def (Flat f) in (let TMP_660 \def (lift h2 d2 
x2) in (let TMP_661 \def (lift h2 d2 x3) in (let TMP_662 \def (THead TMP_659 
TMP_660 TMP_661) in (let TMP_663 \def (lift h2 d2 t2) in (eq T TMP_662 
TMP_663))))))) in (let TMP_665 \def (Flat f) in (let TMP_666 \def (THead 
TMP_665 x2 x3) in (let TMP_667 \def (Flat f) in (let TMP_668 \def (lift h1 d1 
x2) in (let TMP_669 \def (lift h1 d1 x3) in (let TMP_670 \def (THead TMP_667 
TMP_668 TMP_669) in (let TMP_675 \def (\lambda (t2: T).(let TMP_671 \def 
(Flat f) in (let TMP_672 \def (lift h1 d1 x2) in (let TMP_673 \def (lift h1 
d1 x3) in (let TMP_674 \def (THead TMP_671 TMP_672 TMP_673) in (eq T TMP_674 
t2)))))) in (let TMP_676 \def (Flat f) in (let TMP_677 \def (lift h1 d1 x2) 
in (let TMP_678 \def (lift h1 d1 x3) in (let TMP_679 \def (THead TMP_676 
TMP_677 TMP_678) in (let TMP_680 \def (refl_equal T TMP_679) in (let TMP_681 
\def (Flat f) in (let TMP_682 \def (THead TMP_681 x2 x3) in (let TMP_683 \def 
(lift h1 d1 TMP_682) in (let TMP_684 \def (lift_flat f x2 x3 h1 d1) in (let 
TMP_685 \def (eq_ind_r T TMP_670 TMP_675 TMP_680 TMP_683 TMP_684) in (let 
TMP_686 \def (Flat f) in (let TMP_687 \def (lift h2 d2 x2) in (let TMP_688 
\def (lift h2 d2 x3) in (let TMP_689 \def (THead TMP_686 TMP_687 TMP_688) in 
(let TMP_694 \def (\lambda (t2: T).(let TMP_690 \def (Flat f) in (let TMP_691 
\def (lift h2 d2 x2) in (let TMP_692 \def (lift h2 d2 x3) in (let TMP_693 
\def (THead TMP_690 TMP_691 TMP_692) in (eq T TMP_693 t2)))))) in (let 
TMP_695 \def (Flat f) in (let TMP_696 \def (lift h2 d2 x2) in (let TMP_697 
\def (lift h2 d2 x3) in (let TMP_698 \def (THead TMP_695 TMP_696 TMP_697) in 
(let TMP_699 \def (refl_equal T TMP_698) in (let TMP_700 \def (Flat f) in 
(let TMP_701 \def (THead TMP_700 x2 x3) in (let TMP_702 \def (lift h2 d2 
TMP_701) in (let TMP_703 \def (lift_flat f x2 x3 h2 d2) in (let TMP_704 \def 
(eq_ind_r T TMP_689 TMP_694 TMP_699 TMP_702 TMP_703) in (let TMP_705 \def 
(ex_intro2 T TMP_658 TMP_664 TMP_666 TMP_685 TMP_704) in (let TMP_706 \def 
(eq_ind_r T TMP_640 TMP_652 TMP_705 t0 H11) in (eq_ind_r T TMP_628 TMP_639 
TMP_706 x1 H10)))))))))))))))))))))))))))))))))))))))))))) in (let TMP_708 
\def (H0 x1 h1 h2 d1 d2 H1 H7) in (let TMP_709 \def (ex2_ind T TMP_614 
TMP_616 TMP_627 TMP_707 TMP_708) in (let TMP_710 \def (eq_ind_r T TMP_602 
TMP_612 TMP_709 t H9) in (eq_ind_r T TMP_592 TMP_601 TMP_710 x0 
H8))))))))))))))))) in (let TMP_712 \def (H x0 h1 h2 d1 d2 H1 H6) in (let 
TMP_713 \def (ex2_ind T TMP_580 TMP_582 TMP_591 TMP_711 TMP_712) in (eq_ind_r 
T TMP_571 TMP_578 TMP_713 x H5))))))))))))))))) in (let TMP_715 \def (lift h1 
d1 t) in (let TMP_716 \def (lift h1 d1 t0) in (let TMP_717 \def (plus d2 h1) 
in (let TMP_718 \def (lift_gen_flat f TMP_715 TMP_716 x h2 TMP_717 H4) in 
(ex3_2_ind T T TMP_554 TMP_558 TMP_562 TMP_569 TMP_714 
TMP_718)))))))))))))))))))))))) in (K_ind TMP_331 TMP_540 TMP_719 k 
H2)))))))))))))))) in (T_ind TMP_5 TMP_48 TMP_325 TMP_720 t1))))).

theorem lifts_inj:
 \forall (xs: TList).(\forall (ts: TList).(\forall (h: nat).(\forall (d: 
nat).((eq TList (lifts h d xs) (lifts h d ts)) \to (eq TList xs ts)))))
\def
 \lambda (xs: TList).(let TMP_1 \def (\lambda (t: TList).(\forall (ts: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d t) (lifts h 
d ts)) \to (eq TList t ts)))))) in (let TMP_11 \def (\lambda (ts: TList).(let 
TMP_2 \def (\lambda (t: TList).(\forall (h: nat).(\forall (d: nat).((eq TList 
(lifts h d TNil) (lifts h d t)) \to (eq TList TNil t))))) in (let TMP_3 \def 
(\lambda (_: nat).(\lambda (_: nat).(\lambda (_: (eq TList TNil 
TNil)).(refl_equal TList TNil)))) in (let TMP_10 \def (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (_: ((\forall (h: nat).(\forall (d: 
nat).((eq TList TNil (lifts h d t0)) \to (eq TList TNil t0)))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (eq TList TNil (TCons (lift h d t) 
(lifts h d t0)))).(let TMP_4 \def (\lambda (ee: TList).(match ee with [TNil 
\Rightarrow True | (TCons _ _) \Rightarrow False])) in (let TMP_5 \def (lift 
h d t) in (let TMP_6 \def (lifts h d t0) in (let TMP_7 \def (TCons TMP_5 
TMP_6) in (let H1 \def (eq_ind TList TNil TMP_4 I TMP_7 H0) in (let TMP_8 
\def (TCons t t0) in (let TMP_9 \def (eq TList TNil TMP_8) in (False_ind 
TMP_9 H1)))))))))))))) in (TList_ind TMP_2 TMP_3 TMP_10 ts))))) in (let 
TMP_52 \def (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: ((\forall (ts: 
TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h d t0) (lifts h 
d ts)) \to (eq TList t0 ts))))))).(\lambda (ts: TList).(let TMP_13 \def 
(\lambda (t1: TList).(\forall (h: nat).(\forall (d: nat).((eq TList (lifts h 
d (TCons t t0)) (lifts h d t1)) \to (let TMP_12 \def (TCons t t0) in (eq 
TList TMP_12 t1)))))) in (let TMP_20 \def (\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H0: (eq TList (TCons (lift h d t) (lifts h d t0)) TNil)).(let 
TMP_14 \def (lift h d t) in (let TMP_15 \def (lifts h d t0) in (let TMP_16 
\def (TCons TMP_14 TMP_15) in (let TMP_17 \def (\lambda (ee: TList).(match ee 
with [TNil \Rightarrow False | (TCons _ _) \Rightarrow True])) in (let H1 
\def (eq_ind TList TMP_16 TMP_17 I TNil H0) in (let TMP_18 \def (TCons t t0) 
in (let TMP_19 \def (eq TList TMP_18 TNil) in (False_ind TMP_19 H1))))))))))) 
in (let TMP_51 \def (\lambda (t1: T).(\lambda (t2: TList).(\lambda (_: 
((\forall (h: nat).(\forall (d: nat).((eq TList (TCons (lift h d t) (lifts h 
d t0)) (lifts h d t2)) \to (eq TList (TCons t t0) t2)))))).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (eq TList (TCons (lift h d t) (lifts h d 
t0)) (TCons (lift h d t1) (lifts h d t2)))).(let TMP_27 \def (\lambda (e: 
TList).(match e with [TNil \Rightarrow (let TMP_26 \def (\lambda (x: 
nat).(plus x h)) in (lref_map TMP_26 d t)) | (TCons t3 _) \Rightarrow t3])) 
in (let TMP_28 \def (lift h d t) in (let TMP_29 \def (lifts h d t0) in (let 
TMP_30 \def (TCons TMP_28 TMP_29) in (let TMP_31 \def (lift h d t1) in (let 
TMP_32 \def (lifts h d t2) in (let TMP_33 \def (TCons TMP_31 TMP_32) in (let 
H2 \def (f_equal TList T TMP_27 TMP_30 TMP_33 H1) in (let TMP_36 \def 
(\lambda (e: TList).(match e with [TNil \Rightarrow (lifts h d t0) | (TCons _ 
t3) \Rightarrow t3])) in (let TMP_37 \def (lift h d t) in (let TMP_38 \def 
(lifts h d t0) in (let TMP_39 \def (TCons TMP_37 TMP_38) in (let TMP_40 \def 
(lift h d t1) in (let TMP_41 \def (lifts h d t2) in (let TMP_42 \def (TCons 
TMP_40 TMP_41) in (let H3 \def (f_equal TList TList TMP_36 TMP_39 TMP_42 H1) 
in (let TMP_50 \def (\lambda (H4: (eq T (lift h d t) (lift h d t1))).(let 
TMP_45 \def (\lambda (t3: T).(let TMP_43 \def (TCons t t0) in (let TMP_44 
\def (TCons t3 t2) in (eq TList TMP_43 TMP_44)))) in (let TMP_46 \def 
(refl_equal T t) in (let TMP_47 \def (H t2 h d H3) in (let TMP_48 \def 
(f_equal2 T TList TList TCons t t t0 t2 TMP_46 TMP_47) in (let TMP_49 \def 
(lift_inj t t1 h d H4) in (eq_ind T t TMP_45 TMP_48 t1 TMP_49))))))) in 
(TMP_50 H2)))))))))))))))))))))))) in (TList_ind TMP_13 TMP_20 TMP_51 
ts)))))))) in (TList_ind TMP_1 TMP_11 TMP_52 xs)))).

