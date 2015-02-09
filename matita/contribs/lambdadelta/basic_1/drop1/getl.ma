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

include "basic_1/drop1/fwd.ma".

include "basic_1/getl/drop.ma".

theorem drop1_getl_trans:
 \forall (hds: PList).(\forall (c1: C).(\forall (c2: C).((drop1 hds c2 c1) 
\to (\forall (b: B).(\forall (e1: C).(\forall (v: T).(\forall (i: nat).((getl 
i c1 (CHead e1 (Bind b) v)) \to (ex2 C (\lambda (e2: C).(drop1 (ptrans hds i) 
e2 e1)) (\lambda (e2: C).(getl (trans hds i) c2 (CHead e2 (Bind b) (lift1 
(ptrans hds i) v)))))))))))))
\def
 \lambda (hds: PList).(let TMP_9 \def (\lambda (p: PList).(\forall (c1: 
C).(\forall (c2: C).((drop1 p c2 c1) \to (\forall (b: B).(\forall (e1: 
C).(\forall (v: T).(\forall (i: nat).((getl i c1 (CHead e1 (Bind b) v)) \to 
(let TMP_2 \def (\lambda (e2: C).(let TMP_1 \def (ptrans p i) in (drop1 TMP_1 
e2 e1))) in (let TMP_8 \def (\lambda (e2: C).(let TMP_3 \def (trans p i) in 
(let TMP_4 \def (Bind b) in (let TMP_5 \def (ptrans p i) in (let TMP_6 \def 
(lift1 TMP_5 v) in (let TMP_7 \def (CHead e2 TMP_4 TMP_6) in (getl TMP_3 c2 
TMP_7))))))) in (ex2 C TMP_2 TMP_8)))))))))))) in (let TMP_21 \def (\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H: (drop1 PNil c2 c1)).(\lambda (b: 
B).(\lambda (e1: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl i 
c1 (CHead e1 (Bind b) v))).(let H_y \def (drop1_gen_pnil c2 c1 H) in (let 
TMP_14 \def (\lambda (c: C).(let TMP_10 \def (\lambda (e2: C).(drop1 PNil e2 
e1)) in (let TMP_13 \def (\lambda (e2: C).(let TMP_11 \def (Bind b) in (let 
TMP_12 \def (CHead e2 TMP_11 v) in (getl i c TMP_12)))) in (ex2 C TMP_10 
TMP_13)))) in (let TMP_15 \def (\lambda (e2: C).(drop1 PNil e2 e1)) in (let 
TMP_18 \def (\lambda (e2: C).(let TMP_16 \def (Bind b) in (let TMP_17 \def 
(CHead e2 TMP_16 v) in (getl i c1 TMP_17)))) in (let TMP_19 \def (drop1_nil 
e1) in (let TMP_20 \def (ex_intro2 C TMP_15 TMP_18 e1 TMP_19 H0) in (eq_ind_r 
C c1 TMP_14 TMP_20 c2 H_y))))))))))))))) in (let TMP_210 \def (\lambda (h: 
nat).(\lambda (d: nat).(\lambda (hds0: PList).(\lambda (H: ((\forall (c1: 
C).(\forall (c2: C).((drop1 hds0 c2 c1) \to (\forall (b: B).(\forall (e1: 
C).(\forall (v: T).(\forall (i: nat).((getl i c1 (CHead e1 (Bind b) v)) \to 
(ex2 C (\lambda (e2: C).(drop1 (ptrans hds0 i) e2 e1)) (\lambda (e2: C).(getl 
(trans hds0 i) c2 (CHead e2 (Bind b) (lift1 (ptrans hds0 i) 
v))))))))))))))).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H0: (drop1 
(PCons h d hds0) c2 c1)).(\lambda (b: B).(\lambda (e1: C).(\lambda (v: 
T).(\lambda (i: nat).(\lambda (H1: (getl i c1 (CHead e1 (Bind b) v))).(let 
H_x \def (drop1_gen_pcons c2 c1 hds0 h d H0) in (let H2 \def H_x in (let 
TMP_22 \def (\lambda (c3: C).(drop h d c2 c3)) in (let TMP_23 \def (\lambda 
(c3: C).(drop1 hds0 c3 c1)) in (let TMP_31 \def (\lambda (e2: C).(let TMP_24 
\def (trans hds0 i) in (let TMP_25 \def (blt TMP_24 d) in (let TMP_30 \def 
(match TMP_25 with [true \Rightarrow (let TMP_26 \def (trans hds0 i) in (let 
TMP_27 \def (S TMP_26) in (let TMP_28 \def (minus d TMP_27) in (let TMP_29 
\def (ptrans hds0 i) in (PCons h TMP_28 TMP_29))))) | false \Rightarrow 
(ptrans hds0 i)]) in (drop1 TMP_30 e2 e1))))) in (let TMP_46 \def (\lambda 
(e2: C).(let TMP_32 \def (trans hds0 i) in (let TMP_33 \def (blt TMP_32 d) in 
(let TMP_35 \def (match TMP_33 with [true \Rightarrow (trans hds0 i) | false 
\Rightarrow (let TMP_34 \def (trans hds0 i) in (plus TMP_34 h))]) in (let 
TMP_36 \def (Bind b) in (let TMP_37 \def (trans hds0 i) in (let TMP_38 \def 
(blt TMP_37 d) in (let TMP_43 \def (match TMP_38 with [true \Rightarrow (let 
TMP_39 \def (trans hds0 i) in (let TMP_40 \def (S TMP_39) in (let TMP_41 \def 
(minus d TMP_40) in (let TMP_42 \def (ptrans hds0 i) in (PCons h TMP_41 
TMP_42))))) | false \Rightarrow (ptrans hds0 i)]) in (let TMP_44 \def (lift1 
TMP_43 v) in (let TMP_45 \def (CHead e2 TMP_36 TMP_44) in (getl TMP_35 c2 
TMP_45))))))))))) in (let TMP_47 \def (ex2 C TMP_31 TMP_46) in (let TMP_209 
\def (\lambda (x: C).(\lambda (H3: (drop h d c2 x)).(\lambda (H4: (drop1 hds0 
x c1)).(let TMP_48 \def (trans hds0 i) in (let TMP_49 \def (blt TMP_48 d) in 
(let TMP_67 \def (\lambda (b0: bool).(let TMP_55 \def (\lambda (e2: C).(let 
TMP_54 \def (match b0 with [true \Rightarrow (let TMP_50 \def (trans hds0 i) 
in (let TMP_51 \def (S TMP_50) in (let TMP_52 \def (minus d TMP_51) in (let 
TMP_53 \def (ptrans hds0 i) in (PCons h TMP_52 TMP_53))))) | false 
\Rightarrow (ptrans hds0 i)]) in (drop1 TMP_54 e2 e1))) in (let TMP_66 \def 
(\lambda (e2: C).(let TMP_57 \def (match b0 with [true \Rightarrow (trans 
hds0 i) | false \Rightarrow (let TMP_56 \def (trans hds0 i) in (plus TMP_56 
h))]) in (let TMP_58 \def (Bind b) in (let TMP_63 \def (match b0 with [true 
\Rightarrow (let TMP_59 \def (trans hds0 i) in (let TMP_60 \def (S TMP_59) in 
(let TMP_61 \def (minus d TMP_60) in (let TMP_62 \def (ptrans hds0 i) in 
(PCons h TMP_61 TMP_62))))) | false \Rightarrow (ptrans hds0 i)]) in (let 
TMP_64 \def (lift1 TMP_63 v) in (let TMP_65 \def (CHead e2 TMP_58 TMP_64) in 
(getl TMP_57 c2 TMP_65))))))) in (ex2 C TMP_55 TMP_66)))) in (let TMP_208 
\def (\lambda (x_x: bool).(let TMP_85 \def (\lambda (b0: bool).((eq bool (blt 
(trans hds0 i) d) b0) \to (let TMP_73 \def (\lambda (e2: C).(let TMP_72 \def 
(match b0 with [true \Rightarrow (let TMP_68 \def (trans hds0 i) in (let 
TMP_69 \def (S TMP_68) in (let TMP_70 \def (minus d TMP_69) in (let TMP_71 
\def (ptrans hds0 i) in (PCons h TMP_70 TMP_71))))) | false \Rightarrow 
(ptrans hds0 i)]) in (drop1 TMP_72 e2 e1))) in (let TMP_84 \def (\lambda (e2: 
C).(let TMP_75 \def (match b0 with [true \Rightarrow (trans hds0 i) | false 
\Rightarrow (let TMP_74 \def (trans hds0 i) in (plus TMP_74 h))]) in (let 
TMP_76 \def (Bind b) in (let TMP_81 \def (match b0 with [true \Rightarrow 
(let TMP_77 \def (trans hds0 i) in (let TMP_78 \def (S TMP_77) in (let TMP_79 
\def (minus d TMP_78) in (let TMP_80 \def (ptrans hds0 i) in (PCons h TMP_79 
TMP_80))))) | false \Rightarrow (ptrans hds0 i)]) in (let TMP_82 \def (lift1 
TMP_81 v) in (let TMP_83 \def (CHead e2 TMP_76 TMP_82) in (getl TMP_75 c2 
TMP_83))))))) in (ex2 C TMP_73 TMP_84))))) in (let TMP_170 \def (\lambda (H5: 
(eq bool (blt (trans hds0 i) d) true)).(let H_x0 \def (H c1 x H4 b e1 v i H1) 
in (let H6 \def H_x0 in (let TMP_87 \def (\lambda (e2: C).(let TMP_86 \def 
(ptrans hds0 i) in (drop1 TMP_86 e2 e1))) in (let TMP_93 \def (\lambda (e2: 
C).(let TMP_88 \def (trans hds0 i) in (let TMP_89 \def (Bind b) in (let 
TMP_90 \def (ptrans hds0 i) in (let TMP_91 \def (lift1 TMP_90 v) in (let 
TMP_92 \def (CHead e2 TMP_89 TMP_91) in (getl TMP_88 x TMP_92))))))) in (let 
TMP_99 \def (\lambda (e2: C).(let TMP_94 \def (trans hds0 i) in (let TMP_95 
\def (S TMP_94) in (let TMP_96 \def (minus d TMP_95) in (let TMP_97 \def 
(ptrans hds0 i) in (let TMP_98 \def (PCons h TMP_96 TMP_97) in (drop1 TMP_98 
e2 e1))))))) in (let TMP_109 \def (\lambda (e2: C).(let TMP_100 \def (trans 
hds0 i) in (let TMP_101 \def (Bind b) in (let TMP_102 \def (trans hds0 i) in 
(let TMP_103 \def (S TMP_102) in (let TMP_104 \def (minus d TMP_103) in (let 
TMP_105 \def (ptrans hds0 i) in (let TMP_106 \def (PCons h TMP_104 TMP_105) 
in (let TMP_107 \def (lift1 TMP_106 v) in (let TMP_108 \def (CHead e2 TMP_101 
TMP_107) in (getl TMP_100 c2 TMP_108))))))))))) in (let TMP_110 \def (ex2 C 
TMP_99 TMP_109) in (let TMP_169 \def (\lambda (x0: C).(\lambda (H7: (drop1 
(ptrans hds0 i) x0 e1)).(\lambda (H8: (getl (trans hds0 i) x (CHead x0 (Bind 
b) (lift1 (ptrans hds0 i) v)))).(let TMP_111 \def (trans hds0 i) in (let 
TMP_112 \def (trans hds0 i) in (let TMP_113 \def (blt_lt d TMP_112 H5) in 
(let TMP_114 \def (ptrans hds0 i) in (let TMP_115 \def (lift1 TMP_114 v) in 
(let H_x1 \def (drop_getl_trans_lt TMP_111 d TMP_113 c2 x h H3 b x0 TMP_115 
H8) in (let H9 \def H_x1 in (let TMP_125 \def (\lambda (e2: C).(let TMP_116 
\def (trans hds0 i) in (let TMP_117 \def (Bind b) in (let TMP_118 \def (trans 
hds0 i) in (let TMP_119 \def (S TMP_118) in (let TMP_120 \def (minus d 
TMP_119) in (let TMP_121 \def (ptrans hds0 i) in (let TMP_122 \def (lift1 
TMP_121 v) in (let TMP_123 \def (lift h TMP_120 TMP_122) in (let TMP_124 \def 
(CHead e2 TMP_117 TMP_123) in (getl TMP_116 c2 TMP_124))))))))))) in (let 
TMP_129 \def (\lambda (e2: C).(let TMP_126 \def (trans hds0 i) in (let 
TMP_127 \def (S TMP_126) in (let TMP_128 \def (minus d TMP_127) in (drop h 
TMP_128 e2 x0))))) in (let TMP_135 \def (\lambda (e2: C).(let TMP_130 \def 
(trans hds0 i) in (let TMP_131 \def (S TMP_130) in (let TMP_132 \def (minus d 
TMP_131) in (let TMP_133 \def (ptrans hds0 i) in (let TMP_134 \def (PCons h 
TMP_132 TMP_133) in (drop1 TMP_134 e2 e1))))))) in (let TMP_145 \def (\lambda 
(e2: C).(let TMP_136 \def (trans hds0 i) in (let TMP_137 \def (Bind b) in 
(let TMP_138 \def (trans hds0 i) in (let TMP_139 \def (S TMP_138) in (let 
TMP_140 \def (minus d TMP_139) in (let TMP_141 \def (ptrans hds0 i) in (let 
TMP_142 \def (PCons h TMP_140 TMP_141) in (let TMP_143 \def (lift1 TMP_142 v) 
in (let TMP_144 \def (CHead e2 TMP_137 TMP_143) in (getl TMP_136 c2 
TMP_144))))))))))) in (let TMP_146 \def (ex2 C TMP_135 TMP_145) in (let 
TMP_168 \def (\lambda (x1: C).(\lambda (H10: (getl (trans hds0 i) c2 (CHead 
x1 (Bind b) (lift h (minus d (S (trans hds0 i))) (lift1 (ptrans hds0 i) 
v))))).(\lambda (H11: (drop h (minus d (S (trans hds0 i))) x1 x0)).(let 
TMP_152 \def (\lambda (e2: C).(let TMP_147 \def (trans hds0 i) in (let 
TMP_148 \def (S TMP_147) in (let TMP_149 \def (minus d TMP_148) in (let 
TMP_150 \def (ptrans hds0 i) in (let TMP_151 \def (PCons h TMP_149 TMP_150) 
in (drop1 TMP_151 e2 e1))))))) in (let TMP_162 \def (\lambda (e2: C).(let 
TMP_153 \def (trans hds0 i) in (let TMP_154 \def (Bind b) in (let TMP_155 
\def (trans hds0 i) in (let TMP_156 \def (S TMP_155) in (let TMP_157 \def 
(minus d TMP_156) in (let TMP_158 \def (ptrans hds0 i) in (let TMP_159 \def 
(PCons h TMP_157 TMP_158) in (let TMP_160 \def (lift1 TMP_159 v) in (let 
TMP_161 \def (CHead e2 TMP_154 TMP_160) in (getl TMP_153 c2 
TMP_161))))))))))) in (let TMP_163 \def (trans hds0 i) in (let TMP_164 \def 
(S TMP_163) in (let TMP_165 \def (minus d TMP_164) in (let TMP_166 \def 
(ptrans hds0 i) in (let TMP_167 \def (drop1_cons x1 x0 h TMP_165 H11 e1 
TMP_166 H7) in (ex_intro2 C TMP_152 TMP_162 x1 TMP_167 H10))))))))))) in 
(ex2_ind C TMP_125 TMP_129 TMP_146 TMP_168 H9))))))))))))))))) in (ex2_ind C 
TMP_87 TMP_93 TMP_110 TMP_169 H6)))))))))) in (let TMP_207 \def (\lambda (H5: 
(eq bool (blt (trans hds0 i) d) false)).(let H_x0 \def (H c1 x H4 b e1 v i 
H1) in (let H6 \def H_x0 in (let TMP_172 \def (\lambda (e2: C).(let TMP_171 
\def (ptrans hds0 i) in (drop1 TMP_171 e2 e1))) in (let TMP_178 \def (\lambda 
(e2: C).(let TMP_173 \def (trans hds0 i) in (let TMP_174 \def (Bind b) in 
(let TMP_175 \def (ptrans hds0 i) in (let TMP_176 \def (lift1 TMP_175 v) in 
(let TMP_177 \def (CHead e2 TMP_174 TMP_176) in (getl TMP_173 x 
TMP_177))))))) in (let TMP_180 \def (\lambda (e2: C).(let TMP_179 \def 
(ptrans hds0 i) in (drop1 TMP_179 e2 e1))) in (let TMP_187 \def (\lambda (e2: 
C).(let TMP_181 \def (trans hds0 i) in (let TMP_182 \def (plus TMP_181 h) in 
(let TMP_183 \def (Bind b) in (let TMP_184 \def (ptrans hds0 i) in (let 
TMP_185 \def (lift1 TMP_184 v) in (let TMP_186 \def (CHead e2 TMP_183 
TMP_185) in (getl TMP_182 c2 TMP_186)))))))) in (let TMP_188 \def (ex2 C 
TMP_180 TMP_187) in (let TMP_206 \def (\lambda (x0: C).(\lambda (H7: (drop1 
(ptrans hds0 i) x0 e1)).(\lambda (H8: (getl (trans hds0 i) x (CHead x0 (Bind 
b) (lift1 (ptrans hds0 i) v)))).(let TMP_189 \def (trans hds0 i) in (let 
TMP_190 \def (Bind b) in (let TMP_191 \def (ptrans hds0 i) in (let TMP_192 
\def (lift1 TMP_191 v) in (let TMP_193 \def (CHead x0 TMP_190 TMP_192) in 
(let H9 \def (drop_getl_trans_ge TMP_189 c2 x d h H3 TMP_193 H8) in (let 
TMP_195 \def (\lambda (e2: C).(let TMP_194 \def (ptrans hds0 i) in (drop1 
TMP_194 e2 e1))) in (let TMP_202 \def (\lambda (e2: C).(let TMP_196 \def 
(trans hds0 i) in (let TMP_197 \def (plus TMP_196 h) in (let TMP_198 \def 
(Bind b) in (let TMP_199 \def (ptrans hds0 i) in (let TMP_200 \def (lift1 
TMP_199 v) in (let TMP_201 \def (CHead e2 TMP_198 TMP_200) in (getl TMP_197 
c2 TMP_201)))))))) in (let TMP_203 \def (trans hds0 i) in (let TMP_204 \def 
(bge_le d TMP_203 H5) in (let TMP_205 \def (H9 TMP_204) in (ex_intro2 C 
TMP_195 TMP_202 x0 H7 TMP_205))))))))))))))) in (ex2_ind C TMP_172 TMP_178 
TMP_188 TMP_206 H6)))))))))) in (bool_ind TMP_85 TMP_170 TMP_207 x_x))))) in 
(xinduction bool TMP_49 TMP_67 TMP_208)))))))) in (ex2_ind C TMP_22 TMP_23 
TMP_47 TMP_209 H2))))))))))))))))))))) in (PList_ind TMP_9 TMP_21 TMP_210 
hds)))).

