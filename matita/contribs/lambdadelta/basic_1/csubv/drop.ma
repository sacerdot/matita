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

include "basic_1/csubv/props.ma".

include "basic_1/csubv/fwd.ma".

include "basic_1/drop/fwd.ma".

theorem csubv_drop_conf:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (e1: 
C).(\forall (h: nat).((drop h O c1 e1) \to (ex2 C (\lambda (e2: C).(csubv e1 
e2)) (\lambda (e2: C).(drop h O c2 e2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(let TMP_3 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (e1: C).(\forall (h: nat).((drop h 
O c e1) \to (let TMP_1 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_2 
\def (\lambda (e2: C).(drop h O c0 e2)) in (ex2 C TMP_1 TMP_2)))))))) in (let 
TMP_34 \def (\lambda (n: nat).(\lambda (e1: C).(\lambda (h: nat).(\lambda 
(H0: (drop h O (CSort n) e1)).(let TMP_4 \def (CSort n) in (let TMP_5 \def 
(eq C e1 TMP_4) in (let TMP_6 \def (eq nat h O) in (let TMP_7 \def (eq nat O 
O) in (let TMP_8 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_10 \def 
(\lambda (e2: C).(let TMP_9 \def (CSort n) in (drop h O TMP_9 e2))) in (let 
TMP_11 \def (ex2 C TMP_8 TMP_10) in (let TMP_32 \def (\lambda (H1: (eq C e1 
(CSort n))).(\lambda (H2: (eq nat h O)).(\lambda (_: (eq nat O O)).(let 
TMP_15 \def (\lambda (n0: nat).(let TMP_12 \def (\lambda (e2: C).(csubv e1 
e2)) in (let TMP_14 \def (\lambda (e2: C).(let TMP_13 \def (CSort n) in (drop 
n0 O TMP_13 e2))) in (ex2 C TMP_12 TMP_14)))) in (let TMP_16 \def (CSort n) 
in (let TMP_20 \def (\lambda (c: C).(let TMP_17 \def (\lambda (e2: C).(csubv 
c e2)) in (let TMP_19 \def (\lambda (e2: C).(let TMP_18 \def (CSort n) in 
(drop O O TMP_18 e2))) in (ex2 C TMP_17 TMP_19)))) in (let TMP_22 \def 
(\lambda (e2: C).(let TMP_21 \def (CSort n) in (csubv TMP_21 e2))) in (let 
TMP_24 \def (\lambda (e2: C).(let TMP_23 \def (CSort n) in (drop O O TMP_23 
e2))) in (let TMP_25 \def (CSort n) in (let TMP_26 \def (CSort n) in (let 
TMP_27 \def (csubv_refl TMP_26) in (let TMP_28 \def (CSort n) in (let TMP_29 
\def (drop_refl TMP_28) in (let TMP_30 \def (ex_intro2 C TMP_22 TMP_24 TMP_25 
TMP_27 TMP_29) in (let TMP_31 \def (eq_ind_r C TMP_16 TMP_20 TMP_30 e1 H1) in 
(eq_ind_r nat O TMP_15 TMP_31 h H2)))))))))))))))) in (let TMP_33 \def 
(drop_gen_sort n h O e1 H0) in (and3_ind TMP_5 TMP_6 TMP_7 TMP_11 TMP_32 
TMP_33)))))))))))))) in (let TMP_85 \def (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csubv c3 c4)).(\lambda (H1: ((\forall (e1: C).(\forall (h: 
nat).((drop h O c3 e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda 
(e2: C).(drop h O c4 e2)))))))).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(e1: C).(\lambda (h: nat).(\lambda (H2: (drop h O (CHead c3 (Bind Void) v1) 
e1)).(let TMP_39 \def (\lambda (n: nat).((drop n O (CHead c3 (Bind Void) v1) 
e1) \to (let TMP_35 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_38 \def 
(\lambda (e2: C).(let TMP_36 \def (Bind Void) in (let TMP_37 \def (CHead c4 
TMP_36 v2) in (drop n O TMP_37 e2)))) in (ex2 C TMP_35 TMP_38))))) in (let 
TMP_63 \def (\lambda (H3: (drop O O (CHead c3 (Bind Void) v1) e1)).(let 
TMP_40 \def (Bind Void) in (let TMP_41 \def (CHead c3 TMP_40 v1) in (let 
TMP_46 \def (\lambda (c: C).(let TMP_42 \def (\lambda (e2: C).(csubv c e2)) 
in (let TMP_45 \def (\lambda (e2: C).(let TMP_43 \def (Bind Void) in (let 
TMP_44 \def (CHead c4 TMP_43 v2) in (drop O O TMP_44 e2)))) in (ex2 C TMP_42 
TMP_45)))) in (let TMP_49 \def (\lambda (e2: C).(let TMP_47 \def (Bind Void) 
in (let TMP_48 \def (CHead c3 TMP_47 v1) in (csubv TMP_48 e2)))) in (let 
TMP_52 \def (\lambda (e2: C).(let TMP_50 \def (Bind Void) in (let TMP_51 \def 
(CHead c4 TMP_50 v2) in (drop O O TMP_51 e2)))) in (let TMP_53 \def (Bind 
Void) in (let TMP_54 \def (CHead c4 TMP_53 v2) in (let TMP_55 \def 
(csubv_bind_same c3 c4 H0 Void v1 v2) in (let TMP_56 \def (Bind Void) in (let 
TMP_57 \def (CHead c4 TMP_56 v2) in (let TMP_58 \def (drop_refl TMP_57) in 
(let TMP_59 \def (ex_intro2 C TMP_49 TMP_52 TMP_54 TMP_55 TMP_58) in (let 
TMP_60 \def (Bind Void) in (let TMP_61 \def (CHead c3 TMP_60 v1) in (let 
TMP_62 \def (drop_gen_refl TMP_61 e1 H3) in (eq_ind C TMP_41 TMP_46 TMP_59 e1 
TMP_62))))))))))))))))) in (let TMP_84 \def (\lambda (h0: nat).(\lambda (_: 
(((drop h0 O (CHead c3 (Bind Void) v1) e1) \to (ex2 C (\lambda (e2: C).(csubv 
e1 e2)) (\lambda (e2: C).(drop h0 O (CHead c4 (Bind Void) v2) 
e2)))))).(\lambda (H3: (drop (S h0) O (CHead c3 (Bind Void) v1) e1)).(let 
TMP_64 \def (Bind Void) in (let TMP_65 \def (r TMP_64 h0) in (let TMP_66 \def 
(Bind Void) in (let TMP_67 \def (drop_gen_drop TMP_66 c3 e1 v1 h0 H3) in (let 
H_x \def (H1 e1 TMP_65 TMP_67) in (let H4 \def H_x in (let TMP_68 \def 
(\lambda (e2: C).(csubv e1 e2)) in (let TMP_69 \def (\lambda (e2: C).(drop h0 
O c4 e2)) in (let TMP_70 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_74 
\def (\lambda (e2: C).(let TMP_71 \def (S h0) in (let TMP_72 \def (Bind Void) 
in (let TMP_73 \def (CHead c4 TMP_72 v2) in (drop TMP_71 O TMP_73 e2))))) in 
(let TMP_75 \def (ex2 C TMP_70 TMP_74) in (let TMP_83 \def (\lambda (x: 
C).(\lambda (H5: (csubv e1 x)).(\lambda (H6: (drop h0 O c4 x)).(let TMP_76 
\def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_80 \def (\lambda (e2: 
C).(let TMP_77 \def (S h0) in (let TMP_78 \def (Bind Void) in (let TMP_79 
\def (CHead c4 TMP_78 v2) in (drop TMP_77 O TMP_79 e2))))) in (let TMP_81 
\def (Bind Void) in (let TMP_82 \def (drop_drop TMP_81 h0 c4 x H6 v2) in 
(ex_intro2 C TMP_76 TMP_80 x H5 TMP_82)))))))) in (ex2_ind C TMP_68 TMP_69 
TMP_75 TMP_83 H4)))))))))))))))) in (nat_ind TMP_39 TMP_63 TMP_84 h 
H2))))))))))))) in (let TMP_136 \def (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H0: (csubv c3 c4)).(\lambda (H1: ((\forall (e1: C).(\forall (h: 
nat).((drop h O c3 e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) (\lambda 
(e2: C).(drop h O c4 e2)))))))).(\lambda (b1: B).(\lambda (H2: (not (eq B b1 
Void))).(\lambda (b2: B).(\lambda (v1: T).(\lambda (v2: T).(\lambda (e1: 
C).(\lambda (h: nat).(\lambda (H3: (drop h O (CHead c3 (Bind b1) v1) 
e1)).(let TMP_90 \def (\lambda (n: nat).((drop n O (CHead c3 (Bind b1) v1) 
e1) \to (let TMP_86 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_89 \def 
(\lambda (e2: C).(let TMP_87 \def (Bind b2) in (let TMP_88 \def (CHead c4 
TMP_87 v2) in (drop n O TMP_88 e2)))) in (ex2 C TMP_86 TMP_89))))) in (let 
TMP_114 \def (\lambda (H4: (drop O O (CHead c3 (Bind b1) v1) e1)).(let TMP_91 
\def (Bind b1) in (let TMP_92 \def (CHead c3 TMP_91 v1) in (let TMP_97 \def 
(\lambda (c: C).(let TMP_93 \def (\lambda (e2: C).(csubv c e2)) in (let 
TMP_96 \def (\lambda (e2: C).(let TMP_94 \def (Bind b2) in (let TMP_95 \def 
(CHead c4 TMP_94 v2) in (drop O O TMP_95 e2)))) in (ex2 C TMP_93 TMP_96)))) 
in (let TMP_100 \def (\lambda (e2: C).(let TMP_98 \def (Bind b1) in (let 
TMP_99 \def (CHead c3 TMP_98 v1) in (csubv TMP_99 e2)))) in (let TMP_103 \def 
(\lambda (e2: C).(let TMP_101 \def (Bind b2) in (let TMP_102 \def (CHead c4 
TMP_101 v2) in (drop O O TMP_102 e2)))) in (let TMP_104 \def (Bind b2) in 
(let TMP_105 \def (CHead c4 TMP_104 v2) in (let TMP_106 \def (csubv_bind c3 
c4 H0 b1 H2 b2 v1 v2) in (let TMP_107 \def (Bind b2) in (let TMP_108 \def 
(CHead c4 TMP_107 v2) in (let TMP_109 \def (drop_refl TMP_108) in (let 
TMP_110 \def (ex_intro2 C TMP_100 TMP_103 TMP_105 TMP_106 TMP_109) in (let 
TMP_111 \def (Bind b1) in (let TMP_112 \def (CHead c3 TMP_111 v1) in (let 
TMP_113 \def (drop_gen_refl TMP_112 e1 H4) in (eq_ind C TMP_92 TMP_97 TMP_110 
e1 TMP_113))))))))))))))))) in (let TMP_135 \def (\lambda (h0: nat).(\lambda 
(_: (((drop h0 O (CHead c3 (Bind b1) v1) e1) \to (ex2 C (\lambda (e2: 
C).(csubv e1 e2)) (\lambda (e2: C).(drop h0 O (CHead c4 (Bind b2) v2) 
e2)))))).(\lambda (H4: (drop (S h0) O (CHead c3 (Bind b1) v1) e1)).(let 
TMP_115 \def (Bind b1) in (let TMP_116 \def (r TMP_115 h0) in (let TMP_117 
\def (Bind b1) in (let TMP_118 \def (drop_gen_drop TMP_117 c3 e1 v1 h0 H4) in 
(let H_x \def (H1 e1 TMP_116 TMP_118) in (let H5 \def H_x in (let TMP_119 
\def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_120 \def (\lambda (e2: 
C).(drop h0 O c4 e2)) in (let TMP_121 \def (\lambda (e2: C).(csubv e1 e2)) in 
(let TMP_125 \def (\lambda (e2: C).(let TMP_122 \def (S h0) in (let TMP_123 
\def (Bind b2) in (let TMP_124 \def (CHead c4 TMP_123 v2) in (drop TMP_122 O 
TMP_124 e2))))) in (let TMP_126 \def (ex2 C TMP_121 TMP_125) in (let TMP_134 
\def (\lambda (x: C).(\lambda (H6: (csubv e1 x)).(\lambda (H7: (drop h0 O c4 
x)).(let TMP_127 \def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_131 \def 
(\lambda (e2: C).(let TMP_128 \def (S h0) in (let TMP_129 \def (Bind b2) in 
(let TMP_130 \def (CHead c4 TMP_129 v2) in (drop TMP_128 O TMP_130 e2))))) in 
(let TMP_132 \def (Bind b2) in (let TMP_133 \def (drop_drop TMP_132 h0 c4 x 
H7 v2) in (ex_intro2 C TMP_127 TMP_131 x H6 TMP_133)))))))) in (ex2_ind C 
TMP_119 TMP_120 TMP_126 TMP_134 H5)))))))))))))))) in (nat_ind TMP_90 TMP_114 
TMP_135 h H3)))))))))))))))) in (let TMP_188 \def (\lambda (c3: C).(\lambda 
(c4: C).(\lambda (H0: (csubv c3 c4)).(\lambda (H1: ((\forall (e1: C).(\forall 
(h: nat).((drop h O c3 e1) \to (ex2 C (\lambda (e2: C).(csubv e1 e2)) 
(\lambda (e2: C).(drop h O c4 e2)))))))).(\lambda (f1: F).(\lambda (f2: 
F).(\lambda (v1: T).(\lambda (v2: T).(\lambda (e1: C).(\lambda (h: 
nat).(\lambda (H2: (drop h O (CHead c3 (Flat f1) v1) e1)).(let TMP_141 \def 
(\lambda (n: nat).((drop n O (CHead c3 (Flat f1) v1) e1) \to (let TMP_137 
\def (\lambda (e2: C).(csubv e1 e2)) in (let TMP_140 \def (\lambda (e2: 
C).(let TMP_138 \def (Flat f2) in (let TMP_139 \def (CHead c4 TMP_138 v2) in 
(drop n O TMP_139 e2)))) in (ex2 C TMP_137 TMP_140))))) in (let TMP_165 \def 
(\lambda (H3: (drop O O (CHead c3 (Flat f1) v1) e1)).(let TMP_142 \def (Flat 
f1) in (let TMP_143 \def (CHead c3 TMP_142 v1) in (let TMP_148 \def (\lambda 
(c: C).(let TMP_144 \def (\lambda (e2: C).(csubv c e2)) in (let TMP_147 \def 
(\lambda (e2: C).(let TMP_145 \def (Flat f2) in (let TMP_146 \def (CHead c4 
TMP_145 v2) in (drop O O TMP_146 e2)))) in (ex2 C TMP_144 TMP_147)))) in (let 
TMP_151 \def (\lambda (e2: C).(let TMP_149 \def (Flat f1) in (let TMP_150 
\def (CHead c3 TMP_149 v1) in (csubv TMP_150 e2)))) in (let TMP_154 \def 
(\lambda (e2: C).(let TMP_152 \def (Flat f2) in (let TMP_153 \def (CHead c4 
TMP_152 v2) in (drop O O TMP_153 e2)))) in (let TMP_155 \def (Flat f2) in 
(let TMP_156 \def (CHead c4 TMP_155 v2) in (let TMP_157 \def (csubv_flat c3 
c4 H0 f1 f2 v1 v2) in (let TMP_158 \def (Flat f2) in (let TMP_159 \def (CHead 
c4 TMP_158 v2) in (let TMP_160 \def (drop_refl TMP_159) in (let TMP_161 \def 
(ex_intro2 C TMP_151 TMP_154 TMP_156 TMP_157 TMP_160) in (let TMP_162 \def 
(Flat f1) in (let TMP_163 \def (CHead c3 TMP_162 v1) in (let TMP_164 \def 
(drop_gen_refl TMP_163 e1 H3) in (eq_ind C TMP_143 TMP_148 TMP_161 e1 
TMP_164))))))))))))))))) in (let TMP_187 \def (\lambda (h0: nat).(\lambda (_: 
(((drop h0 O (CHead c3 (Flat f1) v1) e1) \to (ex2 C (\lambda (e2: C).(csubv 
e1 e2)) (\lambda (e2: C).(drop h0 O (CHead c4 (Flat f2) v2) e2)))))).(\lambda 
(H3: (drop (S h0) O (CHead c3 (Flat f1) v1) e1)).(let TMP_166 \def (Flat f1) 
in (let TMP_167 \def (r TMP_166 h0) in (let TMP_168 \def (Flat f1) in (let 
TMP_169 \def (drop_gen_drop TMP_168 c3 e1 v1 h0 H3) in (let H_x \def (H1 e1 
TMP_167 TMP_169) in (let H4 \def H_x in (let TMP_170 \def (\lambda (e2: 
C).(csubv e1 e2)) in (let TMP_172 \def (\lambda (e2: C).(let TMP_171 \def (S 
h0) in (drop TMP_171 O c4 e2))) in (let TMP_173 \def (\lambda (e2: C).(csubv 
e1 e2)) in (let TMP_177 \def (\lambda (e2: C).(let TMP_174 \def (S h0) in 
(let TMP_175 \def (Flat f2) in (let TMP_176 \def (CHead c4 TMP_175 v2) in 
(drop TMP_174 O TMP_176 e2))))) in (let TMP_178 \def (ex2 C TMP_173 TMP_177) 
in (let TMP_186 \def (\lambda (x: C).(\lambda (H5: (csubv e1 x)).(\lambda 
(H6: (drop (S h0) O c4 x)).(let TMP_179 \def (\lambda (e2: C).(csubv e1 e2)) 
in (let TMP_183 \def (\lambda (e2: C).(let TMP_180 \def (S h0) in (let 
TMP_181 \def (Flat f2) in (let TMP_182 \def (CHead c4 TMP_181 v2) in (drop 
TMP_180 O TMP_182 e2))))) in (let TMP_184 \def (Flat f2) in (let TMP_185 \def 
(drop_drop TMP_184 h0 c4 x H6 v2) in (ex_intro2 C TMP_179 TMP_183 x H5 
TMP_185)))))))) in (ex2_ind C TMP_170 TMP_172 TMP_178 TMP_186 
H4)))))))))))))))) in (nat_ind TMP_141 TMP_165 TMP_187 h H2))))))))))))))) in 
(csubv_ind TMP_3 TMP_34 TMP_85 TMP_136 TMP_188 c1 c2 H)))))))).

