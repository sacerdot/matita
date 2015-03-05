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

include "basic_1/csubc/fwd.ma".

include "basic_1/sc3/props.ma".

theorem csubc_drop_conf_O:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).(\forall (h: nat).((drop h 
O c1 e1) \to (\forall (c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: 
C).(drop h O c2 e2)) (\lambda (e2: C).(csubc g e1 e2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(let TMP_3 \def (\lambda (c: C).(\forall 
(e1: C).(\forall (h: nat).((drop h O c e1) \to (\forall (c2: C).((csubc g c 
c2) \to (let TMP_1 \def (\lambda (e2: C).(drop h O c2 e2)) in (let TMP_2 \def 
(\lambda (e2: C).(csubc g e1 e2)) in (ex2 C TMP_1 TMP_2))))))))) in (let 
TMP_26 \def (\lambda (n: nat).(\lambda (e1: C).(\lambda (h: nat).(\lambda (H: 
(drop h O (CSort n) e1)).(\lambda (c2: C).(\lambda (H0: (csubc g (CSort n) 
c2)).(let TMP_4 \def (CSort n) in (let TMP_5 \def (eq C e1 TMP_4) in (let 
TMP_6 \def (eq nat h O) in (let TMP_7 \def (eq nat O O) in (let TMP_8 \def 
(\lambda (e2: C).(drop h O c2 e2)) in (let TMP_9 \def (\lambda (e2: C).(csubc 
g e1 e2)) in (let TMP_10 \def (ex2 C TMP_8 TMP_9) in (let TMP_24 \def 
(\lambda (H1: (eq C e1 (CSort n))).(\lambda (H2: (eq nat h O)).(\lambda (_: 
(eq nat O O)).(let TMP_13 \def (\lambda (n0: nat).(let TMP_11 \def (\lambda 
(e2: C).(drop n0 O c2 e2)) in (let TMP_12 \def (\lambda (e2: C).(csubc g e1 
e2)) in (ex2 C TMP_11 TMP_12)))) in (let TMP_14 \def (CSort n) in (let TMP_17 
\def (\lambda (c: C).(let TMP_15 \def (\lambda (e2: C).(drop O O c2 e2)) in 
(let TMP_16 \def (\lambda (e2: C).(csubc g c e2)) in (ex2 C TMP_15 TMP_16)))) 
in (let TMP_18 \def (\lambda (e2: C).(drop O O c2 e2)) in (let TMP_20 \def 
(\lambda (e2: C).(let TMP_19 \def (CSort n) in (csubc g TMP_19 e2))) in (let 
TMP_21 \def (drop_refl c2) in (let TMP_22 \def (ex_intro2 C TMP_18 TMP_20 c2 
TMP_21 H0) in (let TMP_23 \def (eq_ind_r C TMP_14 TMP_17 TMP_22 e1 H1) in 
(eq_ind_r nat O TMP_13 TMP_23 h H2)))))))))))) in (let TMP_25 \def 
(drop_gen_sort n h O e1 H) in (and3_ind TMP_5 TMP_6 TMP_7 TMP_10 TMP_24 
TMP_25)))))))))))))))) in (let TMP_196 \def (\lambda (c: C).(\lambda (H: 
((\forall (e1: C).(\forall (h: nat).((drop h O c e1) \to (\forall (c2: 
C).((csubc g c c2) \to (ex2 C (\lambda (e2: C).(drop h O c2 e2)) (\lambda 
(e2: C).(csubc g e1 e2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda 
(e1: C).(\lambda (h: nat).(let TMP_29 \def (\lambda (n: nat).((drop n O 
(CHead c k t) e1) \to (\forall (c2: C).((csubc g (CHead c k t) c2) \to (let 
TMP_27 \def (\lambda (e2: C).(drop n O c2 e2)) in (let TMP_28 \def (\lambda 
(e2: C).(csubc g e1 e2)) in (ex2 C TMP_27 TMP_28))))))) in (let TMP_41 \def 
(\lambda (H0: (drop O O (CHead c k t) e1)).(\lambda (c2: C).(\lambda (H1: 
(csubc g (CHead c k t) c2)).(let TMP_30 \def (CHead c k t) in (let TMP_33 
\def (\lambda (c0: C).(let TMP_31 \def (\lambda (e2: C).(drop O O c2 e2)) in 
(let TMP_32 \def (\lambda (e2: C).(csubc g c0 e2)) in (ex2 C TMP_31 
TMP_32)))) in (let TMP_34 \def (\lambda (e2: C).(drop O O c2 e2)) in (let 
TMP_36 \def (\lambda (e2: C).(let TMP_35 \def (CHead c k t) in (csubc g 
TMP_35 e2))) in (let TMP_37 \def (drop_refl c2) in (let TMP_38 \def 
(ex_intro2 C TMP_34 TMP_36 c2 TMP_37 H1) in (let TMP_39 \def (CHead c k t) in 
(let TMP_40 \def (drop_gen_refl TMP_39 e1 H0) in (eq_ind C TMP_30 TMP_33 
TMP_38 e1 TMP_40)))))))))))) in (let TMP_195 \def (\lambda (n: nat).(\lambda 
(H0: (((drop n O (CHead c k t) e1) \to (\forall (c2: C).((csubc g (CHead c k 
t) c2) \to (ex2 C (\lambda (e2: C).(drop n O c2 e2)) (\lambda (e2: C).(csubc 
g e1 e2)))))))).(\lambda (H1: (drop (S n) O (CHead c k t) e1)).(\lambda (c2: 
C).(\lambda (H2: (csubc g (CHead c k t) c2)).(let H_x \def (csubc_gen_head_l 
g c c2 t k H2) in (let H3 \def H_x in (let TMP_43 \def (\lambda (c3: C).(let 
TMP_42 \def (CHead c3 k t) in (eq C c2 TMP_42))) in (let TMP_44 \def (\lambda 
(c3: C).(csubc g c c3)) in (let TMP_45 \def (ex2 C TMP_43 TMP_44) in (let 
TMP_47 \def (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(let TMP_46 \def 
(Bind Abst) in (eq K k TMP_46))))) in (let TMP_50 \def (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(let TMP_48 \def (Bind Abbr) in (let 
TMP_49 \def (CHead c3 TMP_48 w) in (eq C c2 TMP_49)))))) in (let TMP_51 \def 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c c3)))) in (let 
TMP_53 \def (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(let TMP_52 \def 
(asucc g a) in (sc3 g TMP_52 c t))))) in (let TMP_54 \def (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_55 \def 
(ex5_3 C T A TMP_47 TMP_50 TMP_51 TMP_53 TMP_54) in (let TMP_58 \def (\lambda 
(b: B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_56 \def (Bind b) in (let 
TMP_57 \def (CHead c3 TMP_56 v2) in (eq C c2 TMP_57)))))) in (let TMP_60 \def 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_59 \def (Bind Void) 
in (eq K k TMP_59))))) in (let TMP_62 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(let TMP_61 \def (eq B b Void) in (not TMP_61))))) in (let 
TMP_63 \def (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c 
c3)))) in (let TMP_64 \def (ex4_3 B C T TMP_58 TMP_60 TMP_62 TMP_63) in (let 
TMP_66 \def (\lambda (e2: C).(let TMP_65 \def (S n) in (drop TMP_65 O c2 
e2))) in (let TMP_67 \def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_68 
\def (ex2 C TMP_66 TMP_67) in (let TMP_99 \def (\lambda (H4: (ex2 C (\lambda 
(c3: C).(eq C c2 (CHead c3 k t))) (\lambda (c3: C).(csubc g c c3)))).(let 
TMP_70 \def (\lambda (c3: C).(let TMP_69 \def (CHead c3 k t) in (eq C c2 
TMP_69))) in (let TMP_71 \def (\lambda (c3: C).(csubc g c c3)) in (let TMP_73 
\def (\lambda (e2: C).(let TMP_72 \def (S n) in (drop TMP_72 O c2 e2))) in 
(let TMP_74 \def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_75 \def (ex2 C 
TMP_73 TMP_74) in (let TMP_98 \def (\lambda (x: C).(\lambda (H5: (eq C c2 
(CHead x k t))).(\lambda (H6: (csubc g c x)).(let TMP_76 \def (CHead x k t) 
in (let TMP_80 \def (\lambda (c0: C).(let TMP_78 \def (\lambda (e2: C).(let 
TMP_77 \def (S n) in (drop TMP_77 O c0 e2))) in (let TMP_79 \def (\lambda 
(e2: C).(csubc g e1 e2)) in (ex2 C TMP_78 TMP_79)))) in (let TMP_81 \def (r k 
n) in (let TMP_82 \def (drop_gen_drop k c e1 t n H1) in (let H_x0 \def (H e1 
TMP_81 TMP_82 x H6) in (let H7 \def H_x0 in (let TMP_84 \def (\lambda (e2: 
C).(let TMP_83 \def (r k n) in (drop TMP_83 O x e2))) in (let TMP_85 \def 
(\lambda (e2: C).(csubc g e1 e2)) in (let TMP_88 \def (\lambda (e2: C).(let 
TMP_86 \def (S n) in (let TMP_87 \def (CHead x k t) in (drop TMP_86 O TMP_87 
e2)))) in (let TMP_89 \def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_90 
\def (ex2 C TMP_88 TMP_89) in (let TMP_96 \def (\lambda (x0: C).(\lambda (H8: 
(drop (r k n) O x x0)).(\lambda (H9: (csubc g e1 x0)).(let TMP_93 \def 
(\lambda (e2: C).(let TMP_91 \def (S n) in (let TMP_92 \def (CHead x k t) in 
(drop TMP_91 O TMP_92 e2)))) in (let TMP_94 \def (\lambda (e2: C).(csubc g e1 
e2)) in (let TMP_95 \def (drop_drop k n x x0 H8 t) in (ex_intro2 C TMP_93 
TMP_94 x0 TMP_95 H9))))))) in (let TMP_97 \def (ex2_ind C TMP_84 TMP_85 
TMP_90 TMP_96 H7) in (eq_ind_r C TMP_76 TMP_80 TMP_97 c2 H5))))))))))))))))) 
in (ex2_ind C TMP_70 TMP_71 TMP_75 TMP_98 H4)))))))) in (let TMP_147 \def 
(\lambda (H4: (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(sc3 g (asucc g a) c t)))) (\lambda (c3: C).(\lambda (w: T).(\lambda 
(a: A).(sc3 g a c3 w)))))).(let TMP_101 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(let TMP_100 \def (Bind Abst) in (eq K k TMP_100))))) in 
(let TMP_104 \def (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(let 
TMP_102 \def (Bind Abbr) in (let TMP_103 \def (CHead c3 TMP_102 w) in (eq C 
c2 TMP_103)))))) in (let TMP_105 \def (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c c3)))) in (let TMP_107 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(let TMP_106 \def (asucc g a) in (sc3 g 
TMP_106 c t))))) in (let TMP_108 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_110 \def (\lambda (e2: 
C).(let TMP_109 \def (S n) in (drop TMP_109 O c2 e2))) in (let TMP_111 \def 
(\lambda (e2: C).(csubc g e1 e2)) in (let TMP_112 \def (ex2 C TMP_110 
TMP_111) in (let TMP_146 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
A).(\lambda (H5: (eq K k (Bind Abst))).(\lambda (H6: (eq C c2 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H7: (csubc g c x0)).(\lambda (_: (sc3 g (asucc g x2) c 
t)).(\lambda (_: (sc3 g x2 x0 x1)).(let TMP_113 \def (Bind Abbr) in (let 
TMP_114 \def (CHead x0 TMP_113 x1) in (let TMP_118 \def (\lambda (c0: C).(let 
TMP_116 \def (\lambda (e2: C).(let TMP_115 \def (S n) in (drop TMP_115 O c0 
e2))) in (let TMP_117 \def (\lambda (e2: C).(csubc g e1 e2)) in (ex2 C 
TMP_116 TMP_117)))) in (let TMP_120 \def (\lambda (k0: K).(let TMP_119 \def 
(r k0 n) in (drop TMP_119 O c e1))) in (let TMP_121 \def (drop_gen_drop k c 
e1 t n H1) in (let TMP_122 \def (Bind Abst) in (let H10 \def (eq_ind K k 
TMP_120 TMP_121 TMP_122 H5) in (let TMP_125 \def (\lambda (k0: K).((drop n O 
(CHead c k0 t) e1) \to (\forall (c3: C).((csubc g (CHead c k0 t) c3) \to (let 
TMP_123 \def (\lambda (e2: C).(drop n O c3 e2)) in (let TMP_124 \def (\lambda 
(e2: C).(csubc g e1 e2)) in (ex2 C TMP_123 TMP_124))))))) in (let TMP_126 
\def (Bind Abst) in (let H11 \def (eq_ind K k TMP_125 H0 TMP_126 H5) in (let 
TMP_127 \def (Bind Abst) in (let TMP_128 \def (r TMP_127 n) in (let H_x0 \def 
(H e1 TMP_128 H10 x0 H7) in (let H12 \def H_x0 in (let TMP_129 \def (\lambda 
(e2: C).(drop n O x0 e2)) in (let TMP_130 \def (\lambda (e2: C).(csubc g e1 
e2)) in (let TMP_134 \def (\lambda (e2: C).(let TMP_131 \def (S n) in (let 
TMP_132 \def (Bind Abbr) in (let TMP_133 \def (CHead x0 TMP_132 x1) in (drop 
TMP_131 O TMP_133 e2))))) in (let TMP_135 \def (\lambda (e2: C).(csubc g e1 
e2)) in (let TMP_136 \def (ex2 C TMP_134 TMP_135) in (let TMP_144 \def 
(\lambda (x: C).(\lambda (H13: (drop n O x0 x)).(\lambda (H14: (csubc g e1 
x)).(let TMP_140 \def (\lambda (e2: C).(let TMP_137 \def (S n) in (let 
TMP_138 \def (Bind Abbr) in (let TMP_139 \def (CHead x0 TMP_138 x1) in (drop 
TMP_137 O TMP_139 e2))))) in (let TMP_141 \def (\lambda (e2: C).(csubc g e1 
e2)) in (let TMP_142 \def (Bind Abbr) in (let TMP_143 \def (drop_drop TMP_142 
n x0 x H13 x1) in (ex_intro2 C TMP_140 TMP_141 x TMP_143 H14)))))))) in (let 
TMP_145 \def (ex2_ind C TMP_129 TMP_130 TMP_136 TMP_144 H12) in (eq_ind_r C 
TMP_114 TMP_118 TMP_145 c2 H6)))))))))))))))))))))))))))))) in (ex5_3_ind C T 
A TMP_101 TMP_104 TMP_105 TMP_107 TMP_108 TMP_112 TMP_146 H4))))))))))) in 
(let TMP_194 \def (\lambda (H4: (ex4_3 B C T (\lambda (b: B).(\lambda (c3: 
C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c c3)))))).(let TMP_150 \def 
(\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_148 \def (Bind b) 
in (let TMP_149 \def (CHead c3 TMP_148 v2) in (eq C c2 TMP_149)))))) in (let 
TMP_152 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_151 
\def (Bind Void) in (eq K k TMP_151))))) in (let TMP_154 \def (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(let TMP_153 \def (eq B b Void) in (not 
TMP_153))))) in (let TMP_155 \def (\lambda (_: B).(\lambda (c3: C).(\lambda 
(_: T).(csubc g c c3)))) in (let TMP_157 \def (\lambda (e2: C).(let TMP_156 
\def (S n) in (drop TMP_156 O c2 e2))) in (let TMP_158 \def (\lambda (e2: 
C).(csubc g e1 e2)) in (let TMP_159 \def (ex2 C TMP_157 TMP_158) in (let 
TMP_193 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H5: 
(eq C c2 (CHead x1 (Bind x0) x2))).(\lambda (H6: (eq K k (Bind 
Void))).(\lambda (_: (not (eq B x0 Void))).(\lambda (H8: (csubc g c x1)).(let 
TMP_160 \def (Bind x0) in (let TMP_161 \def (CHead x1 TMP_160 x2) in (let 
TMP_165 \def (\lambda (c0: C).(let TMP_163 \def (\lambda (e2: C).(let TMP_162 
\def (S n) in (drop TMP_162 O c0 e2))) in (let TMP_164 \def (\lambda (e2: 
C).(csubc g e1 e2)) in (ex2 C TMP_163 TMP_164)))) in (let TMP_167 \def 
(\lambda (k0: K).(let TMP_166 \def (r k0 n) in (drop TMP_166 O c e1))) in 
(let TMP_168 \def (drop_gen_drop k c e1 t n H1) in (let TMP_169 \def (Bind 
Void) in (let H9 \def (eq_ind K k TMP_167 TMP_168 TMP_169 H6) in (let TMP_172 
\def (\lambda (k0: K).((drop n O (CHead c k0 t) e1) \to (\forall (c3: 
C).((csubc g (CHead c k0 t) c3) \to (let TMP_170 \def (\lambda (e2: C).(drop 
n O c3 e2)) in (let TMP_171 \def (\lambda (e2: C).(csubc g e1 e2)) in (ex2 C 
TMP_170 TMP_171))))))) in (let TMP_173 \def (Bind Void) in (let H10 \def 
(eq_ind K k TMP_172 H0 TMP_173 H6) in (let TMP_174 \def (Bind Void) in (let 
TMP_175 \def (r TMP_174 n) in (let H_x0 \def (H e1 TMP_175 H9 x1 H8) in (let 
H11 \def H_x0 in (let TMP_176 \def (\lambda (e2: C).(drop n O x1 e2)) in (let 
TMP_177 \def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_181 \def (\lambda 
(e2: C).(let TMP_178 \def (S n) in (let TMP_179 \def (Bind x0) in (let 
TMP_180 \def (CHead x1 TMP_179 x2) in (drop TMP_178 O TMP_180 e2))))) in (let 
TMP_182 \def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_183 \def (ex2 C 
TMP_181 TMP_182) in (let TMP_191 \def (\lambda (x: C).(\lambda (H12: (drop n 
O x1 x)).(\lambda (H13: (csubc g e1 x)).(let TMP_187 \def (\lambda (e2: 
C).(let TMP_184 \def (S n) in (let TMP_185 \def (Bind x0) in (let TMP_186 
\def (CHead x1 TMP_185 x2) in (drop TMP_184 O TMP_186 e2))))) in (let TMP_188 
\def (\lambda (e2: C).(csubc g e1 e2)) in (let TMP_189 \def (Bind x0) in (let 
TMP_190 \def (drop_drop TMP_189 n x1 x H12 x2) in (ex_intro2 C TMP_187 
TMP_188 x TMP_190 H13)))))))) in (let TMP_192 \def (ex2_ind C TMP_176 TMP_177 
TMP_183 TMP_191 H11) in (eq_ind_r C TMP_161 TMP_165 TMP_192 c2 
H5))))))))))))))))))))))))))))) in (ex4_3_ind B C T TMP_150 TMP_152 TMP_154 
TMP_155 TMP_159 TMP_193 H4)))))))))) in (or3_ind TMP_45 TMP_55 TMP_64 TMP_68 
TMP_99 TMP_147 TMP_194 H3)))))))))))))))))))))))))))) in (nat_ind TMP_29 
TMP_41 TMP_195 h)))))))))) in (C_ind TMP_3 TMP_26 TMP_196 c1))))).

theorem drop_csubc_trans:
 \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall 
(h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c2 c1))))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(let TMP_3 \def (\lambda (c: C).(\forall 
(e2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c e2) \to (\forall 
(e1: C).((csubc g e2 e1) \to (let TMP_1 \def (\lambda (c1: C).(drop h d c1 
e1)) in (let TMP_2 \def (\lambda (c1: C).(csubc g c c1)) in (ex2 C TMP_1 
TMP_2)))))))))) in (let TMP_30 \def (\lambda (n: nat).(\lambda (e2: 
C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e2 e1)).(let TMP_4 \def (CSort 
n) in (let TMP_5 \def (eq C e2 TMP_4) in (let TMP_6 \def (eq nat h O) in (let 
TMP_7 \def (eq nat d O) in (let TMP_8 \def (\lambda (c1: C).(drop h d c1 e1)) 
in (let TMP_10 \def (\lambda (c1: C).(let TMP_9 \def (CSort n) in (csubc g 
TMP_9 c1))) in (let TMP_11 \def (ex2 C TMP_8 TMP_10) in (let TMP_28 \def 
(\lambda (H1: (eq C e2 (CSort n))).(\lambda (H2: (eq nat h O)).(\lambda (H3: 
(eq nat d O)).(let TMP_15 \def (\lambda (n0: nat).(let TMP_12 \def (\lambda 
(c1: C).(drop n0 d c1 e1)) in (let TMP_14 \def (\lambda (c1: C).(let TMP_13 
\def (CSort n) in (csubc g TMP_13 c1))) in (ex2 C TMP_12 TMP_14)))) in (let 
TMP_19 \def (\lambda (n0: nat).(let TMP_16 \def (\lambda (c1: C).(drop O n0 
c1 e1)) in (let TMP_18 \def (\lambda (c1: C).(let TMP_17 \def (CSort n) in 
(csubc g TMP_17 c1))) in (ex2 C TMP_16 TMP_18)))) in (let TMP_20 \def 
(\lambda (c: C).(csubc g c e1)) in (let TMP_21 \def (CSort n) in (let H4 \def 
(eq_ind C e2 TMP_20 H0 TMP_21 H1) in (let TMP_22 \def (\lambda (c1: C).(drop 
O O c1 e1)) in (let TMP_24 \def (\lambda (c1: C).(let TMP_23 \def (CSort n) 
in (csubc g TMP_23 c1))) in (let TMP_25 \def (drop_refl e1) in (let TMP_26 
\def (ex_intro2 C TMP_22 TMP_24 e1 TMP_25 H4) in (let TMP_27 \def (eq_ind_r 
nat O TMP_19 TMP_26 d H3) in (eq_ind_r nat O TMP_15 TMP_27 h H2)))))))))))))) 
in (let TMP_29 \def (drop_gen_sort n h d e2 H) in (and3_ind TMP_5 TMP_6 TMP_7 
TMP_11 TMP_28 TMP_29))))))))))))))))) in (let TMP_354 \def (\lambda (c: 
C).(\lambda (H: ((\forall (e2: C).(\forall (d: nat).(\forall (h: nat).((drop 
h d c e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda (c1: 
C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c c1))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (e2: C).(\lambda (d: nat).(let TMP_34 \def 
(\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c k t) e2) \to (\forall 
(e1: C).((csubc g e2 e1) \to (let TMP_31 \def (\lambda (c1: C).(drop h n c1 
e1)) in (let TMP_33 \def (\lambda (c1: C).(let TMP_32 \def (CHead c k t) in 
(csubc g TMP_32 c1))) in (ex2 C TMP_31 TMP_33)))))))) in (let TMP_67 \def 
(\lambda (h: nat).(let TMP_38 \def (\lambda (n: nat).((drop n O (CHead c k t) 
e2) \to (\forall (e1: C).((csubc g e2 e1) \to (let TMP_35 \def (\lambda (c1: 
C).(drop n O c1 e1)) in (let TMP_37 \def (\lambda (c1: C).(let TMP_36 \def 
(CHead c k t) in (csubc g TMP_36 c1))) in (ex2 C TMP_35 TMP_37))))))) in (let 
TMP_47 \def (\lambda (H0: (drop O O (CHead c k t) e2)).(\lambda (e1: 
C).(\lambda (H1: (csubc g e2 e1)).(let TMP_39 \def (\lambda (c0: C).(csubc g 
c0 e1)) in (let TMP_40 \def (CHead c k t) in (let TMP_41 \def (CHead c k t) 
in (let TMP_42 \def (drop_gen_refl TMP_41 e2 H0) in (let H2 \def (eq_ind_r C 
e2 TMP_39 H1 TMP_40 TMP_42) in (let TMP_43 \def (\lambda (c1: C).(drop O O c1 
e1)) in (let TMP_45 \def (\lambda (c1: C).(let TMP_44 \def (CHead c k t) in 
(csubc g TMP_44 c1))) in (let TMP_46 \def (drop_refl e1) in (ex_intro2 C 
TMP_43 TMP_45 e1 TMP_46 H2)))))))))))) in (let TMP_66 \def (\lambda (n: 
nat).(\lambda (_: (((drop n O (CHead c k t) e2) \to (\forall (e1: C).((csubc 
g e2 e1) \to (ex2 C (\lambda (c1: C).(drop n O c1 e1)) (\lambda (c1: 
C).(csubc g (CHead c k t) c1)))))))).(\lambda (H1: (drop (S n) O (CHead c k 
t) e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e2 e1)).(let TMP_48 \def (r k 
n) in (let TMP_49 \def (drop_gen_drop k c e2 t n H1) in (let H_x \def (H e2 O 
TMP_48 TMP_49 e1 H2) in (let H3 \def H_x in (let TMP_51 \def (\lambda (c1: 
C).(let TMP_50 \def (r k n) in (drop TMP_50 O c1 e1))) in (let TMP_52 \def 
(\lambda (c1: C).(csubc g c c1)) in (let TMP_54 \def (\lambda (c1: C).(let 
TMP_53 \def (S n) in (drop TMP_53 O c1 e1))) in (let TMP_56 \def (\lambda 
(c1: C).(let TMP_55 \def (CHead c k t) in (csubc g TMP_55 c1))) in (let 
TMP_57 \def (ex2 C TMP_54 TMP_56) in (let TMP_65 \def (\lambda (x: 
C).(\lambda (H4: (drop (r k n) O x e1)).(\lambda (H5: (csubc g c x)).(let 
TMP_59 \def (\lambda (c1: C).(let TMP_58 \def (S n) in (drop TMP_58 O c1 
e1))) in (let TMP_61 \def (\lambda (c1: C).(let TMP_60 \def (CHead c k t) in 
(csubc g TMP_60 c1))) in (let TMP_62 \def (CHead x k t) in (let TMP_63 \def 
(drop_drop k n x e1 H4 t) in (let TMP_64 \def (csubc_head g c x H5 k t) in 
(ex_intro2 C TMP_59 TMP_61 TMP_62 TMP_63 TMP_64))))))))) in (ex2_ind C TMP_51 
TMP_52 TMP_57 TMP_65 H3)))))))))))))))) in (nat_ind TMP_38 TMP_47 TMP_66 
h))))) in (let TMP_353 \def (\lambda (n: nat).(\lambda (H0: ((\forall (h: 
nat).((drop h n (CHead c k t) e2) \to (\forall (e1: C).((csubc g e2 e1) \to 
(ex2 C (\lambda (c1: C).(drop h n c1 e1)) (\lambda (c1: C).(csubc g (CHead c 
k t) c1))))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c k t) 
e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e2 e1)).(let TMP_69 \def 
(\lambda (e: C).(\lambda (v: T).(let TMP_68 \def (CHead e k v) in (eq C e2 
TMP_68)))) in (let TMP_72 \def (\lambda (_: C).(\lambda (v: T).(let TMP_70 
\def (r k n) in (let TMP_71 \def (lift h TMP_70 v) in (eq T t TMP_71))))) in 
(let TMP_74 \def (\lambda (e: C).(\lambda (_: T).(let TMP_73 \def (r k n) in 
(drop h TMP_73 c e)))) in (let TMP_76 \def (\lambda (c1: C).(let TMP_75 \def 
(S n) in (drop h TMP_75 c1 e1))) in (let TMP_78 \def (\lambda (c1: C).(let 
TMP_77 \def (CHead c k t) in (csubc g TMP_77 c1))) in (let TMP_79 \def (ex2 C 
TMP_76 TMP_78) in (let TMP_351 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H3: (eq C e2 (CHead x0 k x1))).(\lambda (H4: (eq T t (lift h (r 
k n) x1))).(\lambda (H5: (drop h (r k n) c x0)).(let TMP_80 \def (\lambda 
(c0: C).(csubc g c0 e1)) in (let TMP_81 \def (CHead x0 k x1) in (let H6 \def 
(eq_ind C e2 TMP_80 H2 TMP_81 H3) in (let TMP_85 \def (\lambda (c0: 
C).(\forall (h0: nat).((drop h0 n (CHead c k t) c0) \to (\forall (e3: 
C).((csubc g c0 e3) \to (let TMP_82 \def (\lambda (c1: C).(drop h0 n c1 e3)) 
in (let TMP_84 \def (\lambda (c1: C).(let TMP_83 \def (CHead c k t) in (csubc 
g TMP_83 c1))) in (ex2 C TMP_82 TMP_84)))))))) in (let TMP_86 \def (CHead x0 
k x1) in (let H7 \def (eq_ind C e2 TMP_85 H0 TMP_86 H3) in (let TMP_90 \def 
(\lambda (t0: T).(\forall (h0: nat).((drop h0 n (CHead c k t0) (CHead x0 k 
x1)) \to (\forall (e3: C).((csubc g (CHead x0 k x1) e3) \to (let TMP_87 \def 
(\lambda (c1: C).(drop h0 n c1 e3)) in (let TMP_89 \def (\lambda (c1: C).(let 
TMP_88 \def (CHead c k t0) in (csubc g TMP_88 c1))) in (ex2 C TMP_87 
TMP_89)))))))) in (let TMP_91 \def (r k n) in (let TMP_92 \def (lift h TMP_91 
x1) in (let H8 \def (eq_ind T t TMP_90 H7 TMP_92 H4) in (let TMP_93 \def (r k 
n) in (let TMP_94 \def (lift h TMP_93 x1) in (let TMP_99 \def (\lambda (t0: 
T).(let TMP_96 \def (\lambda (c1: C).(let TMP_95 \def (S n) in (drop h TMP_95 
c1 e1))) in (let TMP_98 \def (\lambda (c1: C).(let TMP_97 \def (CHead c k t0) 
in (csubc g TMP_97 c1))) in (ex2 C TMP_96 TMP_98)))) in (let H_x \def 
(csubc_gen_head_l g x0 e1 x1 k H6) in (let H9 \def H_x in (let TMP_101 \def 
(\lambda (c3: C).(let TMP_100 \def (CHead c3 k x1) in (eq C e1 TMP_100))) in 
(let TMP_102 \def (\lambda (c3: C).(csubc g x0 c3)) in (let TMP_103 \def (ex2 
C TMP_101 TMP_102) in (let TMP_105 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(let TMP_104 \def (Bind Abst) in (eq K k TMP_104))))) in 
(let TMP_108 \def (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(let 
TMP_106 \def (Bind Abbr) in (let TMP_107 \def (CHead c3 TMP_106 w) in (eq C 
e1 TMP_107)))))) in (let TMP_109 \def (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g x0 c3)))) in (let TMP_111 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(let TMP_110 \def (asucc g a) in (sc3 g 
TMP_110 x0 x1))))) in (let TMP_112 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_113 \def (ex5_3 C T A 
TMP_105 TMP_108 TMP_109 TMP_111 TMP_112) in (let TMP_116 \def (\lambda (b: 
B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_114 \def (Bind b) in (let 
TMP_115 \def (CHead c3 TMP_114 v2) in (eq C e1 TMP_115)))))) in (let TMP_118 
\def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_117 \def (Bind 
Void) in (eq K k TMP_117))))) in (let TMP_120 \def (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(let TMP_119 \def (eq B b Void) in (not TMP_119))))) 
in (let TMP_121 \def (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc 
g x0 c3)))) in (let TMP_122 \def (ex4_3 B C T TMP_116 TMP_118 TMP_120 
TMP_121) in (let TMP_124 \def (\lambda (c1: C).(let TMP_123 \def (S n) in 
(drop h TMP_123 c1 e1))) in (let TMP_128 \def (\lambda (c1: C).(let TMP_125 
\def (r k n) in (let TMP_126 \def (lift h TMP_125 x1) in (let TMP_127 \def 
(CHead c k TMP_126) in (csubc g TMP_127 c1))))) in (let TMP_129 \def (ex2 C 
TMP_124 TMP_128) in (let TMP_177 \def (\lambda (H10: (ex2 C (\lambda (c3: 
C).(eq C e1 (CHead c3 k x1))) (\lambda (c3: C).(csubc g x0 c3)))).(let 
TMP_131 \def (\lambda (c3: C).(let TMP_130 \def (CHead c3 k x1) in (eq C e1 
TMP_130))) in (let TMP_132 \def (\lambda (c3: C).(csubc g x0 c3)) in (let 
TMP_134 \def (\lambda (c1: C).(let TMP_133 \def (S n) in (drop h TMP_133 c1 
e1))) in (let TMP_138 \def (\lambda (c1: C).(let TMP_135 \def (r k n) in (let 
TMP_136 \def (lift h TMP_135 x1) in (let TMP_137 \def (CHead c k TMP_136) in 
(csubc g TMP_137 c1))))) in (let TMP_139 \def (ex2 C TMP_134 TMP_138) in (let 
TMP_176 \def (\lambda (x: C).(\lambda (H11: (eq C e1 (CHead x k 
x1))).(\lambda (H12: (csubc g x0 x)).(let TMP_140 \def (CHead x k x1) in (let 
TMP_147 \def (\lambda (c0: C).(let TMP_142 \def (\lambda (c1: C).(let TMP_141 
\def (S n) in (drop h TMP_141 c1 c0))) in (let TMP_146 \def (\lambda (c1: 
C).(let TMP_143 \def (r k n) in (let TMP_144 \def (lift h TMP_143 x1) in (let 
TMP_145 \def (CHead c k TMP_144) in (csubc g TMP_145 c1))))) in (ex2 C 
TMP_142 TMP_146)))) in (let TMP_148 \def (r k n) in (let H_x0 \def (H x0 
TMP_148 h H5 x H12) in (let H13 \def H_x0 in (let TMP_150 \def (\lambda (c1: 
C).(let TMP_149 \def (r k n) in (drop h TMP_149 c1 x))) in (let TMP_151 \def 
(\lambda (c1: C).(csubc g c c1)) in (let TMP_154 \def (\lambda (c1: C).(let 
TMP_152 \def (S n) in (let TMP_153 \def (CHead x k x1) in (drop h TMP_152 c1 
TMP_153)))) in (let TMP_158 \def (\lambda (c1: C).(let TMP_155 \def (r k n) 
in (let TMP_156 \def (lift h TMP_155 x1) in (let TMP_157 \def (CHead c k 
TMP_156) in (csubc g TMP_157 c1))))) in (let TMP_159 \def (ex2 C TMP_154 
TMP_158) in (let TMP_174 \def (\lambda (x2: C).(\lambda (H14: (drop h (r k n) 
x2 x)).(\lambda (H15: (csubc g c x2)).(let TMP_162 \def (\lambda (c1: C).(let 
TMP_160 \def (S n) in (let TMP_161 \def (CHead x k x1) in (drop h TMP_160 c1 
TMP_161)))) in (let TMP_166 \def (\lambda (c1: C).(let TMP_163 \def (r k n) 
in (let TMP_164 \def (lift h TMP_163 x1) in (let TMP_165 \def (CHead c k 
TMP_164) in (csubc g TMP_165 c1))))) in (let TMP_167 \def (r k n) in (let 
TMP_168 \def (lift h TMP_167 x1) in (let TMP_169 \def (CHead x2 k TMP_168) in 
(let TMP_170 \def (drop_skip k h n x2 x H14 x1) in (let TMP_171 \def (r k n) 
in (let TMP_172 \def (lift h TMP_171 x1) in (let TMP_173 \def (csubc_head g c 
x2 H15 k TMP_172) in (ex_intro2 C TMP_162 TMP_166 TMP_169 TMP_170 
TMP_173))))))))))))) in (let TMP_175 \def (ex2_ind C TMP_150 TMP_151 TMP_159 
TMP_174 H13) in (eq_ind_r C TMP_140 TMP_147 TMP_175 e1 H11)))))))))))))))) in 
(ex2_ind C TMP_131 TMP_132 TMP_139 TMP_176 H10)))))))) in (let TMP_266 \def 
(\lambda (H10: (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C e1 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g x0 c3)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g (asucc g a) x0 x1)))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w)))))).(let TMP_179 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(let TMP_178 \def (Bind Abst) in (eq K k 
TMP_178))))) in (let TMP_182 \def (\lambda (c3: C).(\lambda (w: T).(\lambda 
(_: A).(let TMP_180 \def (Bind Abbr) in (let TMP_181 \def (CHead c3 TMP_180 
w) in (eq C e1 TMP_181)))))) in (let TMP_183 \def (\lambda (c3: C).(\lambda 
(_: T).(\lambda (_: A).(csubc g x0 c3)))) in (let TMP_185 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(let TMP_184 \def (asucc g a) in (sc3 g 
TMP_184 x0 x1))))) in (let TMP_186 \def (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w)))) in (let TMP_188 \def (\lambda (c1: 
C).(let TMP_187 \def (S n) in (drop h TMP_187 c1 e1))) in (let TMP_192 \def 
(\lambda (c1: C).(let TMP_189 \def (r k n) in (let TMP_190 \def (lift h 
TMP_189 x1) in (let TMP_191 \def (CHead c k TMP_190) in (csubc g TMP_191 
c1))))) in (let TMP_193 \def (ex2 C TMP_188 TMP_192) in (let TMP_265 \def 
(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H11: (eq K k 
(Bind Abst))).(\lambda (H12: (eq C e1 (CHead x2 (Bind Abbr) x3))).(\lambda 
(H13: (csubc g x0 x2)).(\lambda (H14: (sc3 g (asucc g x4) x0 x1)).(\lambda 
(H15: (sc3 g x4 x2 x3)).(let TMP_194 \def (Bind Abbr) in (let TMP_195 \def 
(CHead x2 TMP_194 x3) in (let TMP_202 \def (\lambda (c0: C).(let TMP_197 \def 
(\lambda (c1: C).(let TMP_196 \def (S n) in (drop h TMP_196 c1 c0))) in (let 
TMP_201 \def (\lambda (c1: C).(let TMP_198 \def (r k n) in (let TMP_199 \def 
(lift h TMP_198 x1) in (let TMP_200 \def (CHead c k TMP_199) in (csubc g 
TMP_200 c1))))) in (ex2 C TMP_197 TMP_201)))) in (let TMP_208 \def (\lambda 
(k0: K).(\forall (h0: nat).((drop h0 n (CHead c k0 (lift h (r k0 n) x1)) 
(CHead x0 k0 x1)) \to (\forall (e3: C).((csubc g (CHead x0 k0 x1) e3) \to 
(let TMP_203 \def (\lambda (c1: C).(drop h0 n c1 e3)) in (let TMP_207 \def 
(\lambda (c1: C).(let TMP_204 \def (r k0 n) in (let TMP_205 \def (lift h 
TMP_204 x1) in (let TMP_206 \def (CHead c k0 TMP_205) in (csubc g TMP_206 
c1))))) in (ex2 C TMP_203 TMP_207)))))))) in (let TMP_209 \def (Bind Abst) in 
(let H16 \def (eq_ind K k TMP_208 H8 TMP_209 H11) in (let TMP_211 \def 
(\lambda (k0: K).(let TMP_210 \def (r k0 n) in (drop h TMP_210 c x0))) in 
(let TMP_212 \def (Bind Abst) in (let H17 \def (eq_ind K k TMP_211 H5 TMP_212 
H11) in (let TMP_213 \def (Bind Abst) in (let TMP_222 \def (\lambda (k0: 
K).(let TMP_217 \def (\lambda (c1: C).(let TMP_214 \def (S n) in (let TMP_215 
\def (Bind Abbr) in (let TMP_216 \def (CHead x2 TMP_215 x3) in (drop h 
TMP_214 c1 TMP_216))))) in (let TMP_221 \def (\lambda (c1: C).(let TMP_218 
\def (r k0 n) in (let TMP_219 \def (lift h TMP_218 x1) in (let TMP_220 \def 
(CHead c k0 TMP_219) in (csubc g TMP_220 c1))))) in (ex2 C TMP_217 
TMP_221)))) in (let TMP_223 \def (Bind Abst) in (let TMP_224 \def (r TMP_223 
n) in (let H_x0 \def (H x0 TMP_224 h H17 x2 H13) in (let H18 \def H_x0 in 
(let TMP_225 \def (\lambda (c1: C).(drop h n c1 x2)) in (let TMP_226 \def 
(\lambda (c1: C).(csubc g c c1)) in (let TMP_230 \def (\lambda (c1: C).(let 
TMP_227 \def (S n) in (let TMP_228 \def (Bind Abbr) in (let TMP_229 \def 
(CHead x2 TMP_228 x3) in (drop h TMP_227 c1 TMP_229))))) in (let TMP_236 \def 
(\lambda (c1: C).(let TMP_231 \def (Bind Abst) in (let TMP_232 \def (Bind 
Abst) in (let TMP_233 \def (r TMP_232 n) in (let TMP_234 \def (lift h TMP_233 
x1) in (let TMP_235 \def (CHead c TMP_231 TMP_234) in (csubc g TMP_235 
c1))))))) in (let TMP_237 \def (ex2 C TMP_230 TMP_236) in (let TMP_262 \def 
(\lambda (x: C).(\lambda (H19: (drop h n x x2)).(\lambda (H20: (csubc g c 
x)).(let TMP_241 \def (\lambda (c1: C).(let TMP_238 \def (S n) in (let 
TMP_239 \def (Bind Abbr) in (let TMP_240 \def (CHead x2 TMP_239 x3) in (drop 
h TMP_238 c1 TMP_240))))) in (let TMP_247 \def (\lambda (c1: C).(let TMP_242 
\def (Bind Abst) in (let TMP_243 \def (Bind Abst) in (let TMP_244 \def (r 
TMP_243 n) in (let TMP_245 \def (lift h TMP_244 x1) in (let TMP_246 \def 
(CHead c TMP_242 TMP_245) in (csubc g TMP_246 c1))))))) in (let TMP_248 \def 
(Bind Abbr) in (let TMP_249 \def (lift h n x3) in (let TMP_250 \def (CHead x 
TMP_248 TMP_249) in (let TMP_251 \def (drop_skip_bind h n x x2 H19 Abbr x3) 
in (let TMP_252 \def (Bind Abst) in (let TMP_253 \def (r TMP_252 n) in (let 
TMP_254 \def (lift h TMP_253 x1) in (let TMP_255 \def (asucc g x4) in (let 
TMP_256 \def (Bind Abst) in (let TMP_257 \def (r TMP_256 n) in (let TMP_258 
\def (sc3_lift g TMP_255 x0 x1 H14 c h TMP_257 H17) in (let TMP_259 \def 
(lift h n x3) in (let TMP_260 \def (sc3_lift g x4 x2 x3 H15 x h n H19) in 
(let TMP_261 \def (csubc_abst g c x H20 TMP_254 x4 TMP_258 TMP_259 TMP_260) 
in (ex_intro2 C TMP_241 TMP_247 TMP_250 TMP_251 TMP_261)))))))))))))))))))) 
in (let TMP_263 \def (ex2_ind C TMP_225 TMP_226 TMP_237 TMP_262 H18) in (let 
TMP_264 \def (eq_ind_r K TMP_213 TMP_222 TMP_263 k H11) in (eq_ind_r C 
TMP_195 TMP_202 TMP_264 e1 H12)))))))))))))))))))))))))))))))) in (ex5_3_ind 
C T A TMP_179 TMP_182 TMP_183 TMP_185 TMP_186 TMP_193 TMP_265 H10))))))))))) 
in (let TMP_349 \def (\lambda (H10: (ex4_3 B C T (\lambda (b: B).(\lambda 
(c3: C).(\lambda (v2: T).(eq C e1 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g x0 c3)))))).(let TMP_269 \def 
(\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(let TMP_267 \def (Bind b) 
in (let TMP_268 \def (CHead c3 TMP_267 v2) in (eq C e1 TMP_268)))))) in (let 
TMP_271 \def (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(let TMP_270 
\def (Bind Void) in (eq K k TMP_270))))) in (let TMP_273 \def (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(let TMP_272 \def (eq B b Void) in (not 
TMP_272))))) in (let TMP_274 \def (\lambda (_: B).(\lambda (c3: C).(\lambda 
(_: T).(csubc g x0 c3)))) in (let TMP_276 \def (\lambda (c1: C).(let TMP_275 
\def (S n) in (drop h TMP_275 c1 e1))) in (let TMP_280 \def (\lambda (c1: 
C).(let TMP_277 \def (r k n) in (let TMP_278 \def (lift h TMP_277 x1) in (let 
TMP_279 \def (CHead c k TMP_278) in (csubc g TMP_279 c1))))) in (let TMP_281 
\def (ex2 C TMP_276 TMP_280) in (let TMP_348 \def (\lambda (x2: B).(\lambda 
(x3: C).(\lambda (x4: T).(\lambda (H11: (eq C e1 (CHead x3 (Bind x2) 
x4))).(\lambda (H12: (eq K k (Bind Void))).(\lambda (H13: (not (eq B x2 
Void))).(\lambda (H14: (csubc g x0 x3)).(let TMP_282 \def (Bind x2) in (let 
TMP_283 \def (CHead x3 TMP_282 x4) in (let TMP_290 \def (\lambda (c0: C).(let 
TMP_285 \def (\lambda (c1: C).(let TMP_284 \def (S n) in (drop h TMP_284 c1 
c0))) in (let TMP_289 \def (\lambda (c1: C).(let TMP_286 \def (r k n) in (let 
TMP_287 \def (lift h TMP_286 x1) in (let TMP_288 \def (CHead c k TMP_287) in 
(csubc g TMP_288 c1))))) in (ex2 C TMP_285 TMP_289)))) in (let TMP_296 \def 
(\lambda (k0: K).(\forall (h0: nat).((drop h0 n (CHead c k0 (lift h (r k0 n) 
x1)) (CHead x0 k0 x1)) \to (\forall (e3: C).((csubc g (CHead x0 k0 x1) e3) 
\to (let TMP_291 \def (\lambda (c1: C).(drop h0 n c1 e3)) in (let TMP_295 
\def (\lambda (c1: C).(let TMP_292 \def (r k0 n) in (let TMP_293 \def (lift h 
TMP_292 x1) in (let TMP_294 \def (CHead c k0 TMP_293) in (csubc g TMP_294 
c1))))) in (ex2 C TMP_291 TMP_295)))))))) in (let TMP_297 \def (Bind Void) in 
(let H15 \def (eq_ind K k TMP_296 H8 TMP_297 H12) in (let TMP_299 \def 
(\lambda (k0: K).(let TMP_298 \def (r k0 n) in (drop h TMP_298 c x0))) in 
(let TMP_300 \def (Bind Void) in (let H16 \def (eq_ind K k TMP_299 H5 TMP_300 
H12) in (let TMP_301 \def (Bind Void) in (let TMP_310 \def (\lambda (k0: 
K).(let TMP_305 \def (\lambda (c1: C).(let TMP_302 \def (S n) in (let TMP_303 
\def (Bind x2) in (let TMP_304 \def (CHead x3 TMP_303 x4) in (drop h TMP_302 
c1 TMP_304))))) in (let TMP_309 \def (\lambda (c1: C).(let TMP_306 \def (r k0 
n) in (let TMP_307 \def (lift h TMP_306 x1) in (let TMP_308 \def (CHead c k0 
TMP_307) in (csubc g TMP_308 c1))))) in (ex2 C TMP_305 TMP_309)))) in (let 
TMP_311 \def (Bind Void) in (let TMP_312 \def (r TMP_311 n) in (let H_x0 \def 
(H x0 TMP_312 h H16 x3 H14) in (let H17 \def H_x0 in (let TMP_313 \def 
(\lambda (c1: C).(drop h n c1 x3)) in (let TMP_314 \def (\lambda (c1: 
C).(csubc g c c1)) in (let TMP_318 \def (\lambda (c1: C).(let TMP_315 \def (S 
n) in (let TMP_316 \def (Bind x2) in (let TMP_317 \def (CHead x3 TMP_316 x4) 
in (drop h TMP_315 c1 TMP_317))))) in (let TMP_324 \def (\lambda (c1: C).(let 
TMP_319 \def (Bind Void) in (let TMP_320 \def (Bind Void) in (let TMP_321 
\def (r TMP_320 n) in (let TMP_322 \def (lift h TMP_321 x1) in (let TMP_323 
\def (CHead c TMP_319 TMP_322) in (csubc g TMP_323 c1))))))) in (let TMP_325 
\def (ex2 C TMP_318 TMP_324) in (let TMP_345 \def (\lambda (x: C).(\lambda 
(H18: (drop h n x x3)).(\lambda (H19: (csubc g c x)).(let TMP_329 \def 
(\lambda (c1: C).(let TMP_326 \def (S n) in (let TMP_327 \def (Bind x2) in 
(let TMP_328 \def (CHead x3 TMP_327 x4) in (drop h TMP_326 c1 TMP_328))))) in 
(let TMP_335 \def (\lambda (c1: C).(let TMP_330 \def (Bind Void) in (let 
TMP_331 \def (Bind Void) in (let TMP_332 \def (r TMP_331 n) in (let TMP_333 
\def (lift h TMP_332 x1) in (let TMP_334 \def (CHead c TMP_330 TMP_333) in 
(csubc g TMP_334 c1))))))) in (let TMP_336 \def (Bind x2) in (let TMP_337 
\def (lift h n x4) in (let TMP_338 \def (CHead x TMP_336 TMP_337) in (let 
TMP_339 \def (drop_skip_bind h n x x3 H18 x2 x4) in (let TMP_340 \def (Bind 
Void) in (let TMP_341 \def (r TMP_340 n) in (let TMP_342 \def (lift h TMP_341 
x1) in (let TMP_343 \def (lift h n x4) in (let TMP_344 \def (csubc_void g c x 
H19 x2 H13 TMP_342 TMP_343) in (ex_intro2 C TMP_329 TMP_335 TMP_338 TMP_339 
TMP_344))))))))))))))) in (let TMP_346 \def (ex2_ind C TMP_313 TMP_314 
TMP_325 TMP_345 H17) in (let TMP_347 \def (eq_ind_r K TMP_301 TMP_310 TMP_346 
k H12) in (eq_ind_r C TMP_283 TMP_290 TMP_347 e1 
H11))))))))))))))))))))))))))))))) in (ex4_3_ind B C T TMP_269 TMP_271 
TMP_273 TMP_274 TMP_281 TMP_348 H10)))))))))) in (let TMP_350 \def (or3_ind 
TMP_103 TMP_113 TMP_122 TMP_129 TMP_177 TMP_266 TMP_349 H9) in (eq_ind_r T 
TMP_94 TMP_99 TMP_350 t H4)))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_352 \def (drop_gen_skip_l c e2 t h n k H1) in (ex3_2_ind C T TMP_69 
TMP_72 TMP_74 TMP_79 TMP_351 TMP_352))))))))))))))) in (nat_ind TMP_34 TMP_67 
TMP_353 d)))))))))) in (C_ind TMP_3 TMP_30 TMP_354 c2))))).

theorem csubc_drop_conf_rev:
 \forall (g: G).(\forall (c2: C).(\forall (e2: C).(\forall (d: nat).(\forall 
(h: nat).((drop h d c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c1 c2))))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(let TMP_3 \def (\lambda (c: C).(\forall 
(e2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c e2) \to (\forall 
(e1: C).((csubc g e1 e2) \to (let TMP_1 \def (\lambda (c1: C).(drop h d c1 
e1)) in (let TMP_2 \def (\lambda (c1: C).(csubc g c1 c)) in (ex2 C TMP_1 
TMP_2)))))))))) in (let TMP_30 \def (\lambda (n: nat).(\lambda (e2: 
C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e1 e2)).(let TMP_4 \def (CSort 
n) in (let TMP_5 \def (eq C e2 TMP_4) in (let TMP_6 \def (eq nat h O) in (let 
TMP_7 \def (eq nat d O) in (let TMP_8 \def (\lambda (c1: C).(drop h d c1 e1)) 
in (let TMP_10 \def (\lambda (c1: C).(let TMP_9 \def (CSort n) in (csubc g c1 
TMP_9))) in (let TMP_11 \def (ex2 C TMP_8 TMP_10) in (let TMP_28 \def 
(\lambda (H1: (eq C e2 (CSort n))).(\lambda (H2: (eq nat h O)).(\lambda (H3: 
(eq nat d O)).(let TMP_15 \def (\lambda (n0: nat).(let TMP_12 \def (\lambda 
(c1: C).(drop n0 d c1 e1)) in (let TMP_14 \def (\lambda (c1: C).(let TMP_13 
\def (CSort n) in (csubc g c1 TMP_13))) in (ex2 C TMP_12 TMP_14)))) in (let 
TMP_19 \def (\lambda (n0: nat).(let TMP_16 \def (\lambda (c1: C).(drop O n0 
c1 e1)) in (let TMP_18 \def (\lambda (c1: C).(let TMP_17 \def (CSort n) in 
(csubc g c1 TMP_17))) in (ex2 C TMP_16 TMP_18)))) in (let TMP_20 \def 
(\lambda (c: C).(csubc g e1 c)) in (let TMP_21 \def (CSort n) in (let H4 \def 
(eq_ind C e2 TMP_20 H0 TMP_21 H1) in (let TMP_22 \def (\lambda (c1: C).(drop 
O O c1 e1)) in (let TMP_24 \def (\lambda (c1: C).(let TMP_23 \def (CSort n) 
in (csubc g c1 TMP_23))) in (let TMP_25 \def (drop_refl e1) in (let TMP_26 
\def (ex_intro2 C TMP_22 TMP_24 e1 TMP_25 H4) in (let TMP_27 \def (eq_ind_r 
nat O TMP_19 TMP_26 d H3) in (eq_ind_r nat O TMP_15 TMP_27 h H2)))))))))))))) 
in (let TMP_29 \def (drop_gen_sort n h d e2 H) in (and3_ind TMP_5 TMP_6 TMP_7 
TMP_11 TMP_28 TMP_29))))))))))))))))) in (let TMP_354 \def (\lambda (c: 
C).(\lambda (H: ((\forall (e2: C).(\forall (d: nat).(\forall (h: nat).((drop 
h d c e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda (c1: 
C).(drop h d c1 e1)) (\lambda (c1: C).(csubc g c1 c))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (e2: C).(\lambda (d: nat).(let TMP_34 \def 
(\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c k t) e2) \to (\forall 
(e1: C).((csubc g e1 e2) \to (let TMP_31 \def (\lambda (c1: C).(drop h n c1 
e1)) in (let TMP_33 \def (\lambda (c1: C).(let TMP_32 \def (CHead c k t) in 
(csubc g c1 TMP_32))) in (ex2 C TMP_31 TMP_33)))))))) in (let TMP_67 \def 
(\lambda (h: nat).(let TMP_38 \def (\lambda (n: nat).((drop n O (CHead c k t) 
e2) \to (\forall (e1: C).((csubc g e1 e2) \to (let TMP_35 \def (\lambda (c1: 
C).(drop n O c1 e1)) in (let TMP_37 \def (\lambda (c1: C).(let TMP_36 \def 
(CHead c k t) in (csubc g c1 TMP_36))) in (ex2 C TMP_35 TMP_37))))))) in (let 
TMP_47 \def (\lambda (H0: (drop O O (CHead c k t) e2)).(\lambda (e1: 
C).(\lambda (H1: (csubc g e1 e2)).(let TMP_39 \def (\lambda (c0: C).(csubc g 
e1 c0)) in (let TMP_40 \def (CHead c k t) in (let TMP_41 \def (CHead c k t) 
in (let TMP_42 \def (drop_gen_refl TMP_41 e2 H0) in (let H2 \def (eq_ind_r C 
e2 TMP_39 H1 TMP_40 TMP_42) in (let TMP_43 \def (\lambda (c1: C).(drop O O c1 
e1)) in (let TMP_45 \def (\lambda (c1: C).(let TMP_44 \def (CHead c k t) in 
(csubc g c1 TMP_44))) in (let TMP_46 \def (drop_refl e1) in (ex_intro2 C 
TMP_43 TMP_45 e1 TMP_46 H2)))))))))))) in (let TMP_66 \def (\lambda (n: 
nat).(\lambda (_: (((drop n O (CHead c k t) e2) \to (\forall (e1: C).((csubc 
g e1 e2) \to (ex2 C (\lambda (c1: C).(drop n O c1 e1)) (\lambda (c1: 
C).(csubc g c1 (CHead c k t))))))))).(\lambda (H1: (drop (S n) O (CHead c k 
t) e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e1 e2)).(let TMP_48 \def (r k 
n) in (let TMP_49 \def (drop_gen_drop k c e2 t n H1) in (let H_x \def (H e2 O 
TMP_48 TMP_49 e1 H2) in (let H3 \def H_x in (let TMP_51 \def (\lambda (c1: 
C).(let TMP_50 \def (r k n) in (drop TMP_50 O c1 e1))) in (let TMP_52 \def 
(\lambda (c1: C).(csubc g c1 c)) in (let TMP_54 \def (\lambda (c1: C).(let 
TMP_53 \def (S n) in (drop TMP_53 O c1 e1))) in (let TMP_56 \def (\lambda 
(c1: C).(let TMP_55 \def (CHead c k t) in (csubc g c1 TMP_55))) in (let 
TMP_57 \def (ex2 C TMP_54 TMP_56) in (let TMP_65 \def (\lambda (x: 
C).(\lambda (H4: (drop (r k n) O x e1)).(\lambda (H5: (csubc g x c)).(let 
TMP_59 \def (\lambda (c1: C).(let TMP_58 \def (S n) in (drop TMP_58 O c1 
e1))) in (let TMP_61 \def (\lambda (c1: C).(let TMP_60 \def (CHead c k t) in 
(csubc g c1 TMP_60))) in (let TMP_62 \def (CHead x k t) in (let TMP_63 \def 
(drop_drop k n x e1 H4 t) in (let TMP_64 \def (csubc_head g x c H5 k t) in 
(ex_intro2 C TMP_59 TMP_61 TMP_62 TMP_63 TMP_64))))))))) in (ex2_ind C TMP_51 
TMP_52 TMP_57 TMP_65 H3)))))))))))))))) in (nat_ind TMP_38 TMP_47 TMP_66 
h))))) in (let TMP_353 \def (\lambda (n: nat).(\lambda (H0: ((\forall (h: 
nat).((drop h n (CHead c k t) e2) \to (\forall (e1: C).((csubc g e1 e2) \to 
(ex2 C (\lambda (c1: C).(drop h n c1 e1)) (\lambda (c1: C).(csubc g c1 (CHead 
c k t)))))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c k t) 
e2)).(\lambda (e1: C).(\lambda (H2: (csubc g e1 e2)).(let TMP_69 \def 
(\lambda (e: C).(\lambda (v: T).(let TMP_68 \def (CHead e k v) in (eq C e2 
TMP_68)))) in (let TMP_72 \def (\lambda (_: C).(\lambda (v: T).(let TMP_70 
\def (r k n) in (let TMP_71 \def (lift h TMP_70 v) in (eq T t TMP_71))))) in 
(let TMP_74 \def (\lambda (e: C).(\lambda (_: T).(let TMP_73 \def (r k n) in 
(drop h TMP_73 c e)))) in (let TMP_76 \def (\lambda (c1: C).(let TMP_75 \def 
(S n) in (drop h TMP_75 c1 e1))) in (let TMP_78 \def (\lambda (c1: C).(let 
TMP_77 \def (CHead c k t) in (csubc g c1 TMP_77))) in (let TMP_79 \def (ex2 C 
TMP_76 TMP_78) in (let TMP_351 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H3: (eq C e2 (CHead x0 k x1))).(\lambda (H4: (eq T t (lift h (r 
k n) x1))).(\lambda (H5: (drop h (r k n) c x0)).(let TMP_80 \def (\lambda 
(c0: C).(csubc g e1 c0)) in (let TMP_81 \def (CHead x0 k x1) in (let H6 \def 
(eq_ind C e2 TMP_80 H2 TMP_81 H3) in (let TMP_85 \def (\lambda (c0: 
C).(\forall (h0: nat).((drop h0 n (CHead c k t) c0) \to (\forall (e3: 
C).((csubc g e3 c0) \to (let TMP_82 \def (\lambda (c1: C).(drop h0 n c1 e3)) 
in (let TMP_84 \def (\lambda (c1: C).(let TMP_83 \def (CHead c k t) in (csubc 
g c1 TMP_83))) in (ex2 C TMP_82 TMP_84)))))))) in (let TMP_86 \def (CHead x0 
k x1) in (let H7 \def (eq_ind C e2 TMP_85 H0 TMP_86 H3) in (let TMP_90 \def 
(\lambda (t0: T).(\forall (h0: nat).((drop h0 n (CHead c k t0) (CHead x0 k 
x1)) \to (\forall (e3: C).((csubc g e3 (CHead x0 k x1)) \to (let TMP_87 \def 
(\lambda (c1: C).(drop h0 n c1 e3)) in (let TMP_89 \def (\lambda (c1: C).(let 
TMP_88 \def (CHead c k t0) in (csubc g c1 TMP_88))) in (ex2 C TMP_87 
TMP_89)))))))) in (let TMP_91 \def (r k n) in (let TMP_92 \def (lift h TMP_91 
x1) in (let H8 \def (eq_ind T t TMP_90 H7 TMP_92 H4) in (let TMP_93 \def (r k 
n) in (let TMP_94 \def (lift h TMP_93 x1) in (let TMP_99 \def (\lambda (t0: 
T).(let TMP_96 \def (\lambda (c1: C).(let TMP_95 \def (S n) in (drop h TMP_95 
c1 e1))) in (let TMP_98 \def (\lambda (c1: C).(let TMP_97 \def (CHead c k t0) 
in (csubc g c1 TMP_97))) in (ex2 C TMP_96 TMP_98)))) in (let H_x \def 
(csubc_gen_head_r g x0 e1 x1 k H6) in (let H9 \def H_x in (let TMP_101 \def 
(\lambda (c1: C).(let TMP_100 \def (CHead c1 k x1) in (eq C e1 TMP_100))) in 
(let TMP_102 \def (\lambda (c1: C).(csubc g c1 x0)) in (let TMP_103 \def (ex2 
C TMP_101 TMP_102) in (let TMP_105 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(let TMP_104 \def (Bind Abbr) in (eq K k TMP_104))))) in 
(let TMP_108 \def (\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(let 
TMP_106 \def (Bind Abst) in (let TMP_107 \def (CHead c1 TMP_106 v) in (eq C 
e1 TMP_107)))))) in (let TMP_109 \def (\lambda (c1: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c1 x0)))) in (let TMP_111 \def (\lambda (c1: 
C).(\lambda (v: T).(\lambda (a: A).(let TMP_110 \def (asucc g a) in (sc3 g 
TMP_110 c1 v))))) in (let TMP_112 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a x0 x1)))) in (let TMP_113 \def (ex5_3 C T A 
TMP_105 TMP_108 TMP_109 TMP_111 TMP_112) in (let TMP_116 \def (\lambda (_: 
B).(\lambda (c1: C).(\lambda (v1: T).(let TMP_114 \def (Bind Void) in (let 
TMP_115 \def (CHead c1 TMP_114 v1) in (eq C e1 TMP_115)))))) in (let TMP_118 
\def (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(let TMP_117 \def (Bind 
b) in (eq K k TMP_117))))) in (let TMP_120 \def (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(let TMP_119 \def (eq B b Void) in (not TMP_119))))) in 
(let TMP_121 \def (\lambda (_: B).(\lambda (c1: C).(\lambda (_: T).(csubc g 
c1 x0)))) in (let TMP_122 \def (ex4_3 B C T TMP_116 TMP_118 TMP_120 TMP_121) 
in (let TMP_124 \def (\lambda (c1: C).(let TMP_123 \def (S n) in (drop h 
TMP_123 c1 e1))) in (let TMP_128 \def (\lambda (c1: C).(let TMP_125 \def (r k 
n) in (let TMP_126 \def (lift h TMP_125 x1) in (let TMP_127 \def (CHead c k 
TMP_126) in (csubc g c1 TMP_127))))) in (let TMP_129 \def (ex2 C TMP_124 
TMP_128) in (let TMP_177 \def (\lambda (H10: (ex2 C (\lambda (c1: C).(eq C e1 
(CHead c1 k x1))) (\lambda (c1: C).(csubc g c1 x0)))).(let TMP_131 \def 
(\lambda (c1: C).(let TMP_130 \def (CHead c1 k x1) in (eq C e1 TMP_130))) in 
(let TMP_132 \def (\lambda (c1: C).(csubc g c1 x0)) in (let TMP_134 \def 
(\lambda (c1: C).(let TMP_133 \def (S n) in (drop h TMP_133 c1 e1))) in (let 
TMP_138 \def (\lambda (c1: C).(let TMP_135 \def (r k n) in (let TMP_136 \def 
(lift h TMP_135 x1) in (let TMP_137 \def (CHead c k TMP_136) in (csubc g c1 
TMP_137))))) in (let TMP_139 \def (ex2 C TMP_134 TMP_138) in (let TMP_176 
\def (\lambda (x: C).(\lambda (H11: (eq C e1 (CHead x k x1))).(\lambda (H12: 
(csubc g x x0)).(let TMP_140 \def (CHead x k x1) in (let TMP_147 \def 
(\lambda (c0: C).(let TMP_142 \def (\lambda (c1: C).(let TMP_141 \def (S n) 
in (drop h TMP_141 c1 c0))) in (let TMP_146 \def (\lambda (c1: C).(let 
TMP_143 \def (r k n) in (let TMP_144 \def (lift h TMP_143 x1) in (let TMP_145 
\def (CHead c k TMP_144) in (csubc g c1 TMP_145))))) in (ex2 C TMP_142 
TMP_146)))) in (let TMP_148 \def (r k n) in (let H_x0 \def (H x0 TMP_148 h H5 
x H12) in (let H13 \def H_x0 in (let TMP_150 \def (\lambda (c1: C).(let 
TMP_149 \def (r k n) in (drop h TMP_149 c1 x))) in (let TMP_151 \def (\lambda 
(c1: C).(csubc g c1 c)) in (let TMP_154 \def (\lambda (c1: C).(let TMP_152 
\def (S n) in (let TMP_153 \def (CHead x k x1) in (drop h TMP_152 c1 
TMP_153)))) in (let TMP_158 \def (\lambda (c1: C).(let TMP_155 \def (r k n) 
in (let TMP_156 \def (lift h TMP_155 x1) in (let TMP_157 \def (CHead c k 
TMP_156) in (csubc g c1 TMP_157))))) in (let TMP_159 \def (ex2 C TMP_154 
TMP_158) in (let TMP_174 \def (\lambda (x2: C).(\lambda (H14: (drop h (r k n) 
x2 x)).(\lambda (H15: (csubc g x2 c)).(let TMP_162 \def (\lambda (c1: C).(let 
TMP_160 \def (S n) in (let TMP_161 \def (CHead x k x1) in (drop h TMP_160 c1 
TMP_161)))) in (let TMP_166 \def (\lambda (c1: C).(let TMP_163 \def (r k n) 
in (let TMP_164 \def (lift h TMP_163 x1) in (let TMP_165 \def (CHead c k 
TMP_164) in (csubc g c1 TMP_165))))) in (let TMP_167 \def (r k n) in (let 
TMP_168 \def (lift h TMP_167 x1) in (let TMP_169 \def (CHead x2 k TMP_168) in 
(let TMP_170 \def (drop_skip k h n x2 x H14 x1) in (let TMP_171 \def (r k n) 
in (let TMP_172 \def (lift h TMP_171 x1) in (let TMP_173 \def (csubc_head g 
x2 c H15 k TMP_172) in (ex_intro2 C TMP_162 TMP_166 TMP_169 TMP_170 
TMP_173))))))))))))) in (let TMP_175 \def (ex2_ind C TMP_150 TMP_151 TMP_159 
TMP_174 H13) in (eq_ind_r C TMP_140 TMP_147 TMP_175 e1 H11)))))))))))))))) in 
(ex2_ind C TMP_131 TMP_132 TMP_139 TMP_176 H10)))))))) in (let TMP_266 \def 
(\lambda (H10: (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: 
A).(eq K k (Bind Abbr))))) (\lambda (c1: C).(\lambda (v: T).(\lambda (_: 
A).(eq C e1 (CHead c1 (Bind Abst) v))))) (\lambda (c1: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c1 x0)))) (\lambda (c1: C).(\lambda (v: 
T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a x0 x1)))))).(let TMP_179 \def (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(let TMP_178 \def (Bind Abbr) in (eq K k 
TMP_178))))) in (let TMP_182 \def (\lambda (c1: C).(\lambda (v: T).(\lambda 
(_: A).(let TMP_180 \def (Bind Abst) in (let TMP_181 \def (CHead c1 TMP_180 
v) in (eq C e1 TMP_181)))))) in (let TMP_183 \def (\lambda (c1: C).(\lambda 
(_: T).(\lambda (_: A).(csubc g c1 x0)))) in (let TMP_185 \def (\lambda (c1: 
C).(\lambda (v: T).(\lambda (a: A).(let TMP_184 \def (asucc g a) in (sc3 g 
TMP_184 c1 v))))) in (let TMP_186 \def (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a x0 x1)))) in (let TMP_188 \def (\lambda (c1: 
C).(let TMP_187 \def (S n) in (drop h TMP_187 c1 e1))) in (let TMP_192 \def 
(\lambda (c1: C).(let TMP_189 \def (r k n) in (let TMP_190 \def (lift h 
TMP_189 x1) in (let TMP_191 \def (CHead c k TMP_190) in (csubc g c1 
TMP_191))))) in (let TMP_193 \def (ex2 C TMP_188 TMP_192) in (let TMP_265 
\def (\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H11: (eq K 
k (Bind Abbr))).(\lambda (H12: (eq C e1 (CHead x2 (Bind Abst) x3))).(\lambda 
(H13: (csubc g x2 x0)).(\lambda (H14: (sc3 g (asucc g x4) x2 x3)).(\lambda 
(H15: (sc3 g x4 x0 x1)).(let TMP_194 \def (Bind Abst) in (let TMP_195 \def 
(CHead x2 TMP_194 x3) in (let TMP_202 \def (\lambda (c0: C).(let TMP_197 \def 
(\lambda (c1: C).(let TMP_196 \def (S n) in (drop h TMP_196 c1 c0))) in (let 
TMP_201 \def (\lambda (c1: C).(let TMP_198 \def (r k n) in (let TMP_199 \def 
(lift h TMP_198 x1) in (let TMP_200 \def (CHead c k TMP_199) in (csubc g c1 
TMP_200))))) in (ex2 C TMP_197 TMP_201)))) in (let TMP_208 \def (\lambda (k0: 
K).(\forall (h0: nat).((drop h0 n (CHead c k0 (lift h (r k0 n) x1)) (CHead x0 
k0 x1)) \to (\forall (e3: C).((csubc g e3 (CHead x0 k0 x1)) \to (let TMP_203 
\def (\lambda (c1: C).(drop h0 n c1 e3)) in (let TMP_207 \def (\lambda (c1: 
C).(let TMP_204 \def (r k0 n) in (let TMP_205 \def (lift h TMP_204 x1) in 
(let TMP_206 \def (CHead c k0 TMP_205) in (csubc g c1 TMP_206))))) in (ex2 C 
TMP_203 TMP_207)))))))) in (let TMP_209 \def (Bind Abbr) in (let H16 \def 
(eq_ind K k TMP_208 H8 TMP_209 H11) in (let TMP_211 \def (\lambda (k0: 
K).(let TMP_210 \def (r k0 n) in (drop h TMP_210 c x0))) in (let TMP_212 \def 
(Bind Abbr) in (let H17 \def (eq_ind K k TMP_211 H5 TMP_212 H11) in (let 
TMP_213 \def (Bind Abbr) in (let TMP_222 \def (\lambda (k0: K).(let TMP_217 
\def (\lambda (c1: C).(let TMP_214 \def (S n) in (let TMP_215 \def (Bind 
Abst) in (let TMP_216 \def (CHead x2 TMP_215 x3) in (drop h TMP_214 c1 
TMP_216))))) in (let TMP_221 \def (\lambda (c1: C).(let TMP_218 \def (r k0 n) 
in (let TMP_219 \def (lift h TMP_218 x1) in (let TMP_220 \def (CHead c k0 
TMP_219) in (csubc g c1 TMP_220))))) in (ex2 C TMP_217 TMP_221)))) in (let 
TMP_223 \def (Bind Abbr) in (let TMP_224 \def (r TMP_223 n) in (let H_x0 \def 
(H x0 TMP_224 h H17 x2 H13) in (let H18 \def H_x0 in (let TMP_225 \def 
(\lambda (c1: C).(drop h n c1 x2)) in (let TMP_226 \def (\lambda (c1: 
C).(csubc g c1 c)) in (let TMP_230 \def (\lambda (c1: C).(let TMP_227 \def (S 
n) in (let TMP_228 \def (Bind Abst) in (let TMP_229 \def (CHead x2 TMP_228 
x3) in (drop h TMP_227 c1 TMP_229))))) in (let TMP_236 \def (\lambda (c1: 
C).(let TMP_231 \def (Bind Abbr) in (let TMP_232 \def (Bind Abbr) in (let 
TMP_233 \def (r TMP_232 n) in (let TMP_234 \def (lift h TMP_233 x1) in (let 
TMP_235 \def (CHead c TMP_231 TMP_234) in (csubc g c1 TMP_235))))))) in (let 
TMP_237 \def (ex2 C TMP_230 TMP_236) in (let TMP_262 \def (\lambda (x: 
C).(\lambda (H19: (drop h n x x2)).(\lambda (H20: (csubc g x c)).(let TMP_241 
\def (\lambda (c1: C).(let TMP_238 \def (S n) in (let TMP_239 \def (Bind 
Abst) in (let TMP_240 \def (CHead x2 TMP_239 x3) in (drop h TMP_238 c1 
TMP_240))))) in (let TMP_247 \def (\lambda (c1: C).(let TMP_242 \def (Bind 
Abbr) in (let TMP_243 \def (Bind Abbr) in (let TMP_244 \def (r TMP_243 n) in 
(let TMP_245 \def (lift h TMP_244 x1) in (let TMP_246 \def (CHead c TMP_242 
TMP_245) in (csubc g c1 TMP_246))))))) in (let TMP_248 \def (Bind Abst) in 
(let TMP_249 \def (lift h n x3) in (let TMP_250 \def (CHead x TMP_248 
TMP_249) in (let TMP_251 \def (drop_skip_bind h n x x2 H19 Abst x3) in (let 
TMP_252 \def (lift h n x3) in (let TMP_253 \def (asucc g x4) in (let TMP_254 
\def (sc3_lift g TMP_253 x2 x3 H14 x h n H19) in (let TMP_255 \def (Bind 
Abbr) in (let TMP_256 \def (r TMP_255 n) in (let TMP_257 \def (lift h TMP_256 
x1) in (let TMP_258 \def (Bind Abbr) in (let TMP_259 \def (r TMP_258 n) in 
(let TMP_260 \def (sc3_lift g x4 x0 x1 H15 c h TMP_259 H17) in (let TMP_261 
\def (csubc_abst g x c H20 TMP_252 x4 TMP_254 TMP_257 TMP_260) in (ex_intro2 
C TMP_241 TMP_247 TMP_250 TMP_251 TMP_261)))))))))))))))))))) in (let TMP_263 
\def (ex2_ind C TMP_225 TMP_226 TMP_237 TMP_262 H18) in (let TMP_264 \def 
(eq_ind_r K TMP_213 TMP_222 TMP_263 k H11) in (eq_ind_r C TMP_195 TMP_202 
TMP_264 e1 H12)))))))))))))))))))))))))))))))) in (ex5_3_ind C T A TMP_179 
TMP_182 TMP_183 TMP_185 TMP_186 TMP_193 TMP_265 H10))))))))))) in (let 
TMP_349 \def (\lambda (H10: (ex4_3 B C T (\lambda (_: B).(\lambda (c1: 
C).(\lambda (v1: T).(eq C e1 (CHead c1 (Bind Void) v1))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c1: C).(\lambda (_: T).(csubc g c1 x0)))))).(let TMP_269 \def 
(\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(let TMP_267 \def (Bind 
Void) in (let TMP_268 \def (CHead c1 TMP_267 v1) in (eq C e1 TMP_268)))))) in 
(let TMP_271 \def (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(let 
TMP_270 \def (Bind b) in (eq K k TMP_270))))) in (let TMP_273 \def (\lambda 
(b: B).(\lambda (_: C).(\lambda (_: T).(let TMP_272 \def (eq B b Void) in 
(not TMP_272))))) in (let TMP_274 \def (\lambda (_: B).(\lambda (c1: 
C).(\lambda (_: T).(csubc g c1 x0)))) in (let TMP_276 \def (\lambda (c1: 
C).(let TMP_275 \def (S n) in (drop h TMP_275 c1 e1))) in (let TMP_280 \def 
(\lambda (c1: C).(let TMP_277 \def (r k n) in (let TMP_278 \def (lift h 
TMP_277 x1) in (let TMP_279 \def (CHead c k TMP_278) in (csubc g c1 
TMP_279))))) in (let TMP_281 \def (ex2 C TMP_276 TMP_280) in (let TMP_348 
\def (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H11: (eq C 
e1 (CHead x3 (Bind Void) x4))).(\lambda (H12: (eq K k (Bind x2))).(\lambda 
(H13: (not (eq B x2 Void))).(\lambda (H14: (csubc g x3 x0)).(let TMP_282 \def 
(Bind Void) in (let TMP_283 \def (CHead x3 TMP_282 x4) in (let TMP_290 \def 
(\lambda (c0: C).(let TMP_285 \def (\lambda (c1: C).(let TMP_284 \def (S n) 
in (drop h TMP_284 c1 c0))) in (let TMP_289 \def (\lambda (c1: C).(let 
TMP_286 \def (r k n) in (let TMP_287 \def (lift h TMP_286 x1) in (let TMP_288 
\def (CHead c k TMP_287) in (csubc g c1 TMP_288))))) in (ex2 C TMP_285 
TMP_289)))) in (let TMP_296 \def (\lambda (k0: K).(\forall (h0: nat).((drop 
h0 n (CHead c k0 (lift h (r k0 n) x1)) (CHead x0 k0 x1)) \to (\forall (e3: 
C).((csubc g e3 (CHead x0 k0 x1)) \to (let TMP_291 \def (\lambda (c1: 
C).(drop h0 n c1 e3)) in (let TMP_295 \def (\lambda (c1: C).(let TMP_292 \def 
(r k0 n) in (let TMP_293 \def (lift h TMP_292 x1) in (let TMP_294 \def (CHead 
c k0 TMP_293) in (csubc g c1 TMP_294))))) in (ex2 C TMP_291 TMP_295)))))))) 
in (let TMP_297 \def (Bind x2) in (let H15 \def (eq_ind K k TMP_296 H8 
TMP_297 H12) in (let TMP_299 \def (\lambda (k0: K).(let TMP_298 \def (r k0 n) 
in (drop h TMP_298 c x0))) in (let TMP_300 \def (Bind x2) in (let H16 \def 
(eq_ind K k TMP_299 H5 TMP_300 H12) in (let TMP_301 \def (Bind x2) in (let 
TMP_310 \def (\lambda (k0: K).(let TMP_305 \def (\lambda (c1: C).(let TMP_302 
\def (S n) in (let TMP_303 \def (Bind Void) in (let TMP_304 \def (CHead x3 
TMP_303 x4) in (drop h TMP_302 c1 TMP_304))))) in (let TMP_309 \def (\lambda 
(c1: C).(let TMP_306 \def (r k0 n) in (let TMP_307 \def (lift h TMP_306 x1) 
in (let TMP_308 \def (CHead c k0 TMP_307) in (csubc g c1 TMP_308))))) in (ex2 
C TMP_305 TMP_309)))) in (let TMP_311 \def (Bind x2) in (let TMP_312 \def (r 
TMP_311 n) in (let H_x0 \def (H x0 TMP_312 h H16 x3 H14) in (let H17 \def 
H_x0 in (let TMP_313 \def (\lambda (c1: C).(drop h n c1 x3)) in (let TMP_314 
\def (\lambda (c1: C).(csubc g c1 c)) in (let TMP_318 \def (\lambda (c1: 
C).(let TMP_315 \def (S n) in (let TMP_316 \def (Bind Void) in (let TMP_317 
\def (CHead x3 TMP_316 x4) in (drop h TMP_315 c1 TMP_317))))) in (let TMP_324 
\def (\lambda (c1: C).(let TMP_319 \def (Bind x2) in (let TMP_320 \def (Bind 
x2) in (let TMP_321 \def (r TMP_320 n) in (let TMP_322 \def (lift h TMP_321 
x1) in (let TMP_323 \def (CHead c TMP_319 TMP_322) in (csubc g c1 
TMP_323))))))) in (let TMP_325 \def (ex2 C TMP_318 TMP_324) in (let TMP_345 
\def (\lambda (x: C).(\lambda (H18: (drop h n x x3)).(\lambda (H19: (csubc g 
x c)).(let TMP_329 \def (\lambda (c1: C).(let TMP_326 \def (S n) in (let 
TMP_327 \def (Bind Void) in (let TMP_328 \def (CHead x3 TMP_327 x4) in (drop 
h TMP_326 c1 TMP_328))))) in (let TMP_335 \def (\lambda (c1: C).(let TMP_330 
\def (Bind x2) in (let TMP_331 \def (Bind x2) in (let TMP_332 \def (r TMP_331 
n) in (let TMP_333 \def (lift h TMP_332 x1) in (let TMP_334 \def (CHead c 
TMP_330 TMP_333) in (csubc g c1 TMP_334))))))) in (let TMP_336 \def (Bind 
Void) in (let TMP_337 \def (lift h n x4) in (let TMP_338 \def (CHead x 
TMP_336 TMP_337) in (let TMP_339 \def (drop_skip_bind h n x x3 H18 Void x4) 
in (let TMP_340 \def (lift h n x4) in (let TMP_341 \def (Bind x2) in (let 
TMP_342 \def (r TMP_341 n) in (let TMP_343 \def (lift h TMP_342 x1) in (let 
TMP_344 \def (csubc_void g x c H19 x2 H13 TMP_340 TMP_343) in (ex_intro2 C 
TMP_329 TMP_335 TMP_338 TMP_339 TMP_344))))))))))))))) in (let TMP_346 \def 
(ex2_ind C TMP_313 TMP_314 TMP_325 TMP_345 H17) in (let TMP_347 \def 
(eq_ind_r K TMP_301 TMP_310 TMP_346 k H12) in (eq_ind_r C TMP_283 TMP_290 
TMP_347 e1 H11))))))))))))))))))))))))))))))) in (ex4_3_ind B C T TMP_269 
TMP_271 TMP_273 TMP_274 TMP_281 TMP_348 H10)))))))))) in (let TMP_350 \def 
(or3_ind TMP_103 TMP_113 TMP_122 TMP_129 TMP_177 TMP_266 TMP_349 H9) in 
(eq_ind_r T TMP_94 TMP_99 TMP_350 t 
H4)))))))))))))))))))))))))))))))))))))))))) in (let TMP_352 \def 
(drop_gen_skip_l c e2 t h n k H1) in (ex3_2_ind C T TMP_69 TMP_72 TMP_74 
TMP_79 TMP_351 TMP_352))))))))))))))) in (nat_ind TMP_34 TMP_67 TMP_353 
d)))))))))) in (C_ind TMP_3 TMP_30 TMP_354 c2))))).

