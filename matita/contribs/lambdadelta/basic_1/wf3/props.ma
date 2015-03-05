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

include "basic_1/wf3/ty3.ma".

include "basic_1/app/defs.ma".

theorem wf3_total:
 \forall (g: G).(\forall (c1: C).(ex C (\lambda (c2: C).(wf3 g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(let TMP_2 \def (\lambda (c: C).(let TMP_1 
\def (\lambda (c2: C).(wf3 g c c2)) in (ex C TMP_1))) in (let TMP_7 \def 
(\lambda (n: nat).(let TMP_4 \def (\lambda (c2: C).(let TMP_3 \def (CSort n) 
in (wf3 g TMP_3 c2))) in (let TMP_5 \def (CSort n) in (let TMP_6 \def 
(wf3_sort g n) in (ex_intro C TMP_4 TMP_5 TMP_6))))) in (let TMP_50 \def 
(\lambda (c: C).(\lambda (H: (ex C (\lambda (c2: C).(wf3 g c c2)))).(\lambda 
(k: K).(\lambda (t: T).(let H0 \def H in (let TMP_8 \def (\lambda (c2: 
C).(wf3 g c c2)) in (let TMP_10 \def (\lambda (c2: C).(let TMP_9 \def (CHead 
c k t) in (wf3 g TMP_9 c2))) in (let TMP_11 \def (ex C TMP_10) in (let TMP_49 
\def (\lambda (x: C).(\lambda (H1: (wf3 g c x)).(let TMP_14 \def (\lambda 
(k0: K).(let TMP_13 \def (\lambda (c2: C).(let TMP_12 \def (CHead c k0 t) in 
(wf3 g TMP_12 c2))) in (ex C TMP_13))) in (let TMP_43 \def (\lambda (b: 
B).(let H_x \def (ty3_inference g c t) in (let H2 \def H_x in (let TMP_15 
\def (\lambda (t2: T).(ty3 g c t t2)) in (let TMP_16 \def (ex T TMP_15) in 
(let TMP_17 \def (\forall (t2: T).((ty3 g c t t2) \to False)) in (let TMP_20 
\def (\lambda (c2: C).(let TMP_18 \def (Bind b) in (let TMP_19 \def (CHead c 
TMP_18 t) in (wf3 g TMP_19 c2)))) in (let TMP_21 \def (ex C TMP_20) in (let 
TMP_34 \def (\lambda (H3: (ex T (\lambda (t2: T).(ty3 g c t t2)))).(let 
TMP_22 \def (\lambda (t2: T).(ty3 g c t t2)) in (let TMP_25 \def (\lambda 
(c2: C).(let TMP_23 \def (Bind b) in (let TMP_24 \def (CHead c TMP_23 t) in 
(wf3 g TMP_24 c2)))) in (let TMP_26 \def (ex C TMP_25) in (let TMP_33 \def 
(\lambda (x0: T).(\lambda (H4: (ty3 g c t x0)).(let TMP_29 \def (\lambda (c2: 
C).(let TMP_27 \def (Bind b) in (let TMP_28 \def (CHead c TMP_27 t) in (wf3 g 
TMP_28 c2)))) in (let TMP_30 \def (Bind b) in (let TMP_31 \def (CHead x 
TMP_30 t) in (let TMP_32 \def (wf3_bind g c x H1 t x0 H4 b) in (ex_intro C 
TMP_29 TMP_31 TMP_32))))))) in (ex_ind T TMP_22 TMP_26 TMP_33 H3)))))) in 
(let TMP_42 \def (\lambda (H3: ((\forall (t2: T).((ty3 g c t t2) \to 
False)))).(let TMP_37 \def (\lambda (c2: C).(let TMP_35 \def (Bind b) in (let 
TMP_36 \def (CHead c TMP_35 t) in (wf3 g TMP_36 c2)))) in (let TMP_38 \def 
(Bind Void) in (let TMP_39 \def (TSort O) in (let TMP_40 \def (CHead x TMP_38 
TMP_39) in (let TMP_41 \def (wf3_void g c x H1 t H3 b) in (ex_intro C TMP_37 
TMP_40 TMP_41))))))) in (or_ind TMP_16 TMP_17 TMP_21 TMP_34 TMP_42 
H2))))))))))) in (let TMP_48 \def (\lambda (f: F).(let TMP_46 \def (\lambda 
(c2: C).(let TMP_44 \def (Flat f) in (let TMP_45 \def (CHead c TMP_44 t) in 
(wf3 g TMP_45 c2)))) in (let TMP_47 \def (wf3_flat g c x H1 t f) in (ex_intro 
C TMP_46 x TMP_47)))) in (K_ind TMP_14 TMP_43 TMP_48 k)))))) in (ex_ind C 
TMP_8 TMP_11 TMP_49 H0)))))))))) in (C_ind TMP_2 TMP_7 TMP_50 c1))))).

theorem ty3_shift1:
 \forall (g: G).(\forall (c: C).((wf3 g c c) \to (\forall (t1: T).(\forall 
(t2: T).((ty3 g c t1 t2) \to (ty3 g (CSort (cbk c)) (app1 c t1) (app1 c 
t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (H: (wf3 g c c)).(let TMP_1 \def 
(\lambda (c0: C).(wf3 g c0 c)) in (let TMP_6 \def (\lambda (c0: C).(\forall 
(t1: T).(\forall (t2: T).((ty3 g c0 t1 t2) \to (let TMP_2 \def (cbk c0) in 
(let TMP_3 \def (CSort TMP_2) in (let TMP_4 \def (app1 c0 t1) in (let TMP_5 
\def (app1 c0 t2) in (ty3 g TMP_3 TMP_4 TMP_5))))))))) in (let TMP_180 \def 
(\lambda (y: C).(\lambda (H0: (wf3 g y c)).(let TMP_11 \def (\lambda (c0: 
C).(\lambda (c1: C).((eq C c0 c1) \to (\forall (t1: T).(\forall (t2: T).((ty3 
g c0 t1 t2) \to (let TMP_7 \def (cbk c0) in (let TMP_8 \def (CSort TMP_7) in 
(let TMP_9 \def (app1 c0 t1) in (let TMP_10 \def (app1 c0 t2) in (ty3 g TMP_8 
TMP_9 TMP_10))))))))))) in (let TMP_12 \def (\lambda (m: nat).(\lambda (_: 
(eq C (CSort m) (CSort m))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H2: 
(ty3 g (CSort m) t1 t2)).H2))))) in (let TMP_46 \def (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: (((eq C c1 c2) 
\to (\forall (t1: T).(\forall (t2: T).((ty3 g c1 t1 t2) \to (ty3 g (CSort 
(cbk c1)) (app1 c1 t1) (app1 c1 t2)))))))).(\lambda (u: T).(\lambda (t: 
T).(\lambda (H3: (ty3 g c1 u t)).(\lambda (b: B).(\lambda (H4: (eq C (CHead 
c1 (Bind b) u) (CHead c2 (Bind b) u))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H5: (ty3 g (CHead c1 (Bind b) u) t1 t2)).(let TMP_13 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) 
\Rightarrow c0])) in (let TMP_14 \def (Bind b) in (let TMP_15 \def (CHead c1 
TMP_14 u) in (let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead c2 TMP_16 
u) in (let H6 \def (f_equal C C TMP_13 TMP_15 TMP_17 H4) in (let TMP_22 \def 
(\lambda (c0: C).((eq C c1 c0) \to (\forall (t3: T).(\forall (t4: T).((ty3 g 
c1 t3 t4) \to (let TMP_18 \def (cbk c1) in (let TMP_19 \def (CSort TMP_18) in 
(let TMP_20 \def (app1 c1 t3) in (let TMP_21 \def (app1 c1 t4) in (ty3 g 
TMP_19 TMP_20 TMP_21)))))))))) in (let H7 \def (eq_ind_r C c2 TMP_22 H2 c1 
H6) in (let TMP_23 \def (\lambda (c0: C).(wf3 g c1 c0)) in (let H8 \def 
(eq_ind_r C c2 TMP_23 H1 c1 H6) in (let TMP_26 \def (\lambda (t0: T).(let 
TMP_24 \def (Bind b) in (let TMP_25 \def (CHead c1 TMP_24 u) in (ty3 g TMP_25 
t2 t0)))) in (let TMP_27 \def (cbk c1) in (let TMP_28 \def (CSort TMP_27) in 
(let TMP_29 \def (Bind b) in (let TMP_30 \def (THead TMP_29 u t1) in (let 
TMP_31 \def (app1 c1 TMP_30) in (let TMP_32 \def (Bind b) in (let TMP_33 \def 
(THead TMP_32 u t2) in (let TMP_34 \def (app1 c1 TMP_33) in (let TMP_35 \def 
(ty3 g TMP_28 TMP_31 TMP_34) in (let TMP_42 \def (\lambda (x: T).(\lambda (_: 
(ty3 g (CHead c1 (Bind b) u) t2 x)).(let TMP_36 \def (refl_equal C c1) in 
(let TMP_37 \def (Bind b) in (let TMP_38 \def (THead TMP_37 u t1) in (let 
TMP_39 \def (Bind b) in (let TMP_40 \def (THead TMP_39 u t2) in (let TMP_41 
\def (ty3_bind g c1 u t H3 b t1 t2 H5) in (H7 TMP_36 TMP_38 TMP_40 
TMP_41))))))))) in (let TMP_43 \def (Bind b) in (let TMP_44 \def (CHead c1 
TMP_43 u) in (let TMP_45 \def (ty3_correct g TMP_44 t1 t2 H5) in (ex_ind T 
TMP_26 TMP_35 TMP_42 TMP_45))))))))))))))))))))))))))))))))))))) in (let 
TMP_139 \def (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 
c2)).(\lambda (H2: (((eq C c1 c2) \to (\forall (t1: T).(\forall (t2: T).((ty3 
g c1 t1 t2) \to (ty3 g (CSort (cbk c1)) (app1 c1 t1) (app1 c1 
t2)))))))).(\lambda (u: T).(\lambda (H3: ((\forall (t: T).((ty3 g c1 u t) \to 
False)))).(\lambda (b: B).(\lambda (H4: (eq C (CHead c1 (Bind b) u) (CHead c2 
(Bind Void) (TSort O)))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H5: (ty3 
g (CHead c1 (Bind b) u) t1 t2)).(let TMP_47 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) in (let 
TMP_48 \def (Bind b) in (let TMP_49 \def (CHead c1 TMP_48 u) in (let TMP_50 
\def (Bind Void) in (let TMP_51 \def (TSort O) in (let TMP_52 \def (CHead c2 
TMP_50 TMP_51) in (let H6 \def (f_equal C C TMP_47 TMP_49 TMP_52 H4) in (let 
TMP_53 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow b | (CHead _ 
k _) \Rightarrow (match k with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow b])])) in (let TMP_54 \def (Bind b) in (let TMP_55 \def (CHead c1 
TMP_54 u) in (let TMP_56 \def (Bind Void) in (let TMP_57 \def (TSort O) in 
(let TMP_58 \def (CHead c2 TMP_56 TMP_57) in (let H7 \def (f_equal C B TMP_53 
TMP_55 TMP_58 H4) in (let TMP_59 \def (\lambda (e: C).(match e with [(CSort 
_) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) in (let TMP_60 \def (Bind 
b) in (let TMP_61 \def (CHead c1 TMP_60 u) in (let TMP_62 \def (Bind Void) in 
(let TMP_63 \def (TSort O) in (let TMP_64 \def (CHead c2 TMP_62 TMP_63) in 
(let H8 \def (f_equal C T TMP_59 TMP_61 TMP_64 H4) in (let TMP_137 \def 
(\lambda (H9: (eq B b Void)).(\lambda (H10: (eq C c1 c2)).(let TMP_67 \def 
(\lambda (b0: B).(let TMP_65 \def (Bind b0) in (let TMP_66 \def (CHead c1 
TMP_65 u) in (ty3 g TMP_66 t1 t2)))) in (let H11 \def (eq_ind B b TMP_67 H5 
Void H9) in (let TMP_78 \def (\lambda (b0: B).(let TMP_68 \def (Bind b0) in 
(let TMP_69 \def (CHead c1 TMP_68 u) in (let TMP_70 \def (cbk TMP_69) in (let 
TMP_71 \def (CSort TMP_70) in (let TMP_72 \def (Bind b0) in (let TMP_73 \def 
(CHead c1 TMP_72 u) in (let TMP_74 \def (app1 TMP_73 t1) in (let TMP_75 \def 
(Bind b0) in (let TMP_76 \def (CHead c1 TMP_75 u) in (let TMP_77 \def (app1 
TMP_76 t2) in (ty3 g TMP_71 TMP_74 TMP_77)))))))))))) in (let TMP_81 \def 
(\lambda (t: T).(let TMP_79 \def (Bind Void) in (let TMP_80 \def (CHead c1 
TMP_79 t) in (ty3 g TMP_80 t1 t2)))) in (let TMP_82 \def (TSort O) in (let 
H12 \def (eq_ind T u TMP_81 H11 TMP_82 H8) in (let TMP_83 \def (\lambda (t: 
T).(\forall (t0: T).((ty3 g c1 t t0) \to False))) in (let TMP_84 \def (TSort 
O) in (let H13 \def (eq_ind T u TMP_83 H3 TMP_84 H8) in (let TMP_85 \def 
(TSort O) in (let TMP_96 \def (\lambda (t: T).(let TMP_86 \def (Bind Void) in 
(let TMP_87 \def (CHead c1 TMP_86 t) in (let TMP_88 \def (cbk TMP_87) in (let 
TMP_89 \def (CSort TMP_88) in (let TMP_90 \def (Bind Void) in (let TMP_91 
\def (CHead c1 TMP_90 t) in (let TMP_92 \def (app1 TMP_91 t1) in (let TMP_93 
\def (Bind Void) in (let TMP_94 \def (CHead c1 TMP_93 t) in (let TMP_95 \def 
(app1 TMP_94 t2) in (ty3 g TMP_89 TMP_92 TMP_95)))))))))))) in (let TMP_101 
\def (\lambda (c0: C).((eq C c1 c0) \to (\forall (t3: T).(\forall (t4: 
T).((ty3 g c1 t3 t4) \to (let TMP_97 \def (cbk c1) in (let TMP_98 \def (CSort 
TMP_97) in (let TMP_99 \def (app1 c1 t3) in (let TMP_100 \def (app1 c1 t4) in 
(ty3 g TMP_98 TMP_99 TMP_100)))))))))) in (let H14 \def (eq_ind_r C c2 
TMP_101 H2 c1 H10) in (let TMP_102 \def (\lambda (c0: C).(wf3 g c1 c0)) in 
(let H15 \def (eq_ind_r C c2 TMP_102 H1 c1 H10) in (let TMP_106 \def (\lambda 
(t: T).(let TMP_103 \def (Bind Void) in (let TMP_104 \def (TSort O) in (let 
TMP_105 \def (CHead c1 TMP_103 TMP_104) in (ty3 g TMP_105 t2 t))))) in (let 
TMP_107 \def (cbk c1) in (let TMP_108 \def (CSort TMP_107) in (let TMP_109 
\def (Bind Void) in (let TMP_110 \def (TSort O) in (let TMP_111 \def (THead 
TMP_109 TMP_110 t1) in (let TMP_112 \def (app1 c1 TMP_111) in (let TMP_113 
\def (Bind Void) in (let TMP_114 \def (TSort O) in (let TMP_115 \def (THead 
TMP_113 TMP_114 t2) in (let TMP_116 \def (app1 c1 TMP_115) in (let TMP_117 
\def (ty3 g TMP_108 TMP_112 TMP_116) in (let TMP_130 \def (\lambda (x: 
T).(\lambda (_: (ty3 g (CHead c1 (Bind Void) (TSort O)) t2 x)).(let TMP_118 
\def (refl_equal C c1) in (let TMP_119 \def (Bind Void) in (let TMP_120 \def 
(TSort O) in (let TMP_121 \def (THead TMP_119 TMP_120 t1) in (let TMP_122 
\def (Bind Void) in (let TMP_123 \def (TSort O) in (let TMP_124 \def (THead 
TMP_122 TMP_123 t2) in (let TMP_125 \def (TSort O) in (let TMP_126 \def (next 
g O) in (let TMP_127 \def (TSort TMP_126) in (let TMP_128 \def (ty3_sort g c1 
O) in (let TMP_129 \def (ty3_bind g c1 TMP_125 TMP_127 TMP_128 Void t1 t2 
H12) in (H14 TMP_118 TMP_121 TMP_124 TMP_129))))))))))))))) in (let TMP_131 
\def (Bind Void) in (let TMP_132 \def (TSort O) in (let TMP_133 \def (CHead 
c1 TMP_131 TMP_132) in (let TMP_134 \def (ty3_correct g TMP_133 t1 t2 H12) in 
(let TMP_135 \def (ex_ind T TMP_106 TMP_117 TMP_130 TMP_134) in (let TMP_136 
\def (eq_ind_r T TMP_85 TMP_96 TMP_135 u H8) in (eq_ind_r B Void TMP_78 
TMP_136 b H9))))))))))))))))))))))))))))))))))))) in (let TMP_138 \def 
(TMP_137 H7) in (TMP_138 H6))))))))))))))))))))))))))))))))))) in (let 
TMP_179 \def (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 
c2)).(\lambda (H2: (((eq C c1 c2) \to (\forall (t1: T).(\forall (t2: T).((ty3 
g c1 t1 t2) \to (ty3 g (CSort (cbk c1)) (app1 c1 t1) (app1 c1 
t2)))))))).(\lambda (u: T).(\lambda (f: F).(\lambda (H3: (eq C (CHead c1 
(Flat f) u) c2)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead 
c1 (Flat f) u) t1 t2)).(let TMP_140 \def (\lambda (e: C).e) in (let TMP_141 
\def (Flat f) in (let TMP_142 \def (CHead c1 TMP_141 u) in (let H5 \def 
(f_equal C C TMP_140 TMP_142 c2 H3) in (let TMP_147 \def (\lambda (c0: 
C).((eq C c1 c0) \to (\forall (t3: T).(\forall (t4: T).((ty3 g c1 t3 t4) \to 
(let TMP_143 \def (cbk c1) in (let TMP_144 \def (CSort TMP_143) in (let 
TMP_145 \def (app1 c1 t3) in (let TMP_146 \def (app1 c1 t4) in (ty3 g TMP_144 
TMP_145 TMP_146)))))))))) in (let TMP_148 \def (Flat f) in (let TMP_149 \def 
(CHead c1 TMP_148 u) in (let H6 \def (eq_ind_r C c2 TMP_147 H2 TMP_149 H5) in 
(let TMP_150 \def (\lambda (c0: C).(wf3 g c1 c0)) in (let TMP_151 \def (Flat 
f) in (let TMP_152 \def (CHead c1 TMP_151 u) in (let H7 \def (eq_ind_r C c2 
TMP_150 H1 TMP_152 H5) in (let TMP_153 \def (Flat f) in (let H_x \def 
(wf3_gen_head2 g c1 c1 u TMP_153 H7) in (let H8 \def H_x in (let TMP_156 \def 
(\lambda (b: B).(let TMP_154 \def (Flat f) in (let TMP_155 \def (Bind b) in 
(eq K TMP_154 TMP_155)))) in (let TMP_157 \def (cbk c1) in (let TMP_158 \def 
(CSort TMP_157) in (let TMP_159 \def (Flat f) in (let TMP_160 \def (THead 
TMP_159 u t1) in (let TMP_161 \def (app1 c1 TMP_160) in (let TMP_162 \def 
(Flat f) in (let TMP_163 \def (THead TMP_162 u t2) in (let TMP_164 \def (app1 
c1 TMP_163) in (let TMP_165 \def (ty3 g TMP_158 TMP_161 TMP_164) in (let 
TMP_178 \def (\lambda (x: B).(\lambda (H9: (eq K (Flat f) (Bind x))).(let 
TMP_166 \def (Flat f) in (let TMP_167 \def (\lambda (ee: K).(match ee with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])) in (let TMP_168 
\def (Bind x) in (let H10 \def (eq_ind K TMP_166 TMP_167 I TMP_168 H9) in 
(let TMP_169 \def (cbk c1) in (let TMP_170 \def (CSort TMP_169) in (let 
TMP_171 \def (Flat f) in (let TMP_172 \def (THead TMP_171 u t1) in (let 
TMP_173 \def (app1 c1 TMP_172) in (let TMP_174 \def (Flat f) in (let TMP_175 
\def (THead TMP_174 u t2) in (let TMP_176 \def (app1 c1 TMP_175) in (let 
TMP_177 \def (ty3 g TMP_170 TMP_173 TMP_176) in (False_ind TMP_177 
H10)))))))))))))))) in (ex_ind B TMP_156 TMP_165 TMP_178 
H8))))))))))))))))))))))))))))))))))))) in (wf3_ind g TMP_11 TMP_12 TMP_46 
TMP_139 TMP_179 y c H0)))))))) in (insert_eq C c TMP_1 TMP_6 TMP_180 H)))))).

theorem wf3_idem:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to (wf3 g 
c2 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wf3 g c1 
c2)).(let TMP_1 \def (\lambda (_: C).(\lambda (c0: C).(wf3 g c0 c0))) in (let 
TMP_2 \def (\lambda (m: nat).(wf3_sort g m)) in (let TMP_4 \def (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (wf3 g c3 c4)).(\lambda (H1: (wf3 g c4 
c4)).(\lambda (u: T).(\lambda (t: T).(\lambda (H2: (ty3 g c3 u t)).(\lambda 
(b: B).(let TMP_3 \def (wf3_ty3_conf g c3 u t H2 c4 H0) in (wf3_bind g c4 c4 
H1 u t TMP_3 b)))))))))) in (let TMP_9 \def (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (wf3 g c3 c4)).(\lambda (H1: (wf3 g c4 c4)).(\lambda (u: 
T).(\lambda (_: ((\forall (t: T).((ty3 g c3 u t) \to False)))).(\lambda (_: 
B).(let TMP_5 \def (TSort O) in (let TMP_6 \def (next g O) in (let TMP_7 \def 
(TSort TMP_6) in (let TMP_8 \def (ty3_sort g c4 O) in (wf3_bind g c4 c4 H1 
TMP_5 TMP_7 TMP_8 Void)))))))))))) in (let TMP_10 \def (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (_: (wf3 g c3 c4)).(\lambda (H1: (wf3 g c4 
c4)).(\lambda (_: T).(\lambda (_: F).H1)))))) in (wf3_ind g TMP_1 TMP_2 TMP_4 
TMP_9 TMP_10 c1 c2 H))))))))).

theorem wf3_ty3:
 \forall (g: G).(\forall (c1: C).(\forall (t: T).(\forall (u: T).((ty3 g c1 t 
u) \to (ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(ty3 g c2 t 
u)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c1 t u)).(let H_x \def (wf3_total g c1) in (let H0 \def H_x in (let 
TMP_1 \def (\lambda (c2: C).(wf3 g c1 c2)) in (let TMP_2 \def (\lambda (c2: 
C).(wf3 g c1 c2)) in (let TMP_3 \def (\lambda (c2: C).(ty3 g c2 t u)) in (let 
TMP_4 \def (ex2 C TMP_2 TMP_3) in (let TMP_8 \def (\lambda (x: C).(\lambda 
(H1: (wf3 g c1 x)).(let TMP_5 \def (\lambda (c2: C).(wf3 g c1 c2)) in (let 
TMP_6 \def (\lambda (c2: C).(ty3 g c2 t u)) in (let TMP_7 \def (wf3_ty3_conf 
g c1 t u H x H1) in (ex_intro2 C TMP_5 TMP_6 x H1 TMP_7)))))) in (ex_ind C 
TMP_1 TMP_4 TMP_8 H0)))))))))))).

