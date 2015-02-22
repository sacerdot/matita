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

include "basic_1/leq/props.ma".

theorem asucc_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
(asucc g a1) (asucc g a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(let TMP_3 \def (\lambda (a: A).(\lambda (a0: A).(let TMP_1 \def (asucc 
g a) in (let TMP_2 \def (asucc g a0) in (leq g TMP_1 TMP_2))))) in (let 
TMP_186 \def (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(let TMP_8 \def (\lambda (n: nat).((eq 
A (aplus g (ASort n n1) k) (aplus g (ASort h2 n2) k)) \to (let TMP_5 \def 
(match n with [O \Rightarrow (let TMP_4 \def (next g n1) in (ASort O TMP_4)) 
| (S h) \Rightarrow (ASort h n1)]) in (let TMP_7 \def (match h2 with [O 
\Rightarrow (let TMP_6 \def (next g n2) in (ASort O TMP_6)) | (S h) 
\Rightarrow (ASort h n2)]) in (leq g TMP_5 TMP_7))))) in (let TMP_97 \def 
(\lambda (H1: (eq A (aplus g (ASort O n1) k) (aplus g (ASort h2 n2) k))).(let 
TMP_13 \def (\lambda (n: nat).((eq A (aplus g (ASort O n1) k) (aplus g (ASort 
n n2) k)) \to (let TMP_9 \def (next g n1) in (let TMP_10 \def (ASort O TMP_9) 
in (let TMP_12 \def (match n with [O \Rightarrow (let TMP_11 \def (next g n2) 
in (ASort O TMP_11)) | (S h) \Rightarrow (ASort h n2)]) in (leq g TMP_10 
TMP_12)))))) in (let TMP_54 \def (\lambda (H2: (eq A (aplus g (ASort O n1) k) 
(aplus g (ASort O n2) k))).(let TMP_14 \def (next g n1) in (let TMP_15 \def 
(next g n2) in (let TMP_16 \def (ASort O n1) in (let TMP_17 \def (S k) in 
(let TMP_18 \def (aplus g TMP_16 TMP_17) in (let TMP_22 \def (\lambda (a: 
A).(let TMP_19 \def (next g n2) in (let TMP_20 \def (ASort O TMP_19) in (let 
TMP_21 \def (aplus g TMP_20 k) in (eq A a TMP_21))))) in (let TMP_23 \def 
(ASort O n2) in (let TMP_24 \def (S k) in (let TMP_25 \def (aplus g TMP_23 
TMP_24) in (let TMP_29 \def (\lambda (a: A).(let TMP_26 \def (ASort O n1) in 
(let TMP_27 \def (S k) in (let TMP_28 \def (aplus g TMP_26 TMP_27) in (eq A 
TMP_28 a))))) in (let TMP_30 \def (ASort O n2) in (let TMP_31 \def (aplus g 
TMP_30 k) in (let TMP_36 \def (\lambda (a: A).(let TMP_32 \def (asucc g a) in 
(let TMP_33 \def (ASort O n2) in (let TMP_34 \def (aplus g TMP_33 k) in (let 
TMP_35 \def (asucc g TMP_34) in (eq A TMP_32 TMP_35)))))) in (let TMP_37 \def 
(ASort O n2) in (let TMP_38 \def (aplus g TMP_37 k) in (let TMP_39 \def 
(asucc g TMP_38) in (let TMP_40 \def (refl_equal A TMP_39) in (let TMP_41 
\def (ASort O n1) in (let TMP_42 \def (aplus g TMP_41 k) in (let TMP_43 \def 
(eq_ind_r A TMP_31 TMP_36 TMP_40 TMP_42 H2) in (let TMP_44 \def (next g n2) 
in (let TMP_45 \def (ASort O TMP_44) in (let TMP_46 \def (aplus g TMP_45 k) 
in (let TMP_47 \def (aplus_sort_O_S_simpl g n2 k) in (let TMP_48 \def (eq_ind 
A TMP_25 TMP_29 TMP_43 TMP_46 TMP_47) in (let TMP_49 \def (next g n1) in (let 
TMP_50 \def (ASort O TMP_49) in (let TMP_51 \def (aplus g TMP_50 k) in (let 
TMP_52 \def (aplus_sort_O_S_simpl g n1 k) in (let TMP_53 \def (eq_ind A 
TMP_18 TMP_22 TMP_48 TMP_51 TMP_52) in (leq_sort g O O TMP_14 TMP_15 k 
TMP_53)))))))))))))))))))))))))))))))) in (let TMP_96 \def (\lambda (h3: 
nat).(\lambda (_: (((eq A (aplus g (ASort O n1) k) (aplus g (ASort h3 n2) k)) 
\to (leq g (ASort O (next g n1)) (match h3 with [O \Rightarrow (ASort O (next 
g n2)) | (S h) \Rightarrow (ASort h n2)]))))).(\lambda (H2: (eq A (aplus g 
(ASort O n1) k) (aplus g (ASort (S h3) n2) k))).(let TMP_55 \def (next g n1) 
in (let TMP_56 \def (ASort O n1) in (let TMP_57 \def (S k) in (let TMP_58 
\def (aplus g TMP_56 TMP_57) in (let TMP_61 \def (\lambda (a: A).(let TMP_59 
\def (ASort h3 n2) in (let TMP_60 \def (aplus g TMP_59 k) in (eq A a 
TMP_60)))) in (let TMP_62 \def (S h3) in (let TMP_63 \def (ASort TMP_62 n2) 
in (let TMP_64 \def (S k) in (let TMP_65 \def (aplus g TMP_63 TMP_64) in (let 
TMP_69 \def (\lambda (a: A).(let TMP_66 \def (ASort O n1) in (let TMP_67 \def 
(S k) in (let TMP_68 \def (aplus g TMP_66 TMP_67) in (eq A TMP_68 a))))) in 
(let TMP_70 \def (S h3) in (let TMP_71 \def (ASort TMP_70 n2) in (let TMP_72 
\def (aplus g TMP_71 k) in (let TMP_78 \def (\lambda (a: A).(let TMP_73 \def 
(asucc g a) in (let TMP_74 \def (S h3) in (let TMP_75 \def (ASort TMP_74 n2) 
in (let TMP_76 \def (aplus g TMP_75 k) in (let TMP_77 \def (asucc g TMP_76) 
in (eq A TMP_73 TMP_77))))))) in (let TMP_79 \def (S h3) in (let TMP_80 \def 
(ASort TMP_79 n2) in (let TMP_81 \def (aplus g TMP_80 k) in (let TMP_82 \def 
(asucc g TMP_81) in (let TMP_83 \def (refl_equal A TMP_82) in (let TMP_84 
\def (ASort O n1) in (let TMP_85 \def (aplus g TMP_84 k) in (let TMP_86 \def 
(eq_ind_r A TMP_72 TMP_78 TMP_83 TMP_85 H2) in (let TMP_87 \def (ASort h3 n2) 
in (let TMP_88 \def (aplus g TMP_87 k) in (let TMP_89 \def 
(aplus_sort_S_S_simpl g n2 h3 k) in (let TMP_90 \def (eq_ind A TMP_65 TMP_69 
TMP_86 TMP_88 TMP_89) in (let TMP_91 \def (next g n1) in (let TMP_92 \def 
(ASort O TMP_91) in (let TMP_93 \def (aplus g TMP_92 k) in (let TMP_94 \def 
(aplus_sort_O_S_simpl g n1 k) in (let TMP_95 \def (eq_ind A TMP_58 TMP_61 
TMP_90 TMP_93 TMP_94) in (leq_sort g O h3 TMP_55 n2 k 
TMP_95))))))))))))))))))))))))))))))))))) in (nat_ind TMP_13 TMP_54 TMP_96 h2 
H1))))) in (let TMP_185 \def (\lambda (h3: nat).(\lambda (IHh1: (((eq A 
(aplus g (ASort h3 n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (match h3 
with [O \Rightarrow (ASort O (next g n1)) | (S h) \Rightarrow (ASort h n1)]) 
(match h2 with [O \Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow 
(ASort h n2)]))))).(\lambda (H1: (eq A (aplus g (ASort (S h3) n1) k) (aplus g 
(ASort h2 n2) k))).(let TMP_101 \def (\lambda (n: nat).((eq A (aplus g (ASort 
(S h3) n1) k) (aplus g (ASort n n2) k)) \to ((((eq A (aplus g (ASort h3 n1) 
k) (aplus g (ASort n n2) k)) \to (leq g (match h3 with [O \Rightarrow (ASort 
O (next g n1)) | (S h) \Rightarrow (ASort h n1)]) (match n with [O 
\Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow (ASort h n2)])))) \to 
(let TMP_98 \def (ASort h3 n1) in (let TMP_100 \def (match n with [O 
\Rightarrow (let TMP_99 \def (next g n2) in (ASort O TMP_99)) | (S h) 
\Rightarrow (ASort h n2)]) in (leq g TMP_98 TMP_100)))))) in (let TMP_141 
\def (\lambda (H2: (eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort O n2) 
k))).(\lambda (_: (((eq A (aplus g (ASort h3 n1) k) (aplus g (ASort O n2) k)) 
\to (leq g (match h3 with [O \Rightarrow (ASort O (next g n1)) | (S h) 
\Rightarrow (ASort h n1)]) (ASort O (next g n2)))))).(let TMP_102 \def (next 
g n2) in (let TMP_103 \def (ASort O n2) in (let TMP_104 \def (S k) in (let 
TMP_105 \def (aplus g TMP_103 TMP_104) in (let TMP_108 \def (\lambda (a: 
A).(let TMP_106 \def (ASort h3 n1) in (let TMP_107 \def (aplus g TMP_106 k) 
in (eq A TMP_107 a)))) in (let TMP_109 \def (S h3) in (let TMP_110 \def 
(ASort TMP_109 n1) in (let TMP_111 \def (S k) in (let TMP_112 \def (aplus g 
TMP_110 TMP_111) in (let TMP_116 \def (\lambda (a: A).(let TMP_113 \def 
(ASort O n2) in (let TMP_114 \def (S k) in (let TMP_115 \def (aplus g TMP_113 
TMP_114) in (eq A a TMP_115))))) in (let TMP_117 \def (ASort O n2) in (let 
TMP_118 \def (aplus g TMP_117 k) in (let TMP_123 \def (\lambda (a: A).(let 
TMP_119 \def (asucc g a) in (let TMP_120 \def (ASort O n2) in (let TMP_121 
\def (aplus g TMP_120 k) in (let TMP_122 \def (asucc g TMP_121) in (eq A 
TMP_119 TMP_122)))))) in (let TMP_124 \def (ASort O n2) in (let TMP_125 \def 
(aplus g TMP_124 k) in (let TMP_126 \def (asucc g TMP_125) in (let TMP_127 
\def (refl_equal A TMP_126) in (let TMP_128 \def (S h3) in (let TMP_129 \def 
(ASort TMP_128 n1) in (let TMP_130 \def (aplus g TMP_129 k) in (let TMP_131 
\def (eq_ind_r A TMP_118 TMP_123 TMP_127 TMP_130 H2) in (let TMP_132 \def 
(ASort h3 n1) in (let TMP_133 \def (aplus g TMP_132 k) in (let TMP_134 \def 
(aplus_sort_S_S_simpl g n1 h3 k) in (let TMP_135 \def (eq_ind A TMP_112 
TMP_116 TMP_131 TMP_133 TMP_134) in (let TMP_136 \def (next g n2) in (let 
TMP_137 \def (ASort O TMP_136) in (let TMP_138 \def (aplus g TMP_137 k) in 
(let TMP_139 \def (aplus_sort_O_S_simpl g n2 k) in (let TMP_140 \def (eq_ind 
A TMP_105 TMP_108 TMP_135 TMP_138 TMP_139) in (leq_sort g h3 O n1 TMP_102 k 
TMP_140))))))))))))))))))))))))))))))))) in (let TMP_184 \def (\lambda (h4: 
nat).(\lambda (_: (((eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort h4 
n2) k)) \to ((((eq A (aplus g (ASort h3 n1) k) (aplus g (ASort h4 n2) k)) \to 
(leq g (match h3 with [O \Rightarrow (ASort O (next g n1)) | (S h) 
\Rightarrow (ASort h n1)]) (match h4 with [O \Rightarrow (ASort O (next g 
n2)) | (S h) \Rightarrow (ASort h n2)])))) \to (leq g (ASort h3 n1) (match h4 
with [O \Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow (ASort h 
n2)])))))).(\lambda (H2: (eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort 
(S h4) n2) k))).(\lambda (_: (((eq A (aplus g (ASort h3 n1) k) (aplus g 
(ASort (S h4) n2) k)) \to (leq g (match h3 with [O \Rightarrow (ASort O (next 
g n1)) | (S h) \Rightarrow (ASort h n1)]) (ASort h4 n2))))).(let TMP_142 \def 
(S h3) in (let TMP_143 \def (ASort TMP_142 n1) in (let TMP_144 \def (S k) in 
(let TMP_145 \def (aplus g TMP_143 TMP_144) in (let TMP_148 \def (\lambda (a: 
A).(let TMP_146 \def (ASort h4 n2) in (let TMP_147 \def (aplus g TMP_146 k) 
in (eq A a TMP_147)))) in (let TMP_149 \def (S h4) in (let TMP_150 \def 
(ASort TMP_149 n2) in (let TMP_151 \def (S k) in (let TMP_152 \def (aplus g 
TMP_150 TMP_151) in (let TMP_157 \def (\lambda (a: A).(let TMP_153 \def (S 
h3) in (let TMP_154 \def (ASort TMP_153 n1) in (let TMP_155 \def (S k) in 
(let TMP_156 \def (aplus g TMP_154 TMP_155) in (eq A TMP_156 a)))))) in (let 
TMP_158 \def (S h4) in (let TMP_159 \def (ASort TMP_158 n2) in (let TMP_160 
\def (aplus g TMP_159 k) in (let TMP_166 \def (\lambda (a: A).(let TMP_161 
\def (asucc g a) in (let TMP_162 \def (S h4) in (let TMP_163 \def (ASort 
TMP_162 n2) in (let TMP_164 \def (aplus g TMP_163 k) in (let TMP_165 \def 
(asucc g TMP_164) in (eq A TMP_161 TMP_165))))))) in (let TMP_167 \def (S h4) 
in (let TMP_168 \def (ASort TMP_167 n2) in (let TMP_169 \def (aplus g TMP_168 
k) in (let TMP_170 \def (asucc g TMP_169) in (let TMP_171 \def (refl_equal A 
TMP_170) in (let TMP_172 \def (S h3) in (let TMP_173 \def (ASort TMP_172 n1) 
in (let TMP_174 \def (aplus g TMP_173 k) in (let TMP_175 \def (eq_ind_r A 
TMP_160 TMP_166 TMP_171 TMP_174 H2) in (let TMP_176 \def (ASort h4 n2) in 
(let TMP_177 \def (aplus g TMP_176 k) in (let TMP_178 \def 
(aplus_sort_S_S_simpl g n2 h4 k) in (let TMP_179 \def (eq_ind A TMP_152 
TMP_157 TMP_175 TMP_177 TMP_178) in (let TMP_180 \def (ASort h3 n1) in (let 
TMP_181 \def (aplus g TMP_180 k) in (let TMP_182 \def (aplus_sort_S_S_simpl g 
n1 h3 k) in (let TMP_183 \def (eq_ind A TMP_145 TMP_148 TMP_179 TMP_181 
TMP_182) in (leq_sort g h3 h4 n1 n2 k 
TMP_183)))))))))))))))))))))))))))))))))))) in (nat_ind TMP_101 TMP_141 
TMP_184 h2 H1 IHh1))))))) in (nat_ind TMP_8 TMP_97 TMP_185 h1 H0)))))))))) in 
(let TMP_189 \def (\lambda (a3: A).(\lambda (a4: A).(\lambda (H0: (leq g a3 
a4)).(\lambda (_: (leq g (asucc g a3) (asucc g a4))).(\lambda (a5: 
A).(\lambda (a6: A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: (leq g (asucc g 
a5) (asucc g a6))).(let TMP_187 \def (asucc g a5) in (let TMP_188 \def (asucc 
g a6) in (leq_head g a3 a4 H0 TMP_187 TMP_188 H3))))))))))) in (leq_ind g 
TMP_3 TMP_186 TMP_189 a1 a2 H))))))).

theorem asucc_inj:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (asucc g a1) (asucc 
g a2)) \to (leq g a1 a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(let TMP_1 \def (\lambda (a: A).(\forall 
(a2: A).((leq g (asucc g a) (asucc g a2)) \to (leq g a a2)))) in (let TMP_315 
\def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (a2: A).(let TMP_3 \def 
(\lambda (a: A).((leq g (asucc g (ASort n n0)) (asucc g a)) \to (let TMP_2 
\def (ASort n n0) in (leq g TMP_2 a)))) in (let TMP_260 \def (\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (H: (leq g (asucc g (ASort n n0)) (asucc g 
(ASort n1 n2)))).(let TMP_6 \def (\lambda (n3: nat).((leq g (asucc g (ASort 
n3 n0)) (asucc g (ASort n1 n2))) \to (let TMP_4 \def (ASort n3 n0) in (let 
TMP_5 \def (ASort n1 n2) in (leq g TMP_4 TMP_5))))) in (let TMP_133 \def 
(\lambda (H0: (leq g (asucc g (ASort O n0)) (asucc g (ASort n1 n2)))).(let 
TMP_9 \def (\lambda (n3: nat).((leq g (asucc g (ASort O n0)) (asucc g (ASort 
n3 n2))) \to (let TMP_7 \def (ASort O n0) in (let TMP_8 \def (ASort n3 n2) in 
(leq g TMP_7 TMP_8))))) in (let TMP_73 \def (\lambda (H1: (leq g (asucc g 
(ASort O n0)) (asucc g (ASort O n2)))).(let TMP_10 \def (next g n0) in (let 
TMP_11 \def (next g n2) in (let TMP_12 \def (ASort O TMP_11) in (let H_x \def 
(leq_gen_sort1 g O TMP_10 TMP_12 H1) in (let H2 \def H_x in (let TMP_18 \def 
(\lambda (n3: nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_13 \def 
(next g n0) in (let TMP_14 \def (ASort O TMP_13) in (let TMP_15 \def (aplus g 
TMP_14 k) in (let TMP_16 \def (ASort h2 n3) in (let TMP_17 \def (aplus g 
TMP_16 k) in (eq A TMP_15 TMP_17))))))))) in (let TMP_22 \def (\lambda (n3: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_19 \def (next g n2) in 
(let TMP_20 \def (ASort O TMP_19) in (let TMP_21 \def (ASort h2 n3) in (eq A 
TMP_20 TMP_21))))))) in (let TMP_23 \def (ASort O n0) in (let TMP_24 \def 
(ASort O n2) in (let TMP_25 \def (leq g TMP_23 TMP_24) in (let TMP_72 \def 
(\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H3: (eq A 
(aplus g (ASort O (next g n0)) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H4: 
(eq A (ASort O (next g n2)) (ASort x1 x0))).(let TMP_26 \def (\lambda (e: 
A).(match e with [(ASort n3 _) \Rightarrow n3 | (AHead _ _) \Rightarrow O])) 
in (let TMP_27 \def (next g n2) in (let TMP_28 \def (ASort O TMP_27) in (let 
TMP_29 \def (ASort x1 x0) in (let H5 \def (f_equal A nat TMP_26 TMP_28 TMP_29 
H4) in (let TMP_31 \def (\lambda (e: A).(match e with [(ASort _ n3) 
\Rightarrow n3 | (AHead _ _) \Rightarrow (let TMP_30 \def (match g with 
[(mk_G next _) \Rightarrow next]) in (TMP_30 n2))])) in (let TMP_32 \def 
(next g n2) in (let TMP_33 \def (ASort O TMP_32) in (let TMP_34 \def (ASort 
x1 x0) in (let H6 \def (f_equal A nat TMP_31 TMP_33 TMP_34 H4) in (let TMP_71 
\def (\lambda (H7: (eq nat O x1)).(let TMP_40 \def (\lambda (n3: nat).(let 
TMP_35 \def (next g n0) in (let TMP_36 \def (ASort O TMP_35) in (let TMP_37 
\def (aplus g TMP_36 x2) in (let TMP_38 \def (ASort n3 x0) in (let TMP_39 
\def (aplus g TMP_38 x2) in (eq A TMP_37 TMP_39))))))) in (let H8 \def 
(eq_ind_r nat x1 TMP_40 H3 O H7) in (let TMP_46 \def (\lambda (n3: nat).(let 
TMP_41 \def (next g n0) in (let TMP_42 \def (ASort O TMP_41) in (let TMP_43 
\def (aplus g TMP_42 x2) in (let TMP_44 \def (ASort O n3) in (let TMP_45 \def 
(aplus g TMP_44 x2) in (eq A TMP_43 TMP_45))))))) in (let TMP_47 \def (next g 
n2) in (let H9 \def (eq_ind_r nat x0 TMP_46 H8 TMP_47 H6) in (let TMP_48 \def 
(next g n0) in (let TMP_49 \def (ASort O TMP_48) in (let TMP_50 \def (aplus g 
TMP_49 x2) in (let TMP_54 \def (\lambda (a: A).(let TMP_51 \def (next g n2) 
in (let TMP_52 \def (ASort O TMP_51) in (let TMP_53 \def (aplus g TMP_52 x2) 
in (eq A a TMP_53))))) in (let TMP_55 \def (ASort O n0) in (let TMP_56 \def 
(S x2) in (let TMP_57 \def (aplus g TMP_55 TMP_56) in (let TMP_58 \def 
(aplus_sort_O_S_simpl g n0 x2) in (let H10 \def (eq_ind_r A TMP_50 TMP_54 H9 
TMP_57 TMP_58) in (let TMP_59 \def (next g n2) in (let TMP_60 \def (ASort O 
TMP_59) in (let TMP_61 \def (aplus g TMP_60 x2) in (let TMP_65 \def (\lambda 
(a: A).(let TMP_62 \def (ASort O n0) in (let TMP_63 \def (S x2) in (let 
TMP_64 \def (aplus g TMP_62 TMP_63) in (eq A TMP_64 a))))) in (let TMP_66 
\def (ASort O n2) in (let TMP_67 \def (S x2) in (let TMP_68 \def (aplus g 
TMP_66 TMP_67) in (let TMP_69 \def (aplus_sort_O_S_simpl g n2 x2) in (let H11 
\def (eq_ind_r A TMP_61 TMP_65 H10 TMP_68 TMP_69) in (let TMP_70 \def (S x2) 
in (leq_sort g O O n0 n2 TMP_70 H11)))))))))))))))))))))))))) in (TMP_71 
H5))))))))))))))))) in (ex2_3_ind nat nat nat TMP_18 TMP_22 TMP_25 TMP_72 
H2))))))))))))) in (let TMP_132 \def (\lambda (n3: nat).(\lambda (_: (((leq g 
(asucc g (ASort O n0)) (asucc g (ASort n3 n2))) \to (leq g (ASort O n0) 
(ASort n3 n2))))).(\lambda (H1: (leq g (asucc g (ASort O n0)) (asucc g (ASort 
(S n3) n2)))).(let TMP_74 \def (next g n0) in (let TMP_75 \def (ASort n3 n2) 
in (let H_x \def (leq_gen_sort1 g O TMP_74 TMP_75 H1) in (let H2 \def H_x in 
(let TMP_81 \def (\lambda (n4: nat).(\lambda (h2: nat).(\lambda (k: nat).(let 
TMP_76 \def (next g n0) in (let TMP_77 \def (ASort O TMP_76) in (let TMP_78 
\def (aplus g TMP_77 k) in (let TMP_79 \def (ASort h2 n4) in (let TMP_80 \def 
(aplus g TMP_79 k) in (eq A TMP_78 TMP_80))))))))) in (let TMP_84 \def 
(\lambda (n4: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_82 \def 
(ASort n3 n2) in (let TMP_83 \def (ASort h2 n4) in (eq A TMP_82 TMP_83)))))) 
in (let TMP_85 \def (ASort O n0) in (let TMP_86 \def (S n3) in (let TMP_87 
\def (ASort TMP_86 n2) in (let TMP_88 \def (leq g TMP_85 TMP_87) in (let 
TMP_131 \def (\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: 
nat).(\lambda (H3: (eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort 
x1 x0) x2))).(\lambda (H4: (eq A (ASort n3 n2) (ASort x1 x0))).(let TMP_89 
\def (\lambda (e: A).(match e with [(ASort n4 _) \Rightarrow n4 | (AHead _ _) 
\Rightarrow n3])) in (let TMP_90 \def (ASort n3 n2) in (let TMP_91 \def 
(ASort x1 x0) in (let H5 \def (f_equal A nat TMP_89 TMP_90 TMP_91 H4) in (let 
TMP_92 \def (\lambda (e: A).(match e with [(ASort _ n4) \Rightarrow n4 | 
(AHead _ _) \Rightarrow n2])) in (let TMP_93 \def (ASort n3 n2) in (let 
TMP_94 \def (ASort x1 x0) in (let H6 \def (f_equal A nat TMP_92 TMP_93 TMP_94 
H4) in (let TMP_130 \def (\lambda (H7: (eq nat n3 x1)).(let TMP_100 \def 
(\lambda (n4: nat).(let TMP_95 \def (next g n0) in (let TMP_96 \def (ASort O 
TMP_95) in (let TMP_97 \def (aplus g TMP_96 x2) in (let TMP_98 \def (ASort n4 
x0) in (let TMP_99 \def (aplus g TMP_98 x2) in (eq A TMP_97 TMP_99))))))) in 
(let H8 \def (eq_ind_r nat x1 TMP_100 H3 n3 H7) in (let TMP_106 \def (\lambda 
(n4: nat).(let TMP_101 \def (next g n0) in (let TMP_102 \def (ASort O 
TMP_101) in (let TMP_103 \def (aplus g TMP_102 x2) in (let TMP_104 \def 
(ASort n3 n4) in (let TMP_105 \def (aplus g TMP_104 x2) in (eq A TMP_103 
TMP_105))))))) in (let H9 \def (eq_ind_r nat x0 TMP_106 H8 n2 H6) in (let 
TMP_107 \def (next g n0) in (let TMP_108 \def (ASort O TMP_107) in (let 
TMP_109 \def (aplus g TMP_108 x2) in (let TMP_112 \def (\lambda (a: A).(let 
TMP_110 \def (ASort n3 n2) in (let TMP_111 \def (aplus g TMP_110 x2) in (eq A 
a TMP_111)))) in (let TMP_113 \def (ASort O n0) in (let TMP_114 \def (S x2) 
in (let TMP_115 \def (aplus g TMP_113 TMP_114) in (let TMP_116 \def 
(aplus_sort_O_S_simpl g n0 x2) in (let H10 \def (eq_ind_r A TMP_109 TMP_112 
H9 TMP_115 TMP_116) in (let TMP_117 \def (ASort n3 n2) in (let TMP_118 \def 
(aplus g TMP_117 x2) in (let TMP_122 \def (\lambda (a: A).(let TMP_119 \def 
(ASort O n0) in (let TMP_120 \def (S x2) in (let TMP_121 \def (aplus g 
TMP_119 TMP_120) in (eq A TMP_121 a))))) in (let TMP_123 \def (S n3) in (let 
TMP_124 \def (ASort TMP_123 n2) in (let TMP_125 \def (S x2) in (let TMP_126 
\def (aplus g TMP_124 TMP_125) in (let TMP_127 \def (aplus_sort_S_S_simpl g 
n2 n3 x2) in (let H11 \def (eq_ind_r A TMP_118 TMP_122 H10 TMP_126 TMP_127) 
in (let TMP_128 \def (S n3) in (let TMP_129 \def (S x2) in (leq_sort g O 
TMP_128 n0 n2 TMP_129 H11)))))))))))))))))))))))))) in (TMP_130 
H5))))))))))))))) in (ex2_3_ind nat nat nat TMP_81 TMP_84 TMP_88 TMP_131 
H2))))))))))))))) in (nat_ind TMP_9 TMP_73 TMP_132 n1 H0))))) in (let TMP_259 
\def (\lambda (n3: nat).(\lambda (IHn: (((leq g (asucc g (ASort n3 n0)) 
(asucc g (ASort n1 n2))) \to (leq g (ASort n3 n0) (ASort n1 n2))))).(\lambda 
(H0: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n1 n2)))).(let 
TMP_137 \def (\lambda (n4: nat).((leq g (asucc g (ASort (S n3) n0)) (asucc g 
(ASort n4 n2))) \to ((((leq g (asucc g (ASort n3 n0)) (asucc g (ASort n4 
n2))) \to (leq g (ASort n3 n0) (ASort n4 n2)))) \to (let TMP_134 \def (S n3) 
in (let TMP_135 \def (ASort TMP_134 n0) in (let TMP_136 \def (ASort n4 n2) in 
(leq g TMP_135 TMP_136))))))) in (let TMP_200 \def (\lambda (H1: (leq g 
(asucc g (ASort (S n3) n0)) (asucc g (ASort O n2)))).(\lambda (_: (((leq g 
(asucc g (ASort n3 n0)) (asucc g (ASort O n2))) \to (leq g (ASort n3 n0) 
(ASort O n2))))).(let TMP_138 \def (next g n2) in (let TMP_139 \def (ASort O 
TMP_138) in (let H_x \def (leq_gen_sort1 g n3 n0 TMP_139 H1) in (let H2 \def 
H_x in (let TMP_144 \def (\lambda (n4: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(let TMP_140 \def (ASort n3 n0) in (let TMP_141 \def (aplus g TMP_140 k) 
in (let TMP_142 \def (ASort h2 n4) in (let TMP_143 \def (aplus g TMP_142 k) 
in (eq A TMP_141 TMP_143)))))))) in (let TMP_148 \def (\lambda (n4: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_145 \def (next g n2) in 
(let TMP_146 \def (ASort O TMP_145) in (let TMP_147 \def (ASort h2 n4) in (eq 
A TMP_146 TMP_147))))))) in (let TMP_149 \def (S n3) in (let TMP_150 \def 
(ASort TMP_149 n0) in (let TMP_151 \def (ASort O n2) in (let TMP_152 \def 
(leq g TMP_150 TMP_151) in (let TMP_199 \def (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort n3 n0) x2) (aplus 
g (ASort x1 x0) x2))).(\lambda (H4: (eq A (ASort O (next g n2)) (ASort x1 
x0))).(let TMP_153 \def (\lambda (e: A).(match e with [(ASort n4 _) 
\Rightarrow n4 | (AHead _ _) \Rightarrow O])) in (let TMP_154 \def (next g 
n2) in (let TMP_155 \def (ASort O TMP_154) in (let TMP_156 \def (ASort x1 x0) 
in (let H5 \def (f_equal A nat TMP_153 TMP_155 TMP_156 H4) in (let TMP_158 
\def (\lambda (e: A).(match e with [(ASort _ n4) \Rightarrow n4 | (AHead _ _) 
\Rightarrow (let TMP_157 \def (match g with [(mk_G next _) \Rightarrow next]) 
in (TMP_157 n2))])) in (let TMP_159 \def (next g n2) in (let TMP_160 \def 
(ASort O TMP_159) in (let TMP_161 \def (ASort x1 x0) in (let H6 \def (f_equal 
A nat TMP_158 TMP_160 TMP_161 H4) in (let TMP_198 \def (\lambda (H7: (eq nat 
O x1)).(let TMP_166 \def (\lambda (n4: nat).(let TMP_162 \def (ASort n3 n0) 
in (let TMP_163 \def (aplus g TMP_162 x2) in (let TMP_164 \def (ASort n4 x0) 
in (let TMP_165 \def (aplus g TMP_164 x2) in (eq A TMP_163 TMP_165)))))) in 
(let H8 \def (eq_ind_r nat x1 TMP_166 H3 O H7) in (let TMP_171 \def (\lambda 
(n4: nat).(let TMP_167 \def (ASort n3 n0) in (let TMP_168 \def (aplus g 
TMP_167 x2) in (let TMP_169 \def (ASort O n4) in (let TMP_170 \def (aplus g 
TMP_169 x2) in (eq A TMP_168 TMP_170)))))) in (let TMP_172 \def (next g n2) 
in (let H9 \def (eq_ind_r nat x0 TMP_171 H8 TMP_172 H6) in (let TMP_173 \def 
(ASort n3 n0) in (let TMP_174 \def (aplus g TMP_173 x2) in (let TMP_178 \def 
(\lambda (a: A).(let TMP_175 \def (next g n2) in (let TMP_176 \def (ASort O 
TMP_175) in (let TMP_177 \def (aplus g TMP_176 x2) in (eq A a TMP_177))))) in 
(let TMP_179 \def (S n3) in (let TMP_180 \def (ASort TMP_179 n0) in (let 
TMP_181 \def (S x2) in (let TMP_182 \def (aplus g TMP_180 TMP_181) in (let 
TMP_183 \def (aplus_sort_S_S_simpl g n0 n3 x2) in (let H10 \def (eq_ind_r A 
TMP_174 TMP_178 H9 TMP_182 TMP_183) in (let TMP_184 \def (next g n2) in (let 
TMP_185 \def (ASort O TMP_184) in (let TMP_186 \def (aplus g TMP_185 x2) in 
(let TMP_191 \def (\lambda (a: A).(let TMP_187 \def (S n3) in (let TMP_188 
\def (ASort TMP_187 n0) in (let TMP_189 \def (S x2) in (let TMP_190 \def 
(aplus g TMP_188 TMP_189) in (eq A TMP_190 a)))))) in (let TMP_192 \def 
(ASort O n2) in (let TMP_193 \def (S x2) in (let TMP_194 \def (aplus g 
TMP_192 TMP_193) in (let TMP_195 \def (aplus_sort_O_S_simpl g n2 x2) in (let 
H11 \def (eq_ind_r A TMP_186 TMP_191 H10 TMP_194 TMP_195) in (let TMP_196 
\def (S n3) in (let TMP_197 \def (S x2) in (leq_sort g TMP_196 O n0 n2 
TMP_197 H11))))))))))))))))))))))))))) in (TMP_198 H5))))))))))))))))) in 
(ex2_3_ind nat nat nat TMP_144 TMP_148 TMP_152 TMP_199 H2)))))))))))))) in 
(let TMP_258 \def (\lambda (n4: nat).(\lambda (_: (((leq g (asucc g (ASort (S 
n3) n0)) (asucc g (ASort n4 n2))) \to ((((leq g (asucc g (ASort n3 n0)) 
(asucc g (ASort n4 n2))) \to (leq g (ASort n3 n0) (ASort n4 n2)))) \to (leq g 
(ASort (S n3) n0) (ASort n4 n2)))))).(\lambda (H1: (leq g (asucc g (ASort (S 
n3) n0)) (asucc g (ASort (S n4) n2)))).(\lambda (_: (((leq g (asucc g (ASort 
n3 n0)) (asucc g (ASort (S n4) n2))) \to (leq g (ASort n3 n0) (ASort (S n4) 
n2))))).(let TMP_201 \def (ASort n4 n2) in (let H_x \def (leq_gen_sort1 g n3 
n0 TMP_201 H1) in (let H2 \def H_x in (let TMP_206 \def (\lambda (n5: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_202 \def (ASort n3 n0) in 
(let TMP_203 \def (aplus g TMP_202 k) in (let TMP_204 \def (ASort h2 n5) in 
(let TMP_205 \def (aplus g TMP_204 k) in (eq A TMP_203 TMP_205)))))))) in 
(let TMP_209 \def (\lambda (n5: nat).(\lambda (h2: nat).(\lambda (_: 
nat).(let TMP_207 \def (ASort n4 n2) in (let TMP_208 \def (ASort h2 n5) in 
(eq A TMP_207 TMP_208)))))) in (let TMP_210 \def (S n3) in (let TMP_211 \def 
(ASort TMP_210 n0) in (let TMP_212 \def (S n4) in (let TMP_213 \def (ASort 
TMP_212 n2) in (let TMP_214 \def (leq g TMP_211 TMP_213) in (let TMP_257 \def 
(\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H3: (eq A 
(aplus g (ASort n3 n0) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H4: (eq A 
(ASort n4 n2) (ASort x1 x0))).(let TMP_215 \def (\lambda (e: A).(match e with 
[(ASort n5 _) \Rightarrow n5 | (AHead _ _) \Rightarrow n4])) in (let TMP_216 
\def (ASort n4 n2) in (let TMP_217 \def (ASort x1 x0) in (let H5 \def 
(f_equal A nat TMP_215 TMP_216 TMP_217 H4) in (let TMP_218 \def (\lambda (e: 
A).(match e with [(ASort _ n5) \Rightarrow n5 | (AHead _ _) \Rightarrow n2])) 
in (let TMP_219 \def (ASort n4 n2) in (let TMP_220 \def (ASort x1 x0) in (let 
H6 \def (f_equal A nat TMP_218 TMP_219 TMP_220 H4) in (let TMP_256 \def 
(\lambda (H7: (eq nat n4 x1)).(let TMP_225 \def (\lambda (n5: nat).(let 
TMP_221 \def (ASort n3 n0) in (let TMP_222 \def (aplus g TMP_221 x2) in (let 
TMP_223 \def (ASort n5 x0) in (let TMP_224 \def (aplus g TMP_223 x2) in (eq A 
TMP_222 TMP_224)))))) in (let H8 \def (eq_ind_r nat x1 TMP_225 H3 n4 H7) in 
(let TMP_230 \def (\lambda (n5: nat).(let TMP_226 \def (ASort n3 n0) in (let 
TMP_227 \def (aplus g TMP_226 x2) in (let TMP_228 \def (ASort n4 n5) in (let 
TMP_229 \def (aplus g TMP_228 x2) in (eq A TMP_227 TMP_229)))))) in (let H9 
\def (eq_ind_r nat x0 TMP_230 H8 n2 H6) in (let TMP_231 \def (ASort n3 n0) in 
(let TMP_232 \def (aplus g TMP_231 x2) in (let TMP_235 \def (\lambda (a: 
A).(let TMP_233 \def (ASort n4 n2) in (let TMP_234 \def (aplus g TMP_233 x2) 
in (eq A a TMP_234)))) in (let TMP_236 \def (S n3) in (let TMP_237 \def 
(ASort TMP_236 n0) in (let TMP_238 \def (S x2) in (let TMP_239 \def (aplus g 
TMP_237 TMP_238) in (let TMP_240 \def (aplus_sort_S_S_simpl g n0 n3 x2) in 
(let H10 \def (eq_ind_r A TMP_232 TMP_235 H9 TMP_239 TMP_240) in (let TMP_241 
\def (ASort n4 n2) in (let TMP_242 \def (aplus g TMP_241 x2) in (let TMP_247 
\def (\lambda (a: A).(let TMP_243 \def (S n3) in (let TMP_244 \def (ASort 
TMP_243 n0) in (let TMP_245 \def (S x2) in (let TMP_246 \def (aplus g TMP_244 
TMP_245) in (eq A TMP_246 a)))))) in (let TMP_248 \def (S n4) in (let TMP_249 
\def (ASort TMP_248 n2) in (let TMP_250 \def (S x2) in (let TMP_251 \def 
(aplus g TMP_249 TMP_250) in (let TMP_252 \def (aplus_sort_S_S_simpl g n2 n4 
x2) in (let H11 \def (eq_ind_r A TMP_242 TMP_247 H10 TMP_251 TMP_252) in (let 
TMP_253 \def (S n3) in (let TMP_254 \def (S n4) in (let TMP_255 \def (S x2) 
in (leq_sort g TMP_253 TMP_254 n0 n2 TMP_255 H11))))))))))))))))))))))))))) 
in (TMP_256 H5))))))))))))))) in (ex2_3_ind nat nat nat TMP_206 TMP_209 
TMP_214 TMP_257 H2)))))))))))))))) in (nat_ind TMP_137 TMP_200 TMP_258 n1 H0 
IHn))))))) in (nat_ind TMP_6 TMP_133 TMP_259 n H))))))) in (let TMP_314 \def 
(\lambda (a: A).(\lambda (H: (((leq g (asucc g (ASort n n0)) (asucc g a)) \to 
(leq g (ASort n n0) a)))).(\lambda (a0: A).(\lambda (H0: (((leq g (asucc g 
(ASort n n0)) (asucc g a0)) \to (leq g (ASort n n0) a0)))).(\lambda (H1: (leq 
g (asucc g (ASort n n0)) (asucc g (AHead a a0)))).(let TMP_263 \def (\lambda 
(n1: nat).((((leq g (asucc g (ASort n1 n0)) (asucc g a)) \to (leq g (ASort n1 
n0) a))) \to ((((leq g (asucc g (ASort n1 n0)) (asucc g a0)) \to (leq g 
(ASort n1 n0) a0))) \to ((leq g (asucc g (ASort n1 n0)) (asucc g (AHead a 
a0))) \to (let TMP_261 \def (ASort n1 n0) in (let TMP_262 \def (AHead a a0) 
in (leq g TMP_261 TMP_262))))))) in (let TMP_288 \def (\lambda (_: (((leq g 
(asucc g (ASort O n0)) (asucc g a)) \to (leq g (ASort O n0) a)))).(\lambda 
(_: (((leq g (asucc g (ASort O n0)) (asucc g a0)) \to (leq g (ASort O n0) 
a0)))).(\lambda (H4: (leq g (asucc g (ASort O n0)) (asucc g (AHead a 
a0)))).(let TMP_264 \def (next g n0) in (let TMP_265 \def (asucc g a0) in 
(let TMP_266 \def (AHead a TMP_265) in (let H_x \def (leq_gen_sort1 g O 
TMP_264 TMP_266 H4) in (let H5 \def H_x in (let TMP_272 \def (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_267 \def (next g n0) in 
(let TMP_268 \def (ASort O TMP_267) in (let TMP_269 \def (aplus g TMP_268 k) 
in (let TMP_270 \def (ASort h2 n2) in (let TMP_271 \def (aplus g TMP_270 k) 
in (eq A TMP_269 TMP_271))))))))) in (let TMP_276 \def (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_273 \def (asucc g a0) in 
(let TMP_274 \def (AHead a TMP_273) in (let TMP_275 \def (ASort h2 n2) in (eq 
A TMP_274 TMP_275))))))) in (let TMP_277 \def (ASort O n0) in (let TMP_278 
\def (AHead a a0) in (let TMP_279 \def (leq g TMP_277 TMP_278) in (let 
TMP_287 \def (\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: 
nat).(\lambda (_: (eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort x1 
x0) x2))).(\lambda (H7: (eq A (AHead a (asucc g a0)) (ASort x1 x0))).(let 
TMP_280 \def (asucc g a0) in (let TMP_281 \def (AHead a TMP_280) in (let 
TMP_282 \def (\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) in (let TMP_283 \def (ASort x1 x0) in (let H8 
\def (eq_ind A TMP_281 TMP_282 I TMP_283 H7) in (let TMP_284 \def (ASort O 
n0) in (let TMP_285 \def (AHead a a0) in (let TMP_286 \def (leq g TMP_284 
TMP_285) in (False_ind TMP_286 H8)))))))))))))) in (ex2_3_ind nat nat nat 
TMP_272 TMP_276 TMP_279 TMP_287 H5))))))))))))))) in (let TMP_313 \def 
(\lambda (n1: nat).(\lambda (_: (((((leq g (asucc g (ASort n1 n0)) (asucc g 
a)) \to (leq g (ASort n1 n0) a))) \to ((((leq g (asucc g (ASort n1 n0)) 
(asucc g a0)) \to (leq g (ASort n1 n0) a0))) \to ((leq g (asucc g (ASort n1 
n0)) (asucc g (AHead a a0))) \to (leq g (ASort n1 n0) (AHead a 
a0))))))).(\lambda (_: (((leq g (asucc g (ASort (S n1) n0)) (asucc g a)) \to 
(leq g (ASort (S n1) n0) a)))).(\lambda (_: (((leq g (asucc g (ASort (S n1) 
n0)) (asucc g a0)) \to (leq g (ASort (S n1) n0) a0)))).(\lambda (H4: (leq g 
(asucc g (ASort (S n1) n0)) (asucc g (AHead a a0)))).(let TMP_289 \def (asucc 
g a0) in (let TMP_290 \def (AHead a TMP_289) in (let H_x \def (leq_gen_sort1 
g n1 n0 TMP_290 H4) in (let H5 \def H_x in (let TMP_295 \def (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_291 \def (ASort n1 n0) in 
(let TMP_292 \def (aplus g TMP_291 k) in (let TMP_293 \def (ASort h2 n2) in 
(let TMP_294 \def (aplus g TMP_293 k) in (eq A TMP_292 TMP_294)))))))) in 
(let TMP_299 \def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: 
nat).(let TMP_296 \def (asucc g a0) in (let TMP_297 \def (AHead a TMP_296) in 
(let TMP_298 \def (ASort h2 n2) in (eq A TMP_297 TMP_298))))))) in (let 
TMP_300 \def (S n1) in (let TMP_301 \def (ASort TMP_300 n0) in (let TMP_302 
\def (AHead a a0) in (let TMP_303 \def (leq g TMP_301 TMP_302) in (let 
TMP_312 \def (\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: 
nat).(\lambda (_: (eq A (aplus g (ASort n1 n0) x2) (aplus g (ASort x1 x0) 
x2))).(\lambda (H7: (eq A (AHead a (asucc g a0)) (ASort x1 x0))).(let TMP_304 
\def (asucc g a0) in (let TMP_305 \def (AHead a TMP_304) in (let TMP_306 \def 
(\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow False | (AHead _ _) 
\Rightarrow True])) in (let TMP_307 \def (ASort x1 x0) in (let H8 \def 
(eq_ind A TMP_305 TMP_306 I TMP_307 H7) in (let TMP_308 \def (S n1) in (let 
TMP_309 \def (ASort TMP_308 n0) in (let TMP_310 \def (AHead a a0) in (let 
TMP_311 \def (leq g TMP_309 TMP_310) in (False_ind TMP_311 H8))))))))))))))) 
in (ex2_3_ind nat nat nat TMP_295 TMP_299 TMP_303 TMP_312 H5))))))))))))))))) 
in (nat_ind TMP_263 TMP_288 TMP_313 n H H0 H1))))))))) in (A_ind TMP_3 
TMP_260 TMP_314 a2))))))) in (let TMP_396 \def (\lambda (a: A).(\lambda (_: 
((\forall (a2: A).((leq g (asucc g a) (asucc g a2)) \to (leq g a 
a2))))).(\lambda (a0: A).(\lambda (H0: ((\forall (a2: A).((leq g (asucc g a0) 
(asucc g a2)) \to (leq g a0 a2))))).(\lambda (a2: A).(let TMP_317 \def 
(\lambda (a3: A).((leq g (asucc g (AHead a a0)) (asucc g a3)) \to (let 
TMP_316 \def (AHead a a0) in (leq g TMP_316 a3)))) in (let TMP_364 \def 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (H1: (leq g (asucc g (AHead a 
a0)) (asucc g (ASort n n0)))).(let TMP_320 \def (\lambda (n1: nat).((leq g 
(asucc g (AHead a a0)) (asucc g (ASort n1 n0))) \to (let TMP_318 \def (AHead 
a a0) in (let TMP_319 \def (ASort n1 n0) in (leq g TMP_318 TMP_319))))) in 
(let TMP_342 \def (\lambda (H2: (leq g (asucc g (AHead a a0)) (asucc g (ASort 
O n0)))).(let TMP_321 \def (asucc g a0) in (let TMP_322 \def (next g n0) in 
(let TMP_323 \def (ASort O TMP_322) in (let H_x \def (leq_gen_head1 g a 
TMP_321 TMP_323 H2) in (let H3 \def H_x in (let TMP_324 \def (\lambda (a3: 
A).(\lambda (_: A).(leq g a a3))) in (let TMP_326 \def (\lambda (_: 
A).(\lambda (a4: A).(let TMP_325 \def (asucc g a0) in (leq g TMP_325 a4)))) 
in (let TMP_330 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_327 \def 
(next g n0) in (let TMP_328 \def (ASort O TMP_327) in (let TMP_329 \def 
(AHead a3 a4) in (eq A TMP_328 TMP_329)))))) in (let TMP_331 \def (AHead a 
a0) in (let TMP_332 \def (ASort O n0) in (let TMP_333 \def (leq g TMP_331 
TMP_332) in (let TMP_341 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: 
(leq g a x0)).(\lambda (_: (leq g (asucc g a0) x1)).(\lambda (H6: (eq A 
(ASort O (next g n0)) (AHead x0 x1))).(let TMP_334 \def (next g n0) in (let 
TMP_335 \def (ASort O TMP_334) in (let TMP_336 \def (\lambda (ee: A).(match 
ee with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow False])) in 
(let TMP_337 \def (AHead x0 x1) in (let H7 \def (eq_ind A TMP_335 TMP_336 I 
TMP_337 H6) in (let TMP_338 \def (AHead a a0) in (let TMP_339 \def (ASort O 
n0) in (let TMP_340 \def (leq g TMP_338 TMP_339) in (False_ind TMP_340 
H7)))))))))))))) in (ex3_2_ind A A TMP_324 TMP_326 TMP_330 TMP_333 TMP_341 
H3)))))))))))))) in (let TMP_363 \def (\lambda (n1: nat).(\lambda (_: (((leq 
g (asucc g (AHead a a0)) (asucc g (ASort n1 n0))) \to (leq g (AHead a a0) 
(ASort n1 n0))))).(\lambda (H2: (leq g (asucc g (AHead a a0)) (asucc g (ASort 
(S n1) n0)))).(let TMP_343 \def (asucc g a0) in (let TMP_344 \def (ASort n1 
n0) in (let H_x \def (leq_gen_head1 g a TMP_343 TMP_344 H2) in (let H3 \def 
H_x in (let TMP_345 \def (\lambda (a3: A).(\lambda (_: A).(leq g a a3))) in 
(let TMP_347 \def (\lambda (_: A).(\lambda (a4: A).(let TMP_346 \def (asucc g 
a0) in (leq g TMP_346 a4)))) in (let TMP_350 \def (\lambda (a3: A).(\lambda 
(a4: A).(let TMP_348 \def (ASort n1 n0) in (let TMP_349 \def (AHead a3 a4) in 
(eq A TMP_348 TMP_349))))) in (let TMP_351 \def (AHead a a0) in (let TMP_352 
\def (S n1) in (let TMP_353 \def (ASort TMP_352 n0) in (let TMP_354 \def (leq 
g TMP_351 TMP_353) in (let TMP_362 \def (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (_: (leq g a x0)).(\lambda (_: (leq g (asucc g a0) x1)).(\lambda 
(H6: (eq A (ASort n1 n0) (AHead x0 x1))).(let TMP_355 \def (ASort n1 n0) in 
(let TMP_356 \def (\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow 
True | (AHead _ _) \Rightarrow False])) in (let TMP_357 \def (AHead x0 x1) in 
(let H7 \def (eq_ind A TMP_355 TMP_356 I TMP_357 H6) in (let TMP_358 \def 
(AHead a a0) in (let TMP_359 \def (S n1) in (let TMP_360 \def (ASort TMP_359 
n0) in (let TMP_361 \def (leq g TMP_358 TMP_360) in (False_ind TMP_361 
H7)))))))))))))) in (ex3_2_ind A A TMP_345 TMP_347 TMP_350 TMP_354 TMP_362 
H3)))))))))))))))) in (nat_ind TMP_320 TMP_342 TMP_363 n H1))))))) in (let 
TMP_395 \def (\lambda (a3: A).(\lambda (_: (((leq g (asucc g (AHead a a0)) 
(asucc g a3)) \to (leq g (AHead a a0) a3)))).(\lambda (a4: A).(\lambda (_: 
(((leq g (asucc g (AHead a a0)) (asucc g a4)) \to (leq g (AHead a a0) 
a4)))).(\lambda (H3: (leq g (asucc g (AHead a a0)) (asucc g (AHead a3 
a4)))).(let TMP_365 \def (asucc g a0) in (let TMP_366 \def (asucc g a4) in 
(let TMP_367 \def (AHead a3 TMP_366) in (let H_x \def (leq_gen_head1 g a 
TMP_365 TMP_367 H3) in (let H4 \def H_x in (let TMP_368 \def (\lambda (a5: 
A).(\lambda (_: A).(leq g a a5))) in (let TMP_370 \def (\lambda (_: 
A).(\lambda (a6: A).(let TMP_369 \def (asucc g a0) in (leq g TMP_369 a6)))) 
in (let TMP_374 \def (\lambda (a5: A).(\lambda (a6: A).(let TMP_371 \def 
(asucc g a4) in (let TMP_372 \def (AHead a3 TMP_371) in (let TMP_373 \def 
(AHead a5 a6) in (eq A TMP_372 TMP_373)))))) in (let TMP_375 \def (AHead a 
a0) in (let TMP_376 \def (AHead a3 a4) in (let TMP_377 \def (leq g TMP_375 
TMP_376) in (let TMP_394 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (H5: 
(leq g a x0)).(\lambda (H6: (leq g (asucc g a0) x1)).(\lambda (H7: (eq A 
(AHead a3 (asucc g a4)) (AHead x0 x1))).(let TMP_378 \def (\lambda (e: 
A).(match e with [(ASort _ _) \Rightarrow a3 | (AHead a5 _) \Rightarrow a5])) 
in (let TMP_379 \def (asucc g a4) in (let TMP_380 \def (AHead a3 TMP_379) in 
(let TMP_381 \def (AHead x0 x1) in (let H8 \def (f_equal A A TMP_378 TMP_380 
TMP_381 H7) in (let TMP_384 \def (\lambda (e: A).(match e with [(ASort _ _) 
\Rightarrow (asucc g a4) | (AHead _ a5) \Rightarrow a5])) in (let TMP_385 
\def (asucc g a4) in (let TMP_386 \def (AHead a3 TMP_385) in (let TMP_387 
\def (AHead x0 x1) in (let H9 \def (f_equal A A TMP_384 TMP_386 TMP_387 H7) 
in (let TMP_393 \def (\lambda (H10: (eq A a3 x0)).(let TMP_389 \def (\lambda 
(a5: A).(let TMP_388 \def (asucc g a0) in (leq g TMP_388 a5))) in (let 
TMP_390 \def (asucc g a4) in (let H11 \def (eq_ind_r A x1 TMP_389 H6 TMP_390 
H9) in (let TMP_391 \def (\lambda (a5: A).(leq g a a5)) in (let H12 \def 
(eq_ind_r A x0 TMP_391 H5 a3 H10) in (let TMP_392 \def (H0 a4 H11) in 
(leq_head g a a3 H12 a0 a4 TMP_392)))))))) in (TMP_393 H8))))))))))))))))) in 
(ex3_2_ind A A TMP_368 TMP_370 TMP_374 TMP_377 TMP_394 H4)))))))))))))))))) 
in (A_ind TMP_317 TMP_364 TMP_395 a2))))))))) in (A_ind TMP_1 TMP_315 TMP_396 
a1))))).

theorem leq_asucc:
 \forall (g: G).(\forall (a: A).(ex A (\lambda (a0: A).(leq g a (asucc g 
a0)))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_3 \def (\lambda (a0: A).(let TMP_2 
\def (\lambda (a1: A).(let TMP_1 \def (asucc g a1) in (leq g a0 TMP_1))) in 
(ex A TMP_2))) in (let TMP_11 \def (\lambda (n: nat).(\lambda (n0: nat).(let 
TMP_6 \def (\lambda (a0: A).(let TMP_4 \def (ASort n n0) in (let TMP_5 \def 
(asucc g a0) in (leq g TMP_4 TMP_5)))) in (let TMP_7 \def (S n) in (let TMP_8 
\def (ASort TMP_7 n0) in (let TMP_9 \def (ASort n n0) in (let TMP_10 \def 
(leq_refl g TMP_9) in (ex_intro A TMP_6 TMP_8 TMP_10)))))))) in (let TMP_26 
\def (\lambda (a0: A).(\lambda (_: (ex A (\lambda (a1: A).(leq g a0 (asucc g 
a1))))).(\lambda (a1: A).(\lambda (H0: (ex A (\lambda (a2: A).(leq g a1 
(asucc g a2))))).(let H1 \def H0 in (let TMP_13 \def (\lambda (a2: A).(let 
TMP_12 \def (asucc g a2) in (leq g a1 TMP_12))) in (let TMP_16 \def (\lambda 
(a2: A).(let TMP_14 \def (AHead a0 a1) in (let TMP_15 \def (asucc g a2) in 
(leq g TMP_14 TMP_15)))) in (let TMP_17 \def (ex A TMP_16) in (let TMP_25 
\def (\lambda (x: A).(\lambda (H2: (leq g a1 (asucc g x))).(let TMP_20 \def 
(\lambda (a2: A).(let TMP_18 \def (AHead a0 a1) in (let TMP_19 \def (asucc g 
a2) in (leq g TMP_18 TMP_19)))) in (let TMP_21 \def (AHead a0 x) in (let 
TMP_22 \def (leq_refl g a0) in (let TMP_23 \def (asucc g x) in (let TMP_24 
\def (leq_head g a0 a0 TMP_22 a1 TMP_23 H2) in (ex_intro A TMP_20 TMP_21 
TMP_24)))))))) in (ex_ind A TMP_13 TMP_17 TMP_25 H1)))))))))) in (A_ind TMP_3 
TMP_11 TMP_26 a))))).

theorem leq_ahead_asucc_false:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) 
(asucc g a1)) \to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a1: A).(let TMP_1 \def (\lambda (a: A).(\forall 
(a2: A).((leq g (AHead a a2) (asucc g a)) \to (\forall (P: Prop).P)))) in 
(let TMP_34 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (a2: 
A).(\lambda (H: (leq g (AHead (ASort n n0) a2) (match n with [O \Rightarrow 
(ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]))).(\lambda (P: 
Prop).(let TMP_2 \def (\lambda (n1: nat).((leq g (AHead (ASort n1 n0) a2) 
(match n1 with [O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow 
(ASort h n0)])) \to P)) in (let TMP_18 \def (\lambda (H0: (leq g (AHead 
(ASort O n0) a2) (ASort O (next g n0)))).(let TMP_3 \def (ASort O n0) in (let 
TMP_4 \def (next g n0) in (let TMP_5 \def (ASort O TMP_4) in (let H_x \def 
(leq_gen_head1 g TMP_3 a2 TMP_5 H0) in (let H1 \def H_x in (let TMP_7 \def 
(\lambda (a3: A).(\lambda (_: A).(let TMP_6 \def (ASort O n0) in (leq g TMP_6 
a3)))) in (let TMP_8 \def (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) in 
(let TMP_12 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_9 \def (next g 
n0) in (let TMP_10 \def (ASort O TMP_9) in (let TMP_11 \def (AHead a3 a4) in 
(eq A TMP_10 TMP_11)))))) in (let TMP_17 \def (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (_: (leq g (ASort O n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda 
(H4: (eq A (ASort O (next g n0)) (AHead x0 x1))).(let TMP_13 \def (next g n0) 
in (let TMP_14 \def (ASort O TMP_13) in (let TMP_15 \def (\lambda (ee: 
A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) in (let TMP_16 \def (AHead x0 x1) in (let H5 \def (eq_ind A TMP_14 
TMP_15 I TMP_16 H4) in (False_ind P H5))))))))))) in (ex3_2_ind A A TMP_7 
TMP_8 TMP_12 P TMP_17 H1))))))))))) in (let TMP_33 \def (\lambda (n1: 
nat).(\lambda (_: (((leq g (AHead (ASort n1 n0) a2) (match n1 with [O 
\Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)])) \to 
P))).(\lambda (H0: (leq g (AHead (ASort (S n1) n0) a2) (ASort n1 n0))).(let 
TMP_19 \def (S n1) in (let TMP_20 \def (ASort TMP_19 n0) in (let TMP_21 \def 
(ASort n1 n0) in (let H_x \def (leq_gen_head1 g TMP_20 a2 TMP_21 H0) in (let 
H1 \def H_x in (let TMP_24 \def (\lambda (a3: A).(\lambda (_: A).(let TMP_22 
\def (S n1) in (let TMP_23 \def (ASort TMP_22 n0) in (leq g TMP_23 a3))))) in 
(let TMP_25 \def (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) in (let 
TMP_28 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_26 \def (ASort n1 n0) 
in (let TMP_27 \def (AHead a3 a4) in (eq A TMP_26 TMP_27))))) in (let TMP_32 
\def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g (ASort (S n1) n0) 
x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H4: (eq A (ASort n1 n0) (AHead x0 
x1))).(let TMP_29 \def (ASort n1 n0) in (let TMP_30 \def (\lambda (ee: 
A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) in (let TMP_31 \def (AHead x0 x1) in (let H5 \def (eq_ind A TMP_29 
TMP_30 I TMP_31 H4) in (False_ind P H5)))))))))) in (ex3_2_ind A A TMP_24 
TMP_25 TMP_28 P TMP_32 H1))))))))))))) in (nat_ind TMP_2 TMP_18 TMP_33 n 
H))))))))) in (let TMP_61 \def (\lambda (a: A).(\lambda (_: ((\forall (a2: 
A).((leq g (AHead a a2) (asucc g a)) \to (\forall (P: Prop).P))))).(\lambda 
(a0: A).(\lambda (_: ((\forall (a2: A).((leq g (AHead a0 a2) (asucc g a0)) 
\to (\forall (P: Prop).P))))).(\lambda (a2: A).(\lambda (H1: (leq g (AHead 
(AHead a a0) a2) (AHead a (asucc g a0)))).(\lambda (P: Prop).(let TMP_35 \def 
(AHead a a0) in (let TMP_36 \def (asucc g a0) in (let TMP_37 \def (AHead a 
TMP_36) in (let H_x \def (leq_gen_head1 g TMP_35 a2 TMP_37 H1) in (let H2 
\def H_x in (let TMP_39 \def (\lambda (a3: A).(\lambda (_: A).(let TMP_38 
\def (AHead a a0) in (leq g TMP_38 a3)))) in (let TMP_40 \def (\lambda (_: 
A).(\lambda (a4: A).(leq g a2 a4))) in (let TMP_44 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_41 \def (asucc g a0) in (let TMP_42 \def (AHead 
a TMP_41) in (let TMP_43 \def (AHead a3 a4) in (eq A TMP_42 TMP_43)))))) in 
(let TMP_60 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (H3: (leq g 
(AHead a a0) x0)).(\lambda (H4: (leq g a2 x1)).(\lambda (H5: (eq A (AHead a 
(asucc g a0)) (AHead x0 x1))).(let TMP_45 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a | (AHead a3 _) \Rightarrow a3])) in (let TMP_46 
\def (asucc g a0) in (let TMP_47 \def (AHead a TMP_46) in (let TMP_48 \def 
(AHead x0 x1) in (let H6 \def (f_equal A A TMP_45 TMP_47 TMP_48 H5) in (let 
TMP_51 \def (\lambda (e: A).(match e with [(ASort _ _) \Rightarrow (asucc g 
a0) | (AHead _ a3) \Rightarrow a3])) in (let TMP_52 \def (asucc g a0) in (let 
TMP_53 \def (AHead a TMP_52) in (let TMP_54 \def (AHead x0 x1) in (let H7 
\def (f_equal A A TMP_51 TMP_53 TMP_54 H5) in (let TMP_59 \def (\lambda (H8: 
(eq A a x0)).(let TMP_55 \def (\lambda (a3: A).(leq g a2 a3)) in (let TMP_56 
\def (asucc g a0) in (let H9 \def (eq_ind_r A x1 TMP_55 H4 TMP_56 H7) in (let 
TMP_58 \def (\lambda (a3: A).(let TMP_57 \def (AHead a a0) in (leq g TMP_57 
a3))) in (let H10 \def (eq_ind_r A x0 TMP_58 H3 a H8) in (leq_ahead_false_1 g 
a a0 H10 P))))))) in (TMP_59 H6))))))))))))))))) in (ex3_2_ind A A TMP_39 
TMP_40 TMP_44 P TMP_60 H2))))))))))))))))) in (A_ind TMP_1 TMP_34 TMP_61 
a1))))).

theorem leq_asucc_false:
 \forall (g: G).(\forall (a: A).((leq g (asucc g a) a) \to (\forall (P: 
Prop).P)))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_1 \def (\lambda (a0: A).((leq g 
(asucc g a0) a0) \to (\forall (P: Prop).P))) in (let TMP_103 \def (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (H: (leq g (match n with [O \Rightarrow 
(ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]) (ASort n 
n0))).(\lambda (P: Prop).(let TMP_2 \def (\lambda (n1: nat).((leq g (match n1 
with [O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]) 
(ASort n1 n0)) \to P)) in (let TMP_50 \def (\lambda (H0: (leq g (ASort O 
(next g n0)) (ASort O n0))).(let TMP_3 \def (next g n0) in (let TMP_4 \def 
(ASort O n0) in (let H_x \def (leq_gen_sort1 g O TMP_3 TMP_4 H0) in (let H1 
\def H_x in (let TMP_10 \def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(k: nat).(let TMP_5 \def (next g n0) in (let TMP_6 \def (ASort O TMP_5) in 
(let TMP_7 \def (aplus g TMP_6 k) in (let TMP_8 \def (ASort h2 n2) in (let 
TMP_9 \def (aplus g TMP_8 k) in (eq A TMP_7 TMP_9))))))))) in (let TMP_13 
\def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_11 \def 
(ASort O n0) in (let TMP_12 \def (ASort h2 n2) in (eq A TMP_11 TMP_12)))))) 
in (let TMP_49 \def (\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: 
nat).(\lambda (H2: (eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort 
x1 x0) x2))).(\lambda (H3: (eq A (ASort O n0) (ASort x1 x0))).(let TMP_14 
\def (\lambda (e: A).(match e with [(ASort n1 _) \Rightarrow n1 | (AHead _ _) 
\Rightarrow O])) in (let TMP_15 \def (ASort O n0) in (let TMP_16 \def (ASort 
x1 x0) in (let H4 \def (f_equal A nat TMP_14 TMP_15 TMP_16 H3) in (let TMP_17 
\def (\lambda (e: A).(match e with [(ASort _ n1) \Rightarrow n1 | (AHead _ _) 
\Rightarrow n0])) in (let TMP_18 \def (ASort O n0) in (let TMP_19 \def (ASort 
x1 x0) in (let H5 \def (f_equal A nat TMP_17 TMP_18 TMP_19 H3) in (let TMP_48 
\def (\lambda (H6: (eq nat O x1)).(let TMP_25 \def (\lambda (n1: nat).(let 
TMP_20 \def (next g n0) in (let TMP_21 \def (ASort O TMP_20) in (let TMP_22 
\def (aplus g TMP_21 x2) in (let TMP_23 \def (ASort n1 x0) in (let TMP_24 
\def (aplus g TMP_23 x2) in (eq A TMP_22 TMP_24))))))) in (let H7 \def 
(eq_ind_r nat x1 TMP_25 H2 O H6) in (let TMP_31 \def (\lambda (n1: nat).(let 
TMP_26 \def (next g n0) in (let TMP_27 \def (ASort O TMP_26) in (let TMP_28 
\def (aplus g TMP_27 x2) in (let TMP_29 \def (ASort O n1) in (let TMP_30 \def 
(aplus g TMP_29 x2) in (eq A TMP_28 TMP_30))))))) in (let H8 \def (eq_ind_r 
nat x0 TMP_31 H7 n0 H5) in (let TMP_32 \def (next g n0) in (let TMP_33 \def 
(ASort O TMP_32) in (let TMP_34 \def (aplus g TMP_33 x2) in (let TMP_37 \def 
(\lambda (a0: A).(let TMP_35 \def (ASort O n0) in (let TMP_36 \def (aplus g 
TMP_35 x2) in (eq A a0 TMP_36)))) in (let TMP_38 \def (ASort O n0) in (let 
TMP_39 \def (S x2) in (let TMP_40 \def (aplus g TMP_38 TMP_39) in (let TMP_41 
\def (aplus_sort_O_S_simpl g n0 x2) in (let H9 \def (eq_ind_r A TMP_34 TMP_37 
H8 TMP_40 TMP_41) in (let TMP_42 \def (S x2) in (let TMP_43 \def (ASort O n0) 
in (let H_y \def (aplus_inj g TMP_42 x2 TMP_43 H9) in (let TMP_44 \def 
(\lambda (n1: nat).(le n1 x2)) in (let TMP_45 \def (le_n x2) in (let TMP_46 
\def (S x2) in (let TMP_47 \def (eq_ind_r nat x2 TMP_44 TMP_45 TMP_46 H_y) in 
(le_Sx_x x2 TMP_47 P)))))))))))))))))))))) in (TMP_48 H4))))))))))))))) in 
(ex2_3_ind nat nat nat TMP_10 TMP_13 P TMP_49 H1))))))))) in (let TMP_102 
\def (\lambda (n1: nat).(\lambda (_: (((leq g (match n1 with [O \Rightarrow 
(ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)]) (ASort n1 n0)) \to 
P))).(\lambda (H0: (leq g (ASort n1 n0) (ASort (S n1) n0))).(let TMP_51 \def 
(S n1) in (let TMP_52 \def (ASort TMP_51 n0) in (let H_x \def (leq_gen_sort1 
g n1 n0 TMP_52 H0) in (let H1 \def H_x in (let TMP_57 \def (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_53 \def (ASort n1 n0) in 
(let TMP_54 \def (aplus g TMP_53 k) in (let TMP_55 \def (ASort h2 n2) in (let 
TMP_56 \def (aplus g TMP_55 k) in (eq A TMP_54 TMP_56)))))))) in (let TMP_61 
\def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_58 \def 
(S n1) in (let TMP_59 \def (ASort TMP_58 n0) in (let TMP_60 \def (ASort h2 
n2) in (eq A TMP_59 TMP_60))))))) in (let TMP_101 \def (\lambda (x0: 
nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H2: (eq A (aplus g 
(ASort n1 n0) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H3: (eq A (ASort (S 
n1) n0) (ASort x1 x0))).(let TMP_62 \def (\lambda (e: A).(match e with 
[(ASort n2 _) \Rightarrow n2 | (AHead _ _) \Rightarrow (S n1)])) in (let 
TMP_63 \def (S n1) in (let TMP_64 \def (ASort TMP_63 n0) in (let TMP_65 \def 
(ASort x1 x0) in (let H4 \def (f_equal A nat TMP_62 TMP_64 TMP_65 H3) in (let 
TMP_66 \def (\lambda (e: A).(match e with [(ASort _ n2) \Rightarrow n2 | 
(AHead _ _) \Rightarrow n0])) in (let TMP_67 \def (S n1) in (let TMP_68 \def 
(ASort TMP_67 n0) in (let TMP_69 \def (ASort x1 x0) in (let H5 \def (f_equal 
A nat TMP_66 TMP_68 TMP_69 H3) in (let TMP_100 \def (\lambda (H6: (eq nat (S 
n1) x1)).(let TMP_74 \def (\lambda (n2: nat).(let TMP_70 \def (ASort n1 n0) 
in (let TMP_71 \def (aplus g TMP_70 x2) in (let TMP_72 \def (ASort n2 x0) in 
(let TMP_73 \def (aplus g TMP_72 x2) in (eq A TMP_71 TMP_73)))))) in (let 
TMP_75 \def (S n1) in (let H7 \def (eq_ind_r nat x1 TMP_74 H2 TMP_75 H6) in 
(let TMP_81 \def (\lambda (n2: nat).(let TMP_76 \def (ASort n1 n0) in (let 
TMP_77 \def (aplus g TMP_76 x2) in (let TMP_78 \def (S n1) in (let TMP_79 
\def (ASort TMP_78 n2) in (let TMP_80 \def (aplus g TMP_79 x2) in (eq A 
TMP_77 TMP_80))))))) in (let H8 \def (eq_ind_r nat x0 TMP_81 H7 n0 H5) in 
(let TMP_82 \def (ASort n1 n0) in (let TMP_83 \def (aplus g TMP_82 x2) in 
(let TMP_87 \def (\lambda (a0: A).(let TMP_84 \def (S n1) in (let TMP_85 \def 
(ASort TMP_84 n0) in (let TMP_86 \def (aplus g TMP_85 x2) in (eq A a0 
TMP_86))))) in (let TMP_88 \def (S n1) in (let TMP_89 \def (ASort TMP_88 n0) 
in (let TMP_90 \def (S x2) in (let TMP_91 \def (aplus g TMP_89 TMP_90) in 
(let TMP_92 \def (aplus_sort_S_S_simpl g n0 n1 x2) in (let H9 \def (eq_ind_r 
A TMP_83 TMP_87 H8 TMP_91 TMP_92) in (let TMP_93 \def (S x2) in (let TMP_94 
\def (S n1) in (let TMP_95 \def (ASort TMP_94 n0) in (let H_y \def (aplus_inj 
g TMP_93 x2 TMP_95 H9) in (let TMP_96 \def (\lambda (n2: nat).(le n2 x2)) in 
(let TMP_97 \def (le_n x2) in (let TMP_98 \def (S x2) in (let TMP_99 \def 
(eq_ind_r nat x2 TMP_96 TMP_97 TMP_98 H_y) in (le_Sx_x x2 TMP_99 
P)))))))))))))))))))))))) in (TMP_100 H4))))))))))))))))) in (ex2_3_ind nat 
nat nat TMP_57 TMP_61 P TMP_101 H1))))))))))) in (nat_ind TMP_2 TMP_50 
TMP_102 n H)))))))) in (let TMP_123 \def (\lambda (a0: A).(\lambda (_: (((leq 
g (asucc g a0) a0) \to (\forall (P: Prop).P)))).(\lambda (a1: A).(\lambda 
(H0: (((leq g (asucc g a1) a1) \to (\forall (P: Prop).P)))).(\lambda (H1: 
(leq g (AHead a0 (asucc g a1)) (AHead a0 a1))).(\lambda (P: Prop).(let 
TMP_104 \def (asucc g a1) in (let TMP_105 \def (AHead a0 a1) in (let H_x \def 
(leq_gen_head1 g a0 TMP_104 TMP_105 H1) in (let H2 \def H_x in (let TMP_106 
\def (\lambda (a3: A).(\lambda (_: A).(leq g a0 a3))) in (let TMP_108 \def 
(\lambda (_: A).(\lambda (a4: A).(let TMP_107 \def (asucc g a1) in (leq g 
TMP_107 a4)))) in (let TMP_111 \def (\lambda (a3: A).(\lambda (a4: A).(let 
TMP_109 \def (AHead a0 a1) in (let TMP_110 \def (AHead a3 a4) in (eq A 
TMP_109 TMP_110))))) in (let TMP_122 \def (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (leq g a0 x0)).(\lambda (H4: (leq g (asucc g a1) 
x1)).(\lambda (H5: (eq A (AHead a0 a1) (AHead x0 x1))).(let TMP_112 \def 
(\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a0 | (AHead a2 _) 
\Rightarrow a2])) in (let TMP_113 \def (AHead a0 a1) in (let TMP_114 \def 
(AHead x0 x1) in (let H6 \def (f_equal A A TMP_112 TMP_113 TMP_114 H5) in 
(let TMP_115 \def (\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a1 | 
(AHead _ a2) \Rightarrow a2])) in (let TMP_116 \def (AHead a0 a1) in (let 
TMP_117 \def (AHead x0 x1) in (let H7 \def (f_equal A A TMP_115 TMP_116 
TMP_117 H5) in (let TMP_121 \def (\lambda (H8: (eq A a0 x0)).(let TMP_119 
\def (\lambda (a2: A).(let TMP_118 \def (asucc g a1) in (leq g TMP_118 a2))) 
in (let H9 \def (eq_ind_r A x1 TMP_119 H4 a1 H7) in (let TMP_120 \def 
(\lambda (a2: A).(leq g a0 a2)) in (let H10 \def (eq_ind_r A x0 TMP_120 H3 a0 
H8) in (H0 H9 P)))))) in (TMP_121 H6))))))))))))))) in (ex3_2_ind A A TMP_106 
TMP_108 TMP_111 P TMP_122 H2))))))))))))))) in (A_ind TMP_1 TMP_103 TMP_123 
a))))).

