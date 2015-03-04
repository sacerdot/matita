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

include "basic_1/arity/props.ma".

include "basic_1/arity/cimp.ma".

include "basic_1/aprem/props.ma".

theorem arity_aprem:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a: A).((arity g c t 
a) \to (\forall (i: nat).(\forall (b: A).((aprem i a b) \to (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c)))) 
(\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(arity g d u (asucc g 
b)))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c t a)).(let TMP_5 \def (\lambda (c0: C).(\lambda (_: T).(\lambda 
(a0: A).(\forall (i: nat).(\forall (b: A).((aprem i a0 b) \to (let TMP_2 \def 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_1 \def (plus i j) 
in (drop TMP_1 O d c0))))) in (let TMP_4 \def (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: nat).(let TMP_3 \def (asucc g b) in (arity g d u TMP_3))))) 
in (ex2_3 C T nat TMP_2 TMP_4))))))))) in (let TMP_11 \def (\lambda (c0: 
C).(\lambda (n: nat).(\lambda (i: nat).(\lambda (b: A).(\lambda (H0: (aprem i 
(ASort O n) b)).(let H_x \def (aprem_gen_sort b i O n H0) in (let H1 \def H_x 
in (let TMP_7 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let 
TMP_6 \def (plus i j) in (drop TMP_6 O d c0))))) in (let TMP_9 \def (\lambda 
(d: C).(\lambda (u: T).(\lambda (_: nat).(let TMP_8 \def (asucc g b) in 
(arity g d u TMP_8))))) in (let TMP_10 \def (ex2_3 C T nat TMP_7 TMP_9) in 
(False_ind TMP_10 H1))))))))))) in (let TMP_45 \def (\lambda (c0: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d 
(Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda 
(H2: ((\forall (i0: nat).(\forall (b: A).((aprem i0 a0 b) \to (ex2_3 C T nat 
(\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d0 
d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 
(asucc g b))))))))))).(\lambda (i0: nat).(\lambda (b: A).(\lambda (H3: (aprem 
i0 a0 b)).(let H_x \def (H2 i0 b H3) in (let H4 \def H_x in (let TMP_13 \def 
(\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_12 \def (plus i0 
j) in (drop TMP_12 O d0 d))))) in (let TMP_15 \def (\lambda (d0: C).(\lambda 
(u0: T).(\lambda (_: nat).(let TMP_14 \def (asucc g b) in (arity g d0 u0 
TMP_14))))) in (let TMP_17 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_16 \def (plus i0 j) in (drop TMP_16 O d0 c0))))) in (let TMP_19 
\def (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_18 \def 
(asucc g b) in (arity g d0 u0 TMP_18))))) in (let TMP_20 \def (ex2_3 C T nat 
TMP_17 TMP_19) in (let TMP_44 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: nat).(\lambda (H5: (drop (plus i0 x2) O x0 d)).(\lambda (H6: (arity g x0 
x1 (asucc g b))).(let TMP_21 \def (plus i0 x2) in (let H_x0 \def 
(getl_drop_conf_rev TMP_21 x0 d H5 Abbr c0 u i H0) in (let H7 \def H_x0 in 
(let TMP_23 \def (\lambda (c1: C).(let TMP_22 \def (plus i0 x2) in (drop 
TMP_22 O c1 c0))) in (let TMP_26 \def (\lambda (c1: C).(let TMP_24 \def (S i) 
in (let TMP_25 \def (plus i0 x2) in (drop TMP_24 TMP_25 c1 x0)))) in (let 
TMP_28 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_27 
\def (plus i0 j) in (drop TMP_27 O d0 c0))))) in (let TMP_30 \def (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_29 \def (asucc g b) in 
(arity g d0 u0 TMP_29))))) in (let TMP_31 \def (ex2_3 C T nat TMP_28 TMP_30) 
in (let TMP_43 \def (\lambda (x: C).(\lambda (H8: (drop (plus i0 x2) O x 
c0)).(\lambda (H9: (drop (S i) (plus i0 x2) x x0)).(let TMP_33 \def (\lambda 
(d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_32 \def (plus i0 j) in 
(drop TMP_32 O d0 c0))))) in (let TMP_35 \def (\lambda (d0: C).(\lambda (u0: 
T).(\lambda (_: nat).(let TMP_34 \def (asucc g b) in (arity g d0 u0 
TMP_34))))) in (let TMP_36 \def (S i) in (let TMP_37 \def (plus i0 x2) in 
(let TMP_38 \def (lift TMP_36 TMP_37 x1) in (let TMP_39 \def (asucc g b) in 
(let TMP_40 \def (S i) in (let TMP_41 \def (plus i0 x2) in (let TMP_42 \def 
(arity_lift g x0 x1 TMP_39 H6 x TMP_40 TMP_41 H9) in (ex2_3_intro C T nat 
TMP_33 TMP_35 x TMP_38 x2 H8 TMP_42))))))))))))) in (ex2_ind C TMP_23 TMP_26 
TMP_31 TMP_43 H7))))))))))))))) in (ex2_3_ind C T nat TMP_13 TMP_15 TMP_20 
TMP_44 H4)))))))))))))))))))) in (let TMP_80 \def (\lambda (c0: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d 
(Bind Abst) u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g 
a0))).(\lambda (H2: ((\forall (i0: nat).(\forall (b: A).((aprem i0 (asucc g 
a0) b) \to (ex2_3 C T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(drop (plus i0 j) O d0 d)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d0 u0 (asucc g b))))))))))).(\lambda (i0: nat).(\lambda (b: 
A).(\lambda (H3: (aprem i0 a0 b)).(let H_y \def (H2 i0 b) in (let TMP_46 \def 
(aprem_asucc g a0 b i0 H3) in (let H4 \def (H_y TMP_46) in (let TMP_48 \def 
(\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_47 \def (plus i0 
j) in (drop TMP_47 O d0 d))))) in (let TMP_50 \def (\lambda (d0: C).(\lambda 
(u0: T).(\lambda (_: nat).(let TMP_49 \def (asucc g b) in (arity g d0 u0 
TMP_49))))) in (let TMP_52 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_51 \def (plus i0 j) in (drop TMP_51 O d0 c0))))) in (let TMP_54 
\def (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_53 \def 
(asucc g b) in (arity g d0 u0 TMP_53))))) in (let TMP_55 \def (ex2_3 C T nat 
TMP_52 TMP_54) in (let TMP_79 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: nat).(\lambda (H5: (drop (plus i0 x2) O x0 d)).(\lambda (H6: (arity g x0 
x1 (asucc g b))).(let TMP_56 \def (plus i0 x2) in (let H_x \def 
(getl_drop_conf_rev TMP_56 x0 d H5 Abst c0 u i H0) in (let H7 \def H_x in 
(let TMP_58 \def (\lambda (c1: C).(let TMP_57 \def (plus i0 x2) in (drop 
TMP_57 O c1 c0))) in (let TMP_61 \def (\lambda (c1: C).(let TMP_59 \def (S i) 
in (let TMP_60 \def (plus i0 x2) in (drop TMP_59 TMP_60 c1 x0)))) in (let 
TMP_63 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_62 
\def (plus i0 j) in (drop TMP_62 O d0 c0))))) in (let TMP_65 \def (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_64 \def (asucc g b) in 
(arity g d0 u0 TMP_64))))) in (let TMP_66 \def (ex2_3 C T nat TMP_63 TMP_65) 
in (let TMP_78 \def (\lambda (x: C).(\lambda (H8: (drop (plus i0 x2) O x 
c0)).(\lambda (H9: (drop (S i) (plus i0 x2) x x0)).(let TMP_68 \def (\lambda 
(d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_67 \def (plus i0 j) in 
(drop TMP_67 O d0 c0))))) in (let TMP_70 \def (\lambda (d0: C).(\lambda (u0: 
T).(\lambda (_: nat).(let TMP_69 \def (asucc g b) in (arity g d0 u0 
TMP_69))))) in (let TMP_71 \def (S i) in (let TMP_72 \def (plus i0 x2) in 
(let TMP_73 \def (lift TMP_71 TMP_72 x1) in (let TMP_74 \def (asucc g b) in 
(let TMP_75 \def (S i) in (let TMP_76 \def (plus i0 x2) in (let TMP_77 \def 
(arity_lift g x0 x1 TMP_74 H6 x TMP_75 TMP_76 H9) in (ex2_3_intro C T nat 
TMP_68 TMP_70 x TMP_73 x2 H8 TMP_77))))))))))))) in (ex2_ind C TMP_58 TMP_61 
TMP_66 TMP_78 H7))))))))))))))) in (ex2_3_ind C T nat TMP_48 TMP_50 TMP_55 
TMP_79 H4))))))))))))))))))))) in (let TMP_106 \def (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (c0: C).(\lambda (u: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: ((\forall (i: nat).(\forall 
(b0: A).((aprem i a1 b0) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(arity g d u0 (asucc g b0))))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 (Bind b) u) t0 
a2)).(\lambda (H4: ((\forall (i: nat).(\forall (b0: A).((aprem i a2 b0) \to 
(ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus 
i j) O d (CHead c0 (Bind b) u))))) (\lambda (d: C).(\lambda (u0: T).(\lambda 
(_: nat).(arity g d u0 (asucc g b0))))))))))).(\lambda (i: nat).(\lambda (b0: 
A).(\lambda (H5: (aprem i a2 b0)).(let H_x \def (H4 i b0 H5) in (let H6 \def 
H_x in (let TMP_84 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_81 \def (plus i j) in (let TMP_82 \def (Bind b) in (let TMP_83 
\def (CHead c0 TMP_82 u) in (drop TMP_81 O d TMP_83))))))) in (let TMP_86 
\def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_85 \def 
(asucc g b0) in (arity g d u0 TMP_85))))) in (let TMP_88 \def (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(let TMP_87 \def (plus i j) in (drop 
TMP_87 O d c0))))) in (let TMP_90 \def (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(let TMP_89 \def (asucc g b0) in (arity g d u0 
TMP_89))))) in (let TMP_91 \def (ex2_3 C T nat TMP_88 TMP_90) in (let TMP_105 
\def (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H7: (drop 
(plus i x2) O x0 (CHead c0 (Bind b) u))).(\lambda (H8: (arity g x0 x1 (asucc 
g b0))).(let TMP_92 \def (plus i x2) in (let TMP_93 \def (S TMP_92) in (let 
TMP_94 \def (\lambda (n: nat).(drop n O x0 c0)) in (let TMP_95 \def (plus i 
x2) in (let TMP_96 \def (drop_S b x0 c0 u TMP_95 H7) in (let TMP_97 \def (S 
x2) in (let TMP_98 \def (plus i TMP_97) in (let TMP_99 \def (plus_n_Sm i x2) 
in (let H9 \def (eq_ind nat TMP_93 TMP_94 TMP_96 TMP_98 TMP_99) in (let 
TMP_101 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_100 
\def (plus i j) in (drop TMP_100 O d c0))))) in (let TMP_103 \def (\lambda 
(d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_102 \def (asucc g b0) in 
(arity g d u0 TMP_102))))) in (let TMP_104 \def (S x2) in (ex2_3_intro C T 
nat TMP_101 TMP_103 x0 x1 TMP_104 H9 H8)))))))))))))))))) in (ex2_3_ind C T 
nat TMP_84 TMP_86 TMP_91 TMP_105 H6))))))))))))))))))))))) in (let TMP_145 
\def (\lambda (c0: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (H0: (arity g 
c0 u (asucc g a1))).(\lambda (_: ((\forall (i: nat).(\forall (b: A).((aprem i 
(asucc g a1) b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda 
(j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (t0: 
T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 
a2)).(\lambda (H3: ((\forall (i: nat).(\forall (b: A).((aprem i a2 b) \to 
(ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus 
i j) O d (CHead c0 (Bind Abst) u))))) (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (i: 
nat).(\lambda (b: A).(\lambda (H4: (aprem i (AHead a1 a2) b)).(let TMP_111 
\def (\lambda (n: nat).((aprem n (AHead a1 a2) b) \to (let TMP_108 \def 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_107 \def (plus n 
j) in (drop TMP_107 O d c0))))) in (let TMP_110 \def (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(let TMP_109 \def (asucc g b) in (arity g d u0 
TMP_109))))) in (ex2_3 C T nat TMP_108 TMP_110))))) in (let TMP_123 \def 
(\lambda (H5: (aprem O (AHead a1 a2) b)).(let H_y \def (aprem_gen_head_O a1 
a2 b H5) in (let TMP_116 \def (\lambda (a0: A).(let TMP_113 \def (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(let TMP_112 \def (plus O j) in (drop 
TMP_112 O d c0))))) in (let TMP_115 \def (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(let TMP_114 \def (asucc g a0) in (arity g d u0 
TMP_114))))) in (ex2_3 C T nat TMP_113 TMP_115)))) in (let TMP_118 \def 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_117 \def (plus O 
j) in (drop TMP_117 O d c0))))) in (let TMP_120 \def (\lambda (d: C).(\lambda 
(u0: T).(\lambda (_: nat).(let TMP_119 \def (asucc g a1) in (arity g d u0 
TMP_119))))) in (let TMP_121 \def (drop_refl c0) in (let TMP_122 \def 
(ex2_3_intro C T nat TMP_118 TMP_120 c0 u O TMP_121 H0) in (eq_ind_r A a1 
TMP_116 TMP_122 b H_y)))))))) in (let TMP_144 \def (\lambda (i0: 
nat).(\lambda (_: (((aprem i0 (AHead a1 a2) b) \to (ex2_3 C T nat (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i0 j) O d c0)))) 
(\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g 
b))))))))).(\lambda (H5: (aprem (S i0) (AHead a1 a2) b)).(let H_y \def 
(aprem_gen_head_S a1 a2 b i0 H5) in (let H_x \def (H3 i0 b H_y) in (let H6 
\def H_x in (let TMP_127 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_124 \def (plus i0 j) in (let TMP_125 \def (Bind Abst) in (let 
TMP_126 \def (CHead c0 TMP_125 u) in (drop TMP_124 O d TMP_126))))))) in (let 
TMP_129 \def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_128 
\def (asucc g b) in (arity g d u0 TMP_128))))) in (let TMP_132 \def (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_130 \def (S i0) in (let 
TMP_131 \def (plus TMP_130 j) in (drop TMP_131 O d c0)))))) in (let TMP_134 
\def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_133 \def 
(asucc g b) in (arity g d u0 TMP_133))))) in (let TMP_135 \def (ex2_3 C T nat 
TMP_132 TMP_134) in (let TMP_143 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: nat).(\lambda (H7: (drop (plus i0 x2) O x0 (CHead c0 (Bind 
Abst) u))).(\lambda (H8: (arity g x0 x1 (asucc g b))).(let TMP_138 \def 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_136 \def (S i0) in 
(let TMP_137 \def (plus TMP_136 j) in (drop TMP_137 O d c0)))))) in (let 
TMP_140 \def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_139 
\def (asucc g b) in (arity g d u0 TMP_139))))) in (let TMP_141 \def (plus i0 
x2) in (let TMP_142 \def (drop_S Abst x0 c0 u TMP_141 H7) in (ex2_3_intro C T 
nat TMP_138 TMP_140 x0 x1 x2 TMP_142 H8)))))))))) in (ex2_3_ind C T nat 
TMP_127 TMP_129 TMP_135 TMP_143 H6))))))))))))) in (nat_ind TMP_111 TMP_123 
TMP_144 i H4)))))))))))))))) in (let TMP_236 \def (\lambda (c0: C).(\lambda 
(u: T).(\lambda (a1: A).(\lambda (_: (arity g c0 u a1)).(\lambda (_: 
((\forall (i: nat).(\forall (b: A).((aprem i a1 b) \to (ex2_3 C T nat 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d c0)))) 
(\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 (asucc g 
b))))))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g c0 t0 
(AHead a1 a2))).(\lambda (H3: ((\forall (i: nat).(\forall (b: A).((aprem i 
(AHead a1 a2) b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda 
(j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(arity g d u0 (asucc g b))))))))))).(\lambda (i: 
nat).(\lambda (b: A).(\lambda (H4: (aprem i a2 b)).(let TMP_146 \def (S i) in 
(let H_y \def (H3 TMP_146 b) in (let TMP_147 \def (aprem_succ a2 b i H4 a1) 
in (let H5 \def (H_y TMP_147) in (let TMP_150 \def (\lambda (d: C).(\lambda 
(_: T).(\lambda (j: nat).(let TMP_148 \def (plus i j) in (let TMP_149 \def (S 
TMP_148) in (drop TMP_149 O d c0)))))) in (let TMP_152 \def (\lambda (d: 
C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_151 \def (asucc g b) in (arity 
g d u0 TMP_151))))) in (let TMP_154 \def (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(let TMP_153 \def (plus i j) in (drop TMP_153 O d 
c0))))) in (let TMP_156 \def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: 
nat).(let TMP_155 \def (asucc g b) in (arity g d u0 TMP_155))))) in (let 
TMP_157 \def (ex2_3 C T nat TMP_154 TMP_156) in (let TMP_235 \def (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H6: (drop (S (plus i 
x2)) O x0 c0)).(\lambda (H7: (arity g x0 x1 (asucc g b))).(let TMP_162 \def 
(\lambda (c1: C).((drop (S (plus i x2)) O c1 c0) \to ((arity g c1 x1 (asucc g 
b)) \to (let TMP_159 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_158 \def (plus i j) in (drop TMP_158 O d c0))))) in (let 
TMP_161 \def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_160 
\def (asucc g b) in (arity g d u0 TMP_160))))) in (ex2_3 C T nat TMP_159 
TMP_161)))))) in (let TMP_186 \def (\lambda (n: nat).(\lambda (H8: (drop (S 
(plus i x2)) O (CSort n) c0)).(\lambda (_: (arity g (CSort n) x1 (asucc g 
b))).(let TMP_163 \def (CSort n) in (let TMP_164 \def (eq C c0 TMP_163) in 
(let TMP_165 \def (plus i x2) in (let TMP_166 \def (S TMP_165) in (let 
TMP_167 \def (eq nat TMP_166 O) in (let TMP_168 \def (eq nat O O) in (let 
TMP_170 \def (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_169 
\def (plus i j) in (drop TMP_169 O d c0))))) in (let TMP_172 \def (\lambda 
(d: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_171 \def (asucc g b) in 
(arity g d u0 TMP_171))))) in (let TMP_173 \def (ex2_3 C T nat TMP_170 
TMP_172) in (let TMP_182 \def (\lambda (_: (eq C c0 (CSort n))).(\lambda 
(H11: (eq nat (S (plus i x2)) O)).(\lambda (_: (eq nat O O)).(let TMP_174 
\def (plus i x2) in (let TMP_175 \def (S TMP_174) in (let TMP_176 \def 
(\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) \Rightarrow 
True])) in (let H13 \def (eq_ind nat TMP_175 TMP_176 I O H11) in (let TMP_178 
\def (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_177 \def 
(plus i j) in (drop TMP_177 O d c0))))) in (let TMP_180 \def (\lambda (d: 
C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_179 \def (asucc g b) in (arity 
g d u0 TMP_179))))) in (let TMP_181 \def (ex2_3 C T nat TMP_178 TMP_180) in 
(False_ind TMP_181 H13))))))))))) in (let TMP_183 \def (plus i x2) in (let 
TMP_184 \def (S TMP_183) in (let TMP_185 \def (drop_gen_sort n TMP_184 O c0 
H8) in (and3_ind TMP_164 TMP_167 TMP_168 TMP_173 TMP_182 
TMP_185))))))))))))))))) in (let TMP_234 \def (\lambda (d: C).(\lambda (IHd: 
(((drop (S (plus i x2)) O d c0) \to ((arity g d x1 (asucc g b)) \to (ex2_3 C 
T nat (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O 
d0 c0)))) (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d0 u0 
(asucc g b)))))))))).(\lambda (k: K).(\lambda (t1: T).(\lambda (H8: (drop (S 
(plus i x2)) O (CHead d k t1) c0)).(\lambda (H9: (arity g (CHead d k t1) x1 
(asucc g b))).(let TMP_191 \def (\lambda (k0: K).((arity g (CHead d k0 t1) x1 
(asucc g b)) \to ((drop (r k0 (plus i x2)) O d c0) \to (let TMP_188 \def 
(\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_187 \def (plus i 
j) in (drop TMP_187 O d0 c0))))) in (let TMP_190 \def (\lambda (d0: 
C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_189 \def (asucc g b) in (arity 
g d0 u0 TMP_189))))) in (ex2_3 C T nat TMP_188 TMP_190)))))) in (let TMP_211 
\def (\lambda (b0: B).(\lambda (H10: (arity g (CHead d (Bind b0) t1) x1 
(asucc g b))).(\lambda (H11: (drop (r (Bind b0) (plus i x2)) O d c0)).(let 
TMP_193 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_192 
\def (plus i j) in (drop TMP_192 O d0 c0))))) in (let TMP_195 \def (\lambda 
(d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_194 \def (asucc g b) in 
(arity g d0 u0 TMP_194))))) in (let TMP_196 \def (Bind b0) in (let TMP_197 
\def (CHead d TMP_196 t1) in (let TMP_198 \def (S x2) in (let TMP_199 \def 
(plus i x2) in (let TMP_200 \def (S TMP_199) in (let TMP_203 \def (\lambda 
(n: nat).(let TMP_201 \def (Bind b0) in (let TMP_202 \def (CHead d TMP_201 
t1) in (drop n O TMP_202 c0)))) in (let TMP_204 \def (Bind b0) in (let 
TMP_205 \def (plus i x2) in (let TMP_206 \def (drop_drop TMP_204 TMP_205 d c0 
H11 t1) in (let TMP_207 \def (S x2) in (let TMP_208 \def (plus i TMP_207) in 
(let TMP_209 \def (plus_n_Sm i x2) in (let TMP_210 \def (eq_ind nat TMP_200 
TMP_203 TMP_206 TMP_208 TMP_209) in (ex2_3_intro C T nat TMP_193 TMP_195 
TMP_197 x1 TMP_198 TMP_210 H10))))))))))))))))))) in (let TMP_231 \def 
(\lambda (f: F).(\lambda (H10: (arity g (CHead d (Flat f) t1) x1 (asucc g 
b))).(\lambda (H11: (drop (r (Flat f) (plus i x2)) O d c0)).(let TMP_212 \def 
(Flat f) in (let TMP_213 \def (CHead d TMP_212 t1) in (let TMP_214 \def 
(asucc g b) in (let TMP_215 \def (cimp_flat_sx f d t1) in (let TMP_216 \def 
(arity_cimp_conf g TMP_213 x1 TMP_214 H10 d TMP_215) in (let H12 \def (IHd 
H11 TMP_216) in (let TMP_218 \def (\lambda (d0: C).(\lambda (_: T).(\lambda 
(j: nat).(let TMP_217 \def (plus i j) in (drop TMP_217 O d0 c0))))) in (let 
TMP_220 \def (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_219 
\def (asucc g b) in (arity g d0 u0 TMP_219))))) in (let TMP_222 \def (\lambda 
(d0: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_221 \def (plus i j) in 
(drop TMP_221 O d0 c0))))) in (let TMP_224 \def (\lambda (d0: C).(\lambda 
(u0: T).(\lambda (_: nat).(let TMP_223 \def (asucc g b) in (arity g d0 u0 
TMP_223))))) in (let TMP_225 \def (ex2_3 C T nat TMP_222 TMP_224) in (let 
TMP_230 \def (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: nat).(\lambda 
(H13: (drop (plus i x5) O x3 c0)).(\lambda (H14: (arity g x3 x4 (asucc g 
b))).(let TMP_227 \def (\lambda (d0: C).(\lambda (_: T).(\lambda (j: 
nat).(let TMP_226 \def (plus i j) in (drop TMP_226 O d0 c0))))) in (let 
TMP_229 \def (\lambda (d0: C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_228 
\def (asucc g b) in (arity g d0 u0 TMP_228))))) in (ex2_3_intro C T nat 
TMP_227 TMP_229 x3 x4 x5 H13 H14)))))))) in (ex2_3_ind C T nat TMP_218 
TMP_220 TMP_225 TMP_230 H12)))))))))))))))) in (let TMP_232 \def (plus i x2) 
in (let TMP_233 \def (drop_gen_drop k d c0 t1 TMP_232 H8) in (K_ind TMP_191 
TMP_211 TMP_231 k H9 TMP_233)))))))))))) in (C_ind TMP_162 TMP_186 TMP_234 x0 
H6 H7))))))))) in (ex2_3_ind C T nat TMP_150 TMP_152 TMP_157 TMP_235 
H5))))))))))))))))))))))) in (let TMP_251 \def (\lambda (c0: C).(\lambda (u: 
T).(\lambda (a0: A).(\lambda (_: (arity g c0 u (asucc g a0))).(\lambda (_: 
((\forall (i: nat).(\forall (b: A).((aprem i (asucc g a0) b) \to (ex2_3 C T 
nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus i j) O d 
c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d u0 
(asucc g b))))))))))).(\lambda (t0: T).(\lambda (_: (arity g c0 t0 
a0)).(\lambda (H3: ((\forall (i: nat).(\forall (b: A).((aprem i a0 b) \to 
(ex2_3 C T nat (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(drop (plus 
i j) O d c0)))) (\lambda (d: C).(\lambda (u0: T).(\lambda (_: nat).(arity g d 
u0 (asucc g b))))))))))).(\lambda (i: nat).(\lambda (b: A).(\lambda (H4: 
(aprem i a0 b)).(let H_x \def (H3 i b H4) in (let H5 \def H_x in (let TMP_238 
\def (\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_237 \def 
(plus i j) in (drop TMP_237 O d c0))))) in (let TMP_240 \def (\lambda (d: 
C).(\lambda (u0: T).(\lambda (_: nat).(let TMP_239 \def (asucc g b) in (arity 
g d u0 TMP_239))))) in (let TMP_242 \def (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(let TMP_241 \def (plus i j) in (drop TMP_241 O d 
c0))))) in (let TMP_244 \def (\lambda (d: C).(\lambda (u0: T).(\lambda (_: 
nat).(let TMP_243 \def (asucc g b) in (arity g d u0 TMP_243))))) in (let 
TMP_245 \def (ex2_3 C T nat TMP_242 TMP_244) in (let TMP_250 \def (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: nat).(\lambda (H6: (drop (plus i x2) O 
x0 c0)).(\lambda (H7: (arity g x0 x1 (asucc g b))).(let TMP_247 \def (\lambda 
(d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_246 \def (plus i j) in 
(drop TMP_246 O d c0))))) in (let TMP_249 \def (\lambda (d: C).(\lambda (u0: 
T).(\lambda (_: nat).(let TMP_248 \def (asucc g b) in (arity g d u0 
TMP_248))))) in (ex2_3_intro C T nat TMP_247 TMP_249 x0 x1 x2 H6 H7)))))))) 
in (ex2_3_ind C T nat TMP_238 TMP_240 TMP_245 TMP_250 H5)))))))))))))))))))) 
in (let TMP_278 \def (\lambda (c0: C).(\lambda (t0: T).(\lambda (a1: 
A).(\lambda (_: (arity g c0 t0 a1)).(\lambda (H1: ((\forall (i: nat).(\forall 
(b: A).((aprem i a1 b) \to (ex2_3 C T nat (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(drop (plus i j) O d c0)))) (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: nat).(arity g d u (asucc g b))))))))))).(\lambda (a2: 
A).(\lambda (H2: (leq g a1 a2)).(\lambda (i: nat).(\lambda (b: A).(\lambda 
(H3: (aprem i a2 b)).(let H_x \def (aprem_repl g a1 a2 H2 i b H3) in (let H4 
\def H_x in (let TMP_252 \def (\lambda (b1: A).(leq g b1 b)) in (let TMP_253 
\def (\lambda (b1: A).(aprem i a1 b1)) in (let TMP_255 \def (\lambda (d: 
C).(\lambda (_: T).(\lambda (j: nat).(let TMP_254 \def (plus i j) in (drop 
TMP_254 O d c0))))) in (let TMP_257 \def (\lambda (d: C).(\lambda (u: 
T).(\lambda (_: nat).(let TMP_256 \def (asucc g b) in (arity g d u 
TMP_256))))) in (let TMP_258 \def (ex2_3 C T nat TMP_255 TMP_257) in (let 
TMP_277 \def (\lambda (x: A).(\lambda (H5: (leq g x b)).(\lambda (H6: (aprem 
i a1 x)).(let H_x0 \def (H1 i x H6) in (let H7 \def H_x0 in (let TMP_260 \def 
(\lambda (d: C).(\lambda (_: T).(\lambda (j: nat).(let TMP_259 \def (plus i 
j) in (drop TMP_259 O d c0))))) in (let TMP_262 \def (\lambda (d: C).(\lambda 
(u: T).(\lambda (_: nat).(let TMP_261 \def (asucc g x) in (arity g d u 
TMP_261))))) in (let TMP_264 \def (\lambda (d: C).(\lambda (_: T).(\lambda 
(j: nat).(let TMP_263 \def (plus i j) in (drop TMP_263 O d c0))))) in (let 
TMP_266 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: nat).(let TMP_265 
\def (asucc g b) in (arity g d u TMP_265))))) in (let TMP_267 \def (ex2_3 C T 
nat TMP_264 TMP_266) in (let TMP_276 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: nat).(\lambda (H8: (drop (plus i x2) O x0 c0)).(\lambda (H9: 
(arity g x0 x1 (asucc g x))).(let TMP_269 \def (\lambda (d: C).(\lambda (_: 
T).(\lambda (j: nat).(let TMP_268 \def (plus i j) in (drop TMP_268 O d 
c0))))) in (let TMP_271 \def (\lambda (d: C).(\lambda (u: T).(\lambda (_: 
nat).(let TMP_270 \def (asucc g b) in (arity g d u TMP_270))))) in (let 
TMP_272 \def (asucc g x) in (let TMP_273 \def (asucc g b) in (let TMP_274 
\def (asucc_repl g x b H5) in (let TMP_275 \def (arity_repl g x0 x1 TMP_272 
H9 TMP_273 TMP_274) in (ex2_3_intro C T nat TMP_269 TMP_271 x0 x1 x2 H8 
TMP_275)))))))))))) in (ex2_3_ind C T nat TMP_260 TMP_262 TMP_267 TMP_276 
H7)))))))))))) in (ex2_ind A TMP_252 TMP_253 TMP_258 TMP_277 
H4))))))))))))))))))) in (arity_ind g TMP_5 TMP_11 TMP_45 TMP_80 TMP_106 
TMP_145 TMP_236 TMP_251 TMP_278 c t a H)))))))))))))).

