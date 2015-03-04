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

include "basic_1/nf2/pr3.ma".

include "basic_1/iso/props.ma".

theorem nf2_iso_appls_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (vs: 
TList).(\forall (u: T).((pr3 c (THeads (Flat Appl) vs (TLRef i)) u) \to (iso 
(THeads (Flat Appl) vs (TLRef i)) u))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(vs: TList).(let TMP_4 \def (\lambda (t: TList).(\forall (u: T).((pr3 c 
(THeads (Flat Appl) t (TLRef i)) u) \to (let TMP_1 \def (Flat Appl) in (let 
TMP_2 \def (TLRef i) in (let TMP_3 \def (THeads TMP_1 t TMP_2) in (iso TMP_3 
u))))))) in (let TMP_14 \def (\lambda (u: T).(\lambda (H0: (pr3 c (TLRef i) 
u)).(let TMP_5 \def (TLRef i) in (let H_y \def (nf2_pr3_unfold c TMP_5 u H0 
H) in (let TMP_7 \def (\lambda (t: T).(let TMP_6 \def (TLRef i) in (pr3 c 
TMP_6 t))) in (let TMP_8 \def (TLRef i) in (let H1 \def (eq_ind_r T u TMP_7 
H0 TMP_8 H_y) in (let TMP_9 \def (TLRef i) in (let TMP_11 \def (\lambda (t: 
T).(let TMP_10 \def (TLRef i) in (iso TMP_10 t))) in (let TMP_12 \def (TLRef 
i) in (let TMP_13 \def (iso_refl TMP_12) in (eq_ind T TMP_9 TMP_11 TMP_13 u 
H_y)))))))))))) in (let TMP_162 \def (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (H0: ((\forall (u: T).((pr3 c (THeads (Flat Appl) t0 (TLRef 
i)) u) \to (iso (THeads (Flat Appl) t0 (TLRef i)) u))))).(\lambda (u: 
T).(\lambda (H1: (pr3 c (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef 
i))) u)).(let TMP_15 \def (Flat Appl) in (let TMP_16 \def (TLRef i) in (let 
TMP_17 \def (THeads TMP_15 t0 TMP_16) in (let H2 \def (pr3_gen_appl c t 
TMP_17 u H1) in (let TMP_20 \def (\lambda (u2: T).(\lambda (t2: T).(let 
TMP_18 \def (Flat Appl) in (let TMP_19 \def (THead TMP_18 u2 t2) in (eq T u 
TMP_19))))) in (let TMP_21 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c t 
u2))) in (let TMP_25 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_22 \def 
(Flat Appl) in (let TMP_23 \def (TLRef i) in (let TMP_24 \def (THeads TMP_22 
t0 TMP_23) in (pr3 c TMP_24 t2)))))) in (let TMP_26 \def (ex3_2 T T TMP_20 
TMP_21 TMP_25) in (let TMP_29 \def (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (t2: T).(let TMP_27 \def (Bind Abbr) in (let TMP_28 \def 
(THead TMP_27 u2 t2) in (pr3 c TMP_28 u))))))) in (let TMP_30 \def (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))) in 
(let TMP_36 \def (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(let TMP_31 \def (Flat Appl) in (let TMP_32 \def (TLRef i) in (let 
TMP_33 \def (THeads TMP_31 t0 TMP_32) in (let TMP_34 \def (Bind Abst) in (let 
TMP_35 \def (THead TMP_34 y1 z1) in (pr3 c TMP_33 TMP_35)))))))))) in (let 
TMP_39 \def (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: 
T).(\forall (b: B).(\forall (u0: T).(let TMP_37 \def (Bind b) in (let TMP_38 
\def (CHead c TMP_37 u0) in (pr3 TMP_38 z1 t2))))))))) in (let TMP_40 \def 
(ex4_4 T T T T TMP_29 TMP_30 TMP_36 TMP_39) in (let TMP_42 \def (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(let TMP_41 \def (eq B b Abst) in (not TMP_41)))))))) in (let TMP_48 
\def (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(let TMP_43 \def (Flat Appl) in (let 
TMP_44 \def (TLRef i) in (let TMP_45 \def (THeads TMP_43 t0 TMP_44) in (let 
TMP_46 \def (Bind b) in (let TMP_47 \def (THead TMP_46 y1 z1) in (pr3 c 
TMP_45 TMP_47)))))))))))) in (let TMP_55 \def (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(let 
TMP_49 \def (Bind b) in (let TMP_50 \def (Flat Appl) in (let TMP_51 \def (S 
O) in (let TMP_52 \def (lift TMP_51 O u2) in (let TMP_53 \def (THead TMP_50 
TMP_52 z2) in (let TMP_54 \def (THead TMP_49 y2 TMP_53) in (pr3 c TMP_54 
u))))))))))))) in (let TMP_56 \def (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) in 
(let TMP_57 \def (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 y2))))))) in (let TMP_60 
\def (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(let TMP_58 \def (Bind b) in (let TMP_59 
\def (CHead c TMP_58 y2) in (pr3 TMP_59 z1 z2))))))))) in (let TMP_61 \def 
(ex6_6 B T T T T T TMP_42 TMP_48 TMP_55 TMP_56 TMP_57 TMP_60) in (let TMP_62 
\def (Flat Appl) in (let TMP_63 \def (Flat Appl) in (let TMP_64 \def (TLRef 
i) in (let TMP_65 \def (THeads TMP_63 t0 TMP_64) in (let TMP_66 \def (THead 
TMP_62 t TMP_65) in (let TMP_67 \def (iso TMP_66 u) in (let TMP_96 \def 
(\lambda (H3: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T u (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) 
t2))))).(let TMP_70 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_68 \def 
(Flat Appl) in (let TMP_69 \def (THead TMP_68 u2 t2) in (eq T u TMP_69))))) 
in (let TMP_71 \def (\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))) in (let 
TMP_75 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_72 \def (Flat Appl) in 
(let TMP_73 \def (TLRef i) in (let TMP_74 \def (THeads TMP_72 t0 TMP_73) in 
(pr3 c TMP_74 t2)))))) in (let TMP_76 \def (Flat Appl) in (let TMP_77 \def 
(Flat Appl) in (let TMP_78 \def (TLRef i) in (let TMP_79 \def (THeads TMP_77 
t0 TMP_78) in (let TMP_80 \def (THead TMP_76 t TMP_79) in (let TMP_81 \def 
(iso TMP_80 u) in (let TMP_95 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H4: (eq T u (THead (Flat Appl) x0 x1))).(\lambda (_: (pr3 c t x0)).(\lambda 
(_: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) x1)).(let TMP_82 \def (Flat 
Appl) in (let TMP_83 \def (THead TMP_82 x0 x1) in (let TMP_89 \def (\lambda 
(t1: T).(let TMP_84 \def (Flat Appl) in (let TMP_85 \def (Flat Appl) in (let 
TMP_86 \def (TLRef i) in (let TMP_87 \def (THeads TMP_85 t0 TMP_86) in (let 
TMP_88 \def (THead TMP_84 t TMP_87) in (iso TMP_88 t1))))))) in (let TMP_90 
\def (Flat Appl) in (let TMP_91 \def (TLRef i) in (let TMP_92 \def (THeads 
TMP_90 t0 TMP_91) in (let TMP_93 \def (Flat Appl) in (let TMP_94 \def 
(iso_head t x0 TMP_92 x1 TMP_93) in (eq_ind_r T TMP_83 TMP_89 TMP_94 u 
H4)))))))))))))) in (ex3_2_ind T T TMP_70 TMP_71 TMP_75 TMP_81 TMP_95 
H3)))))))))))) in (let TMP_125 \def (\lambda (H3: (ex4_4 T T T T (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(pr3 c (THead (Bind 
Abbr) u2 t2) u))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c t u2))))) (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t2: T).(\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) u0) z1 
t2))))))))).(let TMP_99 \def (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(let TMP_97 \def (Bind Abbr) in (let TMP_98 \def (THead 
TMP_97 u2 t2) in (pr3 c TMP_98 u))))))) in (let TMP_100 \def (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))) in (let 
TMP_106 \def (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(let TMP_101 \def (Flat Appl) in (let TMP_102 \def (TLRef i) in (let 
TMP_103 \def (THeads TMP_101 t0 TMP_102) in (let TMP_104 \def (Bind Abst) in 
(let TMP_105 \def (THead TMP_104 y1 z1) in (pr3 c TMP_103 TMP_105)))))))))) 
in (let TMP_109 \def (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u0: T).(let TMP_107 \def (Bind 
b) in (let TMP_108 \def (CHead c TMP_107 u0) in (pr3 TMP_108 z1 t2))))))))) 
in (let TMP_110 \def (Flat Appl) in (let TMP_111 \def (Flat Appl) in (let 
TMP_112 \def (TLRef i) in (let TMP_113 \def (THeads TMP_111 t0 TMP_112) in 
(let TMP_114 \def (THead TMP_110 t TMP_113) in (let TMP_115 \def (iso TMP_114 
u) in (let TMP_124 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (_: (pr3 c (THead (Bind Abbr) x2 x3) 
u)).(\lambda (_: (pr3 c t x2)).(\lambda (H6: (pr3 c (THeads (Flat Appl) t0 
(TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (_: ((\forall (b: B).(\forall 
(u0: T).(pr3 (CHead c (Bind b) u0) x1 x3))))).(let TMP_116 \def (Bind Abst) 
in (let TMP_117 \def (THead TMP_116 x0 x1) in (let H_y \def (H0 TMP_117 H6) 
in (let TMP_118 \def (Flat Appl) in (let TMP_119 \def (Flat Appl) in (let 
TMP_120 \def (TLRef i) in (let TMP_121 \def (THeads TMP_119 t0 TMP_120) in 
(let TMP_122 \def (THead TMP_118 t TMP_121) in (let TMP_123 \def (iso TMP_122 
u) in (iso_flats_lref_bind_false Appl Abst i x0 x1 t0 H_y 
TMP_123)))))))))))))))))) in (ex4_4_ind T T T T TMP_99 TMP_100 TMP_106 
TMP_109 TMP_115 TMP_124 H3))))))))))))) in (let TMP_161 \def (\lambda (H3: 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(pr3 c (THead (Bind b) y2 (THead (Flat Appl) (lift 
(S O) O u2) z2)) u))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr3 c t u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr3 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr3 
(CHead c (Bind b) y2) z1 z2))))))))).(let TMP_127 \def (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(let TMP_126 \def (eq B b Abst) in (not TMP_126)))))))) in (let 
TMP_133 \def (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(let TMP_128 \def (Flat Appl) in (let 
TMP_129 \def (TLRef i) in (let TMP_130 \def (THeads TMP_128 t0 TMP_129) in 
(let TMP_131 \def (Bind b) in (let TMP_132 \def (THead TMP_131 y1 z1) in (pr3 
c TMP_130 TMP_132)))))))))))) in (let TMP_140 \def (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: 
T).(let TMP_134 \def (Bind b) in (let TMP_135 \def (Flat Appl) in (let 
TMP_136 \def (S O) in (let TMP_137 \def (lift TMP_136 O u2) in (let TMP_138 
\def (THead TMP_135 TMP_137 z2) in (let TMP_139 \def (THead TMP_134 y2 
TMP_138) in (pr3 c TMP_139 u))))))))))))) in (let TMP_141 \def (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr3 c t u2))))))) in (let TMP_142 \def (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr3 c y1 
y2))))))) in (let TMP_145 \def (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(let TMP_143 \def (Bind 
b) in (let TMP_144 \def (CHead c TMP_143 y2) in (pr3 TMP_144 z1 z2))))))))) 
in (let TMP_146 \def (Flat Appl) in (let TMP_147 \def (Flat Appl) in (let 
TMP_148 \def (TLRef i) in (let TMP_149 \def (THeads TMP_147 t0 TMP_148) in 
(let TMP_150 \def (THead TMP_146 t TMP_149) in (let TMP_151 \def (iso TMP_150 
u) in (let TMP_160 \def (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B 
x0 Abst))).(\lambda (H5: (pr3 c (THeads (Flat Appl) t0 (TLRef i)) (THead 
(Bind x0) x1 x2))).(\lambda (_: (pr3 c (THead (Bind x0) x5 (THead (Flat Appl) 
(lift (S O) O x4) x3)) u)).(\lambda (_: (pr3 c t x4)).(\lambda (_: (pr3 c x1 
x5)).(\lambda (_: (pr3 (CHead c (Bind x0) x5) x2 x3)).(let TMP_152 \def (Bind 
x0) in (let TMP_153 \def (THead TMP_152 x1 x2) in (let H_y \def (H0 TMP_153 
H5) in (let TMP_154 \def (Flat Appl) in (let TMP_155 \def (Flat Appl) in (let 
TMP_156 \def (TLRef i) in (let TMP_157 \def (THeads TMP_155 t0 TMP_156) in 
(let TMP_158 \def (THead TMP_154 t TMP_157) in (let TMP_159 \def (iso TMP_158 
u) in (iso_flats_lref_bind_false Appl x0 i x1 x2 t0 H_y 
TMP_159)))))))))))))))))))))) in (ex6_6_ind B T T T T T TMP_127 TMP_133 
TMP_140 TMP_141 TMP_142 TMP_145 TMP_151 TMP_160 H3))))))))))))))) in (or3_ind 
TMP_26 TMP_40 TMP_61 TMP_67 TMP_96 TMP_125 TMP_161 
H2))))))))))))))))))))))))))))))))))) in (TList_ind TMP_4 TMP_14 TMP_162 
vs))))))).

