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

include "basic_1/ty3/arity_props.ma".

include "basic_1/nf2/fwd.ma".

theorem pc3_dec:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (pc3 c 
u1 u2) ((pc3 c u1 u2) \to False)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(let H_y \def (ty3_sn3 g c u1 t1 H) in (let H_y0 \def (ty3_sn3 g c u2 
t2 H0) in (let H_x \def (nf2_sn3 c u1 H_y) in (let H1 \def H_x in (let TMP_1 
\def (\lambda (u: T).(pr3 c u1 u)) in (let TMP_2 \def (\lambda (u: T).(nf2 c 
u)) in (let TMP_3 \def (pc3 c u1 u2) in (let TMP_4 \def ((pc3 c u1 u2) \to 
False) in (let TMP_5 \def (or TMP_3 TMP_4) in (let TMP_36 \def (\lambda (x: 
T).(\lambda (H2: (pr3 c u1 x)).(\lambda (H3: (nf2 c x)).(let H_x0 \def 
(nf2_sn3 c u2 H_y0) in (let H4 \def H_x0 in (let TMP_6 \def (\lambda (u: 
T).(pr3 c u2 u)) in (let TMP_7 \def (\lambda (u: T).(nf2 c u)) in (let TMP_8 
\def (pc3 c u1 u2) in (let TMP_9 \def ((pc3 c u1 u2) \to False) in (let 
TMP_10 \def (or TMP_8 TMP_9) in (let TMP_35 \def (\lambda (x0: T).(\lambda 
(H5: (pr3 c u2 x0)).(\lambda (H6: (nf2 c x0)).(let H_x1 \def (term_dec x x0) 
in (let H7 \def H_x1 in (let TMP_11 \def (eq T x x0) in (let TMP_12 \def ((eq 
T x x0) \to (\forall (P: Prop).P)) in (let TMP_13 \def (pc3 c u1 u2) in (let 
TMP_14 \def ((pc3 c u1 u2) \to False) in (let TMP_15 \def (or TMP_13 TMP_14) 
in (let TMP_21 \def (\lambda (H8: (eq T x x0)).(let TMP_16 \def (\lambda (t: 
T).(nf2 c t)) in (let H9 \def (eq_ind_r T x0 TMP_16 H6 x H8) in (let TMP_17 
\def (\lambda (t: T).(pr3 c u2 t)) in (let H10 \def (eq_ind_r T x0 TMP_17 H5 
x H8) in (let TMP_18 \def (pc3 c u1 u2) in (let TMP_19 \def ((pc3 c u1 u2) 
\to False) in (let TMP_20 \def (pc3_pr3_t c u1 x H2 u2 H10) in (or_introl 
TMP_18 TMP_19 TMP_20))))))))) in (let TMP_34 \def (\lambda (H8: (((eq T x x0) 
\to (\forall (P: Prop).P)))).(let TMP_22 \def (pc3 c u1 u2) in (let TMP_23 
\def ((pc3 c u1 u2) \to False) in (let TMP_33 \def (\lambda (H9: (pc3 c u1 
u2)).(let H10 \def H9 in (let TMP_24 \def (\lambda (t: T).(pr3 c u1 t)) in 
(let TMP_25 \def (\lambda (t: T).(pr3 c u2 t)) in (let TMP_32 \def (\lambda 
(x1: T).(\lambda (H11: (pr3 c u1 x1)).(\lambda (H12: (pr3 c u2 x1)).(let H_x2 
\def (pr3_confluence c u2 x0 H5 x1 H12) in (let H13 \def H_x2 in (let TMP_26 
\def (\lambda (t: T).(pr3 c x0 t)) in (let TMP_27 \def (\lambda (t: T).(pr3 c 
x1 t)) in (let TMP_31 \def (\lambda (x2: T).(\lambda (H14: (pr3 c x0 
x2)).(\lambda (H15: (pr3 c x1 x2)).(let H_y1 \def (nf2_pr3_unfold c x0 x2 H14 
H6) in (let TMP_28 \def (\lambda (t: T).(pr3 c x1 t)) in (let H16 \def 
(eq_ind_r T x2 TMP_28 H15 x0 H_y1) in (let H17 \def (nf2_pr3_confluence c x 
H3 x0 H6 u1 H2) in (let TMP_29 \def (pr3_t x1 u1 c H11 x0 H16) in (let TMP_30 
\def (H17 TMP_29) in (H8 TMP_30 False)))))))))) in (ex2_ind T TMP_26 TMP_27 
False TMP_31 H13))))))))) in (ex2_ind T TMP_24 TMP_25 False TMP_32 H10)))))) 
in (or_intror TMP_22 TMP_23 TMP_33))))) in (or_ind TMP_11 TMP_12 TMP_15 
TMP_21 TMP_34 H7))))))))))))) in (ex2_ind T TMP_6 TMP_7 TMP_10 TMP_35 
H4)))))))))))) in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_36 H1)))))))))))))))))).

theorem pc3_abst_dec:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (t1: T).((ty3 g c 
u1 t1) \to (\forall (u2: T).(\forall (t2: T).((ty3 g c u2 t2) \to (or (ex4_2 
T T (\lambda (u: T).(\lambda (_: T).(pc3 c u1 (THead (Bind Abst) u2 u)))) 
(\lambda (u: T).(\lambda (v2: T).(ty3 g c (THead (Bind Abst) v2 u) t1))) 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) (\lambda (_: T).(\lambda 
(v2: T).(nf2 c v2)))) (\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) 
\to False))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(H: (ty3 g c u1 t1)).(\lambda (u2: T).(\lambda (t2: T).(\lambda (H0: (ty3 g c 
u2 t2)).(let H1 \def (ty3_sn3 g c u1 t1 H) in (let H2 \def (ty3_sn3 g c u2 t2 
H0) in (let H_x \def (nf2_sn3 c u1 H1) in (let H3 \def H_x in (let TMP_1 \def 
(\lambda (u: T).(pr3 c u1 u)) in (let TMP_2 \def (\lambda (u: T).(nf2 c u)) 
in (let TMP_5 \def (\lambda (u: T).(\lambda (_: T).(let TMP_3 \def (Bind 
Abst) in (let TMP_4 \def (THead TMP_3 u2 u) in (pc3 c u1 TMP_4))))) in (let 
TMP_8 \def (\lambda (u: T).(\lambda (v2: T).(let TMP_6 \def (Bind Abst) in 
(let TMP_7 \def (THead TMP_6 v2 u) in (ty3 g c TMP_7 t1))))) in (let TMP_9 
\def (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) in (let TMP_10 \def 
(\lambda (_: T).(\lambda (v2: T).(nf2 c v2))) in (let TMP_11 \def (ex4_2 T T 
TMP_5 TMP_8 TMP_9 TMP_10) in (let TMP_12 \def (\forall (u: T).((pc3 c u1 
(THead (Bind Abst) u2 u)) \to False)) in (let TMP_13 \def (or TMP_11 TMP_12) 
in (let TMP_162 \def (\lambda (x: T).(\lambda (H4: (pr3 c u1 x)).(\lambda 
(H5: (nf2 c x)).(let H_x0 \def (nf2_sn3 c u2 H2) in (let H6 \def H_x0 in (let 
TMP_14 \def (\lambda (u: T).(pr3 c u2 u)) in (let TMP_15 \def (\lambda (u: 
T).(nf2 c u)) in (let TMP_18 \def (\lambda (u: T).(\lambda (_: T).(let TMP_16 
\def (Bind Abst) in (let TMP_17 \def (THead TMP_16 u2 u) in (pc3 c u1 
TMP_17))))) in (let TMP_21 \def (\lambda (u: T).(\lambda (v2: T).(let TMP_19 
\def (Bind Abst) in (let TMP_20 \def (THead TMP_19 v2 u) in (ty3 g c TMP_20 
t1))))) in (let TMP_22 \def (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) 
in (let TMP_23 \def (\lambda (_: T).(\lambda (v2: T).(nf2 c v2))) in (let 
TMP_24 \def (ex4_2 T T TMP_18 TMP_21 TMP_22 TMP_23) in (let TMP_25 \def 
(\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) \to False)) in (let 
TMP_26 \def (or TMP_24 TMP_25) in (let TMP_161 \def (\lambda (x0: T).(\lambda 
(H7: (pr3 c u2 x0)).(\lambda (H8: (nf2 c x0)).(let H_x1 \def (abst_dec x x0) 
in (let H9 \def H_x1 in (let TMP_29 \def (\lambda (t: T).(let TMP_27 \def 
(Bind Abst) in (let TMP_28 \def (THead TMP_27 x0 t) in (eq T x TMP_28)))) in 
(let TMP_30 \def (ex T TMP_29) in (let TMP_31 \def (\forall (t: T).((eq T x 
(THead (Bind Abst) x0 t)) \to (\forall (P: Prop).P))) in (let TMP_34 \def 
(\lambda (u: T).(\lambda (_: T).(let TMP_32 \def (Bind Abst) in (let TMP_33 
\def (THead TMP_32 u2 u) in (pc3 c u1 TMP_33))))) in (let TMP_37 \def 
(\lambda (u: T).(\lambda (v2: T).(let TMP_35 \def (Bind Abst) in (let TMP_36 
\def (THead TMP_35 v2 u) in (ty3 g c TMP_36 t1))))) in (let TMP_38 \def 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) in (let TMP_39 \def (\lambda 
(_: T).(\lambda (v2: T).(nf2 c v2))) in (let TMP_40 \def (ex4_2 T T TMP_34 
TMP_37 TMP_38 TMP_39) in (let TMP_41 \def (\forall (u: T).((pc3 c u1 (THead 
(Bind Abst) u2 u)) \to False)) in (let TMP_42 \def (or TMP_40 TMP_41) in (let 
TMP_95 \def (\lambda (H10: (ex T (\lambda (t: T).(eq T x (THead (Bind Abst) 
x0 t))))).(let TMP_45 \def (\lambda (t: T).(let TMP_43 \def (Bind Abst) in 
(let TMP_44 \def (THead TMP_43 x0 t) in (eq T x TMP_44)))) in (let TMP_48 
\def (\lambda (u: T).(\lambda (_: T).(let TMP_46 \def (Bind Abst) in (let 
TMP_47 \def (THead TMP_46 u2 u) in (pc3 c u1 TMP_47))))) in (let TMP_51 \def 
(\lambda (u: T).(\lambda (v2: T).(let TMP_49 \def (Bind Abst) in (let TMP_50 
\def (THead TMP_49 v2 u) in (ty3 g c TMP_50 t1))))) in (let TMP_52 \def 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) in (let TMP_53 \def (\lambda 
(_: T).(\lambda (v2: T).(nf2 c v2))) in (let TMP_54 \def (ex4_2 T T TMP_48 
TMP_51 TMP_52 TMP_53) in (let TMP_55 \def (\forall (u: T).((pc3 c u1 (THead 
(Bind Abst) u2 u)) \to False)) in (let TMP_56 \def (or TMP_54 TMP_55) in (let 
TMP_94 \def (\lambda (x1: T).(\lambda (H11: (eq T x (THead (Bind Abst) x0 
x1))).(let TMP_57 \def (\lambda (t: T).(nf2 c t)) in (let TMP_58 \def (Bind 
Abst) in (let TMP_59 \def (THead TMP_58 x0 x1) in (let H12 \def (eq_ind T x 
TMP_57 H5 TMP_59 H11) in (let TMP_60 \def (\lambda (t: T).(pr3 c u1 t)) in 
(let TMP_61 \def (Bind Abst) in (let TMP_62 \def (THead TMP_61 x0 x1) in (let 
H13 \def (eq_ind T x TMP_60 H4 TMP_62 H11) in (let TMP_63 \def (Bind Abst) in 
(let TMP_64 \def (THead TMP_63 x0 x1) in (let H_y \def (ty3_sred_pr3 c u1 
TMP_64 H13 g t1 H) in (let TMP_67 \def (\lambda (u: T).(\lambda (_: T).(let 
TMP_65 \def (Bind Abst) in (let TMP_66 \def (THead TMP_65 u2 u) in (pc3 c u1 
TMP_66))))) in (let TMP_70 \def (\lambda (u: T).(\lambda (v2: T).(let TMP_68 
\def (Bind Abst) in (let TMP_69 \def (THead TMP_68 v2 u) in (ty3 g c TMP_69 
t1))))) in (let TMP_71 \def (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) 
in (let TMP_72 \def (\lambda (_: T).(\lambda (v2: T).(nf2 c v2))) in (let 
TMP_73 \def (ex4_2 T T TMP_67 TMP_70 TMP_71 TMP_72) in (let TMP_74 \def 
(\forall (u: T).((pc3 c u1 (THead (Bind Abst) u2 u)) \to False)) in (let 
TMP_77 \def (\lambda (u: T).(\lambda (_: T).(let TMP_75 \def (Bind Abst) in 
(let TMP_76 \def (THead TMP_75 u2 u) in (pc3 c u1 TMP_76))))) in (let TMP_80 
\def (\lambda (u: T).(\lambda (v2: T).(let TMP_78 \def (Bind Abst) in (let 
TMP_79 \def (THead TMP_78 v2 u) in (ty3 g c TMP_79 t1))))) in (let TMP_81 
\def (\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) in (let TMP_82 \def 
(\lambda (_: T).(\lambda (v2: T).(nf2 c v2))) in (let TMP_83 \def (Bind Abst) 
in (let TMP_84 \def (THead TMP_83 x0 x1) in (let TMP_85 \def (Bind Abst) in 
(let TMP_86 \def (THead TMP_85 u2 x1) in (let TMP_87 \def (Bind Abst) in (let 
TMP_88 \def (Bind Abst) in (let TMP_89 \def (CHead c TMP_88 x0) in (let 
TMP_90 \def (pr3_refl TMP_89 x1) in (let TMP_91 \def (pr3_head_12 c u2 x0 H7 
TMP_87 x1 x1 TMP_90) in (let TMP_92 \def (pc3_pr3_t c u1 TMP_84 H13 TMP_86 
TMP_91) in (let TMP_93 \def (ex4_2_intro T T TMP_77 TMP_80 TMP_81 TMP_82 x1 
x0 TMP_92 H_y H7 H8) in (or_introl TMP_73 TMP_74 
TMP_93))))))))))))))))))))))))))))))))))) in (ex_ind T TMP_45 TMP_56 TMP_94 
H10))))))))))) in (let TMP_160 \def (\lambda (H10: ((\forall (t: T).((eq T x 
(THead (Bind Abst) x0 t)) \to (\forall (P: Prop).P))))).(let TMP_98 \def 
(\lambda (u: T).(\lambda (_: T).(let TMP_96 \def (Bind Abst) in (let TMP_97 
\def (THead TMP_96 u2 u) in (pc3 c u1 TMP_97))))) in (let TMP_101 \def 
(\lambda (u: T).(\lambda (v2: T).(let TMP_99 \def (Bind Abst) in (let TMP_100 
\def (THead TMP_99 v2 u) in (ty3 g c TMP_100 t1))))) in (let TMP_102 \def 
(\lambda (_: T).(\lambda (v2: T).(pr3 c u2 v2))) in (let TMP_103 \def 
(\lambda (_: T).(\lambda (v2: T).(nf2 c v2))) in (let TMP_104 \def (ex4_2 T T 
TMP_98 TMP_101 TMP_102 TMP_103) in (let TMP_105 \def (\forall (u: T).((pc3 c 
u1 (THead (Bind Abst) u2 u)) \to False)) in (let TMP_159 \def (\lambda (u: 
T).(\lambda (H11: (pc3 c u1 (THead (Bind Abst) u2 u))).(let H12 \def H11 in 
(let TMP_106 \def (\lambda (t: T).(pr3 c u1 t)) in (let TMP_109 \def (\lambda 
(t: T).(let TMP_107 \def (Bind Abst) in (let TMP_108 \def (THead TMP_107 u2 
u) in (pr3 c TMP_108 t)))) in (let TMP_158 \def (\lambda (x1: T).(\lambda 
(H13: (pr3 c u1 x1)).(\lambda (H14: (pr3 c (THead (Bind Abst) u2 u) x1)).(let 
TMP_110 \def (\lambda (t: T).(pr3 c x1 t)) in (let TMP_111 \def (\lambda (t: 
T).(pr3 c x t)) in (let TMP_156 \def (\lambda (x2: T).(\lambda (H15: (pr3 c 
x1 x2)).(\lambda (H16: (pr3 c x x2)).(let H_y \def (nf2_pr3_unfold c x x2 H16 
H5) in (let TMP_112 \def (\lambda (t: T).(pr3 c x1 t)) in (let H17 \def 
(eq_ind_r T x2 TMP_112 H15 x H_y) in (let H18 \def (pr3_gen_abst c u2 u x1 
H14) in (let TMP_115 \def (\lambda (u3: T).(\lambda (t3: T).(let TMP_113 \def 
(Bind Abst) in (let TMP_114 \def (THead TMP_113 u3 t3) in (eq T x1 
TMP_114))))) in (let TMP_116 \def (\lambda (u3: T).(\lambda (_: T).(pr3 c u2 
u3))) in (let TMP_119 \def (\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u0: T).(let TMP_117 \def (Bind b) in (let TMP_118 \def (CHead c 
TMP_117 u0) in (pr3 TMP_118 u t3))))))) in (let TMP_155 \def (\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H19: (eq T x1 (THead (Bind Abst) x3 
x4))).(\lambda (H20: (pr3 c u2 x3)).(\lambda (_: ((\forall (b: B).(\forall 
(u0: T).(pr3 (CHead c (Bind b) u0) u x4))))).(let TMP_120 \def (\lambda (t: 
T).(pr3 c t x)) in (let TMP_121 \def (Bind Abst) in (let TMP_122 \def (THead 
TMP_121 x3 x4) in (let H22 \def (eq_ind T x1 TMP_120 H17 TMP_122 H19) in (let 
H23 \def (pr3_gen_abst c x3 x4 x H22) in (let TMP_125 \def (\lambda (u3: 
T).(\lambda (t3: T).(let TMP_123 \def (Bind Abst) in (let TMP_124 \def (THead 
TMP_123 u3 t3) in (eq T x TMP_124))))) in (let TMP_126 \def (\lambda (u3: 
T).(\lambda (_: T).(pr3 c x3 u3))) in (let TMP_129 \def (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(let TMP_127 \def (Bind 
b) in (let TMP_128 \def (CHead c TMP_127 u0) in (pr3 TMP_128 x4 t3))))))) in 
(let TMP_154 \def (\lambda (x5: T).(\lambda (x6: T).(\lambda (H24: (eq T x 
(THead (Bind Abst) x5 x6))).(\lambda (H25: (pr3 c x3 x5)).(\lambda (_: 
((\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) u0) x4 x6))))).(let 
TMP_130 \def (\lambda (t: T).(\forall (t0: T).((eq T t (THead (Bind Abst) x0 
t0)) \to (\forall (P: Prop).P)))) in (let TMP_131 \def (Bind Abst) in (let 
TMP_132 \def (THead TMP_131 x5 x6) in (let H27 \def (eq_ind T x TMP_130 H10 
TMP_132 H24) in (let TMP_133 \def (\lambda (t: T).(nf2 c t)) in (let TMP_134 
\def (Bind Abst) in (let TMP_135 \def (THead TMP_134 x5 x6) in (let H28 \def 
(eq_ind T x TMP_133 H5 TMP_135 H24) in (let H29 \def (nf2_gen_abst c x5 x6 
H28) in (let TMP_136 \def (nf2 c x5) in (let TMP_137 \def (Bind Abst) in (let 
TMP_138 \def (CHead c TMP_137 x5) in (let TMP_139 \def (nf2 TMP_138 x6) in 
(let TMP_153 \def (\lambda (H30: (nf2 c x5)).(\lambda (_: (nf2 (CHead c (Bind 
Abst) x5) x6)).(let H32 \def (nf2_pr3_confluence c x0 H8 x5 H30 u2 H7) in 
(let TMP_140 \def (Bind Abst) in (let TMP_141 \def (THead TMP_140 x0 x6) in 
(let TMP_142 \def (Bind Abst) in (let TMP_143 \def (THead TMP_142 x5 x6) in 
(let TMP_144 \def (Bind Abst) in (let TMP_145 \def (Bind Abst) in (let 
TMP_146 \def (Bind Abst) in (let TMP_147 \def (refl_equal K TMP_146) in (let 
TMP_148 \def (pr3_t x3 u2 c H20 x5 H25) in (let TMP_149 \def (H32 TMP_148) in 
(let TMP_150 \def (refl_equal T x6) in (let TMP_151 \def (f_equal3 K T T T 
THead TMP_144 TMP_145 x0 x5 x6 x6 TMP_147 TMP_149 TMP_150) in (let TMP_152 
\def (sym_eq T TMP_141 TMP_143 TMP_151) in (H27 x6 TMP_152 
False))))))))))))))))) in (land_ind TMP_136 TMP_139 False TMP_153 
H29)))))))))))))))))))) in (ex3_2_ind T T TMP_125 TMP_126 TMP_129 False 
TMP_154 H23))))))))))))))) in (ex3_2_ind T T TMP_115 TMP_116 TMP_119 False 
TMP_155 H18)))))))))))) in (let TMP_157 \def (pr3_confluence c u1 x1 H13 x 
H4) in (ex2_ind T TMP_110 TMP_111 False TMP_156 TMP_157)))))))) in (ex2_ind T 
TMP_106 TMP_109 False TMP_158 H12))))))) in (or_intror TMP_104 TMP_105 
TMP_159))))))))) in (or_ind TMP_30 TMP_31 TMP_42 TMP_95 TMP_160 
H9)))))))))))))))))) in (ex2_ind T TMP_14 TMP_15 TMP_26 TMP_161 
H6)))))))))))))))) in (ex2_ind T TMP_1 TMP_2 TMP_13 TMP_162 
H3)))))))))))))))))))))).

