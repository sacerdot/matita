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

include "basic_1/pc3/nf2.ma".

include "basic_1/nf2/fwd.ma".

theorem ty3_gen_appl_nf2:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (v: T).(\forall (x: 
T).((ty3 g c (THead (Flat Appl) w v) x) \to (ex4_2 T T (\lambda (u: 
T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) 
(\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) (\lambda (u: T).(\lambda (t: 
T).(nf2 c (THead (Bind Abst) u t))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (v: T).(\lambda (x: 
T).(\lambda (H: (ty3 g c (THead (Flat Appl) w v) x)).(let TMP_5 \def (\lambda 
(u: T).(\lambda (t: T).(let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Bind 
Abst) in (let TMP_3 \def (THead TMP_2 u t) in (let TMP_4 \def (THead TMP_1 w 
TMP_3) in (pc3 c TMP_4 x))))))) in (let TMP_8 \def (\lambda (u: T).(\lambda 
(t: T).(let TMP_6 \def (Bind Abst) in (let TMP_7 \def (THead TMP_6 u t) in 
(ty3 g c v TMP_7))))) in (let TMP_9 \def (\lambda (u: T).(\lambda (_: T).(ty3 
g c w u))) in (let TMP_14 \def (\lambda (u: T).(\lambda (t: T).(let TMP_10 
\def (Flat Appl) in (let TMP_11 \def (Bind Abst) in (let TMP_12 \def (THead 
TMP_11 u t) in (let TMP_13 \def (THead TMP_10 w TMP_12) in (pc3 c TMP_13 
x))))))) in (let TMP_17 \def (\lambda (u: T).(\lambda (t: T).(let TMP_15 \def 
(Bind Abst) in (let TMP_16 \def (THead TMP_15 u t) in (ty3 g c v TMP_16))))) 
in (let TMP_18 \def (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) in (let 
TMP_21 \def (\lambda (u: T).(\lambda (t: T).(let TMP_19 \def (Bind Abst) in 
(let TMP_20 \def (THead TMP_19 u t) in (nf2 c TMP_20))))) in (let TMP_22 \def 
(ex4_2 T T TMP_14 TMP_17 TMP_18 TMP_21) in (let TMP_149 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H0: (pc3 c (THead (Flat Appl) w (THead (Bind 
Abst) x0 x1)) x)).(\lambda (H1: (ty3 g c v (THead (Bind Abst) x0 
x1))).(\lambda (H2: (ty3 g c w x0)).(let TMP_23 \def (Bind Abst) in (let 
TMP_24 \def (THead TMP_23 x0 x1) in (let H_x \def (ty3_correct g c v TMP_24 
H1) in (let H3 \def H_x in (let TMP_27 \def (\lambda (t: T).(let TMP_25 \def 
(Bind Abst) in (let TMP_26 \def (THead TMP_25 x0 x1) in (ty3 g c TMP_26 t)))) 
in (let TMP_32 \def (\lambda (u: T).(\lambda (t: T).(let TMP_28 \def (Flat 
Appl) in (let TMP_29 \def (Bind Abst) in (let TMP_30 \def (THead TMP_29 u t) 
in (let TMP_31 \def (THead TMP_28 w TMP_30) in (pc3 c TMP_31 x))))))) in (let 
TMP_35 \def (\lambda (u: T).(\lambda (t: T).(let TMP_33 \def (Bind Abst) in 
(let TMP_34 \def (THead TMP_33 u t) in (ty3 g c v TMP_34))))) in (let TMP_36 
\def (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) in (let TMP_39 \def 
(\lambda (u: T).(\lambda (t: T).(let TMP_37 \def (Bind Abst) in (let TMP_38 
\def (THead TMP_37 u t) in (nf2 c TMP_38))))) in (let TMP_40 \def (ex4_2 T T 
TMP_32 TMP_35 TMP_36 TMP_39) in (let TMP_148 \def (\lambda (x2: T).(\lambda 
(H4: (ty3 g c (THead (Bind Abst) x0 x1) x2)).(let H_x0 \def (ty3_correct g c 
w x0 H2) in (let H5 \def H_x0 in (let TMP_41 \def (\lambda (t: T).(ty3 g c x0 
t)) in (let TMP_46 \def (\lambda (u: T).(\lambda (t: T).(let TMP_42 \def 
(Flat Appl) in (let TMP_43 \def (Bind Abst) in (let TMP_44 \def (THead TMP_43 
u t) in (let TMP_45 \def (THead TMP_42 w TMP_44) in (pc3 c TMP_45 x))))))) in 
(let TMP_49 \def (\lambda (u: T).(\lambda (t: T).(let TMP_47 \def (Bind Abst) 
in (let TMP_48 \def (THead TMP_47 u t) in (ty3 g c v TMP_48))))) in (let 
TMP_50 \def (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) in (let TMP_53 
\def (\lambda (u: T).(\lambda (t: T).(let TMP_51 \def (Bind Abst) in (let 
TMP_52 \def (THead TMP_51 u t) in (nf2 c TMP_52))))) in (let TMP_54 \def 
(ex4_2 T T TMP_46 TMP_49 TMP_50 TMP_53) in (let TMP_147 \def (\lambda (x3: 
T).(\lambda (H6: (ty3 g c x0 x3)).(let TMP_55 \def (Bind Abst) in (let TMP_56 
\def (THead TMP_55 x0 x1) in (let H7 \def (ty3_sn3 g c TMP_56 x2 H4) in (let 
TMP_57 \def (Bind Abst) in (let TMP_58 \def (THead TMP_57 x0 x1) in (let H_x1 
\def (nf2_sn3 c TMP_58 H7) in (let H8 \def H_x1 in (let TMP_61 \def (\lambda 
(u: T).(let TMP_59 \def (Bind Abst) in (let TMP_60 \def (THead TMP_59 x0 x1) 
in (pr3 c TMP_60 u)))) in (let TMP_62 \def (\lambda (u: T).(nf2 c u)) in (let 
TMP_67 \def (\lambda (u: T).(\lambda (t: T).(let TMP_63 \def (Flat Appl) in 
(let TMP_64 \def (Bind Abst) in (let TMP_65 \def (THead TMP_64 u t) in (let 
TMP_66 \def (THead TMP_63 w TMP_65) in (pc3 c TMP_66 x))))))) in (let TMP_70 
\def (\lambda (u: T).(\lambda (t: T).(let TMP_68 \def (Bind Abst) in (let 
TMP_69 \def (THead TMP_68 u t) in (ty3 g c v TMP_69))))) in (let TMP_71 \def 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) in (let TMP_74 \def (\lambda 
(u: T).(\lambda (t: T).(let TMP_72 \def (Bind Abst) in (let TMP_73 \def 
(THead TMP_72 u t) in (nf2 c TMP_73))))) in (let TMP_75 \def (ex4_2 T T 
TMP_67 TMP_70 TMP_71 TMP_74) in (let TMP_146 \def (\lambda (x4: T).(\lambda 
(H9: (pr3 c (THead (Bind Abst) x0 x1) x4)).(\lambda (H10: (nf2 c x4)).(let 
H11 \def (pr3_gen_abst c x0 x1 x4 H9) in (let TMP_78 \def (\lambda (u2: 
T).(\lambda (t2: T).(let TMP_76 \def (Bind Abst) in (let TMP_77 \def (THead 
TMP_76 u2 t2) in (eq T x4 TMP_77))))) in (let TMP_79 \def (\lambda (u2: 
T).(\lambda (_: T).(pr3 c x0 u2))) in (let TMP_82 \def (\lambda (_: 
T).(\lambda (t2: T).(\forall (b: B).(\forall (u: T).(let TMP_80 \def (Bind b) 
in (let TMP_81 \def (CHead c TMP_80 u) in (pr3 TMP_81 x1 t2))))))) in (let 
TMP_87 \def (\lambda (u: T).(\lambda (t: T).(let TMP_83 \def (Flat Appl) in 
(let TMP_84 \def (Bind Abst) in (let TMP_85 \def (THead TMP_84 u t) in (let 
TMP_86 \def (THead TMP_83 w TMP_85) in (pc3 c TMP_86 x))))))) in (let TMP_90 
\def (\lambda (u: T).(\lambda (t: T).(let TMP_88 \def (Bind Abst) in (let 
TMP_89 \def (THead TMP_88 u t) in (ty3 g c v TMP_89))))) in (let TMP_91 \def 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u))) in (let TMP_94 \def (\lambda 
(u: T).(\lambda (t: T).(let TMP_92 \def (Bind Abst) in (let TMP_93 \def 
(THead TMP_92 u t) in (nf2 c TMP_93))))) in (let TMP_95 \def (ex4_2 T T 
TMP_87 TMP_90 TMP_91 TMP_94) in (let TMP_145 \def (\lambda (x5: T).(\lambda 
(x6: T).(\lambda (H12: (eq T x4 (THead (Bind Abst) x5 x6))).(\lambda (H13: 
(pr3 c x0 x5)).(\lambda (H14: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c 
(Bind b) u) x1 x6))))).(let TMP_96 \def (\lambda (t: T).(nf2 c t)) in (let 
TMP_97 \def (Bind Abst) in (let TMP_98 \def (THead TMP_97 x5 x6) in (let H15 
\def (eq_ind T x4 TMP_96 H10 TMP_98 H12) in (let TMP_99 \def (Bind Abst) in 
(let TMP_100 \def (H14 Abst x5) in (let H16 \def (pr3_head_12 c x0 x5 H13 
TMP_99 x1 x6 TMP_100) in (let TMP_105 \def (\lambda (u: T).(\lambda (t: 
T).(let TMP_101 \def (Flat Appl) in (let TMP_102 \def (Bind Abst) in (let 
TMP_103 \def (THead TMP_102 u t) in (let TMP_104 \def (THead TMP_101 w 
TMP_103) in (pc3 c TMP_104 x))))))) in (let TMP_108 \def (\lambda (u: 
T).(\lambda (t: T).(let TMP_106 \def (Bind Abst) in (let TMP_107 \def (THead 
TMP_106 u t) in (ty3 g c v TMP_107))))) in (let TMP_109 \def (\lambda (u: 
T).(\lambda (_: T).(ty3 g c w u))) in (let TMP_112 \def (\lambda (u: 
T).(\lambda (t: T).(let TMP_110 \def (Bind Abst) in (let TMP_111 \def (THead 
TMP_110 u t) in (nf2 c TMP_111))))) in (let TMP_113 \def (Flat Appl) in (let 
TMP_114 \def (Bind Abst) in (let TMP_115 \def (THead TMP_114 x0 x1) in (let 
TMP_116 \def (THead TMP_113 w TMP_115) in (let TMP_117 \def (Flat Appl) in 
(let TMP_118 \def (Bind Abst) in (let TMP_119 \def (THead TMP_118 x5 x6) in 
(let TMP_120 \def (THead TMP_117 w TMP_119) in (let TMP_121 \def (Bind Abst) 
in (let TMP_122 \def (THead TMP_121 x0 x1) in (let TMP_123 \def (Bind Abst) 
in (let TMP_124 \def (THead TMP_123 x5 x6) in (let TMP_125 \def (pr3_thin_dx 
c TMP_122 TMP_124 H16 w Appl) in (let TMP_126 \def (pc3_pr3_conf c TMP_116 x 
H0 TMP_120 TMP_125) in (let TMP_127 \def (Bind Abst) in (let TMP_128 \def 
(THead TMP_127 x5 x6) in (let TMP_129 \def (Bind Abst) in (let TMP_130 \def 
(THead TMP_129 x0 x1) in (let TMP_131 \def (Bind Abst) in (let TMP_132 \def 
(THead TMP_131 x5 x6) in (let TMP_133 \def (ty3_sred_pr3 c TMP_130 TMP_132 
H16 g x2 H4) in (let TMP_134 \def (Bind Abst) in (let TMP_135 \def (THead 
TMP_134 x0 x1) in (let TMP_136 \def (Bind Abst) in (let TMP_137 \def (THead 
TMP_136 x0 x1) in (let TMP_138 \def (Bind Abst) in (let TMP_139 \def (THead 
TMP_138 x5 x6) in (let TMP_140 \def (pc3_pr3_r c TMP_137 TMP_139 H16) in (let 
TMP_141 \def (ty3_conv g c TMP_128 x2 TMP_133 v TMP_135 H1 TMP_140) in (let 
TMP_142 \def (ty3_sred_pr3 c x0 x5 H13 g x3 H6) in (let TMP_143 \def 
(pc3_pr3_r c x0 x5 H13) in (let TMP_144 \def (ty3_conv g c x5 x3 TMP_142 w x0 
H2 TMP_143) in (ex4_2_intro T T TMP_105 TMP_108 TMP_109 TMP_112 x5 x6 TMP_126 
TMP_141 TMP_144 H15))))))))))))))))))))))))))))))))))))))))))))))))) in 
(ex3_2_ind T T TMP_78 TMP_79 TMP_82 TMP_95 TMP_145 H11)))))))))))))) in 
(ex2_ind T TMP_61 TMP_62 TMP_75 TMP_146 H8)))))))))))))))))) in (ex_ind T 
TMP_41 TMP_54 TMP_147 H5)))))))))))) in (ex_ind T TMP_27 TMP_40 TMP_148 
H3))))))))))))))))) in (let TMP_150 \def (ty3_gen_appl g c w v x H) in 
(ex3_2_ind T T TMP_5 TMP_8 TMP_9 TMP_22 TMP_149 TMP_150)))))))))))))))).

theorem ty3_inv_lref_nf2_pc3:
 \forall (g: G).(\forall (c: C).(\forall (u1: T).(\forall (i: nat).((ty3 g c 
(TLRef i) u1) \to ((nf2 c (TLRef i)) \to (\forall (u2: T).((nf2 c u2) \to 
((pc3 c u1 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u1: T).(\lambda (i: nat).(\lambda 
(H: (ty3 g c (TLRef i) u1)).(let TMP_1 \def (TLRef i) in (let TMP_2 \def 
(\lambda (t: T).(ty3 g c t u1)) in (let TMP_6 \def (\lambda (t: T).((nf2 c t) 
\to (\forall (u2: T).((nf2 c u2) \to ((pc3 c u1 u2) \to (let TMP_5 \def 
(\lambda (u: T).(let TMP_3 \def (S i) in (let TMP_4 \def (lift TMP_3 O u) in 
(eq T u2 TMP_4)))) in (ex T TMP_5))))))) in (let TMP_115 \def (\lambda (y: 
T).(\lambda (H0: (ty3 g c y u1)).(let TMP_10 \def (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq T t (TLRef i)) \to ((nf2 c0 t) \to (\forall (u2: 
T).((nf2 c0 u2) \to ((pc3 c0 t0 u2) \to (let TMP_9 \def (\lambda (u: T).(let 
TMP_7 \def (S i) in (let TMP_8 \def (lift TMP_7 O u) in (eq T u2 TMP_8)))) in 
(ex T TMP_9)))))))))) in (let TMP_23 \def (\lambda (c0: C).(\lambda (t2: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda (_: (((eq T t2 
(TLRef i)) \to ((nf2 c0 t2) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 t 
u2) \to (ex T (\lambda (u: T).(eq T u2 (lift (S i) O u))))))))))).(\lambda 
(u: T).(\lambda (t1: T).(\lambda (H3: (ty3 g c0 u t1)).(\lambda (H4: (((eq T 
u (TLRef i)) \to ((nf2 c0 u) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 
t1 u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S i) O 
u0))))))))))).(\lambda (H5: (pc3 c0 t1 t2)).(\lambda (H6: (eq T u (TLRef 
i))).(\lambda (H7: (nf2 c0 u)).(\lambda (u2: T).(\lambda (H8: (nf2 c0 
u2)).(\lambda (H9: (pc3 c0 t2 u2)).(let TMP_11 \def (\lambda (t0: T).(nf2 c0 
t0)) in (let TMP_12 \def (TLRef i) in (let H10 \def (eq_ind T u TMP_11 H7 
TMP_12 H6) in (let TMP_16 \def (\lambda (t0: T).((eq T t0 (TLRef i)) \to 
((nf2 c0 t0) \to (\forall (u3: T).((nf2 c0 u3) \to ((pc3 c0 t1 u3) \to (let 
TMP_15 \def (\lambda (u0: T).(let TMP_13 \def (S i) in (let TMP_14 \def (lift 
TMP_13 O u0) in (eq T u3 TMP_14)))) in (ex T TMP_15)))))))) in (let TMP_17 
\def (TLRef i) in (let H11 \def (eq_ind T u TMP_16 H4 TMP_17 H6) in (let 
TMP_18 \def (\lambda (t0: T).(ty3 g c0 t0 t1)) in (let TMP_19 \def (TLRef i) 
in (let H12 \def (eq_ind T u TMP_18 H3 TMP_19 H6) in (let TMP_20 \def (TLRef 
i) in (let TMP_21 \def (refl_equal T TMP_20) in (let H_y \def (H11 TMP_21 H10 
u2 H8) in (let TMP_22 \def (pc3_t t2 c0 t1 H5 u2 H9) in (H_y 
TMP_22))))))))))))))))))))))))))))) in (let TMP_31 \def (\lambda (c0: 
C).(\lambda (m: nat).(\lambda (H1: (eq T (TSort m) (TLRef i))).(\lambda (_: 
(nf2 c0 (TSort m))).(\lambda (u2: T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: 
(pc3 c0 (TSort (next g m)) u2)).(let TMP_24 \def (TSort m) in (let TMP_25 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let TMP_26 \def 
(TLRef i) in (let H5 \def (eq_ind T TMP_24 TMP_25 I TMP_26 H1) in (let TMP_29 
\def (\lambda (u: T).(let TMP_27 \def (S i) in (let TMP_28 \def (lift TMP_27 
O u) in (eq T u2 TMP_28)))) in (let TMP_30 \def (ex T TMP_29) in (False_ind 
TMP_30 H5)))))))))))))) in (let TMP_47 \def (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H1: (getl n c0 (CHead d (Bind 
Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (_: (((eq T u 
(TLRef i)) \to ((nf2 d u) \to (\forall (u2: T).((nf2 d u2) \to ((pc3 d t u2) 
\to (ex T (\lambda (u0: T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (H4: 
(eq T (TLRef n) (TLRef i))).(\lambda (H5: (nf2 c0 (TLRef n))).(\lambda (u2: 
T).(\lambda (_: (nf2 c0 u2)).(\lambda (H7: (pc3 c0 (lift (S n) O t) u2)).(let 
TMP_32 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow n | (TLRef 
n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow n])) in (let TMP_33 \def 
(TLRef n) in (let TMP_34 \def (TLRef i) in (let H8 \def (f_equal T nat TMP_32 
TMP_33 TMP_34 H4) in (let TMP_37 \def (\lambda (n0: nat).(let TMP_35 \def (S 
n0) in (let TMP_36 \def (lift TMP_35 O t) in (pc3 c0 TMP_36 u2)))) in (let H9 
\def (eq_ind nat n TMP_37 H7 i H8) in (let TMP_39 \def (\lambda (n0: 
nat).(let TMP_38 \def (TLRef n0) in (nf2 c0 TMP_38))) in (let H10 \def 
(eq_ind nat n TMP_39 H5 i H8) in (let TMP_42 \def (\lambda (n0: nat).(let 
TMP_40 \def (Bind Abbr) in (let TMP_41 \def (CHead d TMP_40 u) in (getl n0 c0 
TMP_41)))) in (let H11 \def (eq_ind nat n TMP_42 H1 i H8) in (let TMP_45 \def 
(\lambda (u0: T).(let TMP_43 \def (S i) in (let TMP_44 \def (lift TMP_43 O 
u0) in (eq T u2 TMP_44)))) in (let TMP_46 \def (ex T TMP_45) in (nf2_gen_lref 
c0 d u i H11 H10 TMP_46)))))))))))))))))))))))))) in (let TMP_87 \def 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H1: (getl n c0 (CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (_: (((eq T u (TLRef i)) \to ((nf2 d u) \to (\forall (u2: 
T).((nf2 d u2) \to ((pc3 d t u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S 
i) O u0))))))))))).(\lambda (H4: (eq T (TLRef n) (TLRef i))).(\lambda (H5: 
(nf2 c0 (TLRef n))).(\lambda (u2: T).(\lambda (H6: (nf2 c0 u2)).(\lambda (H7: 
(pc3 c0 (lift (S n) O u) u2)).(let TMP_48 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow n | (TLRef n0) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n])) in (let TMP_49 \def (TLRef n) in (let TMP_50 \def (TLRef i) 
in (let H8 \def (f_equal T nat TMP_48 TMP_49 TMP_50 H4) in (let TMP_53 \def 
(\lambda (n0: nat).(let TMP_51 \def (S n0) in (let TMP_52 \def (lift TMP_51 O 
u) in (pc3 c0 TMP_52 u2)))) in (let H9 \def (eq_ind nat n TMP_53 H7 i H8) in 
(let TMP_55 \def (\lambda (n0: nat).(let TMP_54 \def (TLRef n0) in (nf2 c0 
TMP_54))) in (let H10 \def (eq_ind nat n TMP_55 H5 i H8) in (let TMP_58 \def 
(\lambda (n0: nat).(let TMP_56 \def (Bind Abst) in (let TMP_57 \def (CHead d 
TMP_56 u) in (getl n0 c0 TMP_57)))) in (let H11 \def (eq_ind nat n TMP_58 H1 
i H8) in (let TMP_59 \def (S i) in (let TMP_60 \def (lift TMP_59 O u) in (let 
H_y \def (pc3_nf2_unfold c0 TMP_60 u2 H9 H6) in (let TMP_61 \def (S i) in 
(let TMP_62 \def (getl_drop Abst c0 d u i H11) in (let H12 \def (pr3_gen_lift 
c0 u u2 TMP_61 O H_y d TMP_62) in (let TMP_65 \def (\lambda (t2: T).(let 
TMP_63 \def (S i) in (let TMP_64 \def (lift TMP_63 O t2) in (eq T u2 
TMP_64)))) in (let TMP_66 \def (\lambda (t2: T).(pr3 d u t2)) in (let TMP_69 
\def (\lambda (u0: T).(let TMP_67 \def (S i) in (let TMP_68 \def (lift TMP_67 
O u0) in (eq T u2 TMP_68)))) in (let TMP_70 \def (ex T TMP_69) in (let TMP_86 
\def (\lambda (x: T).(\lambda (H13: (eq T u2 (lift (S i) O x))).(\lambda (_: 
(pr3 d u x)).(let TMP_71 \def (S i) in (let TMP_72 \def (lift TMP_71 O x) in 
(let TMP_76 \def (\lambda (t0: T).(let TMP_75 \def (\lambda (u0: T).(let 
TMP_73 \def (S i) in (let TMP_74 \def (lift TMP_73 O u0) in (eq T t0 
TMP_74)))) in (ex T TMP_75))) in (let TMP_81 \def (\lambda (u0: T).(let 
TMP_77 \def (S i) in (let TMP_78 \def (lift TMP_77 O x) in (let TMP_79 \def 
(S i) in (let TMP_80 \def (lift TMP_79 O u0) in (eq T TMP_78 TMP_80)))))) in 
(let TMP_82 \def (S i) in (let TMP_83 \def (lift TMP_82 O x) in (let TMP_84 
\def (refl_equal T TMP_83) in (let TMP_85 \def (ex_intro T TMP_81 x TMP_84) 
in (eq_ind_r T TMP_72 TMP_76 TMP_85 u2 H13)))))))))))) in (ex2_ind T TMP_65 
TMP_66 TMP_70 TMP_86 H12))))))))))))))))))))))))))))))))))) in (let TMP_96 
\def (\lambda (c0: C).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 
u t)).(\lambda (_: (((eq T u (TLRef i)) \to ((nf2 c0 u) \to (\forall (u2: 
T).((nf2 c0 u2) \to ((pc3 c0 t u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift 
(S i) O u0))))))))))).(\lambda (b: B).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u) t1 t2)).(\lambda (_: (((eq T t1 
(TLRef i)) \to ((nf2 (CHead c0 (Bind b) u) t1) \to (\forall (u2: T).((nf2 
(CHead c0 (Bind b) u) u2) \to ((pc3 (CHead c0 (Bind b) u) t2 u2) \to (ex T 
(\lambda (u0: T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (H5: (eq T 
(THead (Bind b) u t1) (TLRef i))).(\lambda (_: (nf2 c0 (THead (Bind b) u 
t1))).(\lambda (u2: T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 (THead 
(Bind b) u t2) u2)).(let TMP_88 \def (Bind b) in (let TMP_89 \def (THead 
TMP_88 u t1) in (let TMP_90 \def (\lambda (ee: T).(match ee with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
True])) in (let TMP_91 \def (TLRef i) in (let H9 \def (eq_ind T TMP_89 TMP_90 
I TMP_91 H5) in (let TMP_94 \def (\lambda (u0: T).(let TMP_92 \def (S i) in 
(let TMP_93 \def (lift TMP_92 O u0) in (eq T u2 TMP_93)))) in (let TMP_95 
\def (ex T TMP_94) in (False_ind TMP_95 H9))))))))))))))))))))))) in (let 
TMP_105 \def (\lambda (c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: 
(ty3 g c0 w u)).(\lambda (_: (((eq T w (TLRef i)) \to ((nf2 c0 w) \to 
(\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 u u2) \to (ex T (\lambda (u0: 
T).(eq T u2 (lift (S i) O u0))))))))))).(\lambda (v: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u t))).(\lambda (_: (((eq T v 
(TLRef i)) \to ((nf2 c0 v) \to (\forall (u2: T).((nf2 c0 u2) \to ((pc3 c0 
(THead (Bind Abst) u t) u2) \to (ex T (\lambda (u0: T).(eq T u2 (lift (S i) O 
u0))))))))))).(\lambda (H5: (eq T (THead (Flat Appl) w v) (TLRef 
i))).(\lambda (_: (nf2 c0 (THead (Flat Appl) w v))).(\lambda (u2: T).(\lambda 
(_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) 
u t)) u2)).(let TMP_97 \def (Flat Appl) in (let TMP_98 \def (THead TMP_97 w 
v) in (let TMP_99 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_100 \def (TLRef i) in (let H9 \def (eq_ind T TMP_98 TMP_99 I TMP_100 
H5) in (let TMP_103 \def (\lambda (u0: T).(let TMP_101 \def (S i) in (let 
TMP_102 \def (lift TMP_101 O u0) in (eq T u2 TMP_102)))) in (let TMP_104 \def 
(ex T TMP_103) in (False_ind TMP_104 H9)))))))))))))))))))))) in (let TMP_114 
\def (\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g 
c0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef i)) \to ((nf2 c0 t1) \to (\forall 
(u2: T).((nf2 c0 u2) \to ((pc3 c0 t2 u2) \to (ex T (\lambda (u: T).(eq T u2 
(lift (S i) O u))))))))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t2 
t0)).(\lambda (_: (((eq T t2 (TLRef i)) \to ((nf2 c0 t2) \to (\forall (u2: 
T).((nf2 c0 u2) \to ((pc3 c0 t0 u2) \to (ex T (\lambda (u: T).(eq T u2 (lift 
(S i) O u))))))))))).(\lambda (H5: (eq T (THead (Flat Cast) t2 t1) (TLRef 
i))).(\lambda (_: (nf2 c0 (THead (Flat Cast) t2 t1))).(\lambda (u2: 
T).(\lambda (_: (nf2 c0 u2)).(\lambda (_: (pc3 c0 (THead (Flat Cast) t0 t2) 
u2)).(let TMP_106 \def (Flat Cast) in (let TMP_107 \def (THead TMP_106 t2 t1) 
in (let TMP_108 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in 
(let TMP_109 \def (TLRef i) in (let H9 \def (eq_ind T TMP_107 TMP_108 I 
TMP_109 H5) in (let TMP_112 \def (\lambda (u: T).(let TMP_110 \def (S i) in 
(let TMP_111 \def (lift TMP_110 O u) in (eq T u2 TMP_111)))) in (let TMP_113 
\def (ex T TMP_112) in (False_ind TMP_113 H9))))))))))))))))))))) in (ty3_ind 
g TMP_10 TMP_23 TMP_31 TMP_47 TMP_87 TMP_96 TMP_105 TMP_114 c y u1 
H0))))))))))) in (insert_eq T TMP_1 TMP_2 TMP_6 TMP_115 H))))))))).

theorem ty3_inv_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (i: nat).((ty3 g c 
(TLRef i) u) \to ((nf2 c (TLRef i)) \to ((nf2 c u) \to (ex T (\lambda (u0: 
T).(eq T u (lift (S i) O u0))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (ty3 g c (TLRef i) u)).(\lambda (H0: (nf2 c (TLRef i))).(\lambda (H1: 
(nf2 c u)).(let TMP_1 \def (pc3_refl c u) in (ty3_inv_lref_nf2_pc3 g c u i H 
H0 u H1 TMP_1)))))))).

theorem ty3_inv_appls_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (vs: TList).(\forall (u1: 
T).(\forall (i: nat).((ty3 g c (THeads (Flat Appl) vs (TLRef i)) u1) \to 
((nf2 c (TLRef i)) \to ((nf2 c u1) \to (ex2 T (\lambda (u: T).(nf2 c (lift (S 
i) O u))) (\lambda (u: T).(pc3 c (THeads (Flat Appl) vs (lift (S i) O u)) 
u1))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (vs: TList).(let TMP_9 \def (\lambda 
(t: TList).(\forall (u1: T).(\forall (i: nat).((ty3 g c (THeads (Flat Appl) t 
(TLRef i)) u1) \to ((nf2 c (TLRef i)) \to ((nf2 c u1) \to (let TMP_3 \def 
(\lambda (u: T).(let TMP_1 \def (S i) in (let TMP_2 \def (lift TMP_1 O u) in 
(nf2 c TMP_2)))) in (let TMP_8 \def (\lambda (u: T).(let TMP_4 \def (Flat 
Appl) in (let TMP_5 \def (S i) in (let TMP_6 \def (lift TMP_5 O u) in (let 
TMP_7 \def (THeads TMP_4 t TMP_6) in (pc3 c TMP_7 u1)))))) in (ex2 T TMP_3 
TMP_8))))))))) in (let TMP_45 \def (\lambda (u1: T).(\lambda (i: 
nat).(\lambda (H: (ty3 g c (TLRef i) u1)).(\lambda (H0: (nf2 c (TLRef 
i))).(\lambda (H1: (nf2 c u1)).(let H_x \def (ty3_inv_lref_nf2 g c u1 i H H0 
H1) in (let H2 \def H_x in (let TMP_12 \def (\lambda (u0: T).(let TMP_10 \def 
(S i) in (let TMP_11 \def (lift TMP_10 O u0) in (eq T u1 TMP_11)))) in (let 
TMP_15 \def (\lambda (u: T).(let TMP_13 \def (S i) in (let TMP_14 \def (lift 
TMP_13 O u) in (nf2 c TMP_14)))) in (let TMP_18 \def (\lambda (u: T).(let 
TMP_16 \def (S i) in (let TMP_17 \def (lift TMP_16 O u) in (pc3 c TMP_17 
u1)))) in (let TMP_19 \def (ex2 T TMP_15 TMP_18) in (let TMP_44 \def (\lambda 
(x: T).(\lambda (H3: (eq T u1 (lift (S i) O x))).(let TMP_20 \def (\lambda 
(t: T).(nf2 c t)) in (let TMP_21 \def (S i) in (let TMP_22 \def (lift TMP_21 
O x) in (let H4 \def (eq_ind T u1 TMP_20 H1 TMP_22 H3) in (let TMP_23 \def (S 
i) in (let TMP_24 \def (lift TMP_23 O x) in (let TMP_31 \def (\lambda (t: 
T).(let TMP_27 \def (\lambda (u: T).(let TMP_25 \def (S i) in (let TMP_26 
\def (lift TMP_25 O u) in (nf2 c TMP_26)))) in (let TMP_30 \def (\lambda (u: 
T).(let TMP_28 \def (S i) in (let TMP_29 \def (lift TMP_28 O u) in (pc3 c 
TMP_29 t)))) in (ex2 T TMP_27 TMP_30)))) in (let TMP_34 \def (\lambda (u: 
T).(let TMP_32 \def (S i) in (let TMP_33 \def (lift TMP_32 O u) in (nf2 c 
TMP_33)))) in (let TMP_39 \def (\lambda (u: T).(let TMP_35 \def (S i) in (let 
TMP_36 \def (lift TMP_35 O u) in (let TMP_37 \def (S i) in (let TMP_38 \def 
(lift TMP_37 O x) in (pc3 c TMP_36 TMP_38)))))) in (let TMP_40 \def (S i) in 
(let TMP_41 \def (lift TMP_40 O x) in (let TMP_42 \def (pc3_refl c TMP_41) in 
(let TMP_43 \def (ex_intro2 T TMP_34 TMP_39 x H4 TMP_42) in (eq_ind_r T 
TMP_24 TMP_31 TMP_43 u1 H3)))))))))))))))) in (ex_ind T TMP_12 TMP_19 TMP_44 
H2))))))))))))) in (let TMP_145 \def (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (H: ((\forall (u1: T).(\forall (i: nat).((ty3 g c (THeads 
(Flat Appl) t0 (TLRef i)) u1) \to ((nf2 c (TLRef i)) \to ((nf2 c u1) \to (ex2 
T (\lambda (u: T).(nf2 c (lift (S i) O u))) (\lambda (u: T).(pc3 c (THeads 
(Flat Appl) t0 (lift (S i) O u)) u1)))))))))).(\lambda (u1: T).(\lambda (i: 
nat).(\lambda (H0: (ty3 g c (THead (Flat Appl) t (THeads (Flat Appl) t0 
(TLRef i))) u1)).(\lambda (H1: (nf2 c (TLRef i))).(\lambda (_: (nf2 c 
u1)).(let TMP_46 \def (Flat Appl) in (let TMP_47 \def (TLRef i) in (let 
TMP_48 \def (THeads TMP_46 t0 TMP_47) in (let H_x \def (ty3_gen_appl_nf2 g c 
t TMP_48 u1 H0) in (let H3 \def H_x in (let TMP_53 \def (\lambda (u: 
T).(\lambda (t1: T).(let TMP_49 \def (Flat Appl) in (let TMP_50 \def (Bind 
Abst) in (let TMP_51 \def (THead TMP_50 u t1) in (let TMP_52 \def (THead 
TMP_49 t TMP_51) in (pc3 c TMP_52 u1))))))) in (let TMP_59 \def (\lambda (u: 
T).(\lambda (t1: T).(let TMP_54 \def (Flat Appl) in (let TMP_55 \def (TLRef 
i) in (let TMP_56 \def (THeads TMP_54 t0 TMP_55) in (let TMP_57 \def (Bind 
Abst) in (let TMP_58 \def (THead TMP_57 u t1) in (ty3 g c TMP_56 
TMP_58)))))))) in (let TMP_60 \def (\lambda (u: T).(\lambda (_: T).(ty3 g c t 
u))) in (let TMP_63 \def (\lambda (u: T).(\lambda (t1: T).(let TMP_61 \def 
(Bind Abst) in (let TMP_62 \def (THead TMP_61 u t1) in (nf2 c TMP_62))))) in 
(let TMP_66 \def (\lambda (u: T).(let TMP_64 \def (S i) in (let TMP_65 \def 
(lift TMP_64 O u) in (nf2 c TMP_65)))) in (let TMP_73 \def (\lambda (u: 
T).(let TMP_67 \def (Flat Appl) in (let TMP_68 \def (Flat Appl) in (let 
TMP_69 \def (S i) in (let TMP_70 \def (lift TMP_69 O u) in (let TMP_71 \def 
(THeads TMP_68 t0 TMP_70) in (let TMP_72 \def (THead TMP_67 t TMP_71) in (pc3 
c TMP_72 u1)))))))) in (let TMP_74 \def (ex2 T TMP_66 TMP_73) in (let TMP_144 
\def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (pc3 c (THead (Flat 
Appl) t (THead (Bind Abst) x0 x1)) u1)).(\lambda (H5: (ty3 g c (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (_: (ty3 g c t 
x0)).(\lambda (H7: (nf2 c (THead (Bind Abst) x0 x1))).(let H8 \def 
(nf2_gen_abst c x0 x1 H7) in (let TMP_75 \def (nf2 c x0) in (let TMP_76 \def 
(Bind Abst) in (let TMP_77 \def (CHead c TMP_76 x0) in (let TMP_78 \def (nf2 
TMP_77 x1) in (let TMP_81 \def (\lambda (u: T).(let TMP_79 \def (S i) in (let 
TMP_80 \def (lift TMP_79 O u) in (nf2 c TMP_80)))) in (let TMP_88 \def 
(\lambda (u: T).(let TMP_82 \def (Flat Appl) in (let TMP_83 \def (Flat Appl) 
in (let TMP_84 \def (S i) in (let TMP_85 \def (lift TMP_84 O u) in (let 
TMP_86 \def (THeads TMP_83 t0 TMP_85) in (let TMP_87 \def (THead TMP_82 t 
TMP_86) in (pc3 c TMP_87 u1)))))))) in (let TMP_89 \def (ex2 T TMP_81 TMP_88) 
in (let TMP_143 \def (\lambda (H9: (nf2 c x0)).(\lambda (H10: (nf2 (CHead c 
(Bind Abst) x0) x1)).(let TMP_90 \def (Bind Abst) in (let TMP_91 \def (THead 
TMP_90 x0 x1) in (let H_y \def (H TMP_91 i H5 H1) in (let TMP_92 \def 
(nf2_abst_shift c x0 H9 x1 H10) in (let H11 \def (H_y TMP_92) in (let TMP_95 
\def (\lambda (u: T).(let TMP_93 \def (S i) in (let TMP_94 \def (lift TMP_93 
O u) in (nf2 c TMP_94)))) in (let TMP_102 \def (\lambda (u: T).(let TMP_96 
\def (Flat Appl) in (let TMP_97 \def (S i) in (let TMP_98 \def (lift TMP_97 O 
u) in (let TMP_99 \def (THeads TMP_96 t0 TMP_98) in (let TMP_100 \def (Bind 
Abst) in (let TMP_101 \def (THead TMP_100 x0 x1) in (pc3 c TMP_99 
TMP_101)))))))) in (let TMP_105 \def (\lambda (u: T).(let TMP_103 \def (S i) 
in (let TMP_104 \def (lift TMP_103 O u) in (nf2 c TMP_104)))) in (let TMP_112 
\def (\lambda (u: T).(let TMP_106 \def (Flat Appl) in (let TMP_107 \def (Flat 
Appl) in (let TMP_108 \def (S i) in (let TMP_109 \def (lift TMP_108 O u) in 
(let TMP_110 \def (THeads TMP_107 t0 TMP_109) in (let TMP_111 \def (THead 
TMP_106 t TMP_110) in (pc3 c TMP_111 u1)))))))) in (let TMP_113 \def (ex2 T 
TMP_105 TMP_112) in (let TMP_142 \def (\lambda (x: T).(\lambda (H12: (nf2 c 
(lift (S i) O x))).(\lambda (H13: (pc3 c (THeads (Flat Appl) t0 (lift (S i) O 
x)) (THead (Bind Abst) x0 x1))).(let TMP_116 \def (\lambda (u: T).(let 
TMP_114 \def (S i) in (let TMP_115 \def (lift TMP_114 O u) in (nf2 c 
TMP_115)))) in (let TMP_123 \def (\lambda (u: T).(let TMP_117 \def (Flat 
Appl) in (let TMP_118 \def (Flat Appl) in (let TMP_119 \def (S i) in (let 
TMP_120 \def (lift TMP_119 O u) in (let TMP_121 \def (THeads TMP_118 t0 
TMP_120) in (let TMP_122 \def (THead TMP_117 t TMP_121) in (pc3 c TMP_122 
u1)))))))) in (let TMP_124 \def (Flat Appl) in (let TMP_125 \def (Bind Abst) 
in (let TMP_126 \def (THead TMP_125 x0 x1) in (let TMP_127 \def (THead 
TMP_124 t TMP_126) in (let TMP_128 \def (Flat Appl) in (let TMP_129 \def 
(Flat Appl) in (let TMP_130 \def (S i) in (let TMP_131 \def (lift TMP_130 O 
x) in (let TMP_132 \def (THeads TMP_129 t0 TMP_131) in (let TMP_133 \def 
(THead TMP_128 t TMP_132) in (let TMP_134 \def (Flat Appl) in (let TMP_135 
\def (S i) in (let TMP_136 \def (lift TMP_135 O x) in (let TMP_137 \def 
(THeads TMP_134 t0 TMP_136) in (let TMP_138 \def (Bind Abst) in (let TMP_139 
\def (THead TMP_138 x0 x1) in (let TMP_140 \def (pc3_thin_dx c TMP_137 
TMP_139 H13 t Appl) in (let TMP_141 \def (pc3_t TMP_127 c TMP_133 TMP_140 u1 
H4) in (ex_intro2 T TMP_116 TMP_123 x H12 TMP_141)))))))))))))))))))))))) in 
(ex2_ind T TMP_95 TMP_102 TMP_113 TMP_142 H11)))))))))))))) in (land_ind 
TMP_75 TMP_78 TMP_89 TMP_143 H8)))))))))))))))) in (ex4_2_ind T T TMP_53 
TMP_59 TMP_60 TMP_63 TMP_74 TMP_144 H3)))))))))))))))))))))) in (TList_ind 
TMP_9 TMP_45 TMP_145 vs)))))).

theorem ty3_inv_lref_lref_nf2:
 \forall (g: G).(\forall (c: C).(\forall (i: nat).(\forall (j: nat).((ty3 g c 
(TLRef i) (TLRef j)) \to ((nf2 c (TLRef i)) \to ((nf2 c (TLRef j)) \to (lt i 
j)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (i: nat).(\lambda (j: nat).(\lambda 
(H: (ty3 g c (TLRef i) (TLRef j))).(\lambda (H0: (nf2 c (TLRef i))).(\lambda 
(H1: (nf2 c (TLRef j))).(let TMP_1 \def (TLRef j) in (let H_x \def 
(ty3_inv_lref_nf2 g c TMP_1 i H H0 H1) in (let H2 \def H_x in (let TMP_5 \def 
(\lambda (u0: T).(let TMP_2 \def (TLRef j) in (let TMP_3 \def (S i) in (let 
TMP_4 \def (lift TMP_3 O u0) in (eq T TMP_2 TMP_4))))) in (let TMP_6 \def (lt 
i j) in (let TMP_36 \def (\lambda (x: T).(\lambda (H3: (eq T (TLRef j) (lift 
(S i) O x))).(let TMP_7 \def (S i) in (let H_x0 \def (lift_gen_lref x O TMP_7 
j H3) in (let H4 \def H_x0 in (let TMP_8 \def (lt j O) in (let TMP_9 \def 
(TLRef j) in (let TMP_10 \def (eq T x TMP_9) in (let TMP_11 \def (land TMP_8 
TMP_10) in (let TMP_12 \def (S i) in (let TMP_13 \def (le TMP_12 j) in (let 
TMP_14 \def (S i) in (let TMP_15 \def (minus j TMP_14) in (let TMP_16 \def 
(TLRef TMP_15) in (let TMP_17 \def (eq T x TMP_16) in (let TMP_18 \def (land 
TMP_13 TMP_17) in (let TMP_19 \def (lt i j) in (let TMP_26 \def (\lambda (H5: 
(land (lt j O) (eq T x (TLRef j)))).(let TMP_20 \def (lt j O) in (let TMP_21 
\def (TLRef j) in (let TMP_22 \def (eq T x TMP_21) in (let TMP_23 \def (lt i 
j) in (let TMP_25 \def (\lambda (H6: (lt j O)).(\lambda (_: (eq T x (TLRef 
j))).(let TMP_24 \def (lt i j) in (lt_x_O j H6 TMP_24)))) in (land_ind TMP_20 
TMP_22 TMP_23 TMP_25 H5))))))) in (let TMP_35 \def (\lambda (H5: (land (le (S 
i) j) (eq T x (TLRef (minus j (S i)))))).(let TMP_27 \def (S i) in (let 
TMP_28 \def (le TMP_27 j) in (let TMP_29 \def (S i) in (let TMP_30 \def 
(minus j TMP_29) in (let TMP_31 \def (TLRef TMP_30) in (let TMP_32 \def (eq T 
x TMP_31) in (let TMP_33 \def (lt i j) in (let TMP_34 \def (\lambda (H6: (le 
(S i) j)).(\lambda (_: (eq T x (TLRef (minus j (S i))))).H6)) in (land_ind 
TMP_28 TMP_32 TMP_33 TMP_34 H5)))))))))) in (or_ind TMP_11 TMP_18 TMP_19 
TMP_26 TMP_35 H4)))))))))))))))))))) in (ex_ind T TMP_5 TMP_6 TMP_36 
H2))))))))))))).

