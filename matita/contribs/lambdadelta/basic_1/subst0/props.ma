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

include "basic_1/subst0/fwd.ma".

theorem subst0_refl:
 \forall (u: T).(\forall (t: T).(\forall (d: nat).((subst0 d u t t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (u: T).(\lambda (t: T).(let TMP_1 \def (\lambda (t0: T).(\forall (d: 
nat).((subst0 d u t0 t0) \to (\forall (P: Prop).P)))) in (let TMP_3 \def 
(\lambda (n: nat).(\lambda (d: nat).(\lambda (H: (subst0 d u (TSort n) (TSort 
n))).(\lambda (P: Prop).(let TMP_2 \def (TSort n) in (subst0_gen_sort u TMP_2 
d n H P)))))) in (let TMP_17 \def (\lambda (n: nat).(\lambda (d: 
nat).(\lambda (H: (subst0 d u (TLRef n) (TLRef n))).(\lambda (P: Prop).(let 
TMP_4 \def (eq nat n d) in (let TMP_5 \def (TLRef n) in (let TMP_6 \def (S n) 
in (let TMP_7 \def (lift TMP_6 O u) in (let TMP_8 \def (eq T TMP_5 TMP_7) in 
(let TMP_14 \def (\lambda (_: (eq nat n d)).(\lambda (H1: (eq T (TLRef n) 
(lift (S n) O u))).(let TMP_9 \def (S n) in (let TMP_10 \def (le_O_n n) in 
(let TMP_11 \def (S n) in (let TMP_12 \def (plus O TMP_11) in (let TMP_13 
\def (le_n TMP_12) in (lift_gen_lref_false TMP_9 O n TMP_10 TMP_13 u H1 
P)))))))) in (let TMP_15 \def (TLRef n) in (let TMP_16 \def (subst0_gen_lref 
u TMP_15 d n H) in (land_ind TMP_4 TMP_8 P TMP_14 TMP_16))))))))))))) in (let 
TMP_79 \def (\lambda (k: K).(\lambda (t0: T).(\lambda (H: ((\forall (d: 
nat).((subst0 d u t0 t0) \to (\forall (P: Prop).P))))).(\lambda (t1: 
T).(\lambda (H0: ((\forall (d: nat).((subst0 d u t1 t1) \to (\forall (P: 
Prop).P))))).(\lambda (d: nat).(\lambda (H1: (subst0 d u (THead k t0 t1) 
(THead k t0 t1))).(\lambda (P: Prop).(let TMP_20 \def (\lambda (u2: T).(let 
TMP_18 \def (THead k t0 t1) in (let TMP_19 \def (THead k u2 t1) in (eq T 
TMP_18 TMP_19)))) in (let TMP_21 \def (\lambda (u2: T).(subst0 d u t0 u2)) in 
(let TMP_22 \def (ex2 T TMP_20 TMP_21) in (let TMP_25 \def (\lambda (t2: 
T).(let TMP_23 \def (THead k t0 t1) in (let TMP_24 \def (THead k t0 t2) in 
(eq T TMP_23 TMP_24)))) in (let TMP_27 \def (\lambda (t2: T).(let TMP_26 \def 
(s k d) in (subst0 TMP_26 u t1 t2))) in (let TMP_28 \def (ex2 T TMP_25 
TMP_27) in (let TMP_31 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_29 
\def (THead k t0 t1) in (let TMP_30 \def (THead k u2 t2) in (eq T TMP_29 
TMP_30))))) in (let TMP_32 \def (\lambda (u2: T).(\lambda (_: T).(subst0 d u 
t0 u2))) in (let TMP_34 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_33 
\def (s k d) in (subst0 TMP_33 u t1 t2)))) in (let TMP_35 \def (ex3_2 T T 
TMP_31 TMP_32 TMP_34) in (let TMP_45 \def (\lambda (H2: (ex2 T (\lambda (u2: 
T).(eq T (THead k t0 t1) (THead k u2 t1))) (\lambda (u2: T).(subst0 d u t0 
u2)))).(let TMP_38 \def (\lambda (u2: T).(let TMP_36 \def (THead k t0 t1) in 
(let TMP_37 \def (THead k u2 t1) in (eq T TMP_36 TMP_37)))) in (let TMP_39 
\def (\lambda (u2: T).(subst0 d u t0 u2)) in (let TMP_44 \def (\lambda (x: 
T).(\lambda (H3: (eq T (THead k t0 t1) (THead k x t1))).(\lambda (H4: (subst0 
d u t0 x)).(let TMP_40 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ t2 _) \Rightarrow t2])) 
in (let TMP_41 \def (THead k t0 t1) in (let TMP_42 \def (THead k x t1) in 
(let H5 \def (f_equal T T TMP_40 TMP_41 TMP_42 H3) in (let TMP_43 \def 
(\lambda (t2: T).(subst0 d u t0 t2)) in (let H6 \def (eq_ind_r T x TMP_43 H4 
t0 H5) in (H d H6 P)))))))))) in (ex2_ind T TMP_38 TMP_39 P TMP_44 H2))))) in 
(let TMP_58 \def (\lambda (H2: (ex2 T (\lambda (t2: T).(eq T (THead k t0 t1) 
(THead k t0 t2))) (\lambda (t2: T).(subst0 (s k d) u t1 t2)))).(let TMP_48 
\def (\lambda (t2: T).(let TMP_46 \def (THead k t0 t1) in (let TMP_47 \def 
(THead k t0 t2) in (eq T TMP_46 TMP_47)))) in (let TMP_50 \def (\lambda (t2: 
T).(let TMP_49 \def (s k d) in (subst0 TMP_49 u t1 t2))) in (let TMP_57 \def 
(\lambda (x: T).(\lambda (H3: (eq T (THead k t0 t1) (THead k t0 x))).(\lambda 
(H4: (subst0 (s k d) u t1 x)).(let TMP_51 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ _ t2) 
\Rightarrow t2])) in (let TMP_52 \def (THead k t0 t1) in (let TMP_53 \def 
(THead k t0 x) in (let H5 \def (f_equal T T TMP_51 TMP_52 TMP_53 H3) in (let 
TMP_55 \def (\lambda (t2: T).(let TMP_54 \def (s k d) in (subst0 TMP_54 u t1 
t2))) in (let H6 \def (eq_ind_r T x TMP_55 H4 t1 H5) in (let TMP_56 \def (s k 
d) in (H0 TMP_56 H6 P))))))))))) in (ex2_ind T TMP_48 TMP_50 P TMP_57 H2))))) 
in (let TMP_76 \def (\lambda (H2: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead k t0 t1) (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 d u t0 u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k d) u t1 
t2))))).(let TMP_61 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_59 \def 
(THead k t0 t1) in (let TMP_60 \def (THead k u2 t2) in (eq T TMP_59 
TMP_60))))) in (let TMP_62 \def (\lambda (u2: T).(\lambda (_: T).(subst0 d u 
t0 u2))) in (let TMP_64 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_63 
\def (s k d) in (subst0 TMP_63 u t1 t2)))) in (let TMP_75 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T (THead k t0 t1) (THead k x0 
x1))).(\lambda (H4: (subst0 d u t0 x0)).(\lambda (H5: (subst0 (s k d) u t1 
x1)).(let TMP_65 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 
| (TLRef _) \Rightarrow t0 | (THead _ t2 _) \Rightarrow t2])) in (let TMP_66 
\def (THead k t0 t1) in (let TMP_67 \def (THead k x0 x1) in (let H6 \def 
(f_equal T T TMP_65 TMP_66 TMP_67 H3) in (let TMP_68 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | 
(THead _ _ t2) \Rightarrow t2])) in (let TMP_69 \def (THead k t0 t1) in (let 
TMP_70 \def (THead k x0 x1) in (let H7 \def (f_equal T T TMP_68 TMP_69 TMP_70 
H3) in (let TMP_74 \def (\lambda (H8: (eq T t0 x0)).(let TMP_72 \def (\lambda 
(t2: T).(let TMP_71 \def (s k d) in (subst0 TMP_71 u t1 t2))) in (let H9 \def 
(eq_ind_r T x1 TMP_72 H5 t1 H7) in (let TMP_73 \def (\lambda (t2: T).(subst0 
d u t0 t2)) in (let H10 \def (eq_ind_r T x0 TMP_73 H4 t0 H8) in (H d H10 
P)))))) in (TMP_74 H6))))))))))))))) in (ex3_2_ind T T TMP_61 TMP_62 TMP_64 P 
TMP_75 H2)))))) in (let TMP_77 \def (THead k t0 t1) in (let TMP_78 \def 
(subst0_gen_head k u t0 t1 TMP_77 d H1) in (or3_ind TMP_22 TMP_28 TMP_35 P 
TMP_45 TMP_58 TMP_76 TMP_78)))))))))))))))))))))))) in (T_ind TMP_1 TMP_3 
TMP_17 TMP_79 t)))))).

theorem subst0_lift_lt:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst0 i 
(lift h (minus d (S i)) u) (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(let TMP_6 \def (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (d: nat).((lt n d) \to (\forall 
(h: nat).(let TMP_1 \def (S n) in (let TMP_2 \def (minus d TMP_1) in (let 
TMP_3 \def (lift h TMP_2 t) in (let TMP_4 \def (lift h d t0) in (let TMP_5 
\def (lift h d t3) in (subst0 n TMP_3 TMP_4 TMP_5))))))))))))) in (let TMP_59 
\def (\lambda (v: T).(\lambda (i0: nat).(\lambda (d: nat).(\lambda (H0: (lt 
i0 d)).(\lambda (h: nat).(let TMP_7 \def (TLRef i0) in (let TMP_14 \def 
(\lambda (t: T).(let TMP_8 \def (S i0) in (let TMP_9 \def (minus d TMP_8) in 
(let TMP_10 \def (lift h TMP_9 v) in (let TMP_11 \def (S i0) in (let TMP_12 
\def (lift TMP_11 O v) in (let TMP_13 \def (lift h d TMP_12) in (subst0 i0 
TMP_10 t TMP_13)))))))) in (let TMP_15 \def (S i0) in (let w \def (minus d 
TMP_15) in (let TMP_16 \def (S i0) in (let TMP_17 \def (S i0) in (let TMP_18 
\def (minus d TMP_17) in (let TMP_19 \def (plus TMP_16 TMP_18) in (let TMP_25 
\def (\lambda (n: nat).(let TMP_20 \def (lift h w v) in (let TMP_21 \def 
(TLRef i0) in (let TMP_22 \def (S i0) in (let TMP_23 \def (lift TMP_22 O v) 
in (let TMP_24 \def (lift h n TMP_23) in (subst0 i0 TMP_20 TMP_21 
TMP_24))))))) in (let TMP_26 \def (S i0) in (let TMP_27 \def (S i0) in (let 
TMP_28 \def (minus d TMP_27) in (let TMP_29 \def (lift h TMP_28 v) in (let 
TMP_30 \def (lift TMP_26 O TMP_29) in (let TMP_33 \def (\lambda (t: T).(let 
TMP_31 \def (lift h w v) in (let TMP_32 \def (TLRef i0) in (subst0 i0 TMP_31 
TMP_32 t)))) in (let TMP_34 \def (S i0) in (let TMP_35 \def (minus d TMP_34) 
in (let TMP_36 \def (lift h TMP_35 v) in (let TMP_37 \def (subst0_lref TMP_36 
i0) in (let TMP_38 \def (S i0) in (let TMP_39 \def (S i0) in (let TMP_40 \def 
(minus d TMP_39) in (let TMP_41 \def (plus TMP_38 TMP_40) in (let TMP_42 \def 
(S i0) in (let TMP_43 \def (lift TMP_42 O v) in (let TMP_44 \def (lift h 
TMP_41 TMP_43) in (let TMP_45 \def (S i0) in (let TMP_46 \def (S i0) in (let 
TMP_47 \def (minus d TMP_46) in (let TMP_48 \def (S i0) in (let TMP_49 \def 
(minus d TMP_48) in (let TMP_50 \def (le_O_n TMP_49) in (let TMP_51 \def 
(lift_d v h TMP_45 TMP_47 O TMP_50) in (let TMP_52 \def (eq_ind_r T TMP_30 
TMP_33 TMP_37 TMP_44 TMP_51) in (let TMP_53 \def (S i0) in (let TMP_54 \def 
(le_plus_minus_r TMP_53 d H0) in (let TMP_55 \def (eq_ind nat TMP_19 TMP_25 
TMP_52 d TMP_54) in (let TMP_56 \def (TLRef i0) in (let TMP_57 \def (lift h d 
TMP_56) in (let TMP_58 \def (lift_lref_lt i0 h d H0) in (eq_ind_r T TMP_7 
TMP_14 TMP_55 TMP_57 TMP_58)))))))))))))))))))))))))))))))))))))))))))))) in 
(let TMP_98 \def (\lambda (v: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda 
(i0: nat).(\lambda (_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: 
nat).((lt i0 d) \to (\forall (h: nat).(subst0 i0 (lift h (minus d (S i0)) v) 
(lift h d u1) (lift h d u2))))))).(\lambda (t: T).(\lambda (k: K).(\lambda 
(d: nat).(\lambda (H2: (lt i0 d)).(\lambda (h: nat).(let TMP_60 \def (lift h 
d u1) in (let TMP_61 \def (s k d) in (let TMP_62 \def (lift h TMP_61 t) in 
(let TMP_63 \def (THead k TMP_60 TMP_62) in (let TMP_69 \def (\lambda (t0: 
T).(let TMP_64 \def (S i0) in (let TMP_65 \def (minus d TMP_64) in (let 
TMP_66 \def (lift h TMP_65 v) in (let TMP_67 \def (THead k u2 t) in (let 
TMP_68 \def (lift h d TMP_67) in (subst0 i0 TMP_66 t0 TMP_68))))))) in (let 
TMP_70 \def (lift h d u2) in (let TMP_71 \def (s k d) in (let TMP_72 \def 
(lift h TMP_71 t) in (let TMP_73 \def (THead k TMP_70 TMP_72) in (let TMP_81 
\def (\lambda (t0: T).(let TMP_74 \def (S i0) in (let TMP_75 \def (minus d 
TMP_74) in (let TMP_76 \def (lift h TMP_75 v) in (let TMP_77 \def (lift h d 
u1) in (let TMP_78 \def (s k d) in (let TMP_79 \def (lift h TMP_78 t) in (let 
TMP_80 \def (THead k TMP_77 TMP_79) in (subst0 i0 TMP_76 TMP_80 t0))))))))) 
in (let TMP_82 \def (S i0) in (let TMP_83 \def (minus d TMP_82) in (let 
TMP_84 \def (lift h TMP_83 v) in (let TMP_85 \def (lift h d u2) in (let 
TMP_86 \def (lift h d u1) in (let TMP_87 \def (H1 d H2 h) in (let TMP_88 \def 
(s k d) in (let TMP_89 \def (lift h TMP_88 t) in (let TMP_90 \def (subst0_fst 
TMP_84 TMP_85 TMP_86 i0 TMP_87 TMP_89 k) in (let TMP_91 \def (THead k u2 t) 
in (let TMP_92 \def (lift h d TMP_91) in (let TMP_93 \def (lift_head k u2 t h 
d) in (let TMP_94 \def (eq_ind_r T TMP_73 TMP_81 TMP_90 TMP_92 TMP_93) in 
(let TMP_95 \def (THead k u1 t) in (let TMP_96 \def (lift h d TMP_95) in (let 
TMP_97 \def (lift_head k u1 t h d) in (eq_ind_r T TMP_63 TMP_69 TMP_94 TMP_96 
TMP_97)))))))))))))))))))))))))))))))))))))) in (let TMP_172 \def (\lambda 
(k: K).(\lambda (v: T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 (s k i0) v t3 t0)).(\lambda (H1: ((\forall (d: 
nat).((lt (s k i0) d) \to (\forall (h: nat).(subst0 (s k i0) (lift h (minus d 
(S (s k i0))) v) (lift h d t3) (lift h d t0))))))).(\lambda (u0: T).(\lambda 
(d: nat).(\lambda (H2: (lt i0 d)).(\lambda (h: nat).(let TMP_99 \def (s k i0) 
in (let TMP_100 \def (S TMP_99) in (let TMP_106 \def (\lambda (n: 
nat).(\forall (d0: nat).((lt (s k i0) d0) \to (\forall (h0: nat).(let TMP_101 
\def (s k i0) in (let TMP_102 \def (minus d0 n) in (let TMP_103 \def (lift h0 
TMP_102 v) in (let TMP_104 \def (lift h0 d0 t3) in (let TMP_105 \def (lift h0 
d0 t0) in (subst0 TMP_101 TMP_103 TMP_104 TMP_105)))))))))) in (let TMP_107 
\def (S i0) in (let TMP_108 \def (s k TMP_107) in (let TMP_109 \def (s_S k 
i0) in (let H3 \def (eq_ind_r nat TMP_100 TMP_106 H1 TMP_108 TMP_109) in (let 
TMP_110 \def (lift h d u0) in (let TMP_111 \def (s k d) in (let TMP_112 \def 
(lift h TMP_111 t3) in (let TMP_113 \def (THead k TMP_110 TMP_112) in (let 
TMP_119 \def (\lambda (t: T).(let TMP_114 \def (S i0) in (let TMP_115 \def 
(minus d TMP_114) in (let TMP_116 \def (lift h TMP_115 v) in (let TMP_117 
\def (THead k u0 t0) in (let TMP_118 \def (lift h d TMP_117) in (subst0 i0 
TMP_116 t TMP_118))))))) in (let TMP_120 \def (lift h d u0) in (let TMP_121 
\def (s k d) in (let TMP_122 \def (lift h TMP_121 t0) in (let TMP_123 \def 
(THead k TMP_120 TMP_122) in (let TMP_131 \def (\lambda (t: T).(let TMP_124 
\def (S i0) in (let TMP_125 \def (minus d TMP_124) in (let TMP_126 \def (lift 
h TMP_125 v) in (let TMP_127 \def (lift h d u0) in (let TMP_128 \def (s k d) 
in (let TMP_129 \def (lift h TMP_128 t3) in (let TMP_130 \def (THead k 
TMP_127 TMP_129) in (subst0 i0 TMP_126 TMP_130 t))))))))) in (let TMP_132 
\def (s k d) in (let TMP_133 \def (S i0) in (let TMP_134 \def (s k TMP_133) 
in (let TMP_135 \def (minus TMP_132 TMP_134) in (let TMP_145 \def (\lambda 
(n: nat).(let TMP_136 \def (lift h n v) in (let TMP_137 \def (lift h d u0) in 
(let TMP_138 \def (s k d) in (let TMP_139 \def (lift h TMP_138 t3) in (let 
TMP_140 \def (THead k TMP_137 TMP_139) in (let TMP_141 \def (lift h d u0) in 
(let TMP_142 \def (s k d) in (let TMP_143 \def (lift h TMP_142 t0) in (let 
TMP_144 \def (THead k TMP_141 TMP_143) in (subst0 i0 TMP_136 TMP_140 
TMP_144))))))))))) in (let TMP_146 \def (s k d) in (let TMP_147 \def (S i0) 
in (let TMP_148 \def (s k TMP_147) in (let TMP_149 \def (minus TMP_146 
TMP_148) in (let TMP_150 \def (lift h TMP_149 v) in (let TMP_151 \def (s k d) 
in (let TMP_152 \def (lift h TMP_151 t0) in (let TMP_153 \def (s k d) in (let 
TMP_154 \def (lift h TMP_153 t3) in (let TMP_155 \def (s k d) in (let TMP_156 
\def (s_lt k i0 d H2) in (let TMP_157 \def (H3 TMP_155 TMP_156 h) in (let 
TMP_158 \def (lift h d u0) in (let TMP_159 \def (subst0_snd k TMP_150 TMP_152 
TMP_154 i0 TMP_157 TMP_158) in (let TMP_160 \def (S i0) in (let TMP_161 \def 
(minus d TMP_160) in (let TMP_162 \def (S i0) in (let TMP_163 \def (minus_s_s 
k d TMP_162) in (let TMP_164 \def (eq_ind nat TMP_135 TMP_145 TMP_159 TMP_161 
TMP_163) in (let TMP_165 \def (THead k u0 t0) in (let TMP_166 \def (lift h d 
TMP_165) in (let TMP_167 \def (lift_head k u0 t0 h d) in (let TMP_168 \def 
(eq_ind_r T TMP_123 TMP_131 TMP_164 TMP_166 TMP_167) in (let TMP_169 \def 
(THead k u0 t3) in (let TMP_170 \def (lift h d TMP_169) in (let TMP_171 \def 
(lift_head k u0 t3 h d) in (eq_ind_r T TMP_113 TMP_119 TMP_168 TMP_170 
TMP_171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_243 \def (\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((lt 
i0 d) \to (\forall (h: nat).(subst0 i0 (lift h (minus d (S i0)) v) (lift h d 
u1) (lift h d u2))))))).(\lambda (k: K).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (_: (subst0 (s k i0) v t0 t3)).(\lambda (H3: ((\forall (d: 
nat).((lt (s k i0) d) \to (\forall (h: nat).(subst0 (s k i0) (lift h (minus d 
(S (s k i0))) v) (lift h d t0) (lift h d t3))))))).(\lambda (d: nat).(\lambda 
(H4: (lt i0 d)).(\lambda (h: nat).(let TMP_173 \def (s k i0) in (let TMP_174 
\def (S TMP_173) in (let TMP_180 \def (\lambda (n: nat).(\forall (d0: 
nat).((lt (s k i0) d0) \to (\forall (h0: nat).(let TMP_175 \def (s k i0) in 
(let TMP_176 \def (minus d0 n) in (let TMP_177 \def (lift h0 TMP_176 v) in 
(let TMP_178 \def (lift h0 d0 t0) in (let TMP_179 \def (lift h0 d0 t3) in 
(subst0 TMP_175 TMP_177 TMP_178 TMP_179)))))))))) in (let TMP_181 \def (S i0) 
in (let TMP_182 \def (s k TMP_181) in (let TMP_183 \def (s_S k i0) in (let H5 
\def (eq_ind_r nat TMP_174 TMP_180 H3 TMP_182 TMP_183) in (let TMP_184 \def 
(lift h d u1) in (let TMP_185 \def (s k d) in (let TMP_186 \def (lift h 
TMP_185 t0) in (let TMP_187 \def (THead k TMP_184 TMP_186) in (let TMP_193 
\def (\lambda (t: T).(let TMP_188 \def (S i0) in (let TMP_189 \def (minus d 
TMP_188) in (let TMP_190 \def (lift h TMP_189 v) in (let TMP_191 \def (THead 
k u2 t3) in (let TMP_192 \def (lift h d TMP_191) in (subst0 i0 TMP_190 t 
TMP_192))))))) in (let TMP_194 \def (lift h d u2) in (let TMP_195 \def (s k 
d) in (let TMP_196 \def (lift h TMP_195 t3) in (let TMP_197 \def (THead k 
TMP_194 TMP_196) in (let TMP_205 \def (\lambda (t: T).(let TMP_198 \def (S 
i0) in (let TMP_199 \def (minus d TMP_198) in (let TMP_200 \def (lift h 
TMP_199 v) in (let TMP_201 \def (lift h d u1) in (let TMP_202 \def (s k d) in 
(let TMP_203 \def (lift h TMP_202 t0) in (let TMP_204 \def (THead k TMP_201 
TMP_203) in (subst0 i0 TMP_200 TMP_204 t))))))))) in (let TMP_206 \def (S i0) 
in (let TMP_207 \def (minus d TMP_206) in (let TMP_208 \def (lift h TMP_207 
v) in (let TMP_209 \def (lift h d u1) in (let TMP_210 \def (lift h d u2) in 
(let TMP_211 \def (H1 d H4 h) in (let TMP_212 \def (s k d) in (let TMP_213 
\def (lift h TMP_212 t0) in (let TMP_214 \def (s k d) in (let TMP_215 \def 
(lift h TMP_214 t3) in (let TMP_216 \def (s k d) in (let TMP_217 \def (S i0) 
in (let TMP_218 \def (s k TMP_217) in (let TMP_219 \def (minus TMP_216 
TMP_218) in (let TMP_226 \def (\lambda (n: nat).(let TMP_220 \def (s k i0) in 
(let TMP_221 \def (lift h n v) in (let TMP_222 \def (s k d) in (let TMP_223 
\def (lift h TMP_222 t0) in (let TMP_224 \def (s k d) in (let TMP_225 \def 
(lift h TMP_224 t3) in (subst0 TMP_220 TMP_221 TMP_223 TMP_225)))))))) in 
(let TMP_227 \def (s k d) in (let TMP_228 \def (s_lt k i0 d H4) in (let 
TMP_229 \def (H5 TMP_227 TMP_228 h) in (let TMP_230 \def (S i0) in (let 
TMP_231 \def (minus d TMP_230) in (let TMP_232 \def (S i0) in (let TMP_233 
\def (minus_s_s k d TMP_232) in (let TMP_234 \def (eq_ind nat TMP_219 TMP_226 
TMP_229 TMP_231 TMP_233) in (let TMP_235 \def (subst0_both TMP_208 TMP_209 
TMP_210 i0 TMP_211 k TMP_213 TMP_215 TMP_234) in (let TMP_236 \def (THead k 
u2 t3) in (let TMP_237 \def (lift h d TMP_236) in (let TMP_238 \def 
(lift_head k u2 t3 h d) in (let TMP_239 \def (eq_ind_r T TMP_197 TMP_205 
TMP_235 TMP_237 TMP_238) in (let TMP_240 \def (THead k u1 t0) in (let TMP_241 
\def (lift h d TMP_240) in (let TMP_242 \def (lift_head k u1 t0 h d) in 
(eq_ind_r T TMP_187 TMP_193 TMP_239 TMP_241 
TMP_242))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(subst0_ind TMP_6 TMP_59 TMP_98 TMP_172 TMP_243 i u t1 t2 H)))))))))).

theorem subst0_lift_ge:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall 
(h: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 
(plus i h) u (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (H: (subst0 i u t1 t2)).(let TMP_4 \def (\lambda (n: 
nat).(\lambda (t: T).(\lambda (t0: T).(\lambda (t3: T).(\forall (d: nat).((le 
d n) \to (let TMP_1 \def (plus n h) in (let TMP_2 \def (lift h d t0) in (let 
TMP_3 \def (lift h d t3) in (subst0 TMP_1 t TMP_2 TMP_3)))))))))) in (let 
TMP_52 \def (\lambda (v: T).(\lambda (i0: nat).(\lambda (d: nat).(\lambda 
(H0: (le d i0)).(let TMP_5 \def (plus i0 h) in (let TMP_6 \def (TLRef TMP_5) 
in (let TMP_11 \def (\lambda (t: T).(let TMP_7 \def (plus i0 h) in (let TMP_8 
\def (S i0) in (let TMP_9 \def (lift TMP_8 O v) in (let TMP_10 \def (lift h d 
TMP_9) in (subst0 TMP_7 v t TMP_10)))))) in (let TMP_12 \def (S i0) in (let 
TMP_13 \def (plus h TMP_12) in (let TMP_14 \def (lift TMP_13 O v) in (let 
TMP_18 \def (\lambda (t: T).(let TMP_15 \def (plus i0 h) in (let TMP_16 \def 
(plus i0 h) in (let TMP_17 \def (TLRef TMP_16) in (subst0 TMP_15 v TMP_17 
t))))) in (let TMP_19 \def (plus h i0) in (let TMP_20 \def (S TMP_19) in (let 
TMP_25 \def (\lambda (n: nat).(let TMP_21 \def (plus i0 h) in (let TMP_22 
\def (plus i0 h) in (let TMP_23 \def (TLRef TMP_22) in (let TMP_24 \def (lift 
n O v) in (subst0 TMP_21 v TMP_23 TMP_24)))))) in (let TMP_26 \def (plus h 
i0) in (let TMP_31 \def (\lambda (n: nat).(let TMP_27 \def (TLRef n) in (let 
TMP_28 \def (plus h i0) in (let TMP_29 \def (S TMP_28) in (let TMP_30 \def 
(lift TMP_29 O v) in (subst0 n v TMP_27 TMP_30)))))) in (let TMP_32 \def 
(plus h i0) in (let TMP_33 \def (subst0_lref v TMP_32) in (let TMP_34 \def 
(plus i0 h) in (let TMP_35 \def (plus_sym i0 h) in (let TMP_36 \def (eq_ind_r 
nat TMP_26 TMP_31 TMP_33 TMP_34 TMP_35) in (let TMP_37 \def (S i0) in (let 
TMP_38 \def (plus h TMP_37) in (let TMP_39 \def (plus_n_Sm h i0) in (let 
TMP_40 \def (eq_ind nat TMP_20 TMP_25 TMP_36 TMP_38 TMP_39) in (let TMP_41 
\def (S i0) in (let TMP_42 \def (lift TMP_41 O v) in (let TMP_43 \def (lift h 
d TMP_42) in (let TMP_44 \def (S i0) in (let TMP_45 \def (le_S d i0 H0) in 
(let TMP_46 \def (le_O_n d) in (let TMP_47 \def (lift_free v TMP_44 h O d 
TMP_45 TMP_46) in (let TMP_48 \def (eq_ind_r T TMP_14 TMP_18 TMP_40 TMP_43 
TMP_47) in (let TMP_49 \def (TLRef i0) in (let TMP_50 \def (lift h d TMP_49) 
in (let TMP_51 \def (lift_lref_ge i0 h d H0) in (eq_ind_r T TMP_6 TMP_11 
TMP_48 TMP_50 TMP_51))))))))))))))))))))))))))))))))))))) in (let TMP_85 \def 
(\lambda (v: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i0: nat).(\lambda 
(_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((le d i0) \to 
(subst0 (plus i0 h) v (lift h d u1) (lift h d u2)))))).(\lambda (t: 
T).(\lambda (k: K).(\lambda (d: nat).(\lambda (H2: (le d i0)).(let TMP_53 
\def (lift h d u1) in (let TMP_54 \def (s k d) in (let TMP_55 \def (lift h 
TMP_54 t) in (let TMP_56 \def (THead k TMP_53 TMP_55) in (let TMP_60 \def 
(\lambda (t0: T).(let TMP_57 \def (plus i0 h) in (let TMP_58 \def (THead k u2 
t) in (let TMP_59 \def (lift h d TMP_58) in (subst0 TMP_57 v t0 TMP_59))))) 
in (let TMP_61 \def (lift h d u2) in (let TMP_62 \def (s k d) in (let TMP_63 
\def (lift h TMP_62 t) in (let TMP_64 \def (THead k TMP_61 TMP_63) in (let 
TMP_70 \def (\lambda (t0: T).(let TMP_65 \def (plus i0 h) in (let TMP_66 \def 
(lift h d u1) in (let TMP_67 \def (s k d) in (let TMP_68 \def (lift h TMP_67 
t) in (let TMP_69 \def (THead k TMP_66 TMP_68) in (subst0 TMP_65 v TMP_69 
t0))))))) in (let TMP_71 \def (lift h d u2) in (let TMP_72 \def (lift h d u1) 
in (let TMP_73 \def (plus i0 h) in (let TMP_74 \def (H1 d H2) in (let TMP_75 
\def (s k d) in (let TMP_76 \def (lift h TMP_75 t) in (let TMP_77 \def 
(subst0_fst v TMP_71 TMP_72 TMP_73 TMP_74 TMP_76 k) in (let TMP_78 \def 
(THead k u2 t) in (let TMP_79 \def (lift h d TMP_78) in (let TMP_80 \def 
(lift_head k u2 t h d) in (let TMP_81 \def (eq_ind_r T TMP_64 TMP_70 TMP_77 
TMP_79 TMP_80) in (let TMP_82 \def (THead k u1 t) in (let TMP_83 \def (lift h 
d TMP_82) in (let TMP_84 \def (lift_head k u1 t h d) in (eq_ind_r T TMP_56 
TMP_60 TMP_81 TMP_83 TMP_84))))))))))))))))))))))))))))))))))) in (let 
TMP_129 \def (\lambda (k: K).(\lambda (v: T).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (i0: nat).(\lambda (_: (subst0 (s k i0) v t3 t0)).(\lambda (H1: 
((\forall (d: nat).((le d (s k i0)) \to (subst0 (plus (s k i0) h) v (lift h d 
t3) (lift h d t0)))))).(\lambda (u0: T).(\lambda (d: nat).(\lambda (H2: (le d 
i0)).(let TMP_86 \def (s k i0) in (let TMP_87 \def (plus TMP_86 h) in (let 
TMP_90 \def (\lambda (n: nat).(\forall (d0: nat).((le d0 (s k i0)) \to (let 
TMP_88 \def (lift h d0 t3) in (let TMP_89 \def (lift h d0 t0) in (subst0 n v 
TMP_88 TMP_89)))))) in (let TMP_91 \def (plus i0 h) in (let TMP_92 \def (s k 
TMP_91) in (let TMP_93 \def (s_plus k i0 h) in (let H3 \def (eq_ind_r nat 
TMP_87 TMP_90 H1 TMP_92 TMP_93) in (let TMP_94 \def (lift h d u0) in (let 
TMP_95 \def (s k d) in (let TMP_96 \def (lift h TMP_95 t3) in (let TMP_97 
\def (THead k TMP_94 TMP_96) in (let TMP_101 \def (\lambda (t: T).(let TMP_98 
\def (plus i0 h) in (let TMP_99 \def (THead k u0 t0) in (let TMP_100 \def 
(lift h d TMP_99) in (subst0 TMP_98 v t TMP_100))))) in (let TMP_102 \def 
(lift h d u0) in (let TMP_103 \def (s k d) in (let TMP_104 \def (lift h 
TMP_103 t0) in (let TMP_105 \def (THead k TMP_102 TMP_104) in (let TMP_111 
\def (\lambda (t: T).(let TMP_106 \def (plus i0 h) in (let TMP_107 \def (lift 
h d u0) in (let TMP_108 \def (s k d) in (let TMP_109 \def (lift h TMP_108 t3) 
in (let TMP_110 \def (THead k TMP_107 TMP_109) in (subst0 TMP_106 v TMP_110 
t))))))) in (let TMP_112 \def (s k d) in (let TMP_113 \def (lift h TMP_112 
t0) in (let TMP_114 \def (s k d) in (let TMP_115 \def (lift h TMP_114 t3) in 
(let TMP_116 \def (plus i0 h) in (let TMP_117 \def (s k d) in (let TMP_118 
\def (s_le k d i0 H2) in (let TMP_119 \def (H3 TMP_117 TMP_118) in (let 
TMP_120 \def (lift h d u0) in (let TMP_121 \def (subst0_snd k v TMP_113 
TMP_115 TMP_116 TMP_119 TMP_120) in (let TMP_122 \def (THead k u0 t0) in (let 
TMP_123 \def (lift h d TMP_122) in (let TMP_124 \def (lift_head k u0 t0 h d) 
in (let TMP_125 \def (eq_ind_r T TMP_105 TMP_111 TMP_121 TMP_123 TMP_124) in 
(let TMP_126 \def (THead k u0 t3) in (let TMP_127 \def (lift h d TMP_126) in 
(let TMP_128 \def (lift_head k u0 t3 h d) in (eq_ind_r T TMP_97 TMP_101 
TMP_125 TMP_127 TMP_128))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_175 \def (\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((le 
d i0) \to (subst0 (plus i0 h) v (lift h d u1) (lift h d u2)))))).(\lambda (k: 
K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (subst0 (s k i0) v t0 
t3)).(\lambda (H3: ((\forall (d: nat).((le d (s k i0)) \to (subst0 (plus (s k 
i0) h) v (lift h d t0) (lift h d t3)))))).(\lambda (d: nat).(\lambda (H4: (le 
d i0)).(let TMP_130 \def (s k i0) in (let TMP_131 \def (plus TMP_130 h) in 
(let TMP_134 \def (\lambda (n: nat).(\forall (d0: nat).((le d0 (s k i0)) \to 
(let TMP_132 \def (lift h d0 t0) in (let TMP_133 \def (lift h d0 t3) in 
(subst0 n v TMP_132 TMP_133)))))) in (let TMP_135 \def (plus i0 h) in (let 
TMP_136 \def (s k TMP_135) in (let TMP_137 \def (s_plus k i0 h) in (let H5 
\def (eq_ind_r nat TMP_131 TMP_134 H3 TMP_136 TMP_137) in (let TMP_138 \def 
(lift h d u1) in (let TMP_139 \def (s k d) in (let TMP_140 \def (lift h 
TMP_139 t0) in (let TMP_141 \def (THead k TMP_138 TMP_140) in (let TMP_145 
\def (\lambda (t: T).(let TMP_142 \def (plus i0 h) in (let TMP_143 \def 
(THead k u2 t3) in (let TMP_144 \def (lift h d TMP_143) in (subst0 TMP_142 v 
t TMP_144))))) in (let TMP_146 \def (lift h d u2) in (let TMP_147 \def (s k 
d) in (let TMP_148 \def (lift h TMP_147 t3) in (let TMP_149 \def (THead k 
TMP_146 TMP_148) in (let TMP_155 \def (\lambda (t: T).(let TMP_150 \def (plus 
i0 h) in (let TMP_151 \def (lift h d u1) in (let TMP_152 \def (s k d) in (let 
TMP_153 \def (lift h TMP_152 t0) in (let TMP_154 \def (THead k TMP_151 
TMP_153) in (subst0 TMP_150 v TMP_154 t))))))) in (let TMP_156 \def (lift h d 
u1) in (let TMP_157 \def (lift h d u2) in (let TMP_158 \def (plus i0 h) in 
(let TMP_159 \def (H1 d H4) in (let TMP_160 \def (s k d) in (let TMP_161 \def 
(lift h TMP_160 t0) in (let TMP_162 \def (s k d) in (let TMP_163 \def (lift h 
TMP_162 t3) in (let TMP_164 \def (s k d) in (let TMP_165 \def (s_le k d i0 
H4) in (let TMP_166 \def (H5 TMP_164 TMP_165) in (let TMP_167 \def 
(subst0_both v TMP_156 TMP_157 TMP_158 TMP_159 k TMP_161 TMP_163 TMP_166) in 
(let TMP_168 \def (THead k u2 t3) in (let TMP_169 \def (lift h d TMP_168) in 
(let TMP_170 \def (lift_head k u2 t3 h d) in (let TMP_171 \def (eq_ind_r T 
TMP_149 TMP_155 TMP_167 TMP_169 TMP_170) in (let TMP_172 \def (THead k u1 t0) 
in (let TMP_173 \def (lift h d TMP_172) in (let TMP_174 \def (lift_head k u1 
t0 h d) in (eq_ind_r T TMP_141 TMP_145 TMP_171 TMP_173 
TMP_174)))))))))))))))))))))))))))))))))))))))))))))))))) in (subst0_ind 
TMP_4 TMP_52 TMP_85 TMP_129 TMP_175 i u t1 t2 H))))))))))).

theorem subst0_lift_ge_S:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 (S i) u (lift (S O) d 
t1) (lift (S O) d t2))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(\lambda (d: nat).(\lambda (H0: (le d i)).(let TMP_1 
\def (S O) in (let TMP_2 \def (plus i TMP_1) in (let TMP_7 \def (\lambda (n: 
nat).(let TMP_3 \def (S O) in (let TMP_4 \def (lift TMP_3 d t1) in (let TMP_5 
\def (S O) in (let TMP_6 \def (lift TMP_5 d t2) in (subst0 n u TMP_4 
TMP_6)))))) in (let TMP_8 \def (S O) in (let TMP_9 \def (subst0_lift_ge t1 t2 
u i TMP_8 H d H0) in (let TMP_10 \def (S i) in (let TMP_11 \def (S O) in (let 
TMP_12 \def (plus TMP_11 i) in (let TMP_14 \def (\lambda (n: nat).(let TMP_13 
\def (S i) in (eq nat n TMP_13))) in (let TMP_15 \def (S O) in (let TMP_16 
\def (plus TMP_15 i) in (let TMP_17 \def (S i) in (let TMP_18 \def (S i) in 
(let TMP_19 \def (le_n TMP_18) in (let TMP_20 \def (S O) in (let TMP_21 \def 
(plus TMP_20 i) in (let TMP_22 \def (le_n TMP_21) in (let TMP_23 \def 
(le_antisym TMP_16 TMP_17 TMP_19 TMP_22) in (let TMP_24 \def (S O) in (let 
TMP_25 \def (plus i TMP_24) in (let TMP_26 \def (S O) in (let TMP_27 \def 
(plus_sym i TMP_26) in (let TMP_28 \def (eq_ind_r nat TMP_12 TMP_14 TMP_23 
TMP_25 TMP_27) in (eq_ind nat TMP_2 TMP_7 TMP_9 TMP_10 
TMP_28)))))))))))))))))))))))))))))).

theorem subst0_lift_ge_s:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((le d i) \to (\forall (b: B).(subst0 (s 
(Bind b) i) u (lift (S O) d t1) (lift (S O) d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(\lambda (d: nat).(\lambda (H0: (le d i)).(\lambda 
(_: B).(subst0_lift_ge_S t1 t2 u i H d H0)))))))).

