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

include "basic_1/subst/defs.ma".

include "basic_1/subst0/fwd.ma".

theorem subst_sort:
 \forall (v: T).(\forall (d: nat).(\forall (k: nat).(eq T (subst d v (TSort 
k)) (TSort k))))
\def
 \lambda (_: T).(\lambda (_: nat).(\lambda (k: nat).(let TMP_1 \def (TSort k) 
in (refl_equal T TMP_1)))).

theorem subst_lref_lt:
 \forall (v: T).(\forall (d: nat).(\forall (i: nat).((lt i d) \to (eq T 
(subst d v (TLRef i)) (TLRef i)))))
\def
 \lambda (v: T).(\lambda (d: nat).(\lambda (i: nat).(\lambda (H: (lt i 
d)).(let TMP_5 \def (\lambda (b: bool).(let TMP_3 \def (match b with [true 
\Rightarrow (TLRef i) | false \Rightarrow (let TMP_1 \def (blt d i) in (match 
TMP_1 with [true \Rightarrow (let TMP_2 \def (pred i) in (TLRef TMP_2)) | 
false \Rightarrow (lift d O v)]))]) in (let TMP_4 \def (TLRef i) in (eq T 
TMP_3 TMP_4)))) in (let TMP_6 \def (TLRef i) in (let TMP_7 \def (refl_equal T 
TMP_6) in (let TMP_8 \def (blt i d) in (let TMP_9 \def (lt_blt d i H) in 
(eq_ind_r bool true TMP_5 TMP_7 TMP_8 TMP_9))))))))).

theorem subst_lref_eq:
 \forall (v: T).(\forall (i: nat).(eq T (subst i v (TLRef i)) (lift i O v)))
\def
 \lambda (v: T).(\lambda (i: nat).(let TMP_4 \def (\lambda (b: bool).(let 
TMP_2 \def (match b with [true \Rightarrow (TLRef i) | false \Rightarrow 
(match b with [true \Rightarrow (let TMP_1 \def (pred i) in (TLRef TMP_1)) | 
false \Rightarrow (lift i O v)])]) in (let TMP_3 \def (lift i O v) in (eq T 
TMP_2 TMP_3)))) in (let TMP_5 \def (lift i O v) in (let TMP_6 \def 
(refl_equal T TMP_5) in (let TMP_7 \def (blt i i) in (let TMP_8 \def (le_n i) 
in (let TMP_9 \def (le_bge i i TMP_8) in (eq_ind_r bool false TMP_4 TMP_6 
TMP_7 TMP_9)))))))).

theorem subst_lref_gt:
 \forall (v: T).(\forall (d: nat).(\forall (i: nat).((lt d i) \to (eq T 
(subst d v (TLRef i)) (TLRef (pred i))))))
\def
 \lambda (v: T).(\lambda (d: nat).(\lambda (i: nat).(\lambda (H: (lt d 
i)).(let TMP_6 \def (\lambda (b: bool).(let TMP_3 \def (match b with [true 
\Rightarrow (TLRef i) | false \Rightarrow (let TMP_1 \def (blt d i) in (match 
TMP_1 with [true \Rightarrow (let TMP_2 \def (pred i) in (TLRef TMP_2)) | 
false \Rightarrow (lift d O v)]))]) in (let TMP_4 \def (pred i) in (let TMP_5 
\def (TLRef TMP_4) in (eq T TMP_3 TMP_5))))) in (let TMP_11 \def (\lambda (b: 
bool).(let TMP_8 \def (match b with [true \Rightarrow (let TMP_7 \def (pred 
i) in (TLRef TMP_7)) | false \Rightarrow (lift d O v)]) in (let TMP_9 \def 
(pred i) in (let TMP_10 \def (TLRef TMP_9) in (eq T TMP_8 TMP_10))))) in (let 
TMP_12 \def (pred i) in (let TMP_13 \def (TLRef TMP_12) in (let TMP_14 \def 
(refl_equal T TMP_13) in (let TMP_15 \def (blt d i) in (let TMP_16 \def 
(lt_blt i d H) in (let TMP_17 \def (eq_ind_r bool true TMP_11 TMP_14 TMP_15 
TMP_16) in (let TMP_18 \def (blt i d) in (let TMP_19 \def (lt_le_weak d i H) 
in (let TMP_20 \def (le_bge d i TMP_19) in (eq_ind_r bool false TMP_6 TMP_17 
TMP_18 TMP_20))))))))))))))).

theorem subst_head:
 \forall (k: K).(\forall (w: T).(\forall (u: T).(\forall (t: T).(\forall (d: 
nat).(eq T (subst d w (THead k u t)) (THead k (subst d w u) (subst (s k d) w 
t)))))))
\def
 \lambda (k: K).(\lambda (w: T).(\lambda (u: T).(\lambda (t: T).(\lambda (d: 
nat).(let TMP_1 \def (subst d w u) in (let TMP_2 \def (s k d) in (let TMP_3 
\def (subst TMP_2 w t) in (let TMP_4 \def (THead k TMP_1 TMP_3) in 
(refl_equal T TMP_4))))))))).

theorem subst_lift_SO:
 \forall (v: T).(\forall (t: T).(\forall (d: nat).(eq T (subst d v (lift (S 
O) d t)) t)))
\def
 \lambda (v: T).(\lambda (t: T).(let TMP_4 \def (\lambda (t0: T).(\forall (d: 
nat).(let TMP_1 \def (S O) in (let TMP_2 \def (lift TMP_1 d t0) in (let TMP_3 
\def (subst d v TMP_2) in (eq T TMP_3 t0)))))) in (let TMP_23 \def (\lambda 
(n: nat).(\lambda (d: nat).(let TMP_5 \def (TSort n) in (let TMP_8 \def 
(\lambda (t0: T).(let TMP_6 \def (subst d v t0) in (let TMP_7 \def (TSort n) 
in (eq T TMP_6 TMP_7)))) in (let TMP_9 \def (TSort n) in (let TMP_11 \def 
(\lambda (t0: T).(let TMP_10 \def (TSort n) in (eq T t0 TMP_10))) in (let 
TMP_12 \def (TSort n) in (let TMP_13 \def (refl_equal T TMP_12) in (let 
TMP_14 \def (TSort n) in (let TMP_15 \def (subst d v TMP_14) in (let TMP_16 
\def (subst_sort v d n) in (let TMP_17 \def (eq_ind_r T TMP_9 TMP_11 TMP_13 
TMP_15 TMP_16) in (let TMP_18 \def (S O) in (let TMP_19 \def (TSort n) in 
(let TMP_20 \def (lift TMP_18 d TMP_19) in (let TMP_21 \def (S O) in (let 
TMP_22 \def (lift_sort n TMP_21 d) in (eq_ind_r T TMP_5 TMP_8 TMP_17 TMP_20 
TMP_22)))))))))))))))))) in (let TMP_103 \def (\lambda (n: nat).(\lambda (d: 
nat).(let TMP_24 \def (S O) in (let TMP_25 \def (TLRef n) in (let TMP_26 \def 
(lift TMP_24 d TMP_25) in (let TMP_27 \def (subst d v TMP_26) in (let TMP_28 
\def (TLRef n) in (let TMP_29 \def (eq T TMP_27 TMP_28) in (let TMP_48 \def 
(\lambda (H: (lt n d)).(let TMP_30 \def (TLRef n) in (let TMP_33 \def 
(\lambda (t0: T).(let TMP_31 \def (subst d v t0) in (let TMP_32 \def (TLRef 
n) in (eq T TMP_31 TMP_32)))) in (let TMP_34 \def (TLRef n) in (let TMP_36 
\def (\lambda (t0: T).(let TMP_35 \def (TLRef n) in (eq T t0 TMP_35))) in 
(let TMP_37 \def (TLRef n) in (let TMP_38 \def (refl_equal T TMP_37) in (let 
TMP_39 \def (TLRef n) in (let TMP_40 \def (subst d v TMP_39) in (let TMP_41 
\def (subst_lref_lt v d n H) in (let TMP_42 \def (eq_ind_r T TMP_34 TMP_36 
TMP_38 TMP_40 TMP_41) in (let TMP_43 \def (S O) in (let TMP_44 \def (TLRef n) 
in (let TMP_45 \def (lift TMP_43 d TMP_44) in (let TMP_46 \def (S O) in (let 
TMP_47 \def (lift_lref_lt n TMP_46 d H) in (eq_ind_r T TMP_30 TMP_33 TMP_42 
TMP_45 TMP_47))))))))))))))))) in (let TMP_102 \def (\lambda (H: (le d 
n)).(let TMP_49 \def (S O) in (let TMP_50 \def (plus n TMP_49) in (let TMP_51 
\def (TLRef TMP_50) in (let TMP_54 \def (\lambda (t0: T).(let TMP_52 \def 
(subst d v t0) in (let TMP_53 \def (TLRef n) in (eq T TMP_52 TMP_53)))) in 
(let TMP_55 \def (plus n O) in (let TMP_56 \def (S TMP_55) in (let TMP_60 
\def (\lambda (n0: nat).(let TMP_57 \def (TLRef n0) in (let TMP_58 \def 
(subst d v TMP_57) in (let TMP_59 \def (TLRef n) in (eq T TMP_58 TMP_59))))) 
in (let TMP_61 \def (plus n O) in (let TMP_62 \def (S TMP_61) in (let TMP_63 
\def (pred TMP_62) in (let TMP_64 \def (TLRef TMP_63) in (let TMP_66 \def 
(\lambda (t0: T).(let TMP_65 \def (TLRef n) in (eq T t0 TMP_65))) in (let 
TMP_67 \def (plus n O) in (let TMP_70 \def (\lambda (n0: nat).(let TMP_68 
\def (TLRef n0) in (let TMP_69 \def (TLRef n) in (eq T TMP_68 TMP_69)))) in 
(let TMP_71 \def (plus n O) in (let TMP_72 \def (plus n O) in (let TMP_73 
\def (plus_n_O n) in (let TMP_74 \def (sym_eq nat n TMP_72 TMP_73) in (let 
TMP_75 \def (f_equal nat T TLRef TMP_71 n TMP_74) in (let TMP_76 \def (plus n 
O) in (let TMP_77 \def (S TMP_76) in (let TMP_78 \def (pred TMP_77) in (let 
TMP_79 \def (plus n O) in (let TMP_80 \def (pred_Sn TMP_79) in (let TMP_81 
\def (eq_ind nat TMP_67 TMP_70 TMP_75 TMP_78 TMP_80) in (let TMP_82 \def 
(plus n O) in (let TMP_83 \def (S TMP_82) in (let TMP_84 \def (TLRef TMP_83) 
in (let TMP_85 \def (subst d v TMP_84) in (let TMP_86 \def (plus n O) in (let 
TMP_87 \def (S TMP_86) in (let TMP_88 \def (plus n O) in (let TMP_89 \def 
(le_plus_trans d n O H) in (let TMP_90 \def (le_n_S d TMP_88 TMP_89) in (let 
TMP_91 \def (subst_lref_gt v d TMP_87 TMP_90) in (let TMP_92 \def (eq_ind_r T 
TMP_64 TMP_66 TMP_81 TMP_85 TMP_91) in (let TMP_93 \def (S O) in (let TMP_94 
\def (plus n TMP_93) in (let TMP_95 \def (plus_n_Sm n O) in (let TMP_96 \def 
(eq_ind nat TMP_56 TMP_60 TMP_92 TMP_94 TMP_95) in (let TMP_97 \def (S O) in 
(let TMP_98 \def (TLRef n) in (let TMP_99 \def (lift TMP_97 d TMP_98) in (let 
TMP_100 \def (S O) in (let TMP_101 \def (lift_lref_ge n TMP_100 d H) in 
(eq_ind_r T TMP_51 TMP_54 TMP_96 TMP_99 
TMP_101))))))))))))))))))))))))))))))))))))))))))))))) in (lt_le_e n d TMP_29 
TMP_48 TMP_102))))))))))) in (let TMP_178 \def (\lambda (k: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (d: nat).(eq T (subst d v (lift (S O) d t0)) 
t0)))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: nat).(eq T (subst d v 
(lift (S O) d t1)) t1)))).(\lambda (d: nat).(let TMP_104 \def (S O) in (let 
TMP_105 \def (lift TMP_104 d t0) in (let TMP_106 \def (S O) in (let TMP_107 
\def (s k d) in (let TMP_108 \def (lift TMP_106 TMP_107 t1) in (let TMP_109 
\def (THead k TMP_105 TMP_108) in (let TMP_112 \def (\lambda (t2: T).(let 
TMP_110 \def (subst d v t2) in (let TMP_111 \def (THead k t0 t1) in (eq T 
TMP_110 TMP_111)))) in (let TMP_113 \def (S O) in (let TMP_114 \def (lift 
TMP_113 d t0) in (let TMP_115 \def (subst d v TMP_114) in (let TMP_116 \def 
(s k d) in (let TMP_117 \def (S O) in (let TMP_118 \def (s k d) in (let 
TMP_119 \def (lift TMP_117 TMP_118 t1) in (let TMP_120 \def (subst TMP_116 v 
TMP_119) in (let TMP_121 \def (THead k TMP_115 TMP_120) in (let TMP_123 \def 
(\lambda (t2: T).(let TMP_122 \def (THead k t0 t1) in (eq T t2 TMP_122))) in 
(let TMP_124 \def (THead k t0 t1) in (let TMP_125 \def (S O) in (let TMP_126 
\def (lift TMP_125 d t0) in (let TMP_127 \def (subst d v TMP_126) in (let 
TMP_128 \def (s k d) in (let TMP_129 \def (S O) in (let TMP_130 \def (s k d) 
in (let TMP_131 \def (lift TMP_129 TMP_130 t1) in (let TMP_132 \def (subst 
TMP_128 v TMP_131) in (let TMP_133 \def (THead k TMP_127 TMP_132) in (let 
TMP_134 \def (S O) in (let TMP_135 \def (lift TMP_134 d t0) in (let TMP_136 
\def (subst d v TMP_135) in (let TMP_137 \def (s k d) in (let TMP_138 \def (S 
O) in (let TMP_139 \def (s k d) in (let TMP_140 \def (lift TMP_138 TMP_139 
t1) in (let TMP_141 \def (subst TMP_137 v TMP_140) in (let TMP_142 \def 
(THead k TMP_136 TMP_141) in (let TMP_143 \def (THead k t0 t1) in (let 
TMP_144 \def (S O) in (let TMP_145 \def (lift TMP_144 d t0) in (let TMP_146 
\def (subst d v TMP_145) in (let TMP_147 \def (s k d) in (let TMP_148 \def (S 
O) in (let TMP_149 \def (s k d) in (let TMP_150 \def (lift TMP_148 TMP_149 
t1) in (let TMP_151 \def (subst TMP_147 v TMP_150) in (let TMP_152 \def 
(refl_equal K k) in (let TMP_153 \def (H d) in (let TMP_154 \def (s k d) in 
(let TMP_155 \def (H0 TMP_154) in (let TMP_156 \def (f_equal3 K T T T THead k 
k TMP_146 t0 TMP_151 t1 TMP_152 TMP_153 TMP_155) in (let TMP_157 \def (sym_eq 
T TMP_142 TMP_143 TMP_156) in (let TMP_158 \def (sym_eq T TMP_124 TMP_133 
TMP_157) in (let TMP_159 \def (S O) in (let TMP_160 \def (lift TMP_159 d t0) 
in (let TMP_161 \def (S O) in (let TMP_162 \def (s k d) in (let TMP_163 \def 
(lift TMP_161 TMP_162 t1) in (let TMP_164 \def (THead k TMP_160 TMP_163) in 
(let TMP_165 \def (subst d v TMP_164) in (let TMP_166 \def (S O) in (let 
TMP_167 \def (lift TMP_166 d t0) in (let TMP_168 \def (S O) in (let TMP_169 
\def (s k d) in (let TMP_170 \def (lift TMP_168 TMP_169 t1) in (let TMP_171 
\def (subst_head k v TMP_167 TMP_170 d) in (let TMP_172 \def (eq_ind_r T 
TMP_121 TMP_123 TMP_158 TMP_165 TMP_171) in (let TMP_173 \def (S O) in (let 
TMP_174 \def (THead k t0 t1) in (let TMP_175 \def (lift TMP_173 d TMP_174) in 
(let TMP_176 \def (S O) in (let TMP_177 \def (lift_head k t0 t1 TMP_176 d) in 
(eq_ind_r T TMP_109 TMP_112 TMP_172 TMP_175 
TMP_177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))) in (T_ind TMP_4 TMP_23 TMP_103 TMP_178 t)))))).

theorem subst_subst0:
 \forall (v: T).(\forall (t1: T).(\forall (t2: T).(\forall (d: nat).((subst0 
d v t1 t2) \to (eq T (subst d v t1) (subst d v t2))))))
\def
 \lambda (v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d v t1 t2)).(let TMP_3 \def (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(let TMP_1 \def (subst n t t0) in (let 
TMP_2 \def (subst n t t3) in (eq T TMP_1 TMP_2))))))) in (let TMP_49 \def 
(\lambda (v0: T).(\lambda (i: nat).(let TMP_4 \def (lift i O v0) in (let 
TMP_8 \def (\lambda (t: T).(let TMP_5 \def (S i) in (let TMP_6 \def (lift 
TMP_5 O v0) in (let TMP_7 \def (subst i v0 TMP_6) in (eq T t TMP_7))))) in 
(let TMP_9 \def (S O) in (let TMP_10 \def (plus TMP_9 i) in (let TMP_14 \def 
(\lambda (n: nat).(let TMP_11 \def (lift i O v0) in (let TMP_12 \def (lift n 
O v0) in (let TMP_13 \def (subst i v0 TMP_12) in (eq T TMP_11 TMP_13))))) in 
(let TMP_15 \def (S O) in (let TMP_16 \def (lift i O v0) in (let TMP_17 \def 
(lift TMP_15 i TMP_16) in (let TMP_20 \def (\lambda (t: T).(let TMP_18 \def 
(lift i O v0) in (let TMP_19 \def (subst i v0 t) in (eq T TMP_18 TMP_19)))) 
in (let TMP_21 \def (lift i O v0) in (let TMP_23 \def (\lambda (t: T).(let 
TMP_22 \def (lift i O v0) in (eq T TMP_22 t))) in (let TMP_24 \def (lift i O 
v0) in (let TMP_25 \def (refl_equal T TMP_24) in (let TMP_26 \def (S O) in 
(let TMP_27 \def (lift i O v0) in (let TMP_28 \def (lift TMP_26 i TMP_27) in 
(let TMP_29 \def (subst i v0 TMP_28) in (let TMP_30 \def (lift i O v0) in 
(let TMP_31 \def (subst_lift_SO v0 TMP_30 i) in (let TMP_32 \def (eq_ind_r T 
TMP_21 TMP_23 TMP_25 TMP_29 TMP_31) in (let TMP_33 \def (S O) in (let TMP_34 
\def (plus TMP_33 i) in (let TMP_35 \def (lift TMP_34 O v0) in (let TMP_36 
\def (S O) in (let TMP_37 \def (plus O i) in (let TMP_38 \def (le_n TMP_37) 
in (let TMP_39 \def (le_O_n i) in (let TMP_40 \def (lift_free v0 i TMP_36 O i 
TMP_38 TMP_39) in (let TMP_41 \def (eq_ind T TMP_17 TMP_20 TMP_32 TMP_35 
TMP_40) in (let TMP_42 \def (S i) in (let TMP_43 \def (S i) in (let TMP_44 
\def (refl_equal nat TMP_43) in (let TMP_45 \def (eq_ind nat TMP_10 TMP_14 
TMP_41 TMP_42 TMP_44) in (let TMP_46 \def (TLRef i) in (let TMP_47 \def 
(subst i v0 TMP_46) in (let TMP_48 \def (subst_lref_eq v0 i) in (eq_ind_r T 
TMP_4 TMP_8 TMP_45 TMP_47 TMP_48))))))))))))))))))))))))))))))))))))))) in 
(let TMP_89 \def (\lambda (v0: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda 
(i: nat).(\lambda (_: (subst0 i v0 u1 u2)).(\lambda (H1: (eq T (subst i v0 
u1) (subst i v0 u2))).(\lambda (t: T).(\lambda (k: K).(let TMP_50 \def (subst 
i v0 u1) in (let TMP_51 \def (s k i) in (let TMP_52 \def (subst TMP_51 v0 t) 
in (let TMP_53 \def (THead k TMP_50 TMP_52) in (let TMP_56 \def (\lambda (t0: 
T).(let TMP_54 \def (THead k u2 t) in (let TMP_55 \def (subst i v0 TMP_54) in 
(eq T t0 TMP_55)))) in (let TMP_57 \def (subst i v0 u2) in (let TMP_58 \def 
(s k i) in (let TMP_59 \def (subst TMP_58 v0 t) in (let TMP_60 \def (THead k 
TMP_57 TMP_59) in (let TMP_65 \def (\lambda (t0: T).(let TMP_61 \def (subst i 
v0 u1) in (let TMP_62 \def (s k i) in (let TMP_63 \def (subst TMP_62 v0 t) in 
(let TMP_64 \def (THead k TMP_61 TMP_63) in (eq T TMP_64 t0)))))) in (let 
TMP_66 \def (subst i v0 u2) in (let TMP_74 \def (\lambda (t0: T).(let TMP_67 
\def (s k i) in (let TMP_68 \def (subst TMP_67 v0 t) in (let TMP_69 \def 
(THead k t0 TMP_68) in (let TMP_70 \def (subst i v0 u2) in (let TMP_71 \def 
(s k i) in (let TMP_72 \def (subst TMP_71 v0 t) in (let TMP_73 \def (THead k 
TMP_70 TMP_72) in (eq T TMP_69 TMP_73))))))))) in (let TMP_75 \def (subst i 
v0 u2) in (let TMP_76 \def (s k i) in (let TMP_77 \def (subst TMP_76 v0 t) in 
(let TMP_78 \def (THead k TMP_75 TMP_77) in (let TMP_79 \def (refl_equal T 
TMP_78) in (let TMP_80 \def (subst i v0 u1) in (let TMP_81 \def (eq_ind_r T 
TMP_66 TMP_74 TMP_79 TMP_80 H1) in (let TMP_82 \def (THead k u2 t) in (let 
TMP_83 \def (subst i v0 TMP_82) in (let TMP_84 \def (subst_head k v0 u2 t i) 
in (let TMP_85 \def (eq_ind_r T TMP_60 TMP_65 TMP_81 TMP_83 TMP_84) in (let 
TMP_86 \def (THead k u1 t) in (let TMP_87 \def (subst i v0 TMP_86) in (let 
TMP_88 \def (subst_head k v0 u1 t i) in (eq_ind_r T TMP_53 TMP_56 TMP_85 
TMP_87 TMP_88))))))))))))))))))))))))))))))))))) in (let TMP_130 \def 
(\lambda (k: K).(\lambda (v0: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(i: nat).(\lambda (_: (subst0 (s k i) v0 t4 t3)).(\lambda (H1: (eq T (subst 
(s k i) v0 t4) (subst (s k i) v0 t3))).(\lambda (u: T).(let TMP_90 \def 
(subst i v0 u) in (let TMP_91 \def (s k i) in (let TMP_92 \def (subst TMP_91 
v0 t4) in (let TMP_93 \def (THead k TMP_90 TMP_92) in (let TMP_96 \def 
(\lambda (t: T).(let TMP_94 \def (THead k u t3) in (let TMP_95 \def (subst i 
v0 TMP_94) in (eq T t TMP_95)))) in (let TMP_97 \def (subst i v0 u) in (let 
TMP_98 \def (s k i) in (let TMP_99 \def (subst TMP_98 v0 t3) in (let TMP_100 
\def (THead k TMP_97 TMP_99) in (let TMP_105 \def (\lambda (t: T).(let 
TMP_101 \def (subst i v0 u) in (let TMP_102 \def (s k i) in (let TMP_103 \def 
(subst TMP_102 v0 t4) in (let TMP_104 \def (THead k TMP_101 TMP_103) in (eq T 
TMP_104 t)))))) in (let TMP_106 \def (s k i) in (let TMP_107 \def (subst 
TMP_106 v0 t3) in (let TMP_114 \def (\lambda (t: T).(let TMP_108 \def (subst 
i v0 u) in (let TMP_109 \def (THead k TMP_108 t) in (let TMP_110 \def (subst 
i v0 u) in (let TMP_111 \def (s k i) in (let TMP_112 \def (subst TMP_111 v0 
t3) in (let TMP_113 \def (THead k TMP_110 TMP_112) in (eq T TMP_109 
TMP_113)))))))) in (let TMP_115 \def (subst i v0 u) in (let TMP_116 \def (s k 
i) in (let TMP_117 \def (subst TMP_116 v0 t3) in (let TMP_118 \def (THead k 
TMP_115 TMP_117) in (let TMP_119 \def (refl_equal T TMP_118) in (let TMP_120 
\def (s k i) in (let TMP_121 \def (subst TMP_120 v0 t4) in (let TMP_122 \def 
(eq_ind_r T TMP_107 TMP_114 TMP_119 TMP_121 H1) in (let TMP_123 \def (THead k 
u t3) in (let TMP_124 \def (subst i v0 TMP_123) in (let TMP_125 \def 
(subst_head k v0 u t3 i) in (let TMP_126 \def (eq_ind_r T TMP_100 TMP_105 
TMP_122 TMP_124 TMP_125) in (let TMP_127 \def (THead k u t4) in (let TMP_128 
\def (subst i v0 TMP_127) in (let TMP_129 \def (subst_head k v0 u t4 i) in 
(eq_ind_r T TMP_93 TMP_96 TMP_126 TMP_128 
TMP_129))))))))))))))))))))))))))))))))))))) in (let TMP_182 \def (\lambda 
(v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda (_: 
(subst0 i v0 u1 u2)).(\lambda (H1: (eq T (subst i v0 u1) (subst i v0 
u2))).(\lambda (k: K).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (subst0 
(s k i) v0 t3 t4)).(\lambda (H3: (eq T (subst (s k i) v0 t3) (subst (s k i) 
v0 t4))).(let TMP_131 \def (subst i v0 u1) in (let TMP_132 \def (s k i) in 
(let TMP_133 \def (subst TMP_132 v0 t3) in (let TMP_134 \def (THead k TMP_131 
TMP_133) in (let TMP_137 \def (\lambda (t: T).(let TMP_135 \def (THead k u2 
t4) in (let TMP_136 \def (subst i v0 TMP_135) in (eq T t TMP_136)))) in (let 
TMP_138 \def (subst i v0 u2) in (let TMP_139 \def (s k i) in (let TMP_140 
\def (subst TMP_139 v0 t4) in (let TMP_141 \def (THead k TMP_138 TMP_140) in 
(let TMP_146 \def (\lambda (t: T).(let TMP_142 \def (subst i v0 u1) in (let 
TMP_143 \def (s k i) in (let TMP_144 \def (subst TMP_143 v0 t3) in (let 
TMP_145 \def (THead k TMP_142 TMP_144) in (eq T TMP_145 t)))))) in (let 
TMP_147 \def (subst i v0 u2) in (let TMP_155 \def (\lambda (t: T).(let 
TMP_148 \def (s k i) in (let TMP_149 \def (subst TMP_148 v0 t3) in (let 
TMP_150 \def (THead k t TMP_149) in (let TMP_151 \def (subst i v0 u2) in (let 
TMP_152 \def (s k i) in (let TMP_153 \def (subst TMP_152 v0 t4) in (let 
TMP_154 \def (THead k TMP_151 TMP_153) in (eq T TMP_150 TMP_154))))))))) in 
(let TMP_156 \def (s k i) in (let TMP_157 \def (subst TMP_156 v0 t4) in (let 
TMP_164 \def (\lambda (t: T).(let TMP_158 \def (subst i v0 u2) in (let 
TMP_159 \def (THead k TMP_158 t) in (let TMP_160 \def (subst i v0 u2) in (let 
TMP_161 \def (s k i) in (let TMP_162 \def (subst TMP_161 v0 t4) in (let 
TMP_163 \def (THead k TMP_160 TMP_162) in (eq T TMP_159 TMP_163)))))))) in 
(let TMP_165 \def (subst i v0 u2) in (let TMP_166 \def (s k i) in (let 
TMP_167 \def (subst TMP_166 v0 t4) in (let TMP_168 \def (THead k TMP_165 
TMP_167) in (let TMP_169 \def (refl_equal T TMP_168) in (let TMP_170 \def (s 
k i) in (let TMP_171 \def (subst TMP_170 v0 t3) in (let TMP_172 \def 
(eq_ind_r T TMP_157 TMP_164 TMP_169 TMP_171 H3) in (let TMP_173 \def (subst i 
v0 u1) in (let TMP_174 \def (eq_ind_r T TMP_147 TMP_155 TMP_172 TMP_173 H1) 
in (let TMP_175 \def (THead k u2 t4) in (let TMP_176 \def (subst i v0 
TMP_175) in (let TMP_177 \def (subst_head k v0 u2 t4 i) in (let TMP_178 \def 
(eq_ind_r T TMP_141 TMP_146 TMP_174 TMP_176 TMP_177) in (let TMP_179 \def 
(THead k u1 t3) in (let TMP_180 \def (subst i v0 TMP_179) in (let TMP_181 
\def (subst_head k v0 u1 t3 i) in (eq_ind_r T TMP_134 TMP_137 TMP_178 TMP_180 
TMP_181)))))))))))))))))))))))))))))))))))))))))))) in (subst0_ind TMP_3 
TMP_49 TMP_89 TMP_130 TMP_182 d v t1 t2 H)))))))))).

