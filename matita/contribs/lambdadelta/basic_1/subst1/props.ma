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

include "basic_1/subst1/fwd.ma".

include "basic_1/subst0/props.ma".

theorem subst1_head:
 \forall (v: T).(\forall (u1: T).(\forall (u2: T).(\forall (i: nat).((subst1 
i v u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((subst1 (s 
k i) v t1 t2) \to (subst1 i v (THead k u1 t1) (THead k u2 t2))))))))))
\def
 \lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i v u1 u2)).(let TMP_3 \def (\lambda (t: T).(\forall (k: 
K).(\forall (t1: T).(\forall (t2: T).((subst1 (s k i) v t1 t2) \to (let TMP_1 
\def (THead k u1 t1) in (let TMP_2 \def (THead k t t2) in (subst1 i v TMP_1 
TMP_2)))))))) in (let TMP_14 \def (\lambda (k: K).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H0: (subst1 (s k i) v t1 t2)).(let TMP_4 \def (s k i) in 
(let TMP_7 \def (\lambda (t: T).(let TMP_5 \def (THead k u1 t1) in (let TMP_6 
\def (THead k u1 t) in (subst1 i v TMP_5 TMP_6)))) in (let TMP_8 \def (THead 
k u1 t1) in (let TMP_9 \def (subst1_refl i v TMP_8) in (let TMP_13 \def 
(\lambda (t3: T).(\lambda (H1: (subst0 (s k i) v t1 t3)).(let TMP_10 \def 
(THead k u1 t1) in (let TMP_11 \def (THead k u1 t3) in (let TMP_12 \def 
(subst0_snd k v t3 t1 i H1 u1) in (subst1_single i v TMP_10 TMP_11 
TMP_12)))))) in (subst1_ind TMP_4 v t1 TMP_7 TMP_9 TMP_13 t2 H0)))))))))) in 
(let TMP_27 \def (\lambda (t2: T).(\lambda (H0: (subst0 i v u1 t2)).(\lambda 
(k: K).(\lambda (t1: T).(\lambda (t0: T).(\lambda (H1: (subst1 (s k i) v t1 
t0)).(let TMP_15 \def (s k i) in (let TMP_18 \def (\lambda (t: T).(let TMP_16 
\def (THead k u1 t1) in (let TMP_17 \def (THead k t2 t) in (subst1 i v TMP_16 
TMP_17)))) in (let TMP_19 \def (THead k u1 t1) in (let TMP_20 \def (THead k 
t2 t1) in (let TMP_21 \def (subst0_fst v t2 u1 i H0 t1 k) in (let TMP_22 \def 
(subst1_single i v TMP_19 TMP_20 TMP_21) in (let TMP_26 \def (\lambda (t3: 
T).(\lambda (H2: (subst0 (s k i) v t1 t3)).(let TMP_23 \def (THead k u1 t1) 
in (let TMP_24 \def (THead k t2 t3) in (let TMP_25 \def (subst0_both v u1 t2 
i H0 k t1 t3 H2) in (subst1_single i v TMP_23 TMP_24 TMP_25)))))) in 
(subst1_ind TMP_15 v t1 TMP_18 TMP_22 TMP_26 t0 H1)))))))))))))) in 
(subst1_ind i v u1 TMP_3 TMP_14 TMP_27 u2 H)))))))).

theorem subst1_lift_lt:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst1 i 
(lift h (minus d (S i)) u) (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t1 t2)).(let TMP_6 \def (\lambda (t: T).(\forall (d: 
nat).((lt i d) \to (\forall (h: nat).(let TMP_1 \def (S i) in (let TMP_2 \def 
(minus d TMP_1) in (let TMP_3 \def (lift h TMP_2 u) in (let TMP_4 \def (lift 
h d t1) in (let TMP_5 \def (lift h d t) in (subst1 i TMP_3 TMP_4 
TMP_5)))))))))) in (let TMP_11 \def (\lambda (d: nat).(\lambda (_: (lt i 
d)).(\lambda (h: nat).(let TMP_7 \def (S i) in (let TMP_8 \def (minus d 
TMP_7) in (let TMP_9 \def (lift h TMP_8 u) in (let TMP_10 \def (lift h d t1) 
in (subst1_refl i TMP_9 TMP_10)))))))) in (let TMP_18 \def (\lambda (t3: 
T).(\lambda (H0: (subst0 i u t1 t3)).(\lambda (d: nat).(\lambda (H1: (lt i 
d)).(\lambda (h: nat).(let TMP_12 \def (S i) in (let TMP_13 \def (minus d 
TMP_12) in (let TMP_14 \def (lift h TMP_13 u) in (let TMP_15 \def (lift h d 
t1) in (let TMP_16 \def (lift h d t3) in (let TMP_17 \def (subst0_lift_lt t1 
t3 u i H0 d H1 h) in (subst1_single i TMP_14 TMP_15 TMP_16 TMP_17)))))))))))) 
in (subst1_ind i u t1 TMP_6 TMP_11 TMP_18 t2 H)))))))).

theorem subst1_lift_ge:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall 
(h: nat).((subst1 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst1 
(plus i h) u (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (H: (subst1 i u t1 t2)).(let TMP_4 \def (\lambda (t: 
T).(\forall (d: nat).((le d i) \to (let TMP_1 \def (plus i h) in (let TMP_2 
\def (lift h d t1) in (let TMP_3 \def (lift h d t) in (subst1 TMP_1 u TMP_2 
TMP_3))))))) in (let TMP_7 \def (\lambda (d: nat).(\lambda (_: (le d i)).(let 
TMP_5 \def (plus i h) in (let TMP_6 \def (lift h d t1) in (subst1_refl TMP_5 
u TMP_6))))) in (let TMP_12 \def (\lambda (t3: T).(\lambda (H0: (subst0 i u 
t1 t3)).(\lambda (d: nat).(\lambda (H1: (le d i)).(let TMP_8 \def (plus i h) 
in (let TMP_9 \def (lift h d t1) in (let TMP_10 \def (lift h d t3) in (let 
TMP_11 \def (subst0_lift_ge t1 t3 u i h H0 d H1) in (subst1_single TMP_8 u 
TMP_9 TMP_10 TMP_11))))))))) in (subst1_ind i u t1 TMP_4 TMP_7 TMP_12 t2 
H))))))))).

theorem subst1_ex:
 \forall (u: T).(\forall (t1: T).(\forall (d: nat).(ex T (\lambda (t2: 
T).(subst1 d u t1 (lift (S O) d t2))))))
\def
 \lambda (u: T).(\lambda (t1: T).(let TMP_4 \def (\lambda (t: T).(\forall (d: 
nat).(let TMP_3 \def (\lambda (t2: T).(let TMP_1 \def (S O) in (let TMP_2 
\def (lift TMP_1 d t2) in (subst1 d u t TMP_2)))) in (ex T TMP_3)))) in (let 
TMP_21 \def (\lambda (n: nat).(\lambda (d: nat).(let TMP_8 \def (\lambda (t2: 
T).(let TMP_5 \def (TSort n) in (let TMP_6 \def (S O) in (let TMP_7 \def 
(lift TMP_6 d t2) in (subst1 d u TMP_5 TMP_7))))) in (let TMP_9 \def (TSort 
n) in (let TMP_10 \def (TSort n) in (let TMP_12 \def (\lambda (t: T).(let 
TMP_11 \def (TSort n) in (subst1 d u TMP_11 t))) in (let TMP_13 \def (TSort 
n) in (let TMP_14 \def (subst1_refl d u TMP_13) in (let TMP_15 \def (S O) in 
(let TMP_16 \def (TSort n) in (let TMP_17 \def (lift TMP_15 d TMP_16) in (let 
TMP_18 \def (S O) in (let TMP_19 \def (lift_sort n TMP_18 d) in (let TMP_20 
\def (eq_ind_r T TMP_10 TMP_12 TMP_14 TMP_17 TMP_19) in (ex_intro T TMP_8 
TMP_9 TMP_20))))))))))))))) in (let TMP_92 \def (\lambda (n: nat).(\lambda 
(d: nat).(let TMP_25 \def (\lambda (t2: T).(let TMP_22 \def (TLRef n) in (let 
TMP_23 \def (S O) in (let TMP_24 \def (lift TMP_23 d t2) in (subst1 d u 
TMP_22 TMP_24))))) in (let TMP_26 \def (ex T TMP_25) in (let TMP_43 \def 
(\lambda (H: (lt n d)).(let TMP_30 \def (\lambda (t2: T).(let TMP_27 \def 
(TLRef n) in (let TMP_28 \def (S O) in (let TMP_29 \def (lift TMP_28 d t2) in 
(subst1 d u TMP_27 TMP_29))))) in (let TMP_31 \def (TLRef n) in (let TMP_32 
\def (TLRef n) in (let TMP_34 \def (\lambda (t: T).(let TMP_33 \def (TLRef n) 
in (subst1 d u TMP_33 t))) in (let TMP_35 \def (TLRef n) in (let TMP_36 \def 
(subst1_refl d u TMP_35) in (let TMP_37 \def (S O) in (let TMP_38 \def (TLRef 
n) in (let TMP_39 \def (lift TMP_37 d TMP_38) in (let TMP_40 \def (S O) in 
(let TMP_41 \def (lift_lref_lt n TMP_40 d H) in (let TMP_42 \def (eq_ind_r T 
TMP_32 TMP_34 TMP_36 TMP_39 TMP_41) in (ex_intro T TMP_30 TMP_31 
TMP_42)))))))))))))) in (let TMP_73 \def (\lambda (H: (eq nat n d)).(let 
TMP_48 \def (\lambda (n0: nat).(let TMP_47 \def (\lambda (t2: T).(let TMP_44 
\def (TLRef n) in (let TMP_45 \def (S O) in (let TMP_46 \def (lift TMP_45 n0 
t2) in (subst1 n0 u TMP_44 TMP_46))))) in (ex T TMP_47))) in (let TMP_52 \def 
(\lambda (t2: T).(let TMP_49 \def (TLRef n) in (let TMP_50 \def (S O) in (let 
TMP_51 \def (lift TMP_50 n t2) in (subst1 n u TMP_49 TMP_51))))) in (let 
TMP_53 \def (lift n O u) in (let TMP_54 \def (S O) in (let TMP_55 \def (plus 
TMP_54 n) in (let TMP_56 \def (lift TMP_55 O u) in (let TMP_58 \def (\lambda 
(t: T).(let TMP_57 \def (TLRef n) in (subst1 n u TMP_57 t))) in (let TMP_59 
\def (TLRef n) in (let TMP_60 \def (S n) in (let TMP_61 \def (lift TMP_60 O 
u) in (let TMP_62 \def (subst0_lref u n) in (let TMP_63 \def (subst1_single n 
u TMP_59 TMP_61 TMP_62) in (let TMP_64 \def (S O) in (let TMP_65 \def (lift n 
O u) in (let TMP_66 \def (lift TMP_64 n TMP_65) in (let TMP_67 \def (S O) in 
(let TMP_68 \def (le_plus_r O n) in (let TMP_69 \def (le_O_n n) in (let 
TMP_70 \def (lift_free u n TMP_67 O n TMP_68 TMP_69) in (let TMP_71 \def 
(eq_ind_r T TMP_56 TMP_58 TMP_63 TMP_66 TMP_70) in (let TMP_72 \def (ex_intro 
T TMP_52 TMP_53 TMP_71) in (eq_ind nat n TMP_48 TMP_72 d 
H))))))))))))))))))))))) in (let TMP_91 \def (\lambda (H: (lt d n)).(let 
TMP_77 \def (\lambda (t2: T).(let TMP_74 \def (TLRef n) in (let TMP_75 \def 
(S O) in (let TMP_76 \def (lift TMP_75 d t2) in (subst1 d u TMP_74 
TMP_76))))) in (let TMP_78 \def (pred n) in (let TMP_79 \def (TLRef TMP_78) 
in (let TMP_80 \def (TLRef n) in (let TMP_82 \def (\lambda (t: T).(let TMP_81 
\def (TLRef n) in (subst1 d u TMP_81 t))) in (let TMP_83 \def (TLRef n) in 
(let TMP_84 \def (subst1_refl d u TMP_83) in (let TMP_85 \def (S O) in (let 
TMP_86 \def (pred n) in (let TMP_87 \def (TLRef TMP_86) in (let TMP_88 \def 
(lift TMP_85 d TMP_87) in (let TMP_89 \def (lift_lref_gt d n H) in (let 
TMP_90 \def (eq_ind_r T TMP_80 TMP_82 TMP_84 TMP_88 TMP_89) in (ex_intro T 
TMP_77 TMP_79 TMP_90))))))))))))))) in (lt_eq_gt_e n d TMP_26 TMP_43 TMP_73 
TMP_91)))))))) in (let TMP_139 \def (\lambda (k: K).(\lambda (t: T).(\lambda 
(H: ((\forall (d: nat).(ex T (\lambda (t2: T).(subst1 d u t (lift (S O) d 
t2))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (d: nat).(ex T (\lambda 
(t2: T).(subst1 d u t0 (lift (S O) d t2))))))).(\lambda (d: nat).(let H_x 
\def (H d) in (let H1 \def H_x in (let TMP_95 \def (\lambda (t2: T).(let 
TMP_93 \def (S O) in (let TMP_94 \def (lift TMP_93 d t2) in (subst1 d u t 
TMP_94)))) in (let TMP_99 \def (\lambda (t2: T).(let TMP_96 \def (THead k t 
t0) in (let TMP_97 \def (S O) in (let TMP_98 \def (lift TMP_97 d t2) in 
(subst1 d u TMP_96 TMP_98))))) in (let TMP_100 \def (ex T TMP_99) in (let 
TMP_138 \def (\lambda (x: T).(\lambda (H2: (subst1 d u t (lift (S O) d 
x))).(let TMP_101 \def (s k d) in (let H_x0 \def (H0 TMP_101) in (let H3 \def 
H_x0 in (let TMP_106 \def (\lambda (t2: T).(let TMP_102 \def (s k d) in (let 
TMP_103 \def (S O) in (let TMP_104 \def (s k d) in (let TMP_105 \def (lift 
TMP_103 TMP_104 t2) in (subst1 TMP_102 u t0 TMP_105)))))) in (let TMP_110 
\def (\lambda (t2: T).(let TMP_107 \def (THead k t t0) in (let TMP_108 \def 
(S O) in (let TMP_109 \def (lift TMP_108 d t2) in (subst1 d u TMP_107 
TMP_109))))) in (let TMP_111 \def (ex T TMP_110) in (let TMP_137 \def 
(\lambda (x0: T).(\lambda (H4: (subst1 (s k d) u t0 (lift (S O) (s k d) 
x0))).(let TMP_115 \def (\lambda (t2: T).(let TMP_112 \def (THead k t t0) in 
(let TMP_113 \def (S O) in (let TMP_114 \def (lift TMP_113 d t2) in (subst1 d 
u TMP_112 TMP_114))))) in (let TMP_116 \def (THead k x x0) in (let TMP_117 
\def (S O) in (let TMP_118 \def (lift TMP_117 d x) in (let TMP_119 \def (S O) 
in (let TMP_120 \def (s k d) in (let TMP_121 \def (lift TMP_119 TMP_120 x0) 
in (let TMP_122 \def (THead k TMP_118 TMP_121) in (let TMP_124 \def (\lambda 
(t2: T).(let TMP_123 \def (THead k t t0) in (subst1 d u TMP_123 t2))) in (let 
TMP_125 \def (S O) in (let TMP_126 \def (lift TMP_125 d x) in (let TMP_127 
\def (S O) in (let TMP_128 \def (s k d) in (let TMP_129 \def (lift TMP_127 
TMP_128 x0) in (let TMP_130 \def (subst1_head u t TMP_126 d H2 k t0 TMP_129 
H4) in (let TMP_131 \def (S O) in (let TMP_132 \def (THead k x x0) in (let 
TMP_133 \def (lift TMP_131 d TMP_132) in (let TMP_134 \def (S O) in (let 
TMP_135 \def (lift_head k x x0 TMP_134 d) in (let TMP_136 \def (eq_ind_r T 
TMP_122 TMP_124 TMP_130 TMP_133 TMP_135) in (ex_intro T TMP_115 TMP_116 
TMP_136)))))))))))))))))))))))) in (ex_ind T TMP_106 TMP_111 TMP_137 
H3)))))))))) in (ex_ind T TMP_95 TMP_100 TMP_138 H1))))))))))))) in (T_ind 
TMP_4 TMP_21 TMP_92 TMP_139 t1)))))).

theorem subst1_lift_S:
 \forall (u: T).(\forall (i: nat).(\forall (h: nat).((le h i) \to (subst1 i 
(TLRef h) (lift (S h) (S i) u) (lift (S h) i u)))))
\def
 \lambda (u: T).(let TMP_7 \def (\lambda (t: T).(\forall (i: nat).(\forall 
(h: nat).((le h i) \to (let TMP_1 \def (TLRef h) in (let TMP_2 \def (S h) in 
(let TMP_3 \def (S i) in (let TMP_4 \def (lift TMP_2 TMP_3 t) in (let TMP_5 
\def (S h) in (let TMP_6 \def (lift TMP_5 i t) in (subst1 i TMP_1 TMP_4 
TMP_6))))))))))) in (let TMP_34 \def (\lambda (n: nat).(\lambda (i: 
nat).(\lambda (h: nat).(\lambda (_: (le h i)).(let TMP_8 \def (TSort n) in 
(let TMP_13 \def (\lambda (t: T).(let TMP_9 \def (TLRef h) in (let TMP_10 
\def (S h) in (let TMP_11 \def (TSort n) in (let TMP_12 \def (lift TMP_10 i 
TMP_11) in (subst1 i TMP_9 t TMP_12)))))) in (let TMP_14 \def (TSort n) in 
(let TMP_17 \def (\lambda (t: T).(let TMP_15 \def (TLRef h) in (let TMP_16 
\def (TSort n) in (subst1 i TMP_15 TMP_16 t)))) in (let TMP_18 \def (TLRef h) 
in (let TMP_19 \def (TSort n) in (let TMP_20 \def (subst1_refl i TMP_18 
TMP_19) in (let TMP_21 \def (S h) in (let TMP_22 \def (TSort n) in (let 
TMP_23 \def (lift TMP_21 i TMP_22) in (let TMP_24 \def (S h) in (let TMP_25 
\def (lift_sort n TMP_24 i) in (let TMP_26 \def (eq_ind_r T TMP_14 TMP_17 
TMP_20 TMP_23 TMP_25) in (let TMP_27 \def (S h) in (let TMP_28 \def (S i) in 
(let TMP_29 \def (TSort n) in (let TMP_30 \def (lift TMP_27 TMP_28 TMP_29) in 
(let TMP_31 \def (S h) in (let TMP_32 \def (S i) in (let TMP_33 \def 
(lift_sort n TMP_31 TMP_32) in (eq_ind_r T TMP_8 TMP_13 TMP_26 TMP_30 
TMP_33))))))))))))))))))))))))) in (let TMP_220 \def (\lambda (n: 
nat).(\lambda (i: nat).(\lambda (h: nat).(\lambda (H: (le h i)).(let TMP_35 
\def (TLRef h) in (let TMP_36 \def (S h) in (let TMP_37 \def (S i) in (let 
TMP_38 \def (TLRef n) in (let TMP_39 \def (lift TMP_36 TMP_37 TMP_38) in (let 
TMP_40 \def (S h) in (let TMP_41 \def (TLRef n) in (let TMP_42 \def (lift 
TMP_40 i TMP_41) in (let TMP_43 \def (subst1 i TMP_35 TMP_39 TMP_42) in (let 
TMP_79 \def (\lambda (H0: (lt n i)).(let TMP_44 \def (TLRef n) in (let TMP_49 
\def (\lambda (t: T).(let TMP_45 \def (TLRef h) in (let TMP_46 \def (S h) in 
(let TMP_47 \def (TLRef n) in (let TMP_48 \def (lift TMP_46 i TMP_47) in 
(subst1 i TMP_45 t TMP_48)))))) in (let TMP_50 \def (TLRef n) in (let TMP_53 
\def (\lambda (t: T).(let TMP_51 \def (TLRef h) in (let TMP_52 \def (TLRef n) 
in (subst1 i TMP_51 TMP_52 t)))) in (let TMP_54 \def (TLRef h) in (let TMP_55 
\def (TLRef n) in (let TMP_56 \def (subst1_refl i TMP_54 TMP_55) in (let 
TMP_57 \def (S h) in (let TMP_58 \def (TLRef n) in (let TMP_59 \def (lift 
TMP_57 i TMP_58) in (let TMP_60 \def (S h) in (let TMP_61 \def (lift_lref_lt 
n TMP_60 i H0) in (let TMP_62 \def (eq_ind_r T TMP_50 TMP_53 TMP_56 TMP_59 
TMP_61) in (let TMP_63 \def (S h) in (let TMP_64 \def (S i) in (let TMP_65 
\def (TLRef n) in (let TMP_66 \def (lift TMP_63 TMP_64 TMP_65) in (let TMP_67 
\def (S h) in (let TMP_68 \def (S i) in (let TMP_69 \def (S n) in (let TMP_70 
\def (S i) in (let TMP_71 \def (S n) in (let TMP_72 \def (S TMP_71) in (let 
TMP_73 \def (S i) in (let TMP_74 \def (S n) in (let TMP_75 \def (le_n_S 
TMP_74 i H0) in (let TMP_76 \def (le_S TMP_72 TMP_73 TMP_75) in (let TMP_77 
\def (le_S_n TMP_69 TMP_70 TMP_76) in (let TMP_78 \def (lift_lref_lt n TMP_67 
TMP_68 TMP_77) in (eq_ind_r T TMP_44 TMP_49 TMP_62 TMP_66 
TMP_78))))))))))))))))))))))))))))))) in (let TMP_174 \def (\lambda (H0: (eq 
nat n i)).(let TMP_80 \def (\lambda (n0: nat).(le h n0)) in (let H1 \def 
(eq_ind_r nat i TMP_80 H n H0) in (let TMP_89 \def (\lambda (n0: nat).(let 
TMP_81 \def (TLRef h) in (let TMP_82 \def (S h) in (let TMP_83 \def (S n0) in 
(let TMP_84 \def (TLRef n) in (let TMP_85 \def (lift TMP_82 TMP_83 TMP_84) in 
(let TMP_86 \def (S h) in (let TMP_87 \def (TLRef n) in (let TMP_88 \def 
(lift TMP_86 n0 TMP_87) in (subst1 n0 TMP_81 TMP_85 TMP_88)))))))))) in (let 
TMP_90 \def (TLRef n) in (let TMP_95 \def (\lambda (t: T).(let TMP_91 \def 
(TLRef h) in (let TMP_92 \def (S h) in (let TMP_93 \def (TLRef n) in (let 
TMP_94 \def (lift TMP_92 n TMP_93) in (subst1 n TMP_91 t TMP_94)))))) in (let 
TMP_96 \def (S h) in (let TMP_97 \def (plus n TMP_96) in (let TMP_98 \def 
(TLRef TMP_97) in (let TMP_101 \def (\lambda (t: T).(let TMP_99 \def (TLRef 
h) in (let TMP_100 \def (TLRef n) in (subst1 n TMP_99 TMP_100 t)))) in (let 
TMP_102 \def (plus n h) in (let TMP_103 \def (S TMP_102) in (let TMP_107 \def 
(\lambda (n0: nat).(let TMP_104 \def (TLRef h) in (let TMP_105 \def (TLRef n) 
in (let TMP_106 \def (TLRef n0) in (subst1 n TMP_104 TMP_105 TMP_106))))) in 
(let TMP_108 \def (plus h n) in (let TMP_113 \def (\lambda (n0: nat).(let 
TMP_109 \def (TLRef h) in (let TMP_110 \def (TLRef n) in (let TMP_111 \def (S 
n0) in (let TMP_112 \def (TLRef TMP_111) in (subst1 n TMP_109 TMP_110 
TMP_112)))))) in (let TMP_114 \def (S n) in (let TMP_115 \def (plus h 
TMP_114) in (let TMP_119 \def (\lambda (n0: nat).(let TMP_116 \def (TLRef h) 
in (let TMP_117 \def (TLRef n) in (let TMP_118 \def (TLRef n0) in (subst1 n 
TMP_116 TMP_117 TMP_118))))) in (let TMP_120 \def (S n) in (let TMP_121 \def 
(TLRef h) in (let TMP_122 \def (lift TMP_120 O TMP_121) in (let TMP_125 \def 
(\lambda (t: T).(let TMP_123 \def (TLRef h) in (let TMP_124 \def (TLRef n) in 
(subst1 n TMP_123 TMP_124 t)))) in (let TMP_126 \def (TLRef h) in (let 
TMP_127 \def (TLRef n) in (let TMP_128 \def (S n) in (let TMP_129 \def (TLRef 
h) in (let TMP_130 \def (lift TMP_128 O TMP_129) in (let TMP_131 \def (TLRef 
h) in (let TMP_132 \def (subst0_lref TMP_131 n) in (let TMP_133 \def 
(subst1_single n TMP_126 TMP_127 TMP_130 TMP_132) in (let TMP_134 \def (S n) 
in (let TMP_135 \def (plus h TMP_134) in (let TMP_136 \def (TLRef TMP_135) in 
(let TMP_137 \def (S n) in (let TMP_138 \def (le_O_n h) in (let TMP_139 \def 
(lift_lref_ge h TMP_137 O TMP_138) in (let TMP_140 \def (eq_ind T TMP_122 
TMP_125 TMP_133 TMP_136 TMP_139) in (let TMP_141 \def (plus h n) in (let 
TMP_142 \def (S TMP_141) in (let TMP_143 \def (plus h n) in (let TMP_144 \def 
(S TMP_143) in (let TMP_145 \def (S n) in (let TMP_146 \def (plus h TMP_145) 
in (let TMP_147 \def (plus_n_Sm h n) in (let TMP_148 \def (sym_eq nat TMP_144 
TMP_146 TMP_147) in (let TMP_149 \def (eq_ind nat TMP_115 TMP_119 TMP_140 
TMP_142 TMP_148) in (let TMP_150 \def (plus n h) in (let TMP_151 \def 
(plus_sym n h) in (let TMP_152 \def (eq_ind_r nat TMP_108 TMP_113 TMP_149 
TMP_150 TMP_151) in (let TMP_153 \def (S h) in (let TMP_154 \def (plus n 
TMP_153) in (let TMP_155 \def (plus_n_Sm n h) in (let TMP_156 \def (eq_ind 
nat TMP_103 TMP_107 TMP_152 TMP_154 TMP_155) in (let TMP_157 \def (S h) in 
(let TMP_158 \def (TLRef n) in (let TMP_159 \def (lift TMP_157 n TMP_158) in 
(let TMP_160 \def (S h) in (let TMP_161 \def (le_n n) in (let TMP_162 \def 
(lift_lref_ge n TMP_160 n TMP_161) in (let TMP_163 \def (eq_ind_r T TMP_98 
TMP_101 TMP_156 TMP_159 TMP_162) in (let TMP_164 \def (S h) in (let TMP_165 
\def (S n) in (let TMP_166 \def (TLRef n) in (let TMP_167 \def (lift TMP_164 
TMP_165 TMP_166) in (let TMP_168 \def (S h) in (let TMP_169 \def (S n) in 
(let TMP_170 \def (S n) in (let TMP_171 \def (le_n TMP_170) in (let TMP_172 
\def (lift_lref_lt n TMP_168 TMP_169 TMP_171) in (let TMP_173 \def (eq_ind_r 
T TMP_90 TMP_95 TMP_163 TMP_167 TMP_172) in (eq_ind nat n TMP_89 TMP_173 i 
H0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(let TMP_219 \def (\lambda (H0: (lt i n)).(let TMP_175 \def (S h) in (let 
TMP_176 \def (plus n TMP_175) in (let TMP_177 \def (TLRef TMP_176) in (let 
TMP_182 \def (\lambda (t: T).(let TMP_178 \def (TLRef h) in (let TMP_179 \def 
(S h) in (let TMP_180 \def (TLRef n) in (let TMP_181 \def (lift TMP_179 i 
TMP_180) in (subst1 i TMP_178 t TMP_181)))))) in (let TMP_183 \def (S h) in 
(let TMP_184 \def (plus n TMP_183) in (let TMP_185 \def (TLRef TMP_184) in 
(let TMP_190 \def (\lambda (t: T).(let TMP_186 \def (TLRef h) in (let TMP_187 
\def (S h) in (let TMP_188 \def (plus n TMP_187) in (let TMP_189 \def (TLRef 
TMP_188) in (subst1 i TMP_186 TMP_189 t)))))) in (let TMP_191 \def (TLRef h) 
in (let TMP_192 \def (S h) in (let TMP_193 \def (plus n TMP_192) in (let 
TMP_194 \def (TLRef TMP_193) in (let TMP_195 \def (subst1_refl i TMP_191 
TMP_194) in (let TMP_196 \def (S h) in (let TMP_197 \def (TLRef n) in (let 
TMP_198 \def (lift TMP_196 i TMP_197) in (let TMP_199 \def (S h) in (let 
TMP_200 \def (S i) in (let TMP_201 \def (S n) in (let TMP_202 \def (S i) in 
(let TMP_203 \def (S TMP_202) in (let TMP_204 \def (S n) in (let TMP_205 \def 
(S i) in (let TMP_206 \def (le_n_S TMP_205 n H0) in (let TMP_207 \def (le_S 
TMP_203 TMP_204 TMP_206) in (let TMP_208 \def (le_S_n TMP_200 TMP_201 
TMP_207) in (let TMP_209 \def (le_S_n i n TMP_208) in (let TMP_210 \def 
(lift_lref_ge n TMP_199 i TMP_209) in (let TMP_211 \def (eq_ind_r T TMP_185 
TMP_190 TMP_195 TMP_198 TMP_210) in (let TMP_212 \def (S h) in (let TMP_213 
\def (S i) in (let TMP_214 \def (TLRef n) in (let TMP_215 \def (lift TMP_212 
TMP_213 TMP_214) in (let TMP_216 \def (S h) in (let TMP_217 \def (S i) in 
(let TMP_218 \def (lift_lref_ge n TMP_216 TMP_217 H0) in (eq_ind_r T TMP_177 
TMP_182 TMP_211 TMP_215 TMP_218)))))))))))))))))))))))))))))))))))))) in 
(lt_eq_gt_e n i TMP_43 TMP_79 TMP_174 TMP_219))))))))))))))))) in (let 
TMP_297 \def (\lambda (k: K).(\lambda (t: T).(\lambda (H: ((\forall (i: 
nat).(\forall (h: nat).((le h i) \to (subst1 i (TLRef h) (lift (S h) (S i) t) 
(lift (S h) i t))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (i: 
nat).(\forall (h: nat).((le h i) \to (subst1 i (TLRef h) (lift (S h) (S i) 
t0) (lift (S h) i t0))))))).(\lambda (i: nat).(\lambda (h: nat).(\lambda (H1: 
(le h i)).(let TMP_221 \def (S h) in (let TMP_222 \def (S i) in (let TMP_223 
\def (lift TMP_221 TMP_222 t) in (let TMP_224 \def (S h) in (let TMP_225 \def 
(S i) in (let TMP_226 \def (s k TMP_225) in (let TMP_227 \def (lift TMP_224 
TMP_226 t0) in (let TMP_228 \def (THead k TMP_223 TMP_227) in (let TMP_233 
\def (\lambda (t1: T).(let TMP_229 \def (TLRef h) in (let TMP_230 \def (S h) 
in (let TMP_231 \def (THead k t t0) in (let TMP_232 \def (lift TMP_230 i 
TMP_231) in (subst1 i TMP_229 t1 TMP_232)))))) in (let TMP_234 \def (S h) in 
(let TMP_235 \def (lift TMP_234 i t) in (let TMP_236 \def (S h) in (let 
TMP_237 \def (s k i) in (let TMP_238 \def (lift TMP_236 TMP_237 t0) in (let 
TMP_239 \def (THead k TMP_235 TMP_238) in (let TMP_249 \def (\lambda (t1: 
T).(let TMP_240 \def (TLRef h) in (let TMP_241 \def (S h) in (let TMP_242 
\def (S i) in (let TMP_243 \def (lift TMP_241 TMP_242 t) in (let TMP_244 \def 
(S h) in (let TMP_245 \def (S i) in (let TMP_246 \def (s k TMP_245) in (let 
TMP_247 \def (lift TMP_244 TMP_246 t0) in (let TMP_248 \def (THead k TMP_243 
TMP_247) in (subst1 i TMP_240 TMP_248 t1))))))))))) in (let TMP_250 \def 
(TLRef h) in (let TMP_251 \def (S h) in (let TMP_252 \def (S i) in (let 
TMP_253 \def (lift TMP_251 TMP_252 t) in (let TMP_254 \def (S h) in (let 
TMP_255 \def (lift TMP_254 i t) in (let TMP_256 \def (H i h H1) in (let 
TMP_257 \def (S h) in (let TMP_258 \def (S i) in (let TMP_259 \def (s k 
TMP_258) in (let TMP_260 \def (lift TMP_257 TMP_259 t0) in (let TMP_261 \def 
(S h) in (let TMP_262 \def (s k i) in (let TMP_263 \def (lift TMP_261 TMP_262 
t0) in (let TMP_264 \def (s k i) in (let TMP_265 \def (S TMP_264) in (let 
TMP_273 \def (\lambda (n: nat).(let TMP_266 \def (s k i) in (let TMP_267 \def 
(TLRef h) in (let TMP_268 \def (S h) in (let TMP_269 \def (lift TMP_268 n t0) 
in (let TMP_270 \def (S h) in (let TMP_271 \def (s k i) in (let TMP_272 \def 
(lift TMP_270 TMP_271 t0) in (subst1 TMP_266 TMP_267 TMP_269 TMP_272))))))))) 
in (let TMP_274 \def (s k i) in (let TMP_275 \def (s k i) in (let TMP_276 
\def (s_inc k i) in (let TMP_277 \def (le_trans h i TMP_275 H1 TMP_276) in 
(let TMP_278 \def (H0 TMP_274 h TMP_277) in (let TMP_279 \def (S i) in (let 
TMP_280 \def (s k TMP_279) in (let TMP_281 \def (s_S k i) in (let TMP_282 
\def (eq_ind_r nat TMP_265 TMP_273 TMP_278 TMP_280 TMP_281) in (let TMP_283 
\def (subst1_head TMP_250 TMP_253 TMP_255 i TMP_256 k TMP_260 TMP_263 
TMP_282) in (let TMP_284 \def (S h) in (let TMP_285 \def (THead k t t0) in 
(let TMP_286 \def (lift TMP_284 i TMP_285) in (let TMP_287 \def (S h) in (let 
TMP_288 \def (lift_head k t t0 TMP_287 i) in (let TMP_289 \def (eq_ind_r T 
TMP_239 TMP_249 TMP_283 TMP_286 TMP_288) in (let TMP_290 \def (S h) in (let 
TMP_291 \def (S i) in (let TMP_292 \def (THead k t t0) in (let TMP_293 \def 
(lift TMP_290 TMP_291 TMP_292) in (let TMP_294 \def (S h) in (let TMP_295 
\def (S i) in (let TMP_296 \def (lift_head k t t0 TMP_294 TMP_295) in 
(eq_ind_r T TMP_228 TMP_233 TMP_289 TMP_293 
TMP_296))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(T_ind TMP_7 TMP_34 TMP_220 TMP_297 u))))).

