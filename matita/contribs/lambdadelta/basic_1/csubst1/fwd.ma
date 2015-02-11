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

include "basic_1/csubst1/defs.ma".

include "basic_1/csubst0/fwd.ma".

include "basic_1/subst1/defs.ma".

include "basic_1/s/fwd.ma".

theorem csubst1_ind:
 \forall (i: nat).(\forall (v: T).(\forall (c1: C).(\forall (P: ((C \to 
Prop))).((P c1) \to (((\forall (c2: C).((csubst0 i v c1 c2) \to (P c2)))) \to 
(\forall (c: C).((csubst1 i v c1 c) \to (P c))))))))
\def
 \lambda (i: nat).(\lambda (v: T).(\lambda (c1: C).(\lambda (P: ((C \to 
Prop))).(\lambda (f: (P c1)).(\lambda (f0: ((\forall (c2: C).((csubst0 i v c1 
c2) \to (P c2))))).(\lambda (c: C).(\lambda (c0: (csubst1 i v c1 c)).(match 
c0 with [csubst1_refl \Rightarrow f | (csubst1_sing x x0) \Rightarrow (f0 x 
x0)])))))))).

theorem csubst1_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).(\forall 
(v: T).(\forall (i: nat).((csubst1 (s k i) v (CHead c1 k u1) x) \to (ex3_2 T 
C (\lambda (u2: T).(\lambda (c2: C).(eq C x (CHead c2 k u2)))) (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (c2: 
C).(csubst1 i v c1 c2))))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (csubst1 (s k i) v (CHead c1 k u1) 
x)).(let TMP_1 \def (s k i) in (let TMP_2 \def (CHead c1 k u1) in (let TMP_7 
\def (\lambda (c: C).(let TMP_4 \def (\lambda (u2: T).(\lambda (c2: C).(let 
TMP_3 \def (CHead c2 k u2) in (eq C c TMP_3)))) in (let TMP_5 \def (\lambda 
(u2: T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_6 \def (\lambda (_: 
T).(\lambda (c2: C).(csubst1 i v c1 c2))) in (ex3_2 T C TMP_4 TMP_5 
TMP_6))))) in (let TMP_10 \def (\lambda (u2: T).(\lambda (c2: C).(let TMP_8 
\def (CHead c1 k u1) in (let TMP_9 \def (CHead c2 k u2) in (eq C TMP_8 
TMP_9))))) in (let TMP_11 \def (\lambda (u2: T).(\lambda (_: C).(subst1 i v 
u1 u2))) in (let TMP_12 \def (\lambda (_: T).(\lambda (c2: C).(csubst1 i v c1 
c2))) in (let TMP_13 \def (CHead c1 k u1) in (let TMP_14 \def (refl_equal C 
TMP_13) in (let TMP_15 \def (subst1_refl i v u1) in (let TMP_16 \def 
(csubst1_refl i v c1) in (let TMP_17 \def (ex3_2_intro T C TMP_10 TMP_11 
TMP_12 u1 c1 TMP_14 TMP_15 TMP_16) in (let TMP_138 \def (\lambda (c2: 
C).(\lambda (H0: (csubst0 (s k i) v (CHead c1 k u1) c2)).(let TMP_18 \def (s 
k i) in (let H1 \def (csubst0_gen_head k c1 c2 u1 v TMP_18 H0) in (let TMP_21 
\def (\lambda (_: T).(\lambda (j: nat).(let TMP_19 \def (s k i) in (let 
TMP_20 \def (s k j) in (eq nat TMP_19 TMP_20))))) in (let TMP_23 \def 
(\lambda (u2: T).(\lambda (_: nat).(let TMP_22 \def (CHead c1 k u2) in (eq C 
c2 TMP_22)))) in (let TMP_24 \def (\lambda (u2: T).(\lambda (j: nat).(subst0 
j v u1 u2))) in (let TMP_25 \def (ex3_2 T nat TMP_21 TMP_23 TMP_24) in (let 
TMP_28 \def (\lambda (_: C).(\lambda (j: nat).(let TMP_26 \def (s k i) in 
(let TMP_27 \def (s k j) in (eq nat TMP_26 TMP_27))))) in (let TMP_30 \def 
(\lambda (c3: C).(\lambda (_: nat).(let TMP_29 \def (CHead c3 k u1) in (eq C 
c2 TMP_29)))) in (let TMP_31 \def (\lambda (c3: C).(\lambda (j: nat).(csubst0 
j v c1 c3))) in (let TMP_32 \def (ex3_2 C nat TMP_28 TMP_30 TMP_31) in (let 
TMP_35 \def (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(let TMP_33 
\def (s k i) in (let TMP_34 \def (s k j) in (eq nat TMP_33 TMP_34)))))) in 
(let TMP_37 \def (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(let 
TMP_36 \def (CHead c3 k u2) in (eq C c2 TMP_36))))) in (let TMP_38 \def 
(\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v u1 u2)))) in 
(let TMP_39 \def (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 
j v c1 c3)))) in (let TMP_40 \def (ex4_3 T C nat TMP_35 TMP_37 TMP_38 TMP_39) 
in (let TMP_42 \def (\lambda (u2: T).(\lambda (c3: C).(let TMP_41 \def (CHead 
c3 k u2) in (eq C c2 TMP_41)))) in (let TMP_43 \def (\lambda (u2: T).(\lambda 
(_: C).(subst1 i v u1 u2))) in (let TMP_44 \def (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))) in (let TMP_45 \def (ex3_2 T C TMP_42 TMP_43 TMP_44) 
in (let TMP_75 \def (\lambda (H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat (s k i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 
(CHead c1 k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v u1 
u2))))).(let TMP_48 \def (\lambda (_: T).(\lambda (j: nat).(let TMP_46 \def 
(s k i) in (let TMP_47 \def (s k j) in (eq nat TMP_46 TMP_47))))) in (let 
TMP_50 \def (\lambda (u2: T).(\lambda (_: nat).(let TMP_49 \def (CHead c1 k 
u2) in (eq C c2 TMP_49)))) in (let TMP_51 \def (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v u1 u2))) in (let TMP_53 \def (\lambda (u2: T).(\lambda (c3: 
C).(let TMP_52 \def (CHead c3 k u2) in (eq C c2 TMP_52)))) in (let TMP_54 
\def (\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_55 
\def (\lambda (_: T).(\lambda (c3: C).(csubst1 i v c1 c3))) in (let TMP_56 
\def (ex3_2 T C TMP_53 TMP_54 TMP_55) in (let TMP_74 \def (\lambda (x0: 
T).(\lambda (x1: nat).(\lambda (H3: (eq nat (s k i) (s k x1))).(\lambda (H4: 
(eq C c2 (CHead c1 k x0))).(\lambda (H5: (subst0 x1 v u1 x0)).(let TMP_57 
\def (CHead c1 k x0) in (let TMP_62 \def (\lambda (c: C).(let TMP_59 \def 
(\lambda (u2: T).(\lambda (c3: C).(let TMP_58 \def (CHead c3 k u2) in (eq C c 
TMP_58)))) in (let TMP_60 \def (\lambda (u2: T).(\lambda (_: C).(subst1 i v 
u1 u2))) in (let TMP_61 \def (\lambda (_: T).(\lambda (c3: C).(csubst1 i v c1 
c3))) in (ex3_2 T C TMP_59 TMP_60 TMP_61))))) in (let H_y \def (s_inj k i x1 
H3) in (let TMP_63 \def (\lambda (n: nat).(subst0 n v u1 x0)) in (let H6 \def 
(eq_ind_r nat x1 TMP_63 H5 i H_y) in (let TMP_66 \def (\lambda (u2: 
T).(\lambda (c3: C).(let TMP_64 \def (CHead c1 k x0) in (let TMP_65 \def 
(CHead c3 k u2) in (eq C TMP_64 TMP_65))))) in (let TMP_67 \def (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_68 \def (\lambda (_: 
T).(\lambda (c3: C).(csubst1 i v c1 c3))) in (let TMP_69 \def (CHead c1 k x0) 
in (let TMP_70 \def (refl_equal C TMP_69) in (let TMP_71 \def (subst1_single 
i v u1 x0 H6) in (let TMP_72 \def (csubst1_refl i v c1) in (let TMP_73 \def 
(ex3_2_intro T C TMP_66 TMP_67 TMP_68 x0 c1 TMP_70 TMP_71 TMP_72) in 
(eq_ind_r C TMP_57 TMP_62 TMP_73 c2 H4))))))))))))))))))) in (ex3_2_ind T nat 
TMP_48 TMP_50 TMP_51 TMP_56 TMP_74 H2)))))))))) in (let TMP_105 \def (\lambda 
(H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (s k i) (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u1)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))))).(let TMP_78 \def (\lambda 
(_: C).(\lambda (j: nat).(let TMP_76 \def (s k i) in (let TMP_77 \def (s k j) 
in (eq nat TMP_76 TMP_77))))) in (let TMP_80 \def (\lambda (c3: C).(\lambda 
(_: nat).(let TMP_79 \def (CHead c3 k u1) in (eq C c2 TMP_79)))) in (let 
TMP_81 \def (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 c3))) in (let 
TMP_83 \def (\lambda (u2: T).(\lambda (c3: C).(let TMP_82 \def (CHead c3 k 
u2) in (eq C c2 TMP_82)))) in (let TMP_84 \def (\lambda (u2: T).(\lambda (_: 
C).(subst1 i v u1 u2))) in (let TMP_85 \def (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))) in (let TMP_86 \def (ex3_2 T C TMP_83 TMP_84 TMP_85) 
in (let TMP_104 \def (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq 
nat (s k i) (s k x1))).(\lambda (H4: (eq C c2 (CHead x0 k u1))).(\lambda (H5: 
(csubst0 x1 v c1 x0)).(let TMP_87 \def (CHead x0 k u1) in (let TMP_92 \def 
(\lambda (c: C).(let TMP_89 \def (\lambda (u2: T).(\lambda (c3: C).(let 
TMP_88 \def (CHead c3 k u2) in (eq C c TMP_88)))) in (let TMP_90 \def 
(\lambda (u2: T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_91 \def 
(\lambda (_: T).(\lambda (c3: C).(csubst1 i v c1 c3))) in (ex3_2 T C TMP_89 
TMP_90 TMP_91))))) in (let H_y \def (s_inj k i x1 H3) in (let TMP_93 \def 
(\lambda (n: nat).(csubst0 n v c1 x0)) in (let H6 \def (eq_ind_r nat x1 
TMP_93 H5 i H_y) in (let TMP_96 \def (\lambda (u2: T).(\lambda (c3: C).(let 
TMP_94 \def (CHead x0 k u1) in (let TMP_95 \def (CHead c3 k u2) in (eq C 
TMP_94 TMP_95))))) in (let TMP_97 \def (\lambda (u2: T).(\lambda (_: 
C).(subst1 i v u1 u2))) in (let TMP_98 \def (\lambda (_: T).(\lambda (c3: 
C).(csubst1 i v c1 c3))) in (let TMP_99 \def (CHead x0 k u1) in (let TMP_100 
\def (refl_equal C TMP_99) in (let TMP_101 \def (subst1_refl i v u1) in (let 
TMP_102 \def (csubst1_sing i v c1 x0 H6) in (let TMP_103 \def (ex3_2_intro T 
C TMP_96 TMP_97 TMP_98 u1 x0 TMP_100 TMP_101 TMP_102) in (eq_ind_r C TMP_87 
TMP_92 TMP_103 c2 H4))))))))))))))))))) in (ex3_2_ind C nat TMP_78 TMP_80 
TMP_81 TMP_86 TMP_104 H2)))))))))) in (let TMP_137 \def (\lambda (H2: (ex4_3 
T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (s k i) (s 
k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v 
u1 u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c1 
c3)))))).(let TMP_108 \def (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(let TMP_106 \def (s k i) in (let TMP_107 \def (s k j) in (eq nat 
TMP_106 TMP_107)))))) in (let TMP_110 \def (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(let TMP_109 \def (CHead c3 k u2) in (eq C c2 
TMP_109))))) in (let TMP_111 \def (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v u1 u2)))) in (let TMP_112 \def (\lambda (_: T).(\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c1 c3)))) in (let TMP_114 \def 
(\lambda (u2: T).(\lambda (c3: C).(let TMP_113 \def (CHead c3 k u2) in (eq C 
c2 TMP_113)))) in (let TMP_115 \def (\lambda (u2: T).(\lambda (_: C).(subst1 
i v u1 u2))) in (let TMP_116 \def (\lambda (_: T).(\lambda (c3: C).(csubst1 i 
v c1 c3))) in (let TMP_117 \def (ex3_2 T C TMP_114 TMP_115 TMP_116) in (let 
TMP_136 \def (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda 
(H3: (eq nat (s k i) (s k x2))).(\lambda (H4: (eq C c2 (CHead x1 k 
x0))).(\lambda (H5: (subst0 x2 v u1 x0)).(\lambda (H6: (csubst0 x2 v c1 
x1)).(let TMP_118 \def (CHead x1 k x0) in (let TMP_123 \def (\lambda (c: 
C).(let TMP_120 \def (\lambda (u2: T).(\lambda (c3: C).(let TMP_119 \def 
(CHead c3 k u2) in (eq C c TMP_119)))) in (let TMP_121 \def (\lambda (u2: 
T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_122 \def (\lambda (_: 
T).(\lambda (c3: C).(csubst1 i v c1 c3))) in (ex3_2 T C TMP_120 TMP_121 
TMP_122))))) in (let H_y \def (s_inj k i x2 H3) in (let TMP_124 \def (\lambda 
(n: nat).(csubst0 n v c1 x1)) in (let H7 \def (eq_ind_r nat x2 TMP_124 H6 i 
H_y) in (let TMP_125 \def (\lambda (n: nat).(subst0 n v u1 x0)) in (let H8 
\def (eq_ind_r nat x2 TMP_125 H5 i H_y) in (let TMP_128 \def (\lambda (u2: 
T).(\lambda (c3: C).(let TMP_126 \def (CHead x1 k x0) in (let TMP_127 \def 
(CHead c3 k u2) in (eq C TMP_126 TMP_127))))) in (let TMP_129 \def (\lambda 
(u2: T).(\lambda (_: C).(subst1 i v u1 u2))) in (let TMP_130 \def (\lambda 
(_: T).(\lambda (c3: C).(csubst1 i v c1 c3))) in (let TMP_131 \def (CHead x1 
k x0) in (let TMP_132 \def (refl_equal C TMP_131) in (let TMP_133 \def 
(subst1_single i v u1 x0 H8) in (let TMP_134 \def (csubst1_sing i v c1 x1 H7) 
in (let TMP_135 \def (ex3_2_intro T C TMP_128 TMP_129 TMP_130 x0 x1 TMP_132 
TMP_133 TMP_134) in (eq_ind_r C TMP_118 TMP_123 TMP_135 c2 
H4))))))))))))))))))))))) in (ex4_3_ind T C nat TMP_108 TMP_110 TMP_111 
TMP_112 TMP_117 TMP_136 H2))))))))))) in (or3_ind TMP_25 TMP_32 TMP_40 TMP_45 
TMP_75 TMP_105 TMP_137 H1))))))))))))))))))))))))) in (csubst1_ind TMP_1 v 
TMP_2 TMP_7 TMP_17 TMP_138 x H))))))))))))))))))).

