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

include "basic_1/wcpr0/fwd.ma".

include "basic_1/getl/props.ma".

theorem wcpr0_drop:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 
(CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda 
(_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(let TMP_5 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((drop h O c (CHead e1 k u1)) \to (let TMP_2 \def 
(\lambda (e2: C).(\lambda (u2: T).(let TMP_1 \def (CHead e2 k u2) in (drop h 
O c0 TMP_1)))) in (let TMP_3 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) in (let TMP_4 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))) in 
(ex3_2 C T TMP_2 TMP_3 TMP_4))))))))))) in (let TMP_12 \def (\lambda (c: 
C).(\lambda (h: nat).(\lambda (e1: C).(\lambda (u1: T).(\lambda (k: 
K).(\lambda (H0: (drop h O c (CHead e1 k u1))).(let TMP_7 \def (\lambda (e2: 
C).(\lambda (u2: T).(let TMP_6 \def (CHead e2 k u2) in (drop h O c TMP_6)))) 
in (let TMP_8 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let 
TMP_9 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))) in (let TMP_10 \def 
(wcpr0_refl e1) in (let TMP_11 \def (pr0_refl u1) in (ex3_2_intro C T TMP_7 
TMP_8 TMP_9 e1 u1 H0 TMP_10 TMP_11)))))))))))) in (let TMP_132 \def (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (H0: (wcpr0 c3 c4)).(\lambda (H1: ((\forall 
(h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c3 
(CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O 
c4 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) 
(\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))))))))))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (h: 
nat).(let TMP_18 \def (\lambda (n: nat).(\forall (e1: C).(\forall (u3: 
T).(\forall (k0: K).((drop n O (CHead c3 k u1) (CHead e1 k0 u3)) \to (let 
TMP_15 \def (\lambda (e2: C).(\lambda (u4: T).(let TMP_13 \def (CHead c4 k 
u2) in (let TMP_14 \def (CHead e2 k0 u4) in (drop n O TMP_13 TMP_14))))) in 
(let TMP_16 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let 
TMP_17 \def (\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))) in (ex3_2 C T 
TMP_15 TMP_16 TMP_17))))))))) in (let TMP_67 \def (\lambda (e1: C).(\lambda 
(u0: T).(\lambda (k0: K).(\lambda (H3: (drop O O (CHead c3 k u1) (CHead e1 k0 
u0))).(let TMP_19 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow 
c3 | (CHead c _ _) \Rightarrow c])) in (let TMP_20 \def (CHead c3 k u1) in 
(let TMP_21 \def (CHead e1 k0 u0) in (let TMP_22 \def (CHead c3 k u1) in (let 
TMP_23 \def (CHead e1 k0 u0) in (let TMP_24 \def (drop_gen_refl TMP_22 TMP_23 
H3) in (let H4 \def (f_equal C C TMP_19 TMP_20 TMP_21 TMP_24) in (let TMP_25 
\def (\lambda (e: C).(match e with [(CSort _) \Rightarrow k | (CHead _ k1 _) 
\Rightarrow k1])) in (let TMP_26 \def (CHead c3 k u1) in (let TMP_27 \def 
(CHead e1 k0 u0) in (let TMP_28 \def (CHead c3 k u1) in (let TMP_29 \def 
(CHead e1 k0 u0) in (let TMP_30 \def (drop_gen_refl TMP_28 TMP_29 H3) in (let 
H5 \def (f_equal C K TMP_25 TMP_26 TMP_27 TMP_30) in (let TMP_31 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u1 | (CHead _ _ t) 
\Rightarrow t])) in (let TMP_32 \def (CHead c3 k u1) in (let TMP_33 \def 
(CHead e1 k0 u0) in (let TMP_34 \def (CHead c3 k u1) in (let TMP_35 \def 
(CHead e1 k0 u0) in (let TMP_36 \def (drop_gen_refl TMP_34 TMP_35 H3) in (let 
H6 \def (f_equal C T TMP_31 TMP_32 TMP_33 TMP_36) in (let TMP_65 \def 
(\lambda (H7: (eq K k k0)).(\lambda (H8: (eq C c3 e1)).(let TMP_42 \def 
(\lambda (k1: K).(let TMP_39 \def (\lambda (e2: C).(\lambda (u3: T).(let 
TMP_37 \def (CHead c4 k u2) in (let TMP_38 \def (CHead e2 k1 u3) in (drop O O 
TMP_37 TMP_38))))) in (let TMP_40 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) in (let TMP_41 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3))) in (ex3_2 C T TMP_39 TMP_40 TMP_41))))) in (let TMP_48 \def (\lambda 
(t: T).(let TMP_45 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_43 \def 
(CHead c4 k u2) in (let TMP_44 \def (CHead e2 k u3) in (drop O O TMP_43 
TMP_44))))) in (let TMP_46 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) in (let TMP_47 \def (\lambda (_: C).(\lambda (u3: T).(pr0 t u3))) in 
(ex3_2 C T TMP_45 TMP_46 TMP_47))))) in (let TMP_54 \def (\lambda (c: C).(let 
TMP_51 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_49 \def (CHead c4 k 
u2) in (let TMP_50 \def (CHead e2 k u3) in (drop O O TMP_49 TMP_50))))) in 
(let TMP_52 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 c e2))) in (let 
TMP_53 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in (ex3_2 C T 
TMP_51 TMP_52 TMP_53))))) in (let TMP_57 \def (\lambda (e2: C).(\lambda (u3: 
T).(let TMP_55 \def (CHead c4 k u2) in (let TMP_56 \def (CHead e2 k u3) in 
(drop O O TMP_55 TMP_56))))) in (let TMP_58 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 c3 e2))) in (let TMP_59 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u1 u3))) in (let TMP_60 \def (CHead c4 k u2) in (let TMP_61 \def 
(drop_refl TMP_60) in (let TMP_62 \def (ex3_2_intro C T TMP_57 TMP_58 TMP_59 
c4 u2 TMP_61 H0 H2) in (let TMP_63 \def (eq_ind C c3 TMP_54 TMP_62 e1 H8) in 
(let TMP_64 \def (eq_ind T u1 TMP_48 TMP_63 u0 H6) in (eq_ind K k TMP_42 
TMP_64 k0 H7)))))))))))))) in (let TMP_66 \def (TMP_65 H5) in (TMP_66 
H4)))))))))))))))))))))))))))) in (let TMP_74 \def (\lambda (k0: K).(\forall 
(n: nat).(((\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((drop n O 
(CHead c3 k0 u1) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda 
(u4: T).(drop n O (CHead c4 k0 u2) (CHead e2 k1 u4)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 
u4))))))))) \to (\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((drop (S 
n) O (CHead c3 k0 u1) (CHead e1 k1 u3)) \to (let TMP_71 \def (\lambda (e2: 
C).(\lambda (u4: T).(let TMP_68 \def (S n) in (let TMP_69 \def (CHead c4 k0 
u2) in (let TMP_70 \def (CHead e2 k1 u4) in (drop TMP_68 O TMP_69 
TMP_70)))))) in (let TMP_72 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) in (let TMP_73 \def (\lambda (_: C).(\lambda (u4: T).(pr0 u3 u4))) in 
(ex3_2 C T TMP_71 TMP_72 TMP_73))))))))))) in (let TMP_101 \def (\lambda (b: 
B).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c3 (Bind b) u1) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c4 (Bind b) u2) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c3 (Bind b) u1) (CHead 
e1 k0 u0))).(let TMP_75 \def (Bind b) in (let TMP_76 \def (CHead e1 k0 u0) in 
(let TMP_77 \def (drop_gen_drop TMP_75 c3 TMP_76 u1 n H4) in (let H5 \def (H1 
n e1 u0 k0 TMP_77) in (let TMP_79 \def (\lambda (e2: C).(\lambda (u3: T).(let 
TMP_78 \def (CHead e2 k0 u3) in (drop n O c4 TMP_78)))) in (let TMP_80 \def 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_81 \def (\lambda 
(_: C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_86 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_82 \def (S n) in (let TMP_83 \def (Bind b) in 
(let TMP_84 \def (CHead c4 TMP_83 u2) in (let TMP_85 \def (CHead e2 k0 u3) in 
(drop TMP_82 O TMP_84 TMP_85))))))) in (let TMP_87 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_88 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_89 \def (ex3_2 C T TMP_86 
TMP_87 TMP_88) in (let TMP_100 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (drop n O c4 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 e1 
x0)).(\lambda (H8: (pr0 u0 x1)).(let TMP_94 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_90 \def (S n) in (let TMP_91 \def (Bind b) in (let TMP_92 
\def (CHead c4 TMP_91 u2) in (let TMP_93 \def (CHead e2 k0 u3) in (drop 
TMP_90 O TMP_92 TMP_93))))))) in (let TMP_95 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e1 e2))) in (let TMP_96 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u0 u3))) in (let TMP_97 \def (Bind b) in (let TMP_98 \def (CHead x0 
k0 x1) in (let TMP_99 \def (drop_drop TMP_97 n c4 TMP_98 H6 u2) in 
(ex3_2_intro C T TMP_94 TMP_95 TMP_96 x0 x1 TMP_99 H7 H8)))))))))))) in 
(ex3_2_ind C T TMP_79 TMP_80 TMP_81 TMP_89 TMP_100 H5)))))))))))))))))))) in 
(let TMP_130 \def (\lambda (f: F).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((drop n O (CHead c3 (Flat f) u1) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O 
(CHead c4 (Flat f) u2) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 
u4)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(drop (S n) O (CHead c3 (Flat f) u1) (CHead e1 k0 u0))).(let TMP_102 \def (S 
n) in (let TMP_103 \def (Flat f) in (let TMP_104 \def (CHead e1 k0 u0) in 
(let TMP_105 \def (drop_gen_drop TMP_103 c3 TMP_104 u1 n H4) in (let H5 \def 
(H1 TMP_102 e1 u0 k0 TMP_105) in (let TMP_108 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_106 \def (S n) in (let TMP_107 \def (CHead e2 k0 u3) in 
(drop TMP_106 O c4 TMP_107))))) in (let TMP_109 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_110 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_115 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_111 \def (S n) in (let TMP_112 \def (Flat f) in 
(let TMP_113 \def (CHead c4 TMP_112 u2) in (let TMP_114 \def (CHead e2 k0 u3) 
in (drop TMP_111 O TMP_113 TMP_114))))))) in (let TMP_116 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_117 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_118 \def (ex3_2 C T TMP_115 
TMP_116 TMP_117) in (let TMP_129 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (drop (S n) O c4 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 e1 
x0)).(\lambda (H8: (pr0 u0 x1)).(let TMP_123 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_119 \def (S n) in (let TMP_120 \def (Flat f) in (let TMP_121 
\def (CHead c4 TMP_120 u2) in (let TMP_122 \def (CHead e2 k0 u3) in (drop 
TMP_119 O TMP_121 TMP_122))))))) in (let TMP_124 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_125 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_126 \def (Flat f) in (let 
TMP_127 \def (CHead x0 k0 x1) in (let TMP_128 \def (drop_drop TMP_126 n c4 
TMP_127 H6 u2) in (ex3_2_intro C T TMP_123 TMP_124 TMP_125 x0 x1 TMP_128 H7 
H8)))))))))))) in (ex3_2_ind C T TMP_108 TMP_109 TMP_110 TMP_118 TMP_129 
H5))))))))))))))))))))) in (let TMP_131 \def (K_ind TMP_74 TMP_101 TMP_130 k) 
in (nat_ind TMP_18 TMP_67 TMP_131 h)))))))))))))))) in (wcpr0_ind TMP_5 
TMP_12 TMP_132 c1 c2 H)))))).

theorem wcpr0_drop_back:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c1 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O c2 
(CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda 
(_: C).(\lambda (u2: T).(pr0 u2 u1)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(let TMP_5 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((drop h O c0 (CHead e1 k u1)) \to (let TMP_2 \def 
(\lambda (e2: C).(\lambda (u2: T).(let TMP_1 \def (CHead e2 k u2) in (drop h 
O c TMP_1)))) in (let TMP_3 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) in (let TMP_4 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))) in 
(ex3_2 C T TMP_2 TMP_3 TMP_4))))))))))) in (let TMP_12 \def (\lambda (c: 
C).(\lambda (h: nat).(\lambda (e1: C).(\lambda (u1: T).(\lambda (k: 
K).(\lambda (H0: (drop h O c (CHead e1 k u1))).(let TMP_7 \def (\lambda (e2: 
C).(\lambda (u2: T).(let TMP_6 \def (CHead e2 k u2) in (drop h O c TMP_6)))) 
in (let TMP_8 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let 
TMP_9 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))) in (let TMP_10 \def 
(wcpr0_refl e1) in (let TMP_11 \def (pr0_refl u1) in (ex3_2_intro C T TMP_7 
TMP_8 TMP_9 e1 u1 H0 TMP_10 TMP_11)))))))))))) in (let TMP_132 \def (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (H0: (wcpr0 c3 c4)).(\lambda (H1: ((\forall 
(h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((drop h O c4 
(CHead e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(drop h O 
c3 (CHead e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) 
(\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))))))))))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (h: 
nat).(let TMP_18 \def (\lambda (n: nat).(\forall (e1: C).(\forall (u3: 
T).(\forall (k0: K).((drop n O (CHead c4 k u2) (CHead e1 k0 u3)) \to (let 
TMP_15 \def (\lambda (e2: C).(\lambda (u4: T).(let TMP_13 \def (CHead c3 k 
u1) in (let TMP_14 \def (CHead e2 k0 u4) in (drop n O TMP_13 TMP_14))))) in 
(let TMP_16 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let 
TMP_17 \def (\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))) in (ex3_2 C T 
TMP_15 TMP_16 TMP_17))))))))) in (let TMP_67 \def (\lambda (e1: C).(\lambda 
(u0: T).(\lambda (k0: K).(\lambda (H3: (drop O O (CHead c4 k u2) (CHead e1 k0 
u0))).(let TMP_19 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow 
c4 | (CHead c _ _) \Rightarrow c])) in (let TMP_20 \def (CHead c4 k u2) in 
(let TMP_21 \def (CHead e1 k0 u0) in (let TMP_22 \def (CHead c4 k u2) in (let 
TMP_23 \def (CHead e1 k0 u0) in (let TMP_24 \def (drop_gen_refl TMP_22 TMP_23 
H3) in (let H4 \def (f_equal C C TMP_19 TMP_20 TMP_21 TMP_24) in (let TMP_25 
\def (\lambda (e: C).(match e with [(CSort _) \Rightarrow k | (CHead _ k1 _) 
\Rightarrow k1])) in (let TMP_26 \def (CHead c4 k u2) in (let TMP_27 \def 
(CHead e1 k0 u0) in (let TMP_28 \def (CHead c4 k u2) in (let TMP_29 \def 
(CHead e1 k0 u0) in (let TMP_30 \def (drop_gen_refl TMP_28 TMP_29 H3) in (let 
H5 \def (f_equal C K TMP_25 TMP_26 TMP_27 TMP_30) in (let TMP_31 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u2 | (CHead _ _ t) 
\Rightarrow t])) in (let TMP_32 \def (CHead c4 k u2) in (let TMP_33 \def 
(CHead e1 k0 u0) in (let TMP_34 \def (CHead c4 k u2) in (let TMP_35 \def 
(CHead e1 k0 u0) in (let TMP_36 \def (drop_gen_refl TMP_34 TMP_35 H3) in (let 
H6 \def (f_equal C T TMP_31 TMP_32 TMP_33 TMP_36) in (let TMP_65 \def 
(\lambda (H7: (eq K k k0)).(\lambda (H8: (eq C c4 e1)).(let TMP_42 \def 
(\lambda (k1: K).(let TMP_39 \def (\lambda (e2: C).(\lambda (u3: T).(let 
TMP_37 \def (CHead c3 k u1) in (let TMP_38 \def (CHead e2 k1 u3) in (drop O O 
TMP_37 TMP_38))))) in (let TMP_40 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) in (let TMP_41 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0))) in (ex3_2 C T TMP_39 TMP_40 TMP_41))))) in (let TMP_48 \def (\lambda 
(t: T).(let TMP_45 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_43 \def 
(CHead c3 k u1) in (let TMP_44 \def (CHead e2 k u3) in (drop O O TMP_43 
TMP_44))))) in (let TMP_46 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) in (let TMP_47 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 t))) in 
(ex3_2 C T TMP_45 TMP_46 TMP_47))))) in (let TMP_54 \def (\lambda (c: C).(let 
TMP_51 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_49 \def (CHead c3 k 
u1) in (let TMP_50 \def (CHead e2 k u3) in (drop O O TMP_49 TMP_50))))) in 
(let TMP_52 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 c))) in (let 
TMP_53 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u2))) in (ex3_2 C T 
TMP_51 TMP_52 TMP_53))))) in (let TMP_57 \def (\lambda (e2: C).(\lambda (u3: 
T).(let TMP_55 \def (CHead c3 k u1) in (let TMP_56 \def (CHead e2 k u3) in 
(drop O O TMP_55 TMP_56))))) in (let TMP_58 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 c4))) in (let TMP_59 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u2))) in (let TMP_60 \def (CHead c3 k u1) in (let TMP_61 \def 
(drop_refl TMP_60) in (let TMP_62 \def (ex3_2_intro C T TMP_57 TMP_58 TMP_59 
c3 u1 TMP_61 H0 H2) in (let TMP_63 \def (eq_ind C c4 TMP_54 TMP_62 e1 H8) in 
(let TMP_64 \def (eq_ind T u2 TMP_48 TMP_63 u0 H6) in (eq_ind K k TMP_42 
TMP_64 k0 H7)))))))))))))) in (let TMP_66 \def (TMP_65 H5) in (TMP_66 
H4)))))))))))))))))))))))))))) in (let TMP_74 \def (\lambda (k0: K).(\forall 
(n: nat).(((\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((drop n O 
(CHead c4 k0 u2) (CHead e1 k1 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda 
(u4: T).(drop n O (CHead c3 k0 u1) (CHead e2 k1 u4)))) (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 
u3))))))))) \to (\forall (e1: C).(\forall (u3: T).(\forall (k1: K).((drop (S 
n) O (CHead c4 k0 u2) (CHead e1 k1 u3)) \to (let TMP_71 \def (\lambda (e2: 
C).(\lambda (u4: T).(let TMP_68 \def (S n) in (let TMP_69 \def (CHead c3 k0 
u1) in (let TMP_70 \def (CHead e2 k1 u4) in (drop TMP_68 O TMP_69 
TMP_70)))))) in (let TMP_72 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) in (let TMP_73 \def (\lambda (_: C).(\lambda (u4: T).(pr0 u4 u3))) in 
(ex3_2 C T TMP_71 TMP_72 TMP_73))))))))))) in (let TMP_101 \def (\lambda (b: 
B).(\lambda (n: nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall 
(k0: K).((drop n O (CHead c4 (Bind b) u2) (CHead e1 k0 u3)) \to (ex3_2 C T 
(\lambda (e2: C).(\lambda (u4: T).(drop n O (CHead c3 (Bind b) u1) (CHead e2 
k0 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3)))))))))).(\lambda (e1: C).(\lambda (u0: 
T).(\lambda (k0: K).(\lambda (H4: (drop (S n) O (CHead c4 (Bind b) u2) (CHead 
e1 k0 u0))).(let TMP_75 \def (Bind b) in (let TMP_76 \def (CHead e1 k0 u0) in 
(let TMP_77 \def (drop_gen_drop TMP_75 c4 TMP_76 u2 n H4) in (let H5 \def (H1 
n e1 u0 k0 TMP_77) in (let TMP_79 \def (\lambda (e2: C).(\lambda (u3: T).(let 
TMP_78 \def (CHead e2 k0 u3) in (drop n O c3 TMP_78)))) in (let TMP_80 \def 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_81 \def (\lambda 
(_: C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_86 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_82 \def (S n) in (let TMP_83 \def (Bind b) in 
(let TMP_84 \def (CHead c3 TMP_83 u1) in (let TMP_85 \def (CHead e2 k0 u3) in 
(drop TMP_82 O TMP_84 TMP_85))))))) in (let TMP_87 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_88 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_89 \def (ex3_2 C T TMP_86 
TMP_87 TMP_88) in (let TMP_100 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (drop n O c3 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 x0 
e1)).(\lambda (H8: (pr0 x1 u0)).(let TMP_94 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_90 \def (S n) in (let TMP_91 \def (Bind b) in (let TMP_92 
\def (CHead c3 TMP_91 u1) in (let TMP_93 \def (CHead e2 k0 u3) in (drop 
TMP_90 O TMP_92 TMP_93))))))) in (let TMP_95 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 e1))) in (let TMP_96 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u0))) in (let TMP_97 \def (Bind b) in (let TMP_98 \def (CHead x0 
k0 x1) in (let TMP_99 \def (drop_drop TMP_97 n c3 TMP_98 H6 u1) in 
(ex3_2_intro C T TMP_94 TMP_95 TMP_96 x0 x1 TMP_99 H7 H8)))))))))))) in 
(ex3_2_ind C T TMP_79 TMP_80 TMP_81 TMP_89 TMP_100 H5)))))))))))))))))))) in 
(let TMP_130 \def (\lambda (f: F).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((drop n O (CHead c4 (Flat f) u2) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(drop n O 
(CHead c3 (Flat f) u1) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 
u3)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(drop (S n) O (CHead c4 (Flat f) u2) (CHead e1 k0 u0))).(let TMP_102 \def (S 
n) in (let TMP_103 \def (Flat f) in (let TMP_104 \def (CHead e1 k0 u0) in 
(let TMP_105 \def (drop_gen_drop TMP_103 c4 TMP_104 u2 n H4) in (let H5 \def 
(H1 TMP_102 e1 u0 k0 TMP_105) in (let TMP_108 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_106 \def (S n) in (let TMP_107 \def (CHead e2 k0 u3) in 
(drop TMP_106 O c3 TMP_107))))) in (let TMP_109 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_110 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_115 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_111 \def (S n) in (let TMP_112 \def (Flat f) in 
(let TMP_113 \def (CHead c3 TMP_112 u1) in (let TMP_114 \def (CHead e2 k0 u3) 
in (drop TMP_111 O TMP_113 TMP_114))))))) in (let TMP_116 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_117 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_118 \def (ex3_2 C T TMP_115 
TMP_116 TMP_117) in (let TMP_129 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (drop (S n) O c3 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 x0 
e1)).(\lambda (H8: (pr0 x1 u0)).(let TMP_123 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_119 \def (S n) in (let TMP_120 \def (Flat f) in (let TMP_121 
\def (CHead c3 TMP_120 u1) in (let TMP_122 \def (CHead e2 k0 u3) in (drop 
TMP_119 O TMP_121 TMP_122))))))) in (let TMP_124 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_125 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_126 \def (Flat f) in (let 
TMP_127 \def (CHead x0 k0 x1) in (let TMP_128 \def (drop_drop TMP_126 n c3 
TMP_127 H6 u1) in (ex3_2_intro C T TMP_123 TMP_124 TMP_125 x0 x1 TMP_128 H7 
H8)))))))))))) in (ex3_2_ind C T TMP_108 TMP_109 TMP_110 TMP_118 TMP_129 
H5))))))))))))))))))))) in (let TMP_131 \def (K_ind TMP_74 TMP_101 TMP_130 k) 
in (nat_ind TMP_18 TMP_67 TMP_131 h)))))))))))))))) in (wcpr0_ind TMP_5 
TMP_12 TMP_132 c2 c1 H)))))).

theorem wcpr0_getl:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 
k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c1 c2)).(let TMP_5 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((getl h c (CHead e1 k u1)) \to (let TMP_2 \def 
(\lambda (e2: C).(\lambda (u2: T).(let TMP_1 \def (CHead e2 k u2) in (getl h 
c0 TMP_1)))) in (let TMP_3 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) in (let TMP_4 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))) in 
(ex3_2 C T TMP_2 TMP_3 TMP_4))))))))))) in (let TMP_12 \def (\lambda (c: 
C).(\lambda (h: nat).(\lambda (e1: C).(\lambda (u1: T).(\lambda (k: 
K).(\lambda (H0: (getl h c (CHead e1 k u1))).(let TMP_7 \def (\lambda (e2: 
C).(\lambda (u2: T).(let TMP_6 \def (CHead e2 k u2) in (getl h c TMP_6)))) in 
(let TMP_8 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let 
TMP_9 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))) in (let TMP_10 \def 
(wcpr0_refl e1) in (let TMP_11 \def (pr0_refl u1) in (ex3_2_intro C T TMP_7 
TMP_8 TMP_9 e1 u1 H0 TMP_10 TMP_11)))))))))))) in (let TMP_175 \def (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (H0: (wcpr0 c3 c4)).(\lambda (H1: ((\forall 
(h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c3 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c4 (CHead 
e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2))))))))))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (h: nat).(let TMP_18 
\def (\lambda (n: nat).(\forall (e1: C).(\forall (u3: T).(\forall (k0: 
K).((getl n (CHead c3 k u1) (CHead e1 k0 u3)) \to (let TMP_15 \def (\lambda 
(e2: C).(\lambda (u4: T).(let TMP_13 \def (CHead c4 k u2) in (let TMP_14 \def 
(CHead e2 k0 u4) in (getl n TMP_13 TMP_14))))) in (let TMP_16 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_17 \def (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4))) in (ex3_2 C T TMP_15 TMP_16 TMP_17))))))))) 
in (let TMP_110 \def (\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: 
K).(\lambda (H3: (getl O (CHead c3 k u1) (CHead e1 k0 u0))).(let TMP_24 \def 
(\lambda (k1: K).((clear (CHead c3 k1 u1) (CHead e1 k0 u0)) \to (let TMP_21 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_19 \def (CHead c4 k1 u2) in 
(let TMP_20 \def (CHead e2 k0 u3) in (getl O TMP_19 TMP_20))))) in (let 
TMP_22 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_23 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) in (ex3_2 C T TMP_21 
TMP_22 TMP_23)))))) in (let TMP_80 \def (\lambda (b: B).(\lambda (H4: (clear 
(CHead c3 (Bind b) u1) (CHead e1 k0 u0))).(let TMP_25 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow e1 | (CHead c _ _) \Rightarrow c])) 
in (let TMP_26 \def (CHead e1 k0 u0) in (let TMP_27 \def (Bind b) in (let 
TMP_28 \def (CHead c3 TMP_27 u1) in (let TMP_29 \def (CHead e1 k0 u0) in (let 
TMP_30 \def (clear_gen_bind b c3 TMP_29 u1 H4) in (let H5 \def (f_equal C C 
TMP_25 TMP_26 TMP_28 TMP_30) in (let TMP_31 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) in (let 
TMP_32 \def (CHead e1 k0 u0) in (let TMP_33 \def (Bind b) in (let TMP_34 \def 
(CHead c3 TMP_33 u1) in (let TMP_35 \def (CHead e1 k0 u0) in (let TMP_36 \def 
(clear_gen_bind b c3 TMP_35 u1 H4) in (let H6 \def (f_equal C K TMP_31 TMP_32 
TMP_34 TMP_36) in (let TMP_37 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) in (let TMP_38 \def (CHead e1 
k0 u0) in (let TMP_39 \def (Bind b) in (let TMP_40 \def (CHead c3 TMP_39 u1) 
in (let TMP_41 \def (CHead e1 k0 u0) in (let TMP_42 \def (clear_gen_bind b c3 
TMP_41 u1 H4) in (let H7 \def (f_equal C T TMP_37 TMP_38 TMP_40 TMP_42) in 
(let TMP_78 \def (\lambda (H8: (eq K k0 (Bind b))).(\lambda (H9: (eq C e1 
c3)).(let TMP_43 \def (Bind b) in (let TMP_50 \def (\lambda (k1: K).(let 
TMP_47 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_44 \def (Bind b) in 
(let TMP_45 \def (CHead c4 TMP_44 u2) in (let TMP_46 \def (CHead e2 k1 u3) in 
(getl O TMP_45 TMP_46)))))) in (let TMP_48 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) in (let TMP_49 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3))) in (ex3_2 C T TMP_47 TMP_48 TMP_49))))) in (let TMP_58 \def (\lambda 
(t: T).(let TMP_55 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_51 \def 
(Bind b) in (let TMP_52 \def (CHead c4 TMP_51 u2) in (let TMP_53 \def (Bind 
b) in (let TMP_54 \def (CHead e2 TMP_53 u3) in (getl O TMP_52 TMP_54))))))) 
in (let TMP_56 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let 
TMP_57 \def (\lambda (_: C).(\lambda (u3: T).(pr0 t u3))) in (ex3_2 C T 
TMP_55 TMP_56 TMP_57))))) in (let TMP_66 \def (\lambda (c: C).(let TMP_63 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_59 \def (Bind b) in (let 
TMP_60 \def (CHead c4 TMP_59 u2) in (let TMP_61 \def (Bind b) in (let TMP_62 
\def (CHead e2 TMP_61 u3) in (getl O TMP_60 TMP_62))))))) in (let TMP_64 \def 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 c e2))) in (let TMP_65 \def (\lambda 
(_: C).(\lambda (u3: T).(pr0 u1 u3))) in (ex3_2 C T TMP_63 TMP_64 TMP_65))))) 
in (let TMP_71 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_67 \def (Bind 
b) in (let TMP_68 \def (CHead c4 TMP_67 u2) in (let TMP_69 \def (Bind b) in 
(let TMP_70 \def (CHead e2 TMP_69 u3) in (getl O TMP_68 TMP_70))))))) in (let 
TMP_72 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 c3 e2))) in (let TMP_73 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_74 \def 
(getl_refl b c4 u2) in (let TMP_75 \def (ex3_2_intro C T TMP_71 TMP_72 TMP_73 
c4 u2 TMP_74 H0 H2) in (let TMP_76 \def (eq_ind_r C c3 TMP_66 TMP_75 e1 H9) 
in (let TMP_77 \def (eq_ind_r T u1 TMP_58 TMP_76 u0 H7) in (eq_ind_r K TMP_43 
TMP_50 TMP_77 k0 H8)))))))))))))) in (let TMP_79 \def (TMP_78 H6) in (TMP_79 
H5)))))))))))))))))))))))))) in (let TMP_106 \def (\lambda (f: F).(\lambda 
(H4: (clear (CHead c3 (Flat f) u1) (CHead e1 k0 u0))).(let TMP_81 \def (CHead 
e1 k0 u0) in (let TMP_82 \def (drop_refl c3) in (let TMP_83 \def (CHead e1 k0 
u0) in (let TMP_84 \def (clear_gen_flat f c3 TMP_83 u1 H4) in (let TMP_85 
\def (getl_intro O c3 TMP_81 c3 TMP_82 TMP_84) in (let H5 \def (H1 O e1 u0 k0 
TMP_85) in (let TMP_87 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_86 
\def (CHead e2 k0 u3) in (getl O c4 TMP_86)))) in (let TMP_88 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_89 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_93 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_90 \def (Flat f) in (let TMP_91 \def (CHead c4 
TMP_90 u2) in (let TMP_92 \def (CHead e2 k0 u3) in (getl O TMP_91 
TMP_92)))))) in (let TMP_94 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 
e2))) in (let TMP_95 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) in 
(let TMP_96 \def (ex3_2 C T TMP_93 TMP_94 TMP_95) in (let TMP_105 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl O c4 (CHead x0 k0 
x1))).(\lambda (H7: (wcpr0 e1 x0)).(\lambda (H8: (pr0 u0 x1)).(let TMP_100 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_97 \def (Flat f) in (let 
TMP_98 \def (CHead c4 TMP_97 u2) in (let TMP_99 \def (CHead e2 k0 u3) in 
(getl O TMP_98 TMP_99)))))) in (let TMP_101 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e1 e2))) in (let TMP_102 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u0 u3))) in (let TMP_103 \def (CHead x0 k0 x1) in (let TMP_104 \def 
(getl_flat c4 TMP_103 O H6 f u2) in (ex3_2_intro C T TMP_100 TMP_101 TMP_102 
x0 x1 TMP_104 H7 H8))))))))))) in (ex3_2_ind C T TMP_87 TMP_88 TMP_89 TMP_96 
TMP_105 H5))))))))))))))))) in (let TMP_107 \def (CHead c3 k u1) in (let 
TMP_108 \def (CHead e1 k0 u0) in (let TMP_109 \def (getl_gen_O TMP_107 
TMP_108 H3) in (K_ind TMP_24 TMP_80 TMP_106 k TMP_109))))))))))) in (let 
TMP_117 \def (\lambda (k0: K).(\forall (n: nat).(((\forall (e1: C).(\forall 
(u3: T).(\forall (k1: K).((getl n (CHead c3 k0 u1) (CHead e1 k1 u3)) \to 
(ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n (CHead c4 k0 u2) (CHead 
e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4))))))))) \to (\forall (e1: C).(\forall (u3: 
T).(\forall (k1: K).((getl (S n) (CHead c3 k0 u1) (CHead e1 k1 u3)) \to (let 
TMP_114 \def (\lambda (e2: C).(\lambda (u4: T).(let TMP_111 \def (S n) in 
(let TMP_112 \def (CHead c4 k0 u2) in (let TMP_113 \def (CHead e2 k1 u4) in 
(getl TMP_111 TMP_112 TMP_113)))))) in (let TMP_115 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_116 \def (\lambda (_: 
C).(\lambda (u4: T).(pr0 u3 u4))) in (ex3_2 C T TMP_114 TMP_115 
TMP_116))))))))))) in (let TMP_144 \def (\lambda (b: B).(\lambda (n: 
nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall (k0: K).((getl 
n (CHead c3 (Bind b) u1) (CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl n (CHead c4 (Bind b) u2) (CHead e2 k0 u4)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda 
(u4: T).(pr0 u3 u4)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: 
K).(\lambda (H4: (getl (S n) (CHead c3 (Bind b) u1) (CHead e1 k0 u0))).(let 
TMP_118 \def (Bind b) in (let TMP_119 \def (CHead e1 k0 u0) in (let TMP_120 
\def (getl_gen_S TMP_118 c3 TMP_119 u1 n H4) in (let H5 \def (H1 n e1 u0 k0 
TMP_120) in (let TMP_122 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_121 
\def (CHead e2 k0 u3) in (getl n c4 TMP_121)))) in (let TMP_123 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_124 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_129 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_125 \def (S n) in (let TMP_126 \def (Bind b) in 
(let TMP_127 \def (CHead c4 TMP_126 u2) in (let TMP_128 \def (CHead e2 k0 u3) 
in (getl TMP_125 TMP_127 TMP_128))))))) in (let TMP_130 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_131 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_132 \def (ex3_2 C T TMP_129 
TMP_130 TMP_131) in (let TMP_143 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (getl n c4 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 e1 
x0)).(\lambda (H8: (pr0 u0 x1)).(let TMP_137 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_133 \def (S n) in (let TMP_134 \def (Bind b) in (let TMP_135 
\def (CHead c4 TMP_134 u2) in (let TMP_136 \def (CHead e2 k0 u3) in (getl 
TMP_133 TMP_135 TMP_136))))))) in (let TMP_138 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e1 e2))) in (let TMP_139 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u0 u3))) in (let TMP_140 \def (Bind b) in (let TMP_141 \def (CHead x0 
k0 x1) in (let TMP_142 \def (getl_head TMP_140 n c4 TMP_141 H6 u2) in 
(ex3_2_intro C T TMP_137 TMP_138 TMP_139 x0 x1 TMP_142 H7 H8)))))))))))) in 
(ex3_2_ind C T TMP_122 TMP_123 TMP_124 TMP_132 TMP_143 H5)))))))))))))))))))) 
in (let TMP_173 \def (\lambda (f: F).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c3 (Flat f) u1) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n 
(CHead c4 (Flat f) u2) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) (\lambda (_: C).(\lambda (u4: T).(pr0 u3 
u4)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c3 (Flat f) u1) (CHead e1 k0 u0))).(let TMP_145 \def (S n) 
in (let TMP_146 \def (Flat f) in (let TMP_147 \def (CHead e1 k0 u0) in (let 
TMP_148 \def (getl_gen_S TMP_146 c3 TMP_147 u1 n H4) in (let H5 \def (H1 
TMP_145 e1 u0 k0 TMP_148) in (let TMP_151 \def (\lambda (e2: C).(\lambda (u3: 
T).(let TMP_149 \def (S n) in (let TMP_150 \def (CHead e2 k0 u3) in (getl 
TMP_149 c4 TMP_150))))) in (let TMP_152 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e1 e2))) in (let TMP_153 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u0 u3))) in (let TMP_158 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_154 
\def (S n) in (let TMP_155 \def (Flat f) in (let TMP_156 \def (CHead c4 
TMP_155 u2) in (let TMP_157 \def (CHead e2 k0 u3) in (getl TMP_154 TMP_156 
TMP_157))))))) in (let TMP_159 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e1 e2))) in (let TMP_160 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) 
in (let TMP_161 \def (ex3_2 C T TMP_158 TMP_159 TMP_160) in (let TMP_172 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl (S n) c4 (CHead x0 k0 
x1))).(\lambda (H7: (wcpr0 e1 x0)).(\lambda (H8: (pr0 u0 x1)).(let TMP_166 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_162 \def (S n) in (let 
TMP_163 \def (Flat f) in (let TMP_164 \def (CHead c4 TMP_163 u2) in (let 
TMP_165 \def (CHead e2 k0 u3) in (getl TMP_162 TMP_164 TMP_165))))))) in (let 
TMP_167 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e1 e2))) in (let TMP_168 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u0 u3))) in (let TMP_169 \def 
(Flat f) in (let TMP_170 \def (CHead x0 k0 x1) in (let TMP_171 \def 
(getl_head TMP_169 n c4 TMP_170 H6 u2) in (ex3_2_intro C T TMP_166 TMP_167 
TMP_168 x0 x1 TMP_171 H7 H8)))))))))))) in (ex3_2_ind C T TMP_151 TMP_152 
TMP_153 TMP_161 TMP_172 H5))))))))))))))))))))) in (let TMP_174 \def (K_ind 
TMP_117 TMP_144 TMP_173 k) in (nat_ind TMP_18 TMP_110 TMP_174 
h)))))))))))))))) in (wcpr0_ind TMP_5 TMP_12 TMP_175 c1 c2 H)))))).

theorem wcpr0_getl_back:
 \forall (c1: C).(\forall (c2: C).((wcpr0 c2 c1) \to (\forall (h: 
nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c1 (CHead e1 
k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c2 (CHead e2 
k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u2 u1)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (wcpr0 c2 c1)).(let TMP_5 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (h: nat).(\forall (e1: C).(\forall 
(u1: T).(\forall (k: K).((getl h c0 (CHead e1 k u1)) \to (let TMP_2 \def 
(\lambda (e2: C).(\lambda (u2: T).(let TMP_1 \def (CHead e2 k u2) in (getl h 
c TMP_1)))) in (let TMP_3 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) in (let TMP_4 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))) in 
(ex3_2 C T TMP_2 TMP_3 TMP_4))))))))))) in (let TMP_12 \def (\lambda (c: 
C).(\lambda (h: nat).(\lambda (e1: C).(\lambda (u1: T).(\lambda (k: 
K).(\lambda (H0: (getl h c (CHead e1 k u1))).(let TMP_7 \def (\lambda (e2: 
C).(\lambda (u2: T).(let TMP_6 \def (CHead e2 k u2) in (getl h c TMP_6)))) in 
(let TMP_8 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let 
TMP_9 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u2 u1))) in (let TMP_10 \def 
(wcpr0_refl e1) in (let TMP_11 \def (pr0_refl u1) in (ex3_2_intro C T TMP_7 
TMP_8 TMP_9 e1 u1 H0 TMP_10 TMP_11)))))))))))) in (let TMP_175 \def (\lambda 
(c3: C).(\lambda (c4: C).(\lambda (H0: (wcpr0 c3 c4)).(\lambda (H1: ((\forall 
(h: nat).(\forall (e1: C).(\forall (u1: T).(\forall (k: K).((getl h c4 (CHead 
e1 k u1)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u2: T).(getl h c3 (CHead 
e2 k u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u2 u1))))))))))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (pr0 u1 u2)).(\lambda (k: K).(\lambda (h: nat).(let TMP_18 
\def (\lambda (n: nat).(\forall (e1: C).(\forall (u3: T).(\forall (k0: 
K).((getl n (CHead c4 k u2) (CHead e1 k0 u3)) \to (let TMP_15 \def (\lambda 
(e2: C).(\lambda (u4: T).(let TMP_13 \def (CHead c3 k u1) in (let TMP_14 \def 
(CHead e2 k0 u4) in (getl n TMP_13 TMP_14))))) in (let TMP_16 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_17 \def (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3))) in (ex3_2 C T TMP_15 TMP_16 TMP_17))))))))) 
in (let TMP_110 \def (\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: 
K).(\lambda (H3: (getl O (CHead c4 k u2) (CHead e1 k0 u0))).(let TMP_24 \def 
(\lambda (k1: K).((clear (CHead c4 k1 u2) (CHead e1 k0 u0)) \to (let TMP_21 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_19 \def (CHead c3 k1 u1) in 
(let TMP_20 \def (CHead e2 k0 u3) in (getl O TMP_19 TMP_20))))) in (let 
TMP_22 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_23 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) in (ex3_2 C T TMP_21 
TMP_22 TMP_23)))))) in (let TMP_80 \def (\lambda (b: B).(\lambda (H4: (clear 
(CHead c4 (Bind b) u2) (CHead e1 k0 u0))).(let TMP_25 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow e1 | (CHead c _ _) \Rightarrow c])) 
in (let TMP_26 \def (CHead e1 k0 u0) in (let TMP_27 \def (Bind b) in (let 
TMP_28 \def (CHead c4 TMP_27 u2) in (let TMP_29 \def (CHead e1 k0 u0) in (let 
TMP_30 \def (clear_gen_bind b c4 TMP_29 u2 H4) in (let H5 \def (f_equal C C 
TMP_25 TMP_26 TMP_28 TMP_30) in (let TMP_31 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) in (let 
TMP_32 \def (CHead e1 k0 u0) in (let TMP_33 \def (Bind b) in (let TMP_34 \def 
(CHead c4 TMP_33 u2) in (let TMP_35 \def (CHead e1 k0 u0) in (let TMP_36 \def 
(clear_gen_bind b c4 TMP_35 u2 H4) in (let H6 \def (f_equal C K TMP_31 TMP_32 
TMP_34 TMP_36) in (let TMP_37 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) in (let TMP_38 \def (CHead e1 
k0 u0) in (let TMP_39 \def (Bind b) in (let TMP_40 \def (CHead c4 TMP_39 u2) 
in (let TMP_41 \def (CHead e1 k0 u0) in (let TMP_42 \def (clear_gen_bind b c4 
TMP_41 u2 H4) in (let H7 \def (f_equal C T TMP_37 TMP_38 TMP_40 TMP_42) in 
(let TMP_78 \def (\lambda (H8: (eq K k0 (Bind b))).(\lambda (H9: (eq C e1 
c4)).(let TMP_43 \def (Bind b) in (let TMP_50 \def (\lambda (k1: K).(let 
TMP_47 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_44 \def (Bind b) in 
(let TMP_45 \def (CHead c3 TMP_44 u1) in (let TMP_46 \def (CHead e2 k1 u3) in 
(getl O TMP_45 TMP_46)))))) in (let TMP_48 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) in (let TMP_49 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0))) in (ex3_2 C T TMP_47 TMP_48 TMP_49))))) in (let TMP_58 \def (\lambda 
(t: T).(let TMP_55 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_51 \def 
(Bind b) in (let TMP_52 \def (CHead c3 TMP_51 u1) in (let TMP_53 \def (Bind 
b) in (let TMP_54 \def (CHead e2 TMP_53 u3) in (getl O TMP_52 TMP_54))))))) 
in (let TMP_56 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let 
TMP_57 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 t))) in (ex3_2 C T 
TMP_55 TMP_56 TMP_57))))) in (let TMP_66 \def (\lambda (c: C).(let TMP_63 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_59 \def (Bind b) in (let 
TMP_60 \def (CHead c3 TMP_59 u1) in (let TMP_61 \def (Bind b) in (let TMP_62 
\def (CHead e2 TMP_61 u3) in (getl O TMP_60 TMP_62))))))) in (let TMP_64 \def 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 c))) in (let TMP_65 \def (\lambda 
(_: C).(\lambda (u3: T).(pr0 u3 u2))) in (ex3_2 C T TMP_63 TMP_64 TMP_65))))) 
in (let TMP_71 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_67 \def (Bind 
b) in (let TMP_68 \def (CHead c3 TMP_67 u1) in (let TMP_69 \def (Bind b) in 
(let TMP_70 \def (CHead e2 TMP_69 u3) in (getl O TMP_68 TMP_70))))))) in (let 
TMP_72 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 c4))) in (let TMP_73 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u2))) in (let TMP_74 \def 
(getl_refl b c3 u1) in (let TMP_75 \def (ex3_2_intro C T TMP_71 TMP_72 TMP_73 
c3 u1 TMP_74 H0 H2) in (let TMP_76 \def (eq_ind_r C c4 TMP_66 TMP_75 e1 H9) 
in (let TMP_77 \def (eq_ind_r T u2 TMP_58 TMP_76 u0 H7) in (eq_ind_r K TMP_43 
TMP_50 TMP_77 k0 H8)))))))))))))) in (let TMP_79 \def (TMP_78 H6) in (TMP_79 
H5)))))))))))))))))))))))))) in (let TMP_106 \def (\lambda (f: F).(\lambda 
(H4: (clear (CHead c4 (Flat f) u2) (CHead e1 k0 u0))).(let TMP_81 \def (CHead 
e1 k0 u0) in (let TMP_82 \def (drop_refl c4) in (let TMP_83 \def (CHead e1 k0 
u0) in (let TMP_84 \def (clear_gen_flat f c4 TMP_83 u2 H4) in (let TMP_85 
\def (getl_intro O c4 TMP_81 c4 TMP_82 TMP_84) in (let H5 \def (H1 O e1 u0 k0 
TMP_85) in (let TMP_87 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_86 
\def (CHead e2 k0 u3) in (getl O c3 TMP_86)))) in (let TMP_88 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_89 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_93 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_90 \def (Flat f) in (let TMP_91 \def (CHead c3 
TMP_90 u1) in (let TMP_92 \def (CHead e2 k0 u3) in (getl O TMP_91 
TMP_92)))))) in (let TMP_94 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 
e1))) in (let TMP_95 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) in 
(let TMP_96 \def (ex3_2 C T TMP_93 TMP_94 TMP_95) in (let TMP_105 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl O c3 (CHead x0 k0 
x1))).(\lambda (H7: (wcpr0 x0 e1)).(\lambda (H8: (pr0 x1 u0)).(let TMP_100 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_97 \def (Flat f) in (let 
TMP_98 \def (CHead c3 TMP_97 u1) in (let TMP_99 \def (CHead e2 k0 u3) in 
(getl O TMP_98 TMP_99)))))) in (let TMP_101 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 e1))) in (let TMP_102 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u0))) in (let TMP_103 \def (CHead x0 k0 x1) in (let TMP_104 \def 
(getl_flat c3 TMP_103 O H6 f u1) in (ex3_2_intro C T TMP_100 TMP_101 TMP_102 
x0 x1 TMP_104 H7 H8))))))))))) in (ex3_2_ind C T TMP_87 TMP_88 TMP_89 TMP_96 
TMP_105 H5))))))))))))))))) in (let TMP_107 \def (CHead c4 k u2) in (let 
TMP_108 \def (CHead e1 k0 u0) in (let TMP_109 \def (getl_gen_O TMP_107 
TMP_108 H3) in (K_ind TMP_24 TMP_80 TMP_106 k TMP_109))))))))))) in (let 
TMP_117 \def (\lambda (k0: K).(\forall (n: nat).(((\forall (e1: C).(\forall 
(u3: T).(\forall (k1: K).((getl n (CHead c4 k0 u2) (CHead e1 k1 u3)) \to 
(ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n (CHead c3 k0 u1) (CHead 
e2 k1 u4)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3))))))))) \to (\forall (e1: C).(\forall (u3: 
T).(\forall (k1: K).((getl (S n) (CHead c4 k0 u2) (CHead e1 k1 u3)) \to (let 
TMP_114 \def (\lambda (e2: C).(\lambda (u4: T).(let TMP_111 \def (S n) in 
(let TMP_112 \def (CHead c3 k0 u1) in (let TMP_113 \def (CHead e2 k1 u4) in 
(getl TMP_111 TMP_112 TMP_113)))))) in (let TMP_115 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_116 \def (\lambda (_: 
C).(\lambda (u4: T).(pr0 u4 u3))) in (ex3_2 C T TMP_114 TMP_115 
TMP_116))))))))))) in (let TMP_144 \def (\lambda (b: B).(\lambda (n: 
nat).(\lambda (_: ((\forall (e1: C).(\forall (u3: T).(\forall (k0: K).((getl 
n (CHead c4 (Bind b) u2) (CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: 
C).(\lambda (u4: T).(getl n (CHead c3 (Bind b) u1) (CHead e2 k0 u4)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda 
(u4: T).(pr0 u4 u3)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: 
K).(\lambda (H4: (getl (S n) (CHead c4 (Bind b) u2) (CHead e1 k0 u0))).(let 
TMP_118 \def (Bind b) in (let TMP_119 \def (CHead e1 k0 u0) in (let TMP_120 
\def (getl_gen_S TMP_118 c4 TMP_119 u2 n H4) in (let H5 \def (H1 n e1 u0 k0 
TMP_120) in (let TMP_122 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_121 
\def (CHead e2 k0 u3) in (getl n c3 TMP_121)))) in (let TMP_123 \def (\lambda 
(e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_124 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_129 \def (\lambda (e2: 
C).(\lambda (u3: T).(let TMP_125 \def (S n) in (let TMP_126 \def (Bind b) in 
(let TMP_127 \def (CHead c3 TMP_126 u1) in (let TMP_128 \def (CHead e2 k0 u3) 
in (getl TMP_125 TMP_127 TMP_128))))))) in (let TMP_130 \def (\lambda (e2: 
C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_131 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_132 \def (ex3_2 C T TMP_129 
TMP_130 TMP_131) in (let TMP_143 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (getl n c3 (CHead x0 k0 x1))).(\lambda (H7: (wcpr0 x0 
e1)).(\lambda (H8: (pr0 x1 u0)).(let TMP_137 \def (\lambda (e2: C).(\lambda 
(u3: T).(let TMP_133 \def (S n) in (let TMP_134 \def (Bind b) in (let TMP_135 
\def (CHead c3 TMP_134 u1) in (let TMP_136 \def (CHead e2 k0 u3) in (getl 
TMP_133 TMP_135 TMP_136))))))) in (let TMP_138 \def (\lambda (e2: C).(\lambda 
(_: T).(wcpr0 e2 e1))) in (let TMP_139 \def (\lambda (_: C).(\lambda (u3: 
T).(pr0 u3 u0))) in (let TMP_140 \def (Bind b) in (let TMP_141 \def (CHead x0 
k0 x1) in (let TMP_142 \def (getl_head TMP_140 n c3 TMP_141 H6 u1) in 
(ex3_2_intro C T TMP_137 TMP_138 TMP_139 x0 x1 TMP_142 H7 H8)))))))))))) in 
(ex3_2_ind C T TMP_122 TMP_123 TMP_124 TMP_132 TMP_143 H5)))))))))))))))))))) 
in (let TMP_173 \def (\lambda (f: F).(\lambda (n: nat).(\lambda (_: ((\forall 
(e1: C).(\forall (u3: T).(\forall (k0: K).((getl n (CHead c4 (Flat f) u2) 
(CHead e1 k0 u3)) \to (ex3_2 C T (\lambda (e2: C).(\lambda (u4: T).(getl n 
(CHead c3 (Flat f) u1) (CHead e2 k0 u4)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) (\lambda (_: C).(\lambda (u4: T).(pr0 u4 
u3)))))))))).(\lambda (e1: C).(\lambda (u0: T).(\lambda (k0: K).(\lambda (H4: 
(getl (S n) (CHead c4 (Flat f) u2) (CHead e1 k0 u0))).(let TMP_145 \def (S n) 
in (let TMP_146 \def (Flat f) in (let TMP_147 \def (CHead e1 k0 u0) in (let 
TMP_148 \def (getl_gen_S TMP_146 c4 TMP_147 u2 n H4) in (let H5 \def (H1 
TMP_145 e1 u0 k0 TMP_148) in (let TMP_151 \def (\lambda (e2: C).(\lambda (u3: 
T).(let TMP_149 \def (S n) in (let TMP_150 \def (CHead e2 k0 u3) in (getl 
TMP_149 c3 TMP_150))))) in (let TMP_152 \def (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 e2 e1))) in (let TMP_153 \def (\lambda (_: C).(\lambda (u3: T).(pr0 
u3 u0))) in (let TMP_158 \def (\lambda (e2: C).(\lambda (u3: T).(let TMP_154 
\def (S n) in (let TMP_155 \def (Flat f) in (let TMP_156 \def (CHead c3 
TMP_155 u1) in (let TMP_157 \def (CHead e2 k0 u3) in (getl TMP_154 TMP_156 
TMP_157))))))) in (let TMP_159 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 
e2 e1))) in (let TMP_160 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) 
in (let TMP_161 \def (ex3_2 C T TMP_158 TMP_159 TMP_160) in (let TMP_172 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl (S n) c3 (CHead x0 k0 
x1))).(\lambda (H7: (wcpr0 x0 e1)).(\lambda (H8: (pr0 x1 u0)).(let TMP_166 
\def (\lambda (e2: C).(\lambda (u3: T).(let TMP_162 \def (S n) in (let 
TMP_163 \def (Flat f) in (let TMP_164 \def (CHead c3 TMP_163 u1) in (let 
TMP_165 \def (CHead e2 k0 u3) in (getl TMP_162 TMP_164 TMP_165))))))) in (let 
TMP_167 \def (\lambda (e2: C).(\lambda (_: T).(wcpr0 e2 e1))) in (let TMP_168 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u3 u0))) in (let TMP_169 \def 
(Flat f) in (let TMP_170 \def (CHead x0 k0 x1) in (let TMP_171 \def 
(getl_head TMP_169 n c3 TMP_170 H6 u1) in (ex3_2_intro C T TMP_166 TMP_167 
TMP_168 x0 x1 TMP_171 H7 H8)))))))))))) in (ex3_2_ind C T TMP_151 TMP_152 
TMP_153 TMP_161 TMP_172 H5))))))))))))))))))))) in (let TMP_174 \def (K_ind 
TMP_117 TMP_144 TMP_173 k) in (nat_ind TMP_18 TMP_110 TMP_174 
h)))))))))))))))) in (wcpr0_ind TMP_5 TMP_12 TMP_175 c2 c1 H)))))).

