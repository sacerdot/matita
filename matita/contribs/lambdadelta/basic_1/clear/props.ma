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

include "basic_1/clear/fwd.ma".

theorem clear_clear:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (clear c2 c2)))
\def
 \lambda (c1: C).(let TMP_1 \def (\lambda (c: C).(\forall (c2: C).((clear c 
c2) \to (clear c2 c2)))) in (let TMP_3 \def (\lambda (n: nat).(\lambda (c2: 
C).(\lambda (H: (clear (CSort n) c2)).(let TMP_2 \def (clear c2 c2) in 
(clear_gen_sort c2 n H TMP_2))))) in (let TMP_13 \def (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).((clear c c2) \to (clear c2 
c2))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (H0: (clear 
(CHead c k t) c2)).(let TMP_4 \def (\lambda (k0: K).((clear (CHead c k0 t) 
c2) \to (clear c2 c2))) in (let TMP_10 \def (\lambda (b: B).(\lambda (H1: 
(clear (CHead c (Bind b) t) c2)).(let TMP_5 \def (Bind b) in (let TMP_6 \def 
(CHead c TMP_5 t) in (let TMP_7 \def (\lambda (c0: C).(clear c0 c0)) in (let 
TMP_8 \def (clear_bind b c t) in (let TMP_9 \def (clear_gen_bind b c c2 t H1) 
in (eq_ind_r C TMP_6 TMP_7 TMP_8 c2 TMP_9)))))))) in (let TMP_12 \def 
(\lambda (f: F).(\lambda (H1: (clear (CHead c (Flat f) t) c2)).(let TMP_11 
\def (clear_gen_flat f c c2 t H1) in (H c2 TMP_11)))) in (K_ind TMP_4 TMP_10 
TMP_12 k H0)))))))))) in (C_ind TMP_1 TMP_3 TMP_13 c1)))).

theorem clear_trans:
 \forall (c1: C).(\forall (c: C).((clear c1 c) \to (\forall (c2: C).((clear c 
c2) \to (clear c1 c2)))))
\def
 \lambda (c1: C).(let TMP_1 \def (\lambda (c: C).(\forall (c0: C).((clear c 
c0) \to (\forall (c2: C).((clear c0 c2) \to (clear c c2)))))) in (let TMP_4 
\def (\lambda (n: nat).(\lambda (c: C).(\lambda (H: (clear (CSort n) 
c)).(\lambda (c2: C).(\lambda (_: (clear c c2)).(let TMP_2 \def (CSort n) in 
(let TMP_3 \def (clear TMP_2 c2) in (clear_gen_sort c n H TMP_3)))))))) in 
(let TMP_22 \def (\lambda (c: C).(\lambda (H: ((\forall (c0: C).((clear c c0) 
\to (\forall (c2: C).((clear c0 c2) \to (clear c c2))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c0: C).(\lambda (H0: (clear (CHead c k t) 
c0)).(\lambda (c2: C).(\lambda (H1: (clear c0 c2)).(let TMP_6 \def (\lambda 
(k0: K).((clear (CHead c k0 t) c0) \to (let TMP_5 \def (CHead c k0 t) in 
(clear TMP_5 c2)))) in (let TMP_18 \def (\lambda (b: B).(\lambda (H2: (clear 
(CHead c (Bind b) t) c0)).(let TMP_7 \def (\lambda (c3: C).(clear c3 c2)) in 
(let TMP_8 \def (Bind b) in (let TMP_9 \def (CHead c TMP_8 t) in (let TMP_10 
\def (clear_gen_bind b c c0 t H2) in (let H3 \def (eq_ind C c0 TMP_7 H1 TMP_9 
TMP_10) in (let TMP_11 \def (Bind b) in (let TMP_12 \def (CHead c TMP_11 t) 
in (let TMP_15 \def (\lambda (c3: C).(let TMP_13 \def (Bind b) in (let TMP_14 
\def (CHead c TMP_13 t) in (clear TMP_14 c3)))) in (let TMP_16 \def 
(clear_bind b c t) in (let TMP_17 \def (clear_gen_bind b c c2 t H3) in 
(eq_ind_r C TMP_12 TMP_15 TMP_16 c2 TMP_17))))))))))))) in (let TMP_21 \def 
(\lambda (f: F).(\lambda (H2: (clear (CHead c (Flat f) t) c0)).(let TMP_19 
\def (clear_gen_flat f c c0 t H2) in (let TMP_20 \def (H c0 TMP_19 c2 H1) in 
(clear_flat c c2 TMP_20 f t))))) in (K_ind TMP_6 TMP_18 TMP_21 k 
H0)))))))))))) in (C_ind TMP_1 TMP_4 TMP_22 c1)))).

theorem clear_ctail:
 \forall (b: B).(\forall (c1: C).(\forall (c2: C).(\forall (u2: T).((clear c1 
(CHead c2 (Bind b) u2)) \to (\forall (k: K).(\forall (u1: T).(clear (CTail k 
u1 c1) (CHead (CTail k u1 c2) (Bind b) u2))))))))
\def
 \lambda (b: B).(\lambda (c1: C).(let TMP_5 \def (\lambda (c: C).(\forall 
(c2: C).(\forall (u2: T).((clear c (CHead c2 (Bind b) u2)) \to (\forall (k: 
K).(\forall (u1: T).(let TMP_1 \def (CTail k u1 c) in (let TMP_2 \def (CTail 
k u1 c2) in (let TMP_3 \def (Bind b) in (let TMP_4 \def (CHead TMP_2 TMP_3 
u2) in (clear TMP_1 TMP_4))))))))))) in (let TMP_34 \def (\lambda (n: 
nat).(\lambda (c2: C).(\lambda (u2: T).(\lambda (H: (clear (CSort n) (CHead 
c2 (Bind b) u2))).(\lambda (k: K).(\lambda (u1: T).(let TMP_11 \def (\lambda 
(k0: K).(let TMP_6 \def (CSort n) in (let TMP_7 \def (CHead TMP_6 k0 u1) in 
(let TMP_8 \def (CTail k0 u1 c2) in (let TMP_9 \def (Bind b) in (let TMP_10 
\def (CHead TMP_8 TMP_9 u2) in (clear TMP_7 TMP_10))))))) in (let TMP_22 \def 
(\lambda (b0: B).(let TMP_12 \def (Bind b) in (let TMP_13 \def (CHead c2 
TMP_12 u2) in (let TMP_14 \def (CSort n) in (let TMP_15 \def (Bind b0) in 
(let TMP_16 \def (CHead TMP_14 TMP_15 u1) in (let TMP_17 \def (Bind b0) in 
(let TMP_18 \def (CTail TMP_17 u1 c2) in (let TMP_19 \def (Bind b) in (let 
TMP_20 \def (CHead TMP_18 TMP_19 u2) in (let TMP_21 \def (clear TMP_16 
TMP_20) in (clear_gen_sort TMP_13 n H TMP_21)))))))))))) in (let TMP_33 \def 
(\lambda (f: F).(let TMP_23 \def (Bind b) in (let TMP_24 \def (CHead c2 
TMP_23 u2) in (let TMP_25 \def (CSort n) in (let TMP_26 \def (Flat f) in (let 
TMP_27 \def (CHead TMP_25 TMP_26 u1) in (let TMP_28 \def (Flat f) in (let 
TMP_29 \def (CTail TMP_28 u1 c2) in (let TMP_30 \def (Bind b) in (let TMP_31 
\def (CHead TMP_29 TMP_30 u2) in (let TMP_32 \def (clear TMP_27 TMP_31) in 
(clear_gen_sort TMP_24 n H TMP_32)))))))))))) in (K_ind TMP_11 TMP_22 TMP_33 
k)))))))))) in (let TMP_102 \def (\lambda (c: C).(\lambda (H: ((\forall (c2: 
C).(\forall (u2: T).((clear c (CHead c2 (Bind b) u2)) \to (\forall (k: 
K).(\forall (u1: T).(clear (CTail k u1 c) (CHead (CTail k u1 c2) (Bind b) 
u2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (u2: 
T).(\lambda (H0: (clear (CHead c k t) (CHead c2 (Bind b) u2))).(\lambda (k0: 
K).(\lambda (u1: T).(let TMP_40 \def (\lambda (k1: K).((clear (CHead c k1 t) 
(CHead c2 (Bind b) u2)) \to (let TMP_35 \def (CTail k0 u1 c) in (let TMP_36 
\def (CHead TMP_35 k1 t) in (let TMP_37 \def (CTail k0 u1 c2) in (let TMP_38 
\def (Bind b) in (let TMP_39 \def (CHead TMP_37 TMP_38 u2) in (clear TMP_36 
TMP_39)))))))) in (let TMP_92 \def (\lambda (b0: B).(\lambda (H1: (clear 
(CHead c (Bind b0) t) (CHead c2 (Bind b) u2))).(let TMP_41 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) 
in (let TMP_42 \def (Bind b) in (let TMP_43 \def (CHead c2 TMP_42 u2) in (let 
TMP_44 \def (Bind b0) in (let TMP_45 \def (CHead c TMP_44 t) in (let TMP_46 
\def (Bind b) in (let TMP_47 \def (CHead c2 TMP_46 u2) in (let TMP_48 \def 
(clear_gen_bind b0 c TMP_47 t H1) in (let H2 \def (f_equal C C TMP_41 TMP_43 
TMP_45 TMP_48) in (let TMP_49 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow b | (CHead _ k1 _) \Rightarrow (match k1 with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let TMP_50 \def (Bind b) in 
(let TMP_51 \def (CHead c2 TMP_50 u2) in (let TMP_52 \def (Bind b0) in (let 
TMP_53 \def (CHead c TMP_52 t) in (let TMP_54 \def (Bind b) in (let TMP_55 
\def (CHead c2 TMP_54 u2) in (let TMP_56 \def (clear_gen_bind b0 c TMP_55 t 
H1) in (let H3 \def (f_equal C B TMP_49 TMP_51 TMP_53 TMP_56) in (let TMP_57 
\def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u2 | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_58 \def (Bind b) in (let TMP_59 \def (CHead c2 
TMP_58 u2) in (let TMP_60 \def (Bind b0) in (let TMP_61 \def (CHead c TMP_60 
t) in (let TMP_62 \def (Bind b) in (let TMP_63 \def (CHead c2 TMP_62 u2) in 
(let TMP_64 \def (clear_gen_bind b0 c TMP_63 t H1) in (let H4 \def (f_equal C 
T TMP_57 TMP_59 TMP_61 TMP_64) in (let TMP_90 \def (\lambda (H5: (eq B b 
b0)).(\lambda (H6: (eq C c2 c)).(let TMP_71 \def (\lambda (t0: T).(let TMP_65 
\def (CTail k0 u1 c) in (let TMP_66 \def (Bind b0) in (let TMP_67 \def (CHead 
TMP_65 TMP_66 t) in (let TMP_68 \def (CTail k0 u1 c2) in (let TMP_69 \def 
(Bind b) in (let TMP_70 \def (CHead TMP_68 TMP_69 t0) in (clear TMP_67 
TMP_70)))))))) in (let TMP_78 \def (\lambda (c0: C).(let TMP_72 \def (CTail 
k0 u1 c) in (let TMP_73 \def (Bind b0) in (let TMP_74 \def (CHead TMP_72 
TMP_73 t) in (let TMP_75 \def (CTail k0 u1 c0) in (let TMP_76 \def (Bind b) 
in (let TMP_77 \def (CHead TMP_75 TMP_76 t) in (clear TMP_74 TMP_77)))))))) 
in (let TMP_85 \def (\lambda (b1: B).(let TMP_79 \def (CTail k0 u1 c) in (let 
TMP_80 \def (Bind b1) in (let TMP_81 \def (CHead TMP_79 TMP_80 t) in (let 
TMP_82 \def (CTail k0 u1 c) in (let TMP_83 \def (Bind b) in (let TMP_84 \def 
(CHead TMP_82 TMP_83 t) in (clear TMP_81 TMP_84)))))))) in (let TMP_86 \def 
(CTail k0 u1 c) in (let TMP_87 \def (clear_bind b TMP_86 t) in (let TMP_88 
\def (eq_ind B b TMP_85 TMP_87 b0 H5) in (let TMP_89 \def (eq_ind_r C c 
TMP_78 TMP_88 c2 H6) in (eq_ind_r T t TMP_71 TMP_89 u2 H4)))))))))) in (let 
TMP_91 \def (TMP_90 H3) in (TMP_91 H2)))))))))))))))))))))))))))))))) in (let 
TMP_101 \def (\lambda (f: F).(\lambda (H1: (clear (CHead c (Flat f) t) (CHead 
c2 (Bind b) u2))).(let TMP_93 \def (CTail k0 u1 c) in (let TMP_94 \def (CTail 
k0 u1 c2) in (let TMP_95 \def (Bind b) in (let TMP_96 \def (CHead TMP_94 
TMP_95 u2) in (let TMP_97 \def (Bind b) in (let TMP_98 \def (CHead c2 TMP_97 
u2) in (let TMP_99 \def (clear_gen_flat f c TMP_98 t H1) in (let TMP_100 \def 
(H c2 u2 TMP_99 k0 u1) in (clear_flat TMP_93 TMP_96 TMP_100 f t))))))))))) in 
(K_ind TMP_40 TMP_92 TMP_101 k H0))))))))))))) in (C_ind TMP_5 TMP_34 TMP_102 
c1))))).

