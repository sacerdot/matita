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

include "basic_1/wcpr0/defs.ma".

let rec wcpr0_ind (P: (C \to (C \to Prop))) (f: (\forall (c: C).(P c c))) 
(f0: (\forall (c1: C).(\forall (c2: C).((wcpr0 c1 c2) \to ((P c1 c2) \to 
(\forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (k: K).(P (CHead 
c1 k u1) (CHead c2 k u2))))))))))) (c: C) (c0: C) (w: wcpr0 c c0) on w: P c 
c0 \def match w with [(wcpr0_refl c1) \Rightarrow (f c1) | (wcpr0_comp c1 c2 
w0 u1 u2 p k) \Rightarrow (let TMP_1 \def ((wcpr0_ind P f f0) c1 c2 w0) in 
(f0 c1 c2 w0 TMP_1 u1 u2 p k))].

theorem wcpr0_gen_sort:
 \forall (x: C).(\forall (n: nat).((wcpr0 (CSort n) x) \to (eq C x (CSort 
n))))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (wcpr0 (CSort n) x)).(let 
TMP_1 \def (CSort n) in (let TMP_2 \def (\lambda (c: C).(wcpr0 c x)) in (let 
TMP_3 \def (\lambda (c: C).(eq C x c)) in (let TMP_19 \def (\lambda (y: 
C).(\lambda (H0: (wcpr0 y x)).(let TMP_4 \def (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CSort n)) \to (eq C c0 c)))) in (let TMP_11 \def (\lambda (c: 
C).(\lambda (H1: (eq C c (CSort n))).(let TMP_5 \def (\lambda (e: C).e) in 
(let TMP_6 \def (CSort n) in (let H2 \def (f_equal C C TMP_5 c TMP_6 H1) in 
(let TMP_7 \def (CSort n) in (let TMP_8 \def (\lambda (c0: C).(eq C c0 c0)) 
in (let TMP_9 \def (CSort n) in (let TMP_10 \def (refl_equal C TMP_9) in 
(eq_ind_r C TMP_7 TMP_8 TMP_10 c H2)))))))))) in (let TMP_18 \def (\lambda 
(c1: C).(\lambda (c2: C).(\lambda (_: (wcpr0 c1 c2)).(\lambda (_: (((eq C c1 
(CSort n)) \to (eq C c2 c1)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: 
(pr0 u1 u2)).(\lambda (k: K).(\lambda (H4: (eq C (CHead c1 k u1) (CSort 
n))).(let TMP_12 \def (CHead c1 k u1) in (let TMP_13 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) in (let TMP_14 \def (CSort n) in (let H5 \def (eq_ind C TMP_12 TMP_13 
I TMP_14 H4) in (let TMP_15 \def (CHead c2 k u2) in (let TMP_16 \def (CHead 
c1 k u1) in (let TMP_17 \def (eq C TMP_15 TMP_16) in (False_ind TMP_17 
H5))))))))))))))))) in (wcpr0_ind TMP_4 TMP_11 TMP_18 y x H0)))))) in 
(insert_eq C TMP_1 TMP_2 TMP_3 TMP_19 H))))))).

theorem wcpr0_gen_head:
 \forall (k: K).(\forall (c1: C).(\forall (x: C).(\forall (u1: T).((wcpr0 
(CHead c1 k u1) x) \to (or (eq C x (CHead c1 k u1)) (ex3_2 C T (\lambda (c2: 
C).(\lambda (u2: T).(eq C x (CHead c2 k u2)))) (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2)))))))))
\def
 \lambda (k: K).(\lambda (c1: C).(\lambda (x: C).(\lambda (u1: T).(\lambda 
(H: (wcpr0 (CHead c1 k u1) x)).(let TMP_1 \def (CHead c1 k u1) in (let TMP_2 
\def (\lambda (c: C).(wcpr0 c x)) in (let TMP_9 \def (\lambda (c: C).(let 
TMP_3 \def (eq C x c) in (let TMP_5 \def (\lambda (c2: C).(\lambda (u2: 
T).(let TMP_4 \def (CHead c2 k u2) in (eq C x TMP_4)))) in (let TMP_6 \def 
(\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) in (let TMP_7 \def (\lambda 
(_: C).(\lambda (u2: T).(pr0 u1 u2))) in (let TMP_8 \def (ex3_2 C T TMP_5 
TMP_6 TMP_7) in (or TMP_3 TMP_8))))))) in (let TMP_111 \def (\lambda (y: 
C).(\lambda (H0: (wcpr0 y x)).(let TMP_16 \def (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CHead c1 k u1)) \to (let TMP_10 \def (eq C c0 c) in (let TMP_12 
\def (\lambda (c2: C).(\lambda (u2: T).(let TMP_11 \def (CHead c2 k u2) in 
(eq C c0 TMP_11)))) in (let TMP_13 \def (\lambda (c2: C).(\lambda (_: 
T).(wcpr0 c1 c2))) in (let TMP_14 \def (\lambda (_: C).(\lambda (u2: T).(pr0 
u1 u2))) in (let TMP_15 \def (ex3_2 C T TMP_12 TMP_13 TMP_14) in (or TMP_10 
TMP_15))))))))) in (let TMP_39 \def (\lambda (c: C).(\lambda (H1: (eq C c 
(CHead c1 k u1))).(let TMP_17 \def (\lambda (e: C).e) in (let TMP_18 \def 
(CHead c1 k u1) in (let H2 \def (f_equal C C TMP_17 c TMP_18 H1) in (let 
TMP_19 \def (CHead c1 k u1) in (let TMP_26 \def (\lambda (c0: C).(let TMP_20 
\def (eq C c0 c0) in (let TMP_22 \def (\lambda (c2: C).(\lambda (u2: T).(let 
TMP_21 \def (CHead c2 k u2) in (eq C c0 TMP_21)))) in (let TMP_23 \def 
(\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 c2))) in (let TMP_24 \def (\lambda 
(_: C).(\lambda (u2: T).(pr0 u1 u2))) in (let TMP_25 \def (ex3_2 C T TMP_22 
TMP_23 TMP_24) in (or TMP_20 TMP_25))))))) in (let TMP_27 \def (CHead c1 k 
u1) in (let TMP_28 \def (CHead c1 k u1) in (let TMP_29 \def (eq C TMP_27 
TMP_28) in (let TMP_32 \def (\lambda (c2: C).(\lambda (u2: T).(let TMP_30 
\def (CHead c1 k u1) in (let TMP_31 \def (CHead c2 k u2) in (eq C TMP_30 
TMP_31))))) in (let TMP_33 \def (\lambda (c2: C).(\lambda (_: T).(wcpr0 c1 
c2))) in (let TMP_34 \def (\lambda (_: C).(\lambda (u2: T).(pr0 u1 u2))) in 
(let TMP_35 \def (ex3_2 C T TMP_32 TMP_33 TMP_34) in (let TMP_36 \def (CHead 
c1 k u1) in (let TMP_37 \def (refl_equal C TMP_36) in (let TMP_38 \def 
(or_introl TMP_29 TMP_35 TMP_37) in (eq_ind_r C TMP_19 TMP_26 TMP_38 c 
H2)))))))))))))))))) in (let TMP_110 \def (\lambda (c0: C).(\lambda (c2: 
C).(\lambda (H1: (wcpr0 c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 k u1)) \to 
(or (eq C c2 c0) (ex3_2 C T (\lambda (c3: C).(\lambda (u2: T).(eq C c2 (CHead 
c3 k u2)))) (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u1 u2)))))))).(\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H3: (pr0 u0 u2)).(\lambda (k0: K).(\lambda (H4: (eq C (CHead c0 
k0 u0) (CHead c1 k u1))).(let TMP_40 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) in (let TMP_41 
\def (CHead c0 k0 u0) in (let TMP_42 \def (CHead c1 k u1) in (let H5 \def 
(f_equal C C TMP_40 TMP_41 TMP_42 H4) in (let TMP_43 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) 
in (let TMP_44 \def (CHead c0 k0 u0) in (let TMP_45 \def (CHead c1 k u1) in 
(let H6 \def (f_equal C K TMP_43 TMP_44 TMP_45 H4) in (let TMP_46 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) in (let TMP_47 \def (CHead c0 k0 u0) in (let TMP_48 \def 
(CHead c1 k u1) in (let H7 \def (f_equal C T TMP_46 TMP_47 TMP_48 H4) in (let 
TMP_108 \def (\lambda (H8: (eq K k0 k)).(\lambda (H9: (eq C c0 c1)).(let 
TMP_58 \def (\lambda (k1: K).(let TMP_49 \def (CHead c2 k1 u2) in (let TMP_50 
\def (CHead c0 k1 u0) in (let TMP_51 \def (eq C TMP_49 TMP_50) in (let TMP_54 
\def (\lambda (c3: C).(\lambda (u3: T).(let TMP_52 \def (CHead c2 k1 u2) in 
(let TMP_53 \def (CHead c3 k u3) in (eq C TMP_52 TMP_53))))) in (let TMP_55 
\def (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) in (let TMP_56 \def 
(\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_57 \def (ex3_2 C T 
TMP_54 TMP_55 TMP_56) in (or TMP_51 TMP_57))))))))) in (let TMP_59 \def 
(\lambda (t: T).(pr0 t u2)) in (let H10 \def (eq_ind T u0 TMP_59 H3 u1 H7) in 
(let TMP_69 \def (\lambda (t: T).(let TMP_60 \def (CHead c2 k u2) in (let 
TMP_61 \def (CHead c0 k t) in (let TMP_62 \def (eq C TMP_60 TMP_61) in (let 
TMP_65 \def (\lambda (c3: C).(\lambda (u3: T).(let TMP_63 \def (CHead c2 k 
u2) in (let TMP_64 \def (CHead c3 k u3) in (eq C TMP_63 TMP_64))))) in (let 
TMP_66 \def (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) in (let TMP_67 
\def (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_68 \def 
(ex3_2 C T TMP_65 TMP_66 TMP_67) in (or TMP_62 TMP_68))))))))) in (let TMP_76 
\def (\lambda (c: C).((eq C c (CHead c1 k u1)) \to (let TMP_70 \def (eq C c2 
c) in (let TMP_72 \def (\lambda (c3: C).(\lambda (u3: T).(let TMP_71 \def 
(CHead c3 k u3) in (eq C c2 TMP_71)))) in (let TMP_73 \def (\lambda (c3: 
C).(\lambda (_: T).(wcpr0 c1 c3))) in (let TMP_74 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_75 \def (ex3_2 C T TMP_72 
TMP_73 TMP_74) in (or TMP_70 TMP_75)))))))) in (let H11 \def (eq_ind C c0 
TMP_76 H2 c1 H9) in (let TMP_77 \def (\lambda (c: C).(wcpr0 c c2)) in (let 
H12 \def (eq_ind C c0 TMP_77 H1 c1 H9) in (let TMP_87 \def (\lambda (c: 
C).(let TMP_78 \def (CHead c2 k u2) in (let TMP_79 \def (CHead c k u1) in 
(let TMP_80 \def (eq C TMP_78 TMP_79) in (let TMP_83 \def (\lambda (c3: 
C).(\lambda (u3: T).(let TMP_81 \def (CHead c2 k u2) in (let TMP_82 \def 
(CHead c3 k u3) in (eq C TMP_81 TMP_82))))) in (let TMP_84 \def (\lambda (c3: 
C).(\lambda (_: T).(wcpr0 c1 c3))) in (let TMP_85 \def (\lambda (_: 
C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_86 \def (ex3_2 C T TMP_83 
TMP_84 TMP_85) in (or TMP_80 TMP_86))))))))) in (let TMP_88 \def (CHead c2 k 
u2) in (let TMP_89 \def (CHead c1 k u1) in (let TMP_90 \def (eq C TMP_88 
TMP_89) in (let TMP_93 \def (\lambda (c3: C).(\lambda (u3: T).(let TMP_91 
\def (CHead c2 k u2) in (let TMP_92 \def (CHead c3 k u3) in (eq C TMP_91 
TMP_92))))) in (let TMP_94 \def (\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 
c3))) in (let TMP_95 \def (\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in 
(let TMP_96 \def (ex3_2 C T TMP_93 TMP_94 TMP_95) in (let TMP_99 \def 
(\lambda (c3: C).(\lambda (u3: T).(let TMP_97 \def (CHead c2 k u2) in (let 
TMP_98 \def (CHead c3 k u3) in (eq C TMP_97 TMP_98))))) in (let TMP_100 \def 
(\lambda (c3: C).(\lambda (_: T).(wcpr0 c1 c3))) in (let TMP_101 \def 
(\lambda (_: C).(\lambda (u3: T).(pr0 u1 u3))) in (let TMP_102 \def (CHead c2 
k u2) in (let TMP_103 \def (refl_equal C TMP_102) in (let TMP_104 \def 
(ex3_2_intro C T TMP_99 TMP_100 TMP_101 c2 u2 TMP_103 H12 H10) in (let 
TMP_105 \def (or_intror TMP_90 TMP_96 TMP_104) in (let TMP_106 \def (eq_ind_r 
C c1 TMP_87 TMP_105 c0 H9) in (let TMP_107 \def (eq_ind_r T u1 TMP_69 TMP_106 
u0 H7) in (eq_ind_r K k TMP_58 TMP_107 k0 H8)))))))))))))))))))))))))))) in 
(let TMP_109 \def (TMP_108 H6) in (TMP_109 H5)))))))))))))))))))))))) in 
(wcpr0_ind TMP_16 TMP_39 TMP_110 y x H0)))))) in (insert_eq C TMP_1 TMP_2 
TMP_9 TMP_111 H))))))))).

