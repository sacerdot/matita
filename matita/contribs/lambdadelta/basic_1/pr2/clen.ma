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

include "basic_1/pr2/props.ma".

include "basic_1/clen/getl.ma".

theorem pr2_gen_ctail:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CTail k u c) t1 t2) \to (or (pr2 c t1 t2) (ex3 T (\lambda (_: 
T).(eq K k (Bind Abbr))) (\lambda (t: T).(pr0 t1 t)) (\lambda (t: T).(subst0 
(clen c) u t t2)))))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CTail k u c) t1 t2)).(let TMP_1 \def (CTail k u c) 
in (let TMP_2 \def (\lambda (c0: C).(pr2 c0 t1 t2)) in (let TMP_10 \def 
(\lambda (_: C).(let TMP_3 \def (pr2 c t1 t2) in (let TMP_5 \def (\lambda (_: 
T).(let TMP_4 \def (Bind Abbr) in (eq K k TMP_4))) in (let TMP_6 \def 
(\lambda (t: T).(pr0 t1 t)) in (let TMP_8 \def (\lambda (t: T).(let TMP_7 
\def (clen c) in (subst0 TMP_7 u t t2))) in (let TMP_9 \def (ex3 T TMP_5 
TMP_6 TMP_8) in (or TMP_3 TMP_9))))))) in (let TMP_126 \def (\lambda (y: 
C).(\lambda (H0: (pr2 y t1 t2)).(let TMP_18 \def (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq C c0 (CTail k u c)) \to (let TMP_11 \def (pr2 c 
t t0) in (let TMP_13 \def (\lambda (_: T).(let TMP_12 \def (Bind Abbr) in (eq 
K k TMP_12))) in (let TMP_14 \def (\lambda (t3: T).(pr0 t t3)) in (let TMP_16 
\def (\lambda (t3: T).(let TMP_15 \def (clen c) in (subst0 TMP_15 u t3 t0))) 
in (let TMP_17 \def (ex3 T TMP_13 TMP_14 TMP_16) in (or TMP_11 
TMP_17)))))))))) in (let TMP_27 \def (\lambda (c0: C).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CTail k 
u c))).(let TMP_19 \def (pr2 c t3 t4) in (let TMP_21 \def (\lambda (_: 
T).(let TMP_20 \def (Bind Abbr) in (eq K k TMP_20))) in (let TMP_22 \def 
(\lambda (t: T).(pr0 t3 t)) in (let TMP_24 \def (\lambda (t: T).(let TMP_23 
\def (clen c) in (subst0 TMP_23 u t t4))) in (let TMP_25 \def (ex3 T TMP_21 
TMP_22 TMP_24) in (let TMP_26 \def (pr2_free c t3 t4 H1) in (or_introl TMP_19 
TMP_25 TMP_26)))))))))))) in (let TMP_125 \def (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d (Bind 
Abbr) u0))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H3: (subst0 i u0 t4 t)).(\lambda (H4: (eq C c0 
(CTail k u c))).(let TMP_30 \def (\lambda (c1: C).(let TMP_28 \def (Bind 
Abbr) in (let TMP_29 \def (CHead d TMP_28 u0) in (getl i c1 TMP_29)))) in 
(let TMP_31 \def (CTail k u c) in (let H5 \def (eq_ind C c0 TMP_30 H1 TMP_31 
H4) in (let H_x \def (getl_gen_tail k Abbr u u0 d c i H5) in (let H6 \def H_x 
in (let TMP_33 \def (\lambda (e: C).(let TMP_32 \def (CTail k u e) in (eq C d 
TMP_32))) in (let TMP_36 \def (\lambda (e: C).(let TMP_34 \def (Bind Abbr) in 
(let TMP_35 \def (CHead e TMP_34 u0) in (getl i c TMP_35)))) in (let TMP_37 
\def (ex2 C TMP_33 TMP_36) in (let TMP_39 \def (\lambda (_: nat).(let TMP_38 
\def (clen c) in (eq nat i TMP_38))) in (let TMP_41 \def (\lambda (_: 
nat).(let TMP_40 \def (Bind Abbr) in (eq K k TMP_40))) in (let TMP_42 \def 
(\lambda (_: nat).(eq T u u0)) in (let TMP_44 \def (\lambda (n: nat).(let 
TMP_43 \def (CSort n) in (eq C d TMP_43))) in (let TMP_45 \def (ex4 nat 
TMP_39 TMP_41 TMP_42 TMP_44) in (let TMP_46 \def (pr2 c t3 t) in (let TMP_48 
\def (\lambda (_: T).(let TMP_47 \def (Bind Abbr) in (eq K k TMP_47))) in 
(let TMP_49 \def (\lambda (t0: T).(pr0 t3 t0)) in (let TMP_51 \def (\lambda 
(t0: T).(let TMP_50 \def (clen c) in (subst0 TMP_50 u t0 t))) in (let TMP_52 
\def (ex3 T TMP_48 TMP_49 TMP_51) in (let TMP_53 \def (or TMP_46 TMP_52) in 
(let TMP_76 \def (\lambda (H7: (ex2 C (\lambda (e: C).(eq C d (CTail k u e))) 
(\lambda (e: C).(getl i c (CHead e (Bind Abbr) u0))))).(let TMP_55 \def 
(\lambda (e: C).(let TMP_54 \def (CTail k u e) in (eq C d TMP_54))) in (let 
TMP_58 \def (\lambda (e: C).(let TMP_56 \def (Bind Abbr) in (let TMP_57 \def 
(CHead e TMP_56 u0) in (getl i c TMP_57)))) in (let TMP_59 \def (pr2 c t3 t) 
in (let TMP_61 \def (\lambda (_: T).(let TMP_60 \def (Bind Abbr) in (eq K k 
TMP_60))) in (let TMP_62 \def (\lambda (t0: T).(pr0 t3 t0)) in (let TMP_64 
\def (\lambda (t0: T).(let TMP_63 \def (clen c) in (subst0 TMP_63 u t0 t))) 
in (let TMP_65 \def (ex3 T TMP_61 TMP_62 TMP_64) in (let TMP_66 \def (or 
TMP_59 TMP_65) in (let TMP_75 \def (\lambda (x: C).(\lambda (_: (eq C d 
(CTail k u x))).(\lambda (H9: (getl i c (CHead x (Bind Abbr) u0))).(let 
TMP_67 \def (pr2 c t3 t) in (let TMP_69 \def (\lambda (_: T).(let TMP_68 \def 
(Bind Abbr) in (eq K k TMP_68))) in (let TMP_70 \def (\lambda (t0: T).(pr0 t3 
t0)) in (let TMP_72 \def (\lambda (t0: T).(let TMP_71 \def (clen c) in 
(subst0 TMP_71 u t0 t))) in (let TMP_73 \def (ex3 T TMP_69 TMP_70 TMP_72) in 
(let TMP_74 \def (pr2_delta c x u0 i H9 t3 t4 H2 t H3) in (or_introl TMP_67 
TMP_73 TMP_74)))))))))) in (ex2_ind C TMP_55 TMP_58 TMP_66 TMP_75 
H7))))))))))) in (let TMP_124 \def (\lambda (H7: (ex4 nat (\lambda (_: 
nat).(eq nat i (clen c))) (\lambda (_: nat).(eq K k (Bind Abbr))) (\lambda 
(_: nat).(eq T u u0)) (\lambda (n: nat).(eq C d (CSort n))))).(let TMP_78 
\def (\lambda (_: nat).(let TMP_77 \def (clen c) in (eq nat i TMP_77))) in 
(let TMP_80 \def (\lambda (_: nat).(let TMP_79 \def (Bind Abbr) in (eq K k 
TMP_79))) in (let TMP_81 \def (\lambda (_: nat).(eq T u u0)) in (let TMP_83 
\def (\lambda (n: nat).(let TMP_82 \def (CSort n) in (eq C d TMP_82))) in 
(let TMP_84 \def (pr2 c t3 t) in (let TMP_86 \def (\lambda (_: T).(let TMP_85 
\def (Bind Abbr) in (eq K k TMP_85))) in (let TMP_87 \def (\lambda (t0: 
T).(pr0 t3 t0)) in (let TMP_89 \def (\lambda (t0: T).(let TMP_88 \def (clen 
c) in (subst0 TMP_88 u t0 t))) in (let TMP_90 \def (ex3 T TMP_86 TMP_87 
TMP_89) in (let TMP_91 \def (or TMP_84 TMP_90) in (let TMP_123 \def (\lambda 
(x0: nat).(\lambda (H8: (eq nat i (clen c))).(\lambda (H9: (eq K k (Bind 
Abbr))).(\lambda (H10: (eq T u u0)).(\lambda (_: (eq C d (CSort x0))).(let 
TMP_92 \def (\lambda (n: nat).(subst0 n u0 t4 t)) in (let TMP_93 \def (clen 
c) in (let H12 \def (eq_ind nat i TMP_92 H3 TMP_93 H8) in (let TMP_95 \def 
(\lambda (t0: T).(let TMP_94 \def (clen c) in (subst0 TMP_94 t0 t4 t))) in 
(let H13 \def (eq_ind_r T u0 TMP_95 H12 u H10) in (let TMP_96 \def (Bind 
Abbr) in (let TMP_104 \def (\lambda (k0: K).(let TMP_97 \def (pr2 c t3 t) in 
(let TMP_99 \def (\lambda (_: T).(let TMP_98 \def (Bind Abbr) in (eq K k0 
TMP_98))) in (let TMP_100 \def (\lambda (t0: T).(pr0 t3 t0)) in (let TMP_102 
\def (\lambda (t0: T).(let TMP_101 \def (clen c) in (subst0 TMP_101 u t0 t))) 
in (let TMP_103 \def (ex3 T TMP_99 TMP_100 TMP_102) in (or TMP_97 
TMP_103))))))) in (let TMP_105 \def (pr2 c t3 t) in (let TMP_108 \def 
(\lambda (_: T).(let TMP_106 \def (Bind Abbr) in (let TMP_107 \def (Bind 
Abbr) in (eq K TMP_106 TMP_107)))) in (let TMP_109 \def (\lambda (t0: T).(pr0 
t3 t0)) in (let TMP_111 \def (\lambda (t0: T).(let TMP_110 \def (clen c) in 
(subst0 TMP_110 u t0 t))) in (let TMP_112 \def (ex3 T TMP_108 TMP_109 
TMP_111) in (let TMP_115 \def (\lambda (_: T).(let TMP_113 \def (Bind Abbr) 
in (let TMP_114 \def (Bind Abbr) in (eq K TMP_113 TMP_114)))) in (let TMP_116 
\def (\lambda (t0: T).(pr0 t3 t0)) in (let TMP_118 \def (\lambda (t0: T).(let 
TMP_117 \def (clen c) in (subst0 TMP_117 u t0 t))) in (let TMP_119 \def (Bind 
Abbr) in (let TMP_120 \def (refl_equal K TMP_119) in (let TMP_121 \def 
(ex3_intro T TMP_115 TMP_116 TMP_118 t4 TMP_120 H2 H13) in (let TMP_122 \def 
(or_intror TMP_105 TMP_112 TMP_121) in (eq_ind_r K TMP_96 TMP_104 TMP_122 k 
H9))))))))))))))))))))))))) in (ex4_ind nat TMP_78 TMP_80 TMP_81 TMP_83 
TMP_91 TMP_123 H7))))))))))))) in (or_ind TMP_37 TMP_45 TMP_53 TMP_76 TMP_124 
H6))))))))))))))))))))))))))))))))) in (pr2_ind TMP_18 TMP_27 TMP_125 y t1 t2 
H0)))))) in (insert_eq C TMP_1 TMP_2 TMP_10 TMP_126 H)))))))))).

theorem pr2_gen_cbind:
 \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CHead c (Bind b) v) t1 t2) \to (pr2 c (THead (Bind b) v t1) 
(THead (Bind b) v t2)))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CHead c (Bind b) v) t1 t2)).(let TMP_1 \def (Bind 
b) in (let TMP_2 \def (CHead c TMP_1 v) in (let TMP_3 \def (\lambda (c0: 
C).(pr2 c0 t1 t2)) in (let TMP_8 \def (\lambda (_: C).(let TMP_4 \def (Bind 
b) in (let TMP_5 \def (THead TMP_4 v t1) in (let TMP_6 \def (Bind b) in (let 
TMP_7 \def (THead TMP_6 v t2) in (pr2 c TMP_5 TMP_7)))))) in (let TMP_119 
\def (\lambda (y: C).(\lambda (H0: (pr2 y t1 t2)).(let TMP_13 \def (\lambda 
(c0: C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c (Bind b) v)) \to 
(let TMP_9 \def (Bind b) in (let TMP_10 \def (THead TMP_9 v t) in (let TMP_11 
\def (Bind b) in (let TMP_12 \def (THead TMP_11 v t0) in (pr2 c TMP_10 
TMP_12))))))))) in (let TMP_21 \def (\lambda (c0: C).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c 
(Bind b) v))).(let TMP_14 \def (Bind b) in (let TMP_15 \def (THead TMP_14 v 
t3) in (let TMP_16 \def (Bind b) in (let TMP_17 \def (THead TMP_16 v t4) in 
(let TMP_18 \def (pr0_refl v) in (let TMP_19 \def (Bind b) in (let TMP_20 
\def (pr0_comp v v TMP_18 t3 t4 H1 TMP_19) in (pr2_free c TMP_15 TMP_17 
TMP_20))))))))))))) in (let TMP_118 \def (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H3: (subst0 i u t4 t)).(\lambda (H4: (eq C c0 
(CHead c (Bind b) v))).(let TMP_24 \def (\lambda (c1: C).(let TMP_22 \def 
(Bind Abbr) in (let TMP_23 \def (CHead d TMP_22 u) in (getl i c1 TMP_23)))) 
in (let TMP_25 \def (Bind b) in (let TMP_26 \def (CHead c TMP_25 v) in (let 
H5 \def (eq_ind C c0 TMP_24 H1 TMP_26 H4) in (let TMP_27 \def (Bind Abbr) in 
(let TMP_28 \def (CHead d TMP_27 u) in (let H_x \def (getl_gen_bind b c 
TMP_28 v i H5) in (let H6 \def H_x in (let TMP_29 \def (eq nat i O) in (let 
TMP_30 \def (Bind Abbr) in (let TMP_31 \def (CHead d TMP_30 u) in (let TMP_32 
\def (Bind b) in (let TMP_33 \def (CHead c TMP_32 v) in (let TMP_34 \def (eq 
C TMP_31 TMP_33) in (let TMP_35 \def (land TMP_29 TMP_34) in (let TMP_37 \def 
(\lambda (j: nat).(let TMP_36 \def (S j) in (eq nat i TMP_36))) in (let 
TMP_40 \def (\lambda (j: nat).(let TMP_38 \def (Bind Abbr) in (let TMP_39 
\def (CHead d TMP_38 u) in (getl j c TMP_39)))) in (let TMP_41 \def (ex2 nat 
TMP_37 TMP_40) in (let TMP_42 \def (Bind b) in (let TMP_43 \def (THead TMP_42 
v t3) in (let TMP_44 \def (Bind b) in (let TMP_45 \def (THead TMP_44 v t) in 
(let TMP_46 \def (pr2 c TMP_43 TMP_45) in (let TMP_90 \def (\lambda (H7: 
(land (eq nat i O) (eq C (CHead d (Bind Abbr) u) (CHead c (Bind b) v)))).(let 
TMP_47 \def (eq nat i O) in (let TMP_48 \def (Bind Abbr) in (let TMP_49 \def 
(CHead d TMP_48 u) in (let TMP_50 \def (Bind b) in (let TMP_51 \def (CHead c 
TMP_50 v) in (let TMP_52 \def (eq C TMP_49 TMP_51) in (let TMP_53 \def (Bind 
b) in (let TMP_54 \def (THead TMP_53 v t3) in (let TMP_55 \def (Bind b) in 
(let TMP_56 \def (THead TMP_55 v t) in (let TMP_57 \def (pr2 c TMP_54 TMP_56) 
in (let TMP_89 \def (\lambda (H8: (eq nat i O)).(\lambda (H9: (eq C (CHead d 
(Bind Abbr) u) (CHead c (Bind b) v))).(let TMP_58 \def (\lambda (e: C).(match 
e with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) in (let 
TMP_59 \def (Bind Abbr) in (let TMP_60 \def (CHead d TMP_59 u) in (let TMP_61 
\def (Bind b) in (let TMP_62 \def (CHead c TMP_61 v) in (let H10 \def 
(f_equal C C TMP_58 TMP_60 TMP_62 H9) in (let TMP_63 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow 
(match k with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_64 \def (Bind Abbr) in (let TMP_65 \def (CHead d TMP_64 u) in (let 
TMP_66 \def (Bind b) in (let TMP_67 \def (CHead c TMP_66 v) in (let H11 \def 
(f_equal C B TMP_63 TMP_65 TMP_67 H9) in (let TMP_68 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) 
in (let TMP_69 \def (Bind Abbr) in (let TMP_70 \def (CHead d TMP_69 u) in 
(let TMP_71 \def (Bind b) in (let TMP_72 \def (CHead c TMP_71 v) in (let H12 
\def (f_equal C T TMP_68 TMP_70 TMP_72 H9) in (let TMP_87 \def (\lambda (H13: 
(eq B Abbr b)).(\lambda (_: (eq C d c)).(let TMP_73 \def (\lambda (n: 
nat).(subst0 n u t4 t)) in (let H15 \def (eq_ind nat i TMP_73 H3 O H8) in 
(let TMP_74 \def (\lambda (t0: T).(subst0 O t0 t4 t)) in (let H16 \def 
(eq_ind T u TMP_74 H15 v H12) in (let TMP_79 \def (\lambda (b0: B).(let 
TMP_75 \def (Bind b0) in (let TMP_76 \def (THead TMP_75 v t3) in (let TMP_77 
\def (Bind b0) in (let TMP_78 \def (THead TMP_77 v t) in (pr2 c TMP_76 
TMP_78)))))) in (let TMP_80 \def (Bind Abbr) in (let TMP_81 \def (THead 
TMP_80 v t3) in (let TMP_82 \def (Bind Abbr) in (let TMP_83 \def (THead 
TMP_82 v t) in (let TMP_84 \def (pr0_refl v) in (let TMP_85 \def (pr0_delta v 
v TMP_84 t3 t4 H2 t H16) in (let TMP_86 \def (pr2_free c TMP_81 TMP_83 
TMP_85) in (eq_ind B Abbr TMP_79 TMP_86 b H13))))))))))))))) in (let TMP_88 
\def (TMP_87 H11) in (TMP_88 H10))))))))))))))))))))))) in (land_ind TMP_47 
TMP_52 TMP_57 TMP_89 H7)))))))))))))) in (let TMP_117 \def (\lambda (H7: (ex2 
nat (\lambda (j: nat).(eq nat i (S j))) (\lambda (j: nat).(getl j c (CHead d 
(Bind Abbr) u))))).(let TMP_92 \def (\lambda (j: nat).(let TMP_91 \def (S j) 
in (eq nat i TMP_91))) in (let TMP_95 \def (\lambda (j: nat).(let TMP_93 \def 
(Bind Abbr) in (let TMP_94 \def (CHead d TMP_93 u) in (getl j c TMP_94)))) in 
(let TMP_96 \def (Bind b) in (let TMP_97 \def (THead TMP_96 v t3) in (let 
TMP_98 \def (Bind b) in (let TMP_99 \def (THead TMP_98 v t) in (let TMP_100 
\def (pr2 c TMP_97 TMP_99) in (let TMP_116 \def (\lambda (x: nat).(\lambda 
(H8: (eq nat i (S x))).(\lambda (H9: (getl x c (CHead d (Bind Abbr) u))).(let 
TMP_101 \def (\lambda (e: nat).e) in (let TMP_102 \def (S x) in (let H10 \def 
(f_equal nat nat TMP_101 i TMP_102 H8) in (let TMP_103 \def (\lambda (n: 
nat).(subst0 n u t4 t)) in (let TMP_104 \def (S x) in (let H11 \def (eq_ind 
nat i TMP_103 H3 TMP_104 H10) in (let TMP_105 \def (Bind b) in (let TMP_106 
\def (Bind b) in (let TMP_107 \def (CHead c TMP_106 v) in (let TMP_108 \def 
(S x) in (let TMP_109 \def (Bind b) in (let TMP_110 \def (CHead c TMP_109 v) 
in (let TMP_111 \def (clear_bind b c v) in (let TMP_112 \def (Bind Abbr) in 
(let TMP_113 \def (CHead d TMP_112 u) in (let TMP_114 \def (getl_clear_bind b 
TMP_110 c v TMP_111 TMP_113 x H9) in (let TMP_115 \def (pr2_delta TMP_107 d u 
TMP_108 TMP_114 t3 t4 H2 t H11) in (pr2_head_2 c v t3 t TMP_105 
TMP_115))))))))))))))))))))) in (ex2_ind nat TMP_92 TMP_95 TMP_100 TMP_116 
H7)))))))))) in (or_ind TMP_35 TMP_41 TMP_46 TMP_90 TMP_117 
H6))))))))))))))))))))))))))))))))))))) in (pr2_ind TMP_13 TMP_21 TMP_118 y 
t1 t2 H0)))))) in (insert_eq C TMP_2 TMP_3 TMP_8 TMP_119 H))))))))))).

theorem pr2_gen_cflat:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CHead c (Flat f) v) t1 t2) \to (pr2 c t1 t2))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CHead c (Flat f) v) t1 t2)).(let TMP_1 \def (Flat 
f) in (let TMP_2 \def (CHead c TMP_1 v) in (let TMP_3 \def (\lambda (c0: 
C).(pr2 c0 t1 t2)) in (let TMP_4 \def (\lambda (_: C).(pr2 c t1 t2)) in (let 
TMP_15 \def (\lambda (y: C).(\lambda (H0: (pr2 y t1 t2)).(let TMP_5 \def 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c (Flat f) 
v)) \to (pr2 c t t0))))) in (let TMP_6 \def (\lambda (c0: C).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c 
(Flat f) v))).(pr2_free c t3 t4 H1)))))) in (let TMP_14 \def (\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 
(CHead d (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: 
(pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: (subst0 i u t4 t)).(\lambda (H4: 
(eq C c0 (CHead c (Flat f) v))).(let TMP_9 \def (\lambda (c1: C).(let TMP_7 
\def (Bind Abbr) in (let TMP_8 \def (CHead d TMP_7 u) in (getl i c1 TMP_8)))) 
in (let TMP_10 \def (Flat f) in (let TMP_11 \def (CHead c TMP_10 v) in (let 
H5 \def (eq_ind C c0 TMP_9 H1 TMP_11 H4) in (let TMP_12 \def (Bind Abbr) in 
(let TMP_13 \def (CHead d TMP_12 u) in (let H_y \def (getl_gen_flat f c 
TMP_13 v i H5) in (pr2_delta c d u i H_y t3 t4 H2 t H3))))))))))))))))))) in 
(pr2_ind TMP_5 TMP_6 TMP_14 y t1 t2 H0)))))) in (insert_eq C TMP_2 TMP_3 
TMP_4 TMP_15 H))))))))))).

