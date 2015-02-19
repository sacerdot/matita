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

include "basic_1/sty1/props.ma".

include "basic_1/cnt/props.ma".

theorem sty1_cnt:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((sty0 g c 
t1 t) \to (ex2 T (\lambda (t2: T).(sty1 g c t1 t2)) (\lambda (t2: T).(cnt 
t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(sty0 g c t1 t)).(let TMP_3 \def (\lambda (c0: C).(\lambda (t0: T).(\lambda 
(_: T).(let TMP_1 \def (\lambda (t3: T).(sty1 g c0 t0 t3)) in (let TMP_2 \def 
(\lambda (t3: T).(cnt t3)) in (ex2 T TMP_1 TMP_2)))))) in (let TMP_16 \def 
(\lambda (c0: C).(\lambda (n: nat).(let TMP_5 \def (\lambda (t2: T).(let 
TMP_4 \def (TSort n) in (sty1 g c0 TMP_4 t2))) in (let TMP_6 \def (\lambda 
(t2: T).(cnt t2)) in (let TMP_7 \def (next g n) in (let TMP_8 \def (TSort 
TMP_7) in (let TMP_9 \def (TSort n) in (let TMP_10 \def (next g n) in (let 
TMP_11 \def (TSort TMP_10) in (let TMP_12 \def (sty0_sort g c0 n) in (let 
TMP_13 \def (sty1_sty0 g c0 TMP_9 TMP_11 TMP_12) in (let TMP_14 \def (next g 
n) in (let TMP_15 \def (cnt_sort TMP_14) in (ex_intro2 T TMP_5 TMP_6 TMP_8 
TMP_13 TMP_15)))))))))))))) in (let TMP_32 \def (\lambda (c0: C).(\lambda (d: 
C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v w)).(\lambda (H2: (ex2 T 
(\lambda (t2: T).(sty1 g d v t2)) (\lambda (t2: T).(cnt t2)))).(let H3 \def 
H2 in (let TMP_17 \def (\lambda (t2: T).(sty1 g d v t2)) in (let TMP_18 \def 
(\lambda (t2: T).(cnt t2)) in (let TMP_20 \def (\lambda (t2: T).(let TMP_19 
\def (TLRef i) in (sty1 g c0 TMP_19 t2))) in (let TMP_21 \def (\lambda (t2: 
T).(cnt t2)) in (let TMP_22 \def (ex2 T TMP_20 TMP_21) in (let TMP_31 \def 
(\lambda (x: T).(\lambda (H4: (sty1 g d v x)).(\lambda (H5: (cnt x)).(let 
TMP_24 \def (\lambda (t2: T).(let TMP_23 \def (TLRef i) in (sty1 g c0 TMP_23 
t2))) in (let TMP_25 \def (\lambda (t2: T).(cnt t2)) in (let TMP_26 \def (S 
i) in (let TMP_27 \def (lift TMP_26 O x) in (let TMP_28 \def (sty1_abbr g c0 
d v i H0 x H4) in (let TMP_29 \def (S i) in (let TMP_30 \def (cnt_lift x H5 
TMP_29 O) in (ex_intro2 T TMP_24 TMP_25 TMP_27 TMP_28 TMP_30))))))))))) in 
(ex2_ind T TMP_17 TMP_18 TMP_22 TMP_31 H3)))))))))))))))) in (let TMP_61 \def 
(\lambda (c0: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c0 (CHead d (Bind Abst) v))).(\lambda (w: T).(\lambda (H1: (sty0 
g d v w)).(\lambda (H2: (ex2 T (\lambda (t2: T).(sty1 g d v t2)) (\lambda 
(t2: T).(cnt t2)))).(let H3 \def H2 in (let TMP_33 \def (\lambda (t2: 
T).(sty1 g d v t2)) in (let TMP_34 \def (\lambda (t2: T).(cnt t2)) in (let 
TMP_36 \def (\lambda (t2: T).(let TMP_35 \def (TLRef i) in (sty1 g c0 TMP_35 
t2))) in (let TMP_37 \def (\lambda (t2: T).(cnt t2)) in (let TMP_38 \def (ex2 
T TMP_36 TMP_37) in (let TMP_60 \def (\lambda (x: T).(\lambda (H4: (sty1 g d 
v x)).(\lambda (H5: (cnt x)).(let TMP_40 \def (\lambda (t2: T).(let TMP_39 
\def (TLRef i) in (sty1 g c0 TMP_39 t2))) in (let TMP_41 \def (\lambda (t2: 
T).(cnt t2)) in (let TMP_42 \def (S i) in (let TMP_43 \def (lift TMP_42 O x) 
in (let TMP_44 \def (TLRef i) in (let TMP_45 \def (S i) in (let TMP_46 \def 
(lift TMP_45 O v) in (let TMP_47 \def (TLRef i) in (let TMP_48 \def (S i) in 
(let TMP_49 \def (lift TMP_48 O v) in (let TMP_50 \def (sty0_abst g c0 d v i 
H0 w H1) in (let TMP_51 \def (sty1_sty0 g c0 TMP_47 TMP_49 TMP_50) in (let 
TMP_52 \def (S i) in (let TMP_53 \def (lift TMP_52 O x) in (let TMP_54 \def 
(S i) in (let TMP_55 \def (getl_drop Abst c0 d v i H0) in (let TMP_56 \def 
(sty1_lift g d v x H4 c0 TMP_54 O TMP_55) in (let TMP_57 \def (sty1_trans g 
c0 TMP_44 TMP_46 TMP_51 TMP_53 TMP_56) in (let TMP_58 \def (S i) in (let 
TMP_59 \def (cnt_lift x H5 TMP_58 O) in (ex_intro2 T TMP_40 TMP_41 TMP_43 
TMP_57 TMP_59)))))))))))))))))))))))) in (ex2_ind T TMP_33 TMP_34 TMP_38 
TMP_60 H3)))))))))))))))) in (let TMP_81 \def (\lambda (b: B).(\lambda (c0: 
C).(\lambda (v: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g 
(CHead c0 (Bind b) v) t2 t3)).(\lambda (H1: (ex2 T (\lambda (t4: T).(sty1 g 
(CHead c0 (Bind b) v) t2 t4)) (\lambda (t4: T).(cnt t4)))).(let H2 \def H1 in 
(let TMP_64 \def (\lambda (t4: T).(let TMP_62 \def (Bind b) in (let TMP_63 
\def (CHead c0 TMP_62 v) in (sty1 g TMP_63 t2 t4)))) in (let TMP_65 \def 
(\lambda (t4: T).(cnt t4)) in (let TMP_68 \def (\lambda (t4: T).(let TMP_66 
\def (Bind b) in (let TMP_67 \def (THead TMP_66 v t2) in (sty1 g c0 TMP_67 
t4)))) in (let TMP_69 \def (\lambda (t4: T).(cnt t4)) in (let TMP_70 \def 
(ex2 T TMP_68 TMP_69) in (let TMP_80 \def (\lambda (x: T).(\lambda (H3: (sty1 
g (CHead c0 (Bind b) v) t2 x)).(\lambda (H4: (cnt x)).(let TMP_73 \def 
(\lambda (t4: T).(let TMP_71 \def (Bind b) in (let TMP_72 \def (THead TMP_71 
v t2) in (sty1 g c0 TMP_72 t4)))) in (let TMP_74 \def (\lambda (t4: T).(cnt 
t4)) in (let TMP_75 \def (Bind b) in (let TMP_76 \def (THead TMP_75 v x) in 
(let TMP_77 \def (sty1_bind g b c0 v t2 x H3) in (let TMP_78 \def (Bind b) in 
(let TMP_79 \def (cnt_head x H4 TMP_78 v) in (ex_intro2 T TMP_73 TMP_74 
TMP_76 TMP_77 TMP_79))))))))))) in (ex2_ind T TMP_64 TMP_65 TMP_70 TMP_80 
H2))))))))))))))) in (let TMP_99 \def (\lambda (c0: C).(\lambda (v: 
T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g c0 t2 t3)).(\lambda 
(H1: (ex2 T (\lambda (t4: T).(sty1 g c0 t2 t4)) (\lambda (t4: T).(cnt 
t4)))).(let H2 \def H1 in (let TMP_82 \def (\lambda (t4: T).(sty1 g c0 t2 
t4)) in (let TMP_83 \def (\lambda (t4: T).(cnt t4)) in (let TMP_86 \def 
(\lambda (t4: T).(let TMP_84 \def (Flat Appl) in (let TMP_85 \def (THead 
TMP_84 v t2) in (sty1 g c0 TMP_85 t4)))) in (let TMP_87 \def (\lambda (t4: 
T).(cnt t4)) in (let TMP_88 \def (ex2 T TMP_86 TMP_87) in (let TMP_98 \def 
(\lambda (x: T).(\lambda (H3: (sty1 g c0 t2 x)).(\lambda (H4: (cnt x)).(let 
TMP_91 \def (\lambda (t4: T).(let TMP_89 \def (Flat Appl) in (let TMP_90 \def 
(THead TMP_89 v t2) in (sty1 g c0 TMP_90 t4)))) in (let TMP_92 \def (\lambda 
(t4: T).(cnt t4)) in (let TMP_93 \def (Flat Appl) in (let TMP_94 \def (THead 
TMP_93 v x) in (let TMP_95 \def (sty1_appl g c0 v t2 x H3) in (let TMP_96 
\def (Flat Appl) in (let TMP_97 \def (cnt_head x H4 TMP_96 v) in (ex_intro2 T 
TMP_91 TMP_92 TMP_94 TMP_95 TMP_97))))))))))) in (ex2_ind T TMP_82 TMP_83 
TMP_88 TMP_98 H2)))))))))))))) in (let TMP_128 \def (\lambda (c0: C).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (H0: (sty0 g c0 v1 v2)).(\lambda (_: (ex2 T 
(\lambda (t2: T).(sty1 g c0 v1 t2)) (\lambda (t2: T).(cnt t2)))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g c0 t2 t3)).(\lambda (H3: (ex2 T 
(\lambda (t4: T).(sty1 g c0 t2 t4)) (\lambda (t4: T).(cnt t4)))).(let H4 \def 
H3 in (let TMP_100 \def (\lambda (t4: T).(sty1 g c0 t2 t4)) in (let TMP_101 
\def (\lambda (t4: T).(cnt t4)) in (let TMP_104 \def (\lambda (t4: T).(let 
TMP_102 \def (Flat Cast) in (let TMP_103 \def (THead TMP_102 v1 t2) in (sty1 
g c0 TMP_103 t4)))) in (let TMP_105 \def (\lambda (t4: T).(cnt t4)) in (let 
TMP_106 \def (ex2 T TMP_104 TMP_105) in (let TMP_127 \def (\lambda (x: 
T).(\lambda (H5: (sty1 g c0 t2 x)).(\lambda (H6: (cnt x)).(let H_x \def 
(sty1_cast2 g c0 t2 x H5 v1 v2 H0) in (let H7 \def H_x in (let TMP_107 \def 
(\lambda (v3: T).(sty1 g c0 v1 v3)) in (let TMP_112 \def (\lambda (v3: 
T).(let TMP_108 \def (Flat Cast) in (let TMP_109 \def (THead TMP_108 v1 t2) 
in (let TMP_110 \def (Flat Cast) in (let TMP_111 \def (THead TMP_110 v3 x) in 
(sty1 g c0 TMP_109 TMP_111)))))) in (let TMP_115 \def (\lambda (t4: T).(let 
TMP_113 \def (Flat Cast) in (let TMP_114 \def (THead TMP_113 v1 t2) in (sty1 
g c0 TMP_114 t4)))) in (let TMP_116 \def (\lambda (t4: T).(cnt t4)) in (let 
TMP_117 \def (ex2 T TMP_115 TMP_116) in (let TMP_126 \def (\lambda (x0: 
T).(\lambda (_: (sty1 g c0 v1 x0)).(\lambda (H9: (sty1 g c0 (THead (Flat 
Cast) v1 t2) (THead (Flat Cast) x0 x))).(let TMP_120 \def (\lambda (t4: 
T).(let TMP_118 \def (Flat Cast) in (let TMP_119 \def (THead TMP_118 v1 t2) 
in (sty1 g c0 TMP_119 t4)))) in (let TMP_121 \def (\lambda (t4: T).(cnt t4)) 
in (let TMP_122 \def (Flat Cast) in (let TMP_123 \def (THead TMP_122 x0 x) in 
(let TMP_124 \def (Flat Cast) in (let TMP_125 \def (cnt_head x H6 TMP_124 x0) 
in (ex_intro2 T TMP_120 TMP_121 TMP_123 H9 TMP_125)))))))))) in (ex2_ind T 
TMP_107 TMP_112 TMP_117 TMP_126 H7)))))))))))) in (ex2_ind T TMP_100 TMP_101 
TMP_106 TMP_127 H4))))))))))))))))) in (sty0_ind g TMP_3 TMP_16 TMP_32 TMP_61 
TMP_81 TMP_99 TMP_128 c t1 t H)))))))))))).

