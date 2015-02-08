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

include "basic_1/getl/props.ma".

theorem getl_dec:
 \forall (c: C).(\forall (i: nat).(or (ex_3 C B T (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(getl i c (CHead e (Bind b) v)))))) (\forall (d: 
C).((getl i c d) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(let TMP_6 \def (\lambda (c0: C).(\forall (i: nat).(let TMP_3 
\def (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(let TMP_1 \def (Bind b) 
in (let TMP_2 \def (CHead e TMP_1 v) in (getl i c0 TMP_2)))))) in (let TMP_4 
\def (ex_3 C B T TMP_3) in (let TMP_5 \def (\forall (d: C).((getl i c0 d) \to 
(\forall (P: Prop).P))) in (or TMP_4 TMP_5)))))) in (let TMP_14 \def (\lambda 
(n: nat).(\lambda (i: nat).(let TMP_10 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_7 \def (CSort n) in (let TMP_8 \def (Bind b) in 
(let TMP_9 \def (CHead e TMP_8 v) in (getl i TMP_7 TMP_9))))))) in (let 
TMP_11 \def (ex_3 C B T TMP_10) in (let TMP_12 \def (\forall (d: C).((getl i 
(CSort n) d) \to (\forall (P: Prop).P))) in (let TMP_13 \def (\lambda (d: 
C).(\lambda (H: (getl i (CSort n) d)).(\lambda (P: Prop).(getl_gen_sort n i d 
H P)))) in (or_intror TMP_11 TMP_12 TMP_13))))))) in (let TMP_159 \def 
(\lambda (c0: C).(\lambda (H: ((\forall (i: nat).(or (ex_3 C B T (\lambda (e: 
C).(\lambda (b: B).(\lambda (v: T).(getl i c0 (CHead e (Bind b) v)))))) 
(\forall (d: C).((getl i c0 d) \to (\forall (P: Prop).P))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (i: nat).(let TMP_21 \def (\lambda (n: nat).(let 
TMP_18 \def (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(let TMP_15 \def 
(CHead c0 k t) in (let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead e 
TMP_16 v) in (getl n TMP_15 TMP_17))))))) in (let TMP_19 \def (ex_3 C B T 
TMP_18) in (let TMP_20 \def (\forall (d: C).((getl n (CHead c0 k t) d) \to 
(\forall (P: Prop).P))) in (or TMP_19 TMP_20))))) in (let TMP_28 \def 
(\lambda (k0: K).(let TMP_25 \def (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(let TMP_22 \def (CHead c0 k0 t) in (let TMP_23 \def (Bind b) in (let 
TMP_24 \def (CHead e TMP_23 v) in (getl O TMP_22 TMP_24))))))) in (let TMP_26 
\def (ex_3 C B T TMP_25) in (let TMP_27 \def (\forall (d: C).((getl O (CHead 
c0 k0 t) d) \to (\forall (P: Prop).P))) in (or TMP_26 TMP_27))))) in (let 
TMP_43 \def (\lambda (b: B).(let TMP_33 \def (\lambda (e: C).(\lambda (b0: 
B).(\lambda (v: T).(let TMP_29 \def (Bind b) in (let TMP_30 \def (CHead c0 
TMP_29 t) in (let TMP_31 \def (Bind b0) in (let TMP_32 \def (CHead e TMP_31 
v) in (getl O TMP_30 TMP_32)))))))) in (let TMP_34 \def (ex_3 C B T TMP_33) 
in (let TMP_35 \def (\forall (d: C).((getl O (CHead c0 (Bind b) t) d) \to 
(\forall (P: Prop).P))) in (let TMP_40 \def (\lambda (e: C).(\lambda (b0: 
B).(\lambda (v: T).(let TMP_36 \def (Bind b) in (let TMP_37 \def (CHead c0 
TMP_36 t) in (let TMP_38 \def (Bind b0) in (let TMP_39 \def (CHead e TMP_38 
v) in (getl O TMP_37 TMP_39)))))))) in (let TMP_41 \def (getl_refl b c0 t) in 
(let TMP_42 \def (ex_3_intro C B T TMP_40 c0 b t TMP_41) in (or_introl TMP_34 
TMP_35 TMP_42)))))))) in (let TMP_101 \def (\lambda (f: F).(let H_x \def (H 
O) in (let H0 \def H_x in (let TMP_46 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_44 \def (Bind b) in (let TMP_45 \def (CHead e 
TMP_44 v) in (getl O c0 TMP_45)))))) in (let TMP_47 \def (ex_3 C B T TMP_46) 
in (let TMP_48 \def (\forall (d: C).((getl O c0 d) \to (\forall (P: 
Prop).P))) in (let TMP_53 \def (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(let TMP_49 \def (Flat f) in (let TMP_50 \def (CHead c0 TMP_49 t) in (let 
TMP_51 \def (Bind b) in (let TMP_52 \def (CHead e TMP_51 v) in (getl O TMP_50 
TMP_52)))))))) in (let TMP_54 \def (ex_3 C B T TMP_53) in (let TMP_55 \def 
(\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to (\forall (P: Prop).P))) 
in (let TMP_56 \def (or TMP_54 TMP_55) in (let TMP_85 \def (\lambda (H1: 
(ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(getl O c0 (CHead 
e (Bind b) v))))))).(let TMP_59 \def (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(let TMP_57 \def (Bind b) in (let TMP_58 \def (CHead e TMP_57 v) in 
(getl O c0 TMP_58)))))) in (let TMP_64 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_60 \def (Flat f) in (let TMP_61 \def (CHead c0 
TMP_60 t) in (let TMP_62 \def (Bind b) in (let TMP_63 \def (CHead e TMP_62 v) 
in (getl O TMP_61 TMP_63)))))))) in (let TMP_65 \def (ex_3 C B T TMP_64) in 
(let TMP_66 \def (\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to 
(\forall (P: Prop).P))) in (let TMP_67 \def (or TMP_65 TMP_66) in (let TMP_84 
\def (\lambda (x0: C).(\lambda (x1: B).(\lambda (x2: T).(\lambda (H2: (getl O 
c0 (CHead x0 (Bind x1) x2))).(let TMP_72 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_68 \def (Flat f) in (let TMP_69 \def (CHead c0 
TMP_68 t) in (let TMP_70 \def (Bind b) in (let TMP_71 \def (CHead e TMP_70 v) 
in (getl O TMP_69 TMP_71)))))))) in (let TMP_73 \def (ex_3 C B T TMP_72) in 
(let TMP_74 \def (\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to 
(\forall (P: Prop).P))) in (let TMP_79 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_75 \def (Flat f) in (let TMP_76 \def (CHead c0 
TMP_75 t) in (let TMP_77 \def (Bind b) in (let TMP_78 \def (CHead e TMP_77 v) 
in (getl O TMP_76 TMP_78)))))))) in (let TMP_80 \def (Bind x1) in (let TMP_81 
\def (CHead x0 TMP_80 x2) in (let TMP_82 \def (getl_flat c0 TMP_81 O H2 f t) 
in (let TMP_83 \def (ex_3_intro C B T TMP_79 x0 x1 x2 TMP_82) in (or_introl 
TMP_73 TMP_74 TMP_83))))))))))))) in (ex_3_ind C B T TMP_59 TMP_67 TMP_84 
H1)))))))) in (let TMP_100 \def (\lambda (H1: ((\forall (d: C).((getl O c0 d) 
\to (\forall (P: Prop).P))))).(let TMP_90 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_86 \def (Flat f) in (let TMP_87 \def (CHead c0 
TMP_86 t) in (let TMP_88 \def (Bind b) in (let TMP_89 \def (CHead e TMP_88 v) 
in (getl O TMP_87 TMP_89)))))))) in (let TMP_91 \def (ex_3 C B T TMP_90) in 
(let TMP_92 \def (\forall (d: C).((getl O (CHead c0 (Flat f) t) d) \to 
(\forall (P: Prop).P))) in (let TMP_99 \def (\lambda (d: C).(\lambda (H2: 
(getl O (CHead c0 (Flat f) t) d)).(\lambda (P: Prop).(let TMP_93 \def 
(drop_refl c0) in (let TMP_94 \def (Flat f) in (let TMP_95 \def (CHead c0 
TMP_94 t) in (let TMP_96 \def (getl_gen_O TMP_95 d H2) in (let TMP_97 \def 
(clear_gen_flat f c0 d t TMP_96) in (let TMP_98 \def (getl_intro O c0 d c0 
TMP_93 TMP_97) in (H1 d TMP_98 P)))))))))) in (or_intror TMP_91 TMP_92 
TMP_99)))))) in (or_ind TMP_47 TMP_48 TMP_56 TMP_85 TMP_100 H0))))))))))))) 
in (let TMP_102 \def (K_ind TMP_28 TMP_43 TMP_101 k) in (let TMP_158 \def 
(\lambda (n: nat).(\lambda (_: (or (ex_3 C B T (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(getl n (CHead c0 k t) (CHead e (Bind b) v)))))) (\forall 
(d: C).((getl n (CHead c0 k t) d) \to (\forall (P: Prop).P))))).(let TMP_103 
\def (r k n) in (let H_x \def (H TMP_103) in (let H1 \def H_x in (let TMP_107 
\def (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(let TMP_104 \def (r k 
n) in (let TMP_105 \def (Bind b) in (let TMP_106 \def (CHead e TMP_105 v) in 
(getl TMP_104 c0 TMP_106))))))) in (let TMP_108 \def (ex_3 C B T TMP_107) in 
(let TMP_109 \def (\forall (d: C).((getl (r k n) c0 d) \to (\forall (P: 
Prop).P))) in (let TMP_114 \def (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(let TMP_110 \def (S n) in (let TMP_111 \def (CHead c0 k t) in (let 
TMP_112 \def (Bind b) in (let TMP_113 \def (CHead e TMP_112 v) in (getl 
TMP_110 TMP_111 TMP_113)))))))) in (let TMP_115 \def (ex_3 C B T TMP_114) in 
(let TMP_116 \def (\forall (d: C).((getl (S n) (CHead c0 k t) d) \to (\forall 
(P: Prop).P))) in (let TMP_117 \def (or TMP_115 TMP_116) in (let TMP_147 \def 
(\lambda (H2: (ex_3 C B T (\lambda (e: C).(\lambda (b: B).(\lambda (v: 
T).(getl (r k n) c0 (CHead e (Bind b) v))))))).(let TMP_121 \def (\lambda (e: 
C).(\lambda (b: B).(\lambda (v: T).(let TMP_118 \def (r k n) in (let TMP_119 
\def (Bind b) in (let TMP_120 \def (CHead e TMP_119 v) in (getl TMP_118 c0 
TMP_120))))))) in (let TMP_126 \def (\lambda (e: C).(\lambda (b: B).(\lambda 
(v: T).(let TMP_122 \def (S n) in (let TMP_123 \def (CHead c0 k t) in (let 
TMP_124 \def (Bind b) in (let TMP_125 \def (CHead e TMP_124 v) in (getl 
TMP_122 TMP_123 TMP_125)))))))) in (let TMP_127 \def (ex_3 C B T TMP_126) in 
(let TMP_128 \def (\forall (d: C).((getl (S n) (CHead c0 k t) d) \to (\forall 
(P: Prop).P))) in (let TMP_129 \def (or TMP_127 TMP_128) in (let TMP_146 \def 
(\lambda (x0: C).(\lambda (x1: B).(\lambda (x2: T).(\lambda (H3: (getl (r k 
n) c0 (CHead x0 (Bind x1) x2))).(let TMP_134 \def (\lambda (e: C).(\lambda 
(b: B).(\lambda (v: T).(let TMP_130 \def (S n) in (let TMP_131 \def (CHead c0 
k t) in (let TMP_132 \def (Bind b) in (let TMP_133 \def (CHead e TMP_132 v) 
in (getl TMP_130 TMP_131 TMP_133)))))))) in (let TMP_135 \def (ex_3 C B T 
TMP_134) in (let TMP_136 \def (\forall (d: C).((getl (S n) (CHead c0 k t) d) 
\to (\forall (P: Prop).P))) in (let TMP_141 \def (\lambda (e: C).(\lambda (b: 
B).(\lambda (v: T).(let TMP_137 \def (S n) in (let TMP_138 \def (CHead c0 k 
t) in (let TMP_139 \def (Bind b) in (let TMP_140 \def (CHead e TMP_139 v) in 
(getl TMP_137 TMP_138 TMP_140)))))))) in (let TMP_142 \def (Bind x1) in (let 
TMP_143 \def (CHead x0 TMP_142 x2) in (let TMP_144 \def (getl_head k n c0 
TMP_143 H3 t) in (let TMP_145 \def (ex_3_intro C B T TMP_141 x0 x1 x2 
TMP_144) in (or_introl TMP_135 TMP_136 TMP_145))))))))))))) in (ex_3_ind C B 
T TMP_121 TMP_129 TMP_146 H2)))))))) in (let TMP_157 \def (\lambda (H2: 
((\forall (d: C).((getl (r k n) c0 d) \to (\forall (P: Prop).P))))).(let 
TMP_152 \def (\lambda (e: C).(\lambda (b: B).(\lambda (v: T).(let TMP_148 
\def (S n) in (let TMP_149 \def (CHead c0 k t) in (let TMP_150 \def (Bind b) 
in (let TMP_151 \def (CHead e TMP_150 v) in (getl TMP_148 TMP_149 
TMP_151)))))))) in (let TMP_153 \def (ex_3 C B T TMP_152) in (let TMP_154 
\def (\forall (d: C).((getl (S n) (CHead c0 k t) d) \to (\forall (P: 
Prop).P))) in (let TMP_156 \def (\lambda (d: C).(\lambda (H3: (getl (S n) 
(CHead c0 k t) d)).(\lambda (P: Prop).(let TMP_155 \def (getl_gen_S k c0 d t 
n H3) in (H2 d TMP_155 P))))) in (or_intror TMP_153 TMP_154 TMP_156)))))) in 
(or_ind TMP_108 TMP_109 TMP_117 TMP_147 TMP_157 H1))))))))))))))) in (nat_ind 
TMP_21 TMP_102 TMP_158 i)))))))))))) in (C_ind TMP_6 TMP_14 TMP_159 c)))).

