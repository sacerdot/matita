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

include "basic_1/lift/props.ma".

include "basic_1/drop1/defs.ma".

theorem lift1_lift1:
 \forall (is1: PList).(\forall (is2: PList).(\forall (t: T).(eq T (lift1 is1 
(lift1 is2 t)) (lift1 (papp is1 is2) t))))
\def
 \lambda (is1: PList).(let TMP_5 \def (\lambda (p: PList).(\forall (is2: 
PList).(\forall (t: T).(let TMP_1 \def (lift1 is2 t) in (let TMP_2 \def 
(lift1 p TMP_1) in (let TMP_3 \def (papp p is2) in (let TMP_4 \def (lift1 
TMP_3 t) in (eq T TMP_2 TMP_4)))))))) in (let TMP_7 \def (\lambda (is2: 
PList).(\lambda (t: T).(let TMP_6 \def (lift1 is2 t) in (refl_equal T 
TMP_6)))) in (let TMP_15 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(p: PList).(\lambda (H: ((\forall (is2: PList).(\forall (t: T).(eq T (lift1 p 
(lift1 is2 t)) (lift1 (papp p is2) t)))))).(\lambda (is2: PList).(\lambda (t: 
T).(let TMP_8 \def (lift1 is2 t) in (let TMP_9 \def (lift1 p TMP_8) in (let 
TMP_10 \def (papp p is2) in (let TMP_11 \def (lift1 TMP_10 t) in (let TMP_12 
\def (refl_equal nat n) in (let TMP_13 \def (refl_equal nat n0) in (let 
TMP_14 \def (H is2 t) in (f_equal3 nat nat T T lift n n n0 n0 TMP_9 TMP_11 
TMP_12 TMP_13 TMP_14)))))))))))))) in (PList_ind TMP_5 TMP_7 TMP_15 is1)))).

theorem lift1_xhg:
 \forall (hds: PList).(\forall (t: T).(eq T (lift1 (Ss hds) (lift (S O) O t)) 
(lift (S O) O (lift1 hds t))))
\def
 \lambda (hds: PList).(let TMP_8 \def (\lambda (p: PList).(\forall (t: 
T).(let TMP_1 \def (Ss p) in (let TMP_2 \def (S O) in (let TMP_3 \def (lift 
TMP_2 O t) in (let TMP_4 \def (lift1 TMP_1 TMP_3) in (let TMP_5 \def (S O) in 
(let TMP_6 \def (lift1 p t) in (let TMP_7 \def (lift TMP_5 O TMP_6) in (eq T 
TMP_4 TMP_7)))))))))) in (let TMP_11 \def (\lambda (t: T).(let TMP_9 \def (S 
O) in (let TMP_10 \def (lift TMP_9 O t) in (refl_equal T TMP_10)))) in (let 
TMP_67 \def (\lambda (h: nat).(\lambda (d: nat).(\lambda (p: PList).(\lambda 
(H: ((\forall (t: T).(eq T (lift1 (Ss p) (lift (S O) O t)) (lift (S O) O 
(lift1 p t)))))).(\lambda (t: T).(let TMP_12 \def (S O) in (let TMP_13 \def 
(lift1 p t) in (let TMP_14 \def (lift TMP_12 O TMP_13) in (let TMP_21 \def 
(\lambda (t0: T).(let TMP_15 \def (S d) in (let TMP_16 \def (lift h TMP_15 
t0) in (let TMP_17 \def (S O) in (let TMP_18 \def (lift1 p t) in (let TMP_19 
\def (lift h d TMP_18) in (let TMP_20 \def (lift TMP_17 O TMP_19) in (eq T 
TMP_16 TMP_20)))))))) in (let TMP_22 \def (S O) in (let TMP_23 \def (plus 
TMP_22 d) in (let TMP_32 \def (\lambda (n: nat).(let TMP_24 \def (S O) in 
(let TMP_25 \def (lift1 p t) in (let TMP_26 \def (lift TMP_24 O TMP_25) in 
(let TMP_27 \def (lift h n TMP_26) in (let TMP_28 \def (S O) in (let TMP_29 
\def (lift1 p t) in (let TMP_30 \def (lift h d TMP_29) in (let TMP_31 \def 
(lift TMP_28 O TMP_30) in (eq T TMP_27 TMP_31)))))))))) in (let TMP_33 \def 
(S O) in (let TMP_34 \def (lift1 p t) in (let TMP_35 \def (lift h d TMP_34) 
in (let TMP_36 \def (lift TMP_33 O TMP_35) in (let TMP_41 \def (\lambda (t0: 
T).(let TMP_37 \def (S O) in (let TMP_38 \def (lift1 p t) in (let TMP_39 \def 
(lift h d TMP_38) in (let TMP_40 \def (lift TMP_37 O TMP_39) in (eq T t0 
TMP_40)))))) in (let TMP_42 \def (S O) in (let TMP_43 \def (lift1 p t) in 
(let TMP_44 \def (lift h d TMP_43) in (let TMP_45 \def (lift TMP_42 O TMP_44) 
in (let TMP_46 \def (refl_equal T TMP_45) in (let TMP_47 \def (S O) in (let 
TMP_48 \def (plus TMP_47 d) in (let TMP_49 \def (S O) in (let TMP_50 \def 
(lift1 p t) in (let TMP_51 \def (lift TMP_49 O TMP_50) in (let TMP_52 \def 
(lift h TMP_48 TMP_51) in (let TMP_53 \def (lift1 p t) in (let TMP_54 \def (S 
O) in (let TMP_55 \def (le_O_n d) in (let TMP_56 \def (lift_d TMP_53 h TMP_54 
d O TMP_55) in (let TMP_57 \def (eq_ind_r T TMP_36 TMP_41 TMP_46 TMP_52 
TMP_56) in (let TMP_58 \def (S d) in (let TMP_59 \def (S d) in (let TMP_60 
\def (refl_equal nat TMP_59) in (let TMP_61 \def (eq_ind nat TMP_23 TMP_32 
TMP_57 TMP_58 TMP_60) in (let TMP_62 \def (Ss p) in (let TMP_63 \def (S O) in 
(let TMP_64 \def (lift TMP_63 O t) in (let TMP_65 \def (lift1 TMP_62 TMP_64) 
in (let TMP_66 \def (H t) in (eq_ind_r T TMP_14 TMP_21 TMP_61 TMP_65 
TMP_66))))))))))))))))))))))))))))))))))))))))))) in (PList_ind TMP_8 TMP_11 
TMP_67 hds)))).

theorem lifts1_xhg:
 \forall (hds: PList).(\forall (ts: TList).(eq TList (lifts1 (Ss hds) (lifts 
(S O) O ts)) (lifts (S O) O (lifts1 hds ts))))
\def
 \lambda (hds: PList).(\lambda (ts: TList).(let TMP_8 \def (\lambda (t: 
TList).(let TMP_1 \def (Ss hds) in (let TMP_2 \def (S O) in (let TMP_3 \def 
(lifts TMP_2 O t) in (let TMP_4 \def (lifts1 TMP_1 TMP_3) in (let TMP_5 \def 
(S O) in (let TMP_6 \def (lifts1 hds t) in (let TMP_7 \def (lifts TMP_5 O 
TMP_6) in (eq TList TMP_4 TMP_7))))))))) in (let TMP_9 \def (refl_equal TList 
TNil) in (let TMP_59 \def (\lambda (t: T).(\lambda (t0: TList).(\lambda (H: 
(eq TList (lifts1 (Ss hds) (lifts (S O) O t0)) (lifts (S O) O (lifts1 hds 
t0)))).(let TMP_10 \def (S O) in (let TMP_11 \def (lift1 hds t) in (let 
TMP_12 \def (lift TMP_10 O TMP_11) in (let TMP_25 \def (\lambda (t1: T).(let 
TMP_13 \def (Ss hds) in (let TMP_14 \def (S O) in (let TMP_15 \def (lifts 
TMP_14 O t0) in (let TMP_16 \def (lifts1 TMP_13 TMP_15) in (let TMP_17 \def 
(TCons t1 TMP_16) in (let TMP_18 \def (S O) in (let TMP_19 \def (lift1 hds t) 
in (let TMP_20 \def (lift TMP_18 O TMP_19) in (let TMP_21 \def (S O) in (let 
TMP_22 \def (lifts1 hds t0) in (let TMP_23 \def (lifts TMP_21 O TMP_22) in 
(let TMP_24 \def (TCons TMP_20 TMP_23) in (eq TList TMP_17 
TMP_24)))))))))))))) in (let TMP_26 \def (S O) in (let TMP_27 \def (lifts1 
hds t0) in (let TMP_28 \def (lifts TMP_26 O TMP_27) in (let TMP_40 \def 
(\lambda (t1: TList).(let TMP_29 \def (S O) in (let TMP_30 \def (lift1 hds t) 
in (let TMP_31 \def (lift TMP_29 O TMP_30) in (let TMP_32 \def (TCons TMP_31 
t1) in (let TMP_33 \def (S O) in (let TMP_34 \def (lift1 hds t) in (let 
TMP_35 \def (lift TMP_33 O TMP_34) in (let TMP_36 \def (S O) in (let TMP_37 
\def (lifts1 hds t0) in (let TMP_38 \def (lifts TMP_36 O TMP_37) in (let 
TMP_39 \def (TCons TMP_35 TMP_38) in (eq TList TMP_32 TMP_39))))))))))))) in 
(let TMP_41 \def (S O) in (let TMP_42 \def (lift1 hds t) in (let TMP_43 \def 
(lift TMP_41 O TMP_42) in (let TMP_44 \def (S O) in (let TMP_45 \def (lifts1 
hds t0) in (let TMP_46 \def (lifts TMP_44 O TMP_45) in (let TMP_47 \def 
(TCons TMP_43 TMP_46) in (let TMP_48 \def (refl_equal TList TMP_47) in (let 
TMP_49 \def (Ss hds) in (let TMP_50 \def (S O) in (let TMP_51 \def (lifts 
TMP_50 O t0) in (let TMP_52 \def (lifts1 TMP_49 TMP_51) in (let TMP_53 \def 
(eq_ind_r TList TMP_28 TMP_40 TMP_48 TMP_52 H) in (let TMP_54 \def (Ss hds) 
in (let TMP_55 \def (S O) in (let TMP_56 \def (lift TMP_55 O t) in (let 
TMP_57 \def (lift1 TMP_54 TMP_56) in (let TMP_58 \def (lift1_xhg hds t) in 
(eq_ind_r T TMP_12 TMP_25 TMP_53 TMP_57 TMP_58)))))))))))))))))))))))))))))) 
in (TList_ind TMP_8 TMP_9 TMP_59 ts))))).

theorem lift1_free:
 \forall (hds: PList).(\forall (i: nat).(\forall (t: T).(eq T (lift1 hds 
(lift (S i) O t)) (lift (S (trans hds i)) O (lift1 (ptrans hds i) t)))))
\def
 \lambda (hds: PList).(let TMP_9 \def (\lambda (p: PList).(\forall (i: 
nat).(\forall (t: T).(let TMP_1 \def (S i) in (let TMP_2 \def (lift TMP_1 O 
t) in (let TMP_3 \def (lift1 p TMP_2) in (let TMP_4 \def (trans p i) in (let 
TMP_5 \def (S TMP_4) in (let TMP_6 \def (ptrans p i) in (let TMP_7 \def 
(lift1 TMP_6 t) in (let TMP_8 \def (lift TMP_5 O TMP_7) in (eq T TMP_3 
TMP_8)))))))))))) in (let TMP_12 \def (\lambda (i: nat).(\lambda (t: T).(let 
TMP_10 \def (S i) in (let TMP_11 \def (lift TMP_10 O t) in (refl_equal T 
TMP_11))))) in (let TMP_262 \def (\lambda (h: nat).(\lambda (d: nat).(\lambda 
(hds0: PList).(\lambda (H: ((\forall (i: nat).(\forall (t: T).(eq T (lift1 
hds0 (lift (S i) O t)) (lift (S (trans hds0 i)) O (lift1 (ptrans hds0 i) 
t))))))).(\lambda (i: nat).(\lambda (t: T).(let TMP_13 \def (trans hds0 i) in 
(let TMP_14 \def (S TMP_13) in (let TMP_15 \def (ptrans hds0 i) in (let 
TMP_16 \def (lift1 TMP_15 t) in (let TMP_17 \def (lift TMP_14 O TMP_16) in 
(let TMP_33 \def (\lambda (t0: T).(let TMP_18 \def (lift h d t0) in (let 
TMP_19 \def (trans hds0 i) in (let TMP_20 \def (blt TMP_19 d) in (let TMP_22 
\def (match TMP_20 with [true \Rightarrow (trans hds0 i) | false \Rightarrow 
(let TMP_21 \def (trans hds0 i) in (plus TMP_21 h))]) in (let TMP_23 \def (S 
TMP_22) in (let TMP_24 \def (trans hds0 i) in (let TMP_25 \def (blt TMP_24 d) 
in (let TMP_30 \def (match TMP_25 with [true \Rightarrow (let TMP_26 \def 
(trans hds0 i) in (let TMP_27 \def (S TMP_26) in (let TMP_28 \def (minus d 
TMP_27) in (let TMP_29 \def (ptrans hds0 i) in (PCons h TMP_28 TMP_29))))) | 
false \Rightarrow (ptrans hds0 i)]) in (let TMP_31 \def (lift1 TMP_30 t) in 
(let TMP_32 \def (lift TMP_23 O TMP_31) in (eq T TMP_18 TMP_32)))))))))))) in 
(let TMP_34 \def (trans hds0 i) in (let TMP_35 \def (blt TMP_34 d) in (let 
TMP_52 \def (\lambda (b: bool).(let TMP_36 \def (trans hds0 i) in (let TMP_37 
\def (S TMP_36) in (let TMP_38 \def (ptrans hds0 i) in (let TMP_39 \def 
(lift1 TMP_38 t) in (let TMP_40 \def (lift TMP_37 O TMP_39) in (let TMP_41 
\def (lift h d TMP_40) in (let TMP_43 \def (match b with [true \Rightarrow 
(trans hds0 i) | false \Rightarrow (let TMP_42 \def (trans hds0 i) in (plus 
TMP_42 h))]) in (let TMP_44 \def (S TMP_43) in (let TMP_49 \def (match b with 
[true \Rightarrow (let TMP_45 \def (trans hds0 i) in (let TMP_46 \def (S 
TMP_45) in (let TMP_47 \def (minus d TMP_46) in (let TMP_48 \def (ptrans hds0 
i) in (PCons h TMP_47 TMP_48))))) | false \Rightarrow (ptrans hds0 i)]) in 
(let TMP_50 \def (lift1 TMP_49 t) in (let TMP_51 \def (lift TMP_44 O TMP_50) 
in (eq T TMP_41 TMP_51))))))))))))) in (let TMP_256 \def (\lambda (x_x: 
bool).(let TMP_69 \def (\lambda (b: bool).((eq bool (blt (trans hds0 i) d) b) 
\to (let TMP_53 \def (trans hds0 i) in (let TMP_54 \def (S TMP_53) in (let 
TMP_55 \def (ptrans hds0 i) in (let TMP_56 \def (lift1 TMP_55 t) in (let 
TMP_57 \def (lift TMP_54 O TMP_56) in (let TMP_58 \def (lift h d TMP_57) in 
(let TMP_60 \def (match b with [true \Rightarrow (trans hds0 i) | false 
\Rightarrow (let TMP_59 \def (trans hds0 i) in (plus TMP_59 h))]) in (let 
TMP_61 \def (S TMP_60) in (let TMP_66 \def (match b with [true \Rightarrow 
(let TMP_62 \def (trans hds0 i) in (let TMP_63 \def (S TMP_62) in (let TMP_64 
\def (minus d TMP_63) in (let TMP_65 \def (ptrans hds0 i) in (PCons h TMP_64 
TMP_65))))) | false \Rightarrow (ptrans hds0 i)]) in (let TMP_67 \def (lift1 
TMP_66 t) in (let TMP_68 \def (lift TMP_61 O TMP_67) in (eq T TMP_58 
TMP_68)))))))))))))) in (let TMP_159 \def (\lambda (H0: (eq bool (blt (trans 
hds0 i) d) true)).(let TMP_70 \def (trans hds0 i) in (let TMP_71 \def (S 
TMP_70) in (let TMP_72 \def (trans hds0 i) in (let TMP_73 \def (S TMP_72) in 
(let TMP_74 \def (minus d TMP_73) in (let TMP_75 \def (plus TMP_71 TMP_74) in 
(let TMP_91 \def (\lambda (n: nat).(let TMP_76 \def (trans hds0 i) in (let 
TMP_77 \def (S TMP_76) in (let TMP_78 \def (ptrans hds0 i) in (let TMP_79 
\def (lift1 TMP_78 t) in (let TMP_80 \def (lift TMP_77 O TMP_79) in (let 
TMP_81 \def (lift h n TMP_80) in (let TMP_82 \def (trans hds0 i) in (let 
TMP_83 \def (S TMP_82) in (let TMP_84 \def (trans hds0 i) in (let TMP_85 \def 
(S TMP_84) in (let TMP_86 \def (minus d TMP_85) in (let TMP_87 \def (ptrans 
hds0 i) in (let TMP_88 \def (PCons h TMP_86 TMP_87) in (let TMP_89 \def 
(lift1 TMP_88 t) in (let TMP_90 \def (lift TMP_83 O TMP_89) in (eq T TMP_81 
TMP_90))))))))))))))))) in (let TMP_92 \def (trans hds0 i) in (let TMP_93 
\def (S TMP_92) in (let TMP_94 \def (trans hds0 i) in (let TMP_95 \def (S 
TMP_94) in (let TMP_96 \def (minus d TMP_95) in (let TMP_97 \def (ptrans hds0 
i) in (let TMP_98 \def (lift1 TMP_97 t) in (let TMP_99 \def (lift h TMP_96 
TMP_98) in (let TMP_100 \def (lift TMP_93 O TMP_99) in (let TMP_110 \def 
(\lambda (t0: T).(let TMP_101 \def (trans hds0 i) in (let TMP_102 \def (S 
TMP_101) in (let TMP_103 \def (trans hds0 i) in (let TMP_104 \def (S TMP_103) 
in (let TMP_105 \def (minus d TMP_104) in (let TMP_106 \def (ptrans hds0 i) 
in (let TMP_107 \def (PCons h TMP_105 TMP_106) in (let TMP_108 \def (lift1 
TMP_107 t) in (let TMP_109 \def (lift TMP_102 O TMP_108) in (eq T t0 
TMP_109))))))))))) in (let TMP_111 \def (trans hds0 i) in (let TMP_112 \def 
(S TMP_111) in (let TMP_113 \def (trans hds0 i) in (let TMP_114 \def (S 
TMP_113) in (let TMP_115 \def (minus d TMP_114) in (let TMP_116 \def (ptrans 
hds0 i) in (let TMP_117 \def (PCons h TMP_115 TMP_116) in (let TMP_118 \def 
(lift1 TMP_117 t) in (let TMP_119 \def (lift TMP_112 O TMP_118) in (let 
TMP_120 \def (refl_equal T TMP_119) in (let TMP_121 \def (trans hds0 i) in 
(let TMP_122 \def (S TMP_121) in (let TMP_123 \def (trans hds0 i) in (let 
TMP_124 \def (S TMP_123) in (let TMP_125 \def (minus d TMP_124) in (let 
TMP_126 \def (plus TMP_122 TMP_125) in (let TMP_127 \def (trans hds0 i) in 
(let TMP_128 \def (S TMP_127) in (let TMP_129 \def (ptrans hds0 i) in (let 
TMP_130 \def (lift1 TMP_129 t) in (let TMP_131 \def (lift TMP_128 O TMP_130) 
in (let TMP_132 \def (lift h TMP_126 TMP_131) in (let TMP_133 \def (ptrans 
hds0 i) in (let TMP_134 \def (lift1 TMP_133 t) in (let TMP_135 \def (trans 
hds0 i) in (let TMP_136 \def (S TMP_135) in (let TMP_137 \def (trans hds0 i) 
in (let TMP_138 \def (S TMP_137) in (let TMP_139 \def (minus d TMP_138) in 
(let TMP_140 \def (trans hds0 i) in (let TMP_141 \def (S TMP_140) in (let 
TMP_142 \def (minus d TMP_141) in (let TMP_143 \def (le_O_n TMP_142) in (let 
TMP_144 \def (lift_d TMP_134 h TMP_136 TMP_139 O TMP_143) in (let TMP_145 
\def (eq_ind_r T TMP_100 TMP_110 TMP_120 TMP_132 TMP_144) in (let TMP_146 
\def (trans hds0 i) in (let TMP_147 \def (S TMP_146) in (let TMP_148 \def 
(trans hds0 i) in (let TMP_149 \def (S TMP_148) in (let TMP_150 \def (trans 
hds0 i) in (let TMP_151 \def (S TMP_150) in (let TMP_152 \def (trans hds0 i) 
in (let TMP_153 \def (trans hds0 i) in (let TMP_154 \def (blt_lt d TMP_153 
H0) in (let TMP_155 \def (lt_le_S TMP_152 d TMP_154) in (let TMP_156 \def 
(le_bge TMP_151 d TMP_155) in (let TMP_157 \def (bge_le TMP_149 d TMP_156) in 
(let TMP_158 \def (le_plus_minus TMP_147 d TMP_157) in (eq_ind_r nat TMP_75 
TMP_91 TMP_145 d 
TMP_158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in 
(let TMP_255 \def (\lambda (H0: (eq bool (blt (trans hds0 i) d) false)).(let 
TMP_160 \def (trans hds0 i) in (let TMP_161 \def (S TMP_160) in (let TMP_162 
\def (plus h TMP_161) in (let TMP_163 \def (ptrans hds0 i) in (let TMP_164 
\def (lift1 TMP_163 t) in (let TMP_165 \def (lift TMP_162 O TMP_164) in (let 
TMP_172 \def (\lambda (t0: T).(let TMP_166 \def (trans hds0 i) in (let 
TMP_167 \def (plus TMP_166 h) in (let TMP_168 \def (S TMP_167) in (let 
TMP_169 \def (ptrans hds0 i) in (let TMP_170 \def (lift1 TMP_169 t) in (let 
TMP_171 \def (lift TMP_168 O TMP_170) in (eq T t0 TMP_171)))))))) in (let 
TMP_173 \def (trans hds0 i) in (let TMP_174 \def (plus h TMP_173) in (let 
TMP_175 \def (S TMP_174) in (let TMP_185 \def (\lambda (n: nat).(let TMP_176 
\def (ptrans hds0 i) in (let TMP_177 \def (lift1 TMP_176 t) in (let TMP_178 
\def (lift n O TMP_177) in (let TMP_179 \def (trans hds0 i) in (let TMP_180 
\def (plus TMP_179 h) in (let TMP_181 \def (S TMP_180) in (let TMP_182 \def 
(ptrans hds0 i) in (let TMP_183 \def (lift1 TMP_182 t) in (let TMP_184 \def 
(lift TMP_181 O TMP_183) in (eq T TMP_178 TMP_184))))))))))) in (let TMP_186 
\def (trans hds0 i) in (let TMP_187 \def (plus TMP_186 h) in (let TMP_198 
\def (\lambda (n: nat).(let TMP_188 \def (S n) in (let TMP_189 \def (ptrans 
hds0 i) in (let TMP_190 \def (lift1 TMP_189 t) in (let TMP_191 \def (lift 
TMP_188 O TMP_190) in (let TMP_192 \def (trans hds0 i) in (let TMP_193 \def 
(plus TMP_192 h) in (let TMP_194 \def (S TMP_193) in (let TMP_195 \def 
(ptrans hds0 i) in (let TMP_196 \def (lift1 TMP_195 t) in (let TMP_197 \def 
(lift TMP_194 O TMP_196) in (eq T TMP_191 TMP_197)))))))))))) in (let TMP_199 
\def (trans hds0 i) in (let TMP_200 \def (plus TMP_199 h) in (let TMP_201 
\def (S TMP_200) in (let TMP_202 \def (ptrans hds0 i) in (let TMP_203 \def 
(lift1 TMP_202 t) in (let TMP_204 \def (lift TMP_201 O TMP_203) in (let 
TMP_205 \def (refl_equal T TMP_204) in (let TMP_206 \def (trans hds0 i) in 
(let TMP_207 \def (plus h TMP_206) in (let TMP_208 \def (trans hds0 i) in 
(let TMP_209 \def (plus_sym h TMP_208) in (let TMP_210 \def (eq_ind_r nat 
TMP_187 TMP_198 TMP_205 TMP_207 TMP_209) in (let TMP_211 \def (trans hds0 i) 
in (let TMP_212 \def (S TMP_211) in (let TMP_213 \def (plus h TMP_212) in 
(let TMP_214 \def (trans hds0 i) in (let TMP_215 \def (plus_n_Sm h TMP_214) 
in (let TMP_216 \def (eq_ind nat TMP_175 TMP_185 TMP_210 TMP_213 TMP_215) in 
(let TMP_217 \def (trans hds0 i) in (let TMP_218 \def (S TMP_217) in (let 
TMP_219 \def (ptrans hds0 i) in (let TMP_220 \def (lift1 TMP_219 t) in (let 
TMP_221 \def (lift TMP_218 O TMP_220) in (let TMP_222 \def (lift h d TMP_221) 
in (let TMP_223 \def (ptrans hds0 i) in (let TMP_224 \def (lift1 TMP_223 t) 
in (let TMP_225 \def (trans hds0 i) in (let TMP_226 \def (S TMP_225) in (let 
TMP_227 \def (trans hds0 i) in (let TMP_228 \def (plus O TMP_227) in (let 
TMP_229 \def (S TMP_228) in (let TMP_230 \def (\lambda (n: nat).(le d n)) in 
(let TMP_231 \def (trans hds0 i) in (let TMP_232 \def (plus TMP_231 O) in 
(let TMP_234 \def (\lambda (n: nat).(let TMP_233 \def (S n) in (le d 
TMP_233))) in (let TMP_235 \def (trans hds0 i) in (let TMP_236 \def (plus 
TMP_235 O) in (let TMP_237 \def (trans hds0 i) in (let TMP_238 \def (trans 
hds0 i) in (let TMP_239 \def (bge_le d TMP_238 H0) in (let TMP_240 \def 
(le_plus_trans d TMP_237 O TMP_239) in (let TMP_241 \def (le_S d TMP_236 
TMP_240) in (let TMP_242 \def (trans hds0 i) in (let TMP_243 \def (plus O 
TMP_242) in (let TMP_244 \def (trans hds0 i) in (let TMP_245 \def (plus_sym O 
TMP_244) in (let TMP_246 \def (eq_ind_r nat TMP_232 TMP_234 TMP_241 TMP_243 
TMP_245) in (let TMP_247 \def (trans hds0 i) in (let TMP_248 \def (S TMP_247) 
in (let TMP_249 \def (plus O TMP_248) in (let TMP_250 \def (trans hds0 i) in 
(let TMP_251 \def (plus_n_Sm O TMP_250) in (let TMP_252 \def (eq_ind nat 
TMP_229 TMP_230 TMP_246 TMP_249 TMP_251) in (let TMP_253 \def (le_O_n d) in 
(let TMP_254 \def (lift_free TMP_224 TMP_226 h O d TMP_252 TMP_253) in 
(eq_ind_r T TMP_165 TMP_172 TMP_216 TMP_222 
TMP_254)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 in (bool_ind TMP_69 TMP_159 TMP_255 x_x))))) in (let TMP_257 \def 
(xinduction bool TMP_35 TMP_52 TMP_256) in (let TMP_258 \def (S i) in (let 
TMP_259 \def (lift TMP_258 O t) in (let TMP_260 \def (lift1 hds0 TMP_259) in 
(let TMP_261 \def (H i t) in (eq_ind_r T TMP_17 TMP_33 TMP_257 TMP_260 
TMP_261)))))))))))))))))))))) in (PList_ind TMP_9 TMP_12 TMP_262 hds)))).

