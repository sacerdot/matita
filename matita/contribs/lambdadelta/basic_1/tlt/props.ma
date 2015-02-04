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

include "basic_1/T/fwd.ma".

include "basic_1/tlt/defs.ma".

theorem wadd_le:
 \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: 
nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((le v w) \to 
(\forall (n: nat).(le (wadd f v n) (wadd g w n))))))))
\def
 \lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n: nat).(le (f n) (g n))))).(\lambda (v: nat).(\lambda (w: 
nat).(\lambda (H0: (le v w)).(\lambda (n: nat).(let TMP_3 \def (\lambda (n0: 
nat).(let TMP_1 \def (wadd f v n0) in (let TMP_2 \def (wadd g w n0) in (le 
TMP_1 TMP_2)))) in (let TMP_4 \def (\lambda (n0: nat).(\lambda (_: (le (wadd 
f v n0) (wadd g w n0))).(H n0))) in (nat_ind TMP_3 H0 TMP_4 n))))))))).

theorem wadd_lt:
 \forall (f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: 
nat).(le (f n) (g n)))) \to (\forall (v: nat).(\forall (w: nat).((lt v w) \to 
(\forall (n: nat).(le (wadd f v n) (wadd g w n))))))))
\def
 \lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n: nat).(le (f n) (g n))))).(\lambda (v: nat).(\lambda (w: 
nat).(\lambda (H0: (lt v w)).(\lambda (n: nat).(let TMP_3 \def (\lambda (n0: 
nat).(let TMP_1 \def (wadd f v n0) in (let TMP_2 \def (wadd g w n0) in (le 
TMP_1 TMP_2)))) in (let TMP_4 \def (S v) in (let TMP_5 \def (S w) in (let 
TMP_6 \def (S v) in (let TMP_7 \def (S TMP_6) in (let TMP_8 \def (S w) in 
(let TMP_9 \def (S v) in (let TMP_10 \def (le_n_S TMP_9 w H0) in (let TMP_11 
\def (le_S TMP_7 TMP_8 TMP_10) in (let TMP_12 \def (le_S_n TMP_4 TMP_5 
TMP_11) in (let TMP_13 \def (le_S_n v w TMP_12) in (let TMP_14 \def (\lambda 
(n0: nat).(\lambda (_: (le (wadd f v n0) (wadd g w n0))).(H n0))) in (nat_ind 
TMP_3 TMP_13 TMP_14 n))))))))))))))))))).

theorem wadd_O:
 \forall (n: nat).(eq nat (wadd (\lambda (_: nat).O) O n) O)
\def
 \lambda (n: nat).(let TMP_3 \def (\lambda (n0: nat).(let TMP_1 \def (\lambda 
(_: nat).O) in (let TMP_2 \def (wadd TMP_1 O n0) in (eq nat TMP_2 O)))) in 
(let TMP_4 \def (refl_equal nat O) in (let TMP_5 \def (\lambda (n0: 
nat).(\lambda (_: (eq nat (wadd (\lambda (_: nat).O) O n0) O)).(refl_equal 
nat O))) in (nat_ind TMP_3 TMP_4 TMP_5 n)))).

theorem weight_le:
 \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t) 
(weight_map g t)))))
\def
 \lambda (t: T).(let TMP_3 \def (\lambda (t0: T).(\forall (f: ((nat \to 
nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) 
\to (let TMP_1 \def (weight_map f t0) in (let TMP_2 \def (weight_map g t0) in 
(le TMP_1 TMP_2))))))) in (let TMP_6 \def (\lambda (n: nat).(\lambda (f: 
((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (_: ((\forall (n0: 
nat).(le (f n0) (g n0))))).(let TMP_4 \def (TSort n) in (let TMP_5 \def 
(weight_map g TMP_4) in (le_O_n TMP_5))))))) in (let TMP_7 \def (\lambda (n: 
nat).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H: 
((\forall (n0: nat).(le (f n0) (g n0))))).(H n))))) in (let TMP_144 \def 
(\lambda (k: K).(let TMP_12 \def (\lambda (k0: K).(\forall (t0: T).(((\forall 
(f: ((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f 
n) (g n)))) \to (le (weight_map f t0) (weight_map g t0)))))) \to (\forall 
(t1: T).(((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t1) 
(weight_map g t1)))))) \to (\forall (f: ((nat \to nat))).(\forall (g: ((nat 
\to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (let TMP_8 \def (THead 
k0 t0 t1) in (let TMP_9 \def (weight_map f TMP_8) in (let TMP_10 \def (THead 
k0 t0 t1) in (let TMP_11 \def (weight_map g TMP_10) in (le TMP_9 
TMP_11))))))))))))) in (let TMP_129 \def (\lambda (b: B).(let TMP_43 \def 
(\lambda (b0: B).(\forall (t0: T).(((\forall (f: ((nat \to nat))).(\forall 
(g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le 
(weight_map f t0) (weight_map g t0)))))) \to (\forall (t1: T).(((\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (le (weight_map f t1) (weight_map g t1)))))) \to (\forall (f: 
((nat \to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) 
(g n)))) \to (let TMP_27 \def (match b0 with [Abbr \Rightarrow (let TMP_21 
\def (weight_map f t0) in (let TMP_22 \def (weight_map f t0) in (let TMP_23 
\def (S TMP_22) in (let TMP_24 \def (wadd f TMP_23) in (let TMP_25 \def 
(weight_map TMP_24 t1) in (let TMP_26 \def (plus TMP_21 TMP_25) in (S 
TMP_26))))))) | Abst \Rightarrow (let TMP_17 \def (weight_map f t0) in (let 
TMP_18 \def (wadd f O) in (let TMP_19 \def (weight_map TMP_18 t1) in (let 
TMP_20 \def (plus TMP_17 TMP_19) in (S TMP_20))))) | Void \Rightarrow (let 
TMP_13 \def (weight_map f t0) in (let TMP_14 \def (wadd f O) in (let TMP_15 
\def (weight_map TMP_14 t1) in (let TMP_16 \def (plus TMP_13 TMP_15) in (S 
TMP_16)))))]) in (let TMP_42 \def (match b0 with [Abbr \Rightarrow (let 
TMP_36 \def (weight_map g t0) in (let TMP_37 \def (weight_map g t0) in (let 
TMP_38 \def (S TMP_37) in (let TMP_39 \def (wadd g TMP_38) in (let TMP_40 
\def (weight_map TMP_39 t1) in (let TMP_41 \def (plus TMP_36 TMP_40) in (S 
TMP_41))))))) | Abst \Rightarrow (let TMP_32 \def (weight_map g t0) in (let 
TMP_33 \def (wadd g O) in (let TMP_34 \def (weight_map TMP_33 t1) in (let 
TMP_35 \def (plus TMP_32 TMP_34) in (S TMP_35))))) | Void \Rightarrow (let 
TMP_28 \def (weight_map g t0) in (let TMP_29 \def (wadd g O) in (let TMP_30 
\def (weight_map TMP_29 t1) in (let TMP_31 \def (plus TMP_28 TMP_30) in (S 
TMP_31)))))]) in (le TMP_27 TMP_42))))))))))) in (let TMP_84 \def (\lambda 
(t0: T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t0) 
(weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g 
n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f n) (g n))))).(let TMP_44 \def (weight_map f t0) in (let TMP_45 \def 
(weight_map f t0) in (let TMP_46 \def (S TMP_45) in (let TMP_47 \def (wadd f 
TMP_46) in (let TMP_48 \def (weight_map TMP_47 t1) in (let TMP_49 \def (plus 
TMP_44 TMP_48) in (let TMP_50 \def (weight_map g t0) in (let TMP_51 \def 
(weight_map g t0) in (let TMP_52 \def (S TMP_51) in (let TMP_53 \def (wadd g 
TMP_52) in (let TMP_54 \def (weight_map TMP_53 t1) in (let TMP_55 \def (plus 
TMP_50 TMP_54) in (let TMP_56 \def (weight_map f t0) in (let TMP_57 \def 
(weight_map g t0) in (let TMP_58 \def (weight_map f t0) in (let TMP_59 \def 
(S TMP_58) in (let TMP_60 \def (wadd f TMP_59) in (let TMP_61 \def 
(weight_map TMP_60 t1) in (let TMP_62 \def (weight_map g t0) in (let TMP_63 
\def (S TMP_62) in (let TMP_64 \def (wadd g TMP_63) in (let TMP_65 \def 
(weight_map TMP_64 t1) in (let TMP_66 \def (H f g H1) in (let TMP_67 \def 
(weight_map f t0) in (let TMP_68 \def (S TMP_67) in (let TMP_69 \def (wadd f 
TMP_68) in (let TMP_70 \def (weight_map g t0) in (let TMP_71 \def (S TMP_70) 
in (let TMP_72 \def (wadd g TMP_71) in (let TMP_81 \def (\lambda (n: 
nat).(let TMP_73 \def (weight_map f t0) in (let TMP_74 \def (S TMP_73) in 
(let TMP_75 \def (weight_map g t0) in (let TMP_76 \def (S TMP_75) in (let 
TMP_77 \def (weight_map f t0) in (let TMP_78 \def (weight_map g t0) in (let 
TMP_79 \def (H f g H1) in (let TMP_80 \def (le_n_S TMP_77 TMP_78 TMP_79) in 
(wadd_le f g H1 TMP_74 TMP_76 TMP_80 n)))))))))) in (let TMP_82 \def (H0 
TMP_69 TMP_72 TMP_81) in (let TMP_83 \def (le_plus_plus TMP_56 TMP_57 TMP_61 
TMP_65 TMP_66 TMP_82) in (le_n_S TMP_49 TMP_55 
TMP_83)))))))))))))))))))))))))))))))))))))))) in (let TMP_106 \def (\lambda 
(t0: T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t0) 
(weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g 
n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f n) (g n))))).(let TMP_85 \def (weight_map f t0) in (let TMP_86 \def (wadd 
f O) in (let TMP_87 \def (weight_map TMP_86 t1) in (let TMP_88 \def (plus 
TMP_85 TMP_87) in (let TMP_89 \def (weight_map g t0) in (let TMP_90 \def 
(wadd g O) in (let TMP_91 \def (weight_map TMP_90 t1) in (let TMP_92 \def 
(plus TMP_89 TMP_91) in (let TMP_93 \def (weight_map f t0) in (let TMP_94 
\def (weight_map g t0) in (let TMP_95 \def (wadd f O) in (let TMP_96 \def 
(weight_map TMP_95 t1) in (let TMP_97 \def (wadd g O) in (let TMP_98 \def 
(weight_map TMP_97 t1) in (let TMP_99 \def (H f g H1) in (let TMP_100 \def 
(wadd f O) in (let TMP_101 \def (wadd g O) in (let TMP_103 \def (\lambda (n: 
nat).(let TMP_102 \def (le_O_n O) in (wadd_le f g H1 O O TMP_102 n))) in (let 
TMP_104 \def (H0 TMP_100 TMP_101 TMP_103) in (let TMP_105 \def (le_plus_plus 
TMP_93 TMP_94 TMP_96 TMP_98 TMP_99 TMP_104) in (le_n_S TMP_88 TMP_92 
TMP_105)))))))))))))))))))))))))))) in (let TMP_128 \def (\lambda (t0: 
T).(\lambda (H: ((\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f n) (g n)))) \to (le (weight_map f t0) 
(weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f n) (g 
n)))) \to (le (weight_map f t1) (weight_map g t1))))))).(\lambda (f: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f n) (g n))))).(let TMP_107 \def (weight_map f t0) in (let TMP_108 \def 
(wadd f O) in (let TMP_109 \def (weight_map TMP_108 t1) in (let TMP_110 \def 
(plus TMP_107 TMP_109) in (let TMP_111 \def (weight_map g t0) in (let TMP_112 
\def (wadd g O) in (let TMP_113 \def (weight_map TMP_112 t1) in (let TMP_114 
\def (plus TMP_111 TMP_113) in (let TMP_115 \def (weight_map f t0) in (let 
TMP_116 \def (weight_map g t0) in (let TMP_117 \def (wadd f O) in (let 
TMP_118 \def (weight_map TMP_117 t1) in (let TMP_119 \def (wadd g O) in (let 
TMP_120 \def (weight_map TMP_119 t1) in (let TMP_121 \def (H f g H1) in (let 
TMP_122 \def (wadd f O) in (let TMP_123 \def (wadd g O) in (let TMP_125 \def 
(\lambda (n: nat).(let TMP_124 \def (le_O_n O) in (wadd_le f g H1 O O TMP_124 
n))) in (let TMP_126 \def (H0 TMP_122 TMP_123 TMP_125) in (let TMP_127 \def 
(le_plus_plus TMP_115 TMP_116 TMP_118 TMP_120 TMP_121 TMP_126) in (le_n_S 
TMP_110 TMP_114 TMP_127)))))))))))))))))))))))))))) in (B_ind TMP_43 TMP_84 
TMP_106 TMP_128 b)))))) in (let TMP_143 \def (\lambda (_: F).(\lambda (t0: 
T).(\lambda (H: ((\forall (f0: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(le (f0 n) (g n)))) \to (le (weight_map f0 t0) 
(weight_map g t0))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (f0: ((nat 
\to nat))).(\forall (g: ((nat \to nat))).(((\forall (n: nat).(le (f0 n) (g 
n)))) \to (le (weight_map f0 t1) (weight_map g t1))))))).(\lambda (f0: ((nat 
\to nat))).(\lambda (g: ((nat \to nat))).(\lambda (H1: ((\forall (n: nat).(le 
(f0 n) (g n))))).(let TMP_130 \def (weight_map f0 t0) in (let TMP_131 \def 
(weight_map f0 t1) in (let TMP_132 \def (plus TMP_130 TMP_131) in (let 
TMP_133 \def (weight_map g t0) in (let TMP_134 \def (weight_map g t1) in (let 
TMP_135 \def (plus TMP_133 TMP_134) in (let TMP_136 \def (weight_map f0 t0) 
in (let TMP_137 \def (weight_map g t0) in (let TMP_138 \def (weight_map f0 
t1) in (let TMP_139 \def (weight_map g t1) in (let TMP_140 \def (H f0 g H1) 
in (let TMP_141 \def (H0 f0 g H1) in (let TMP_142 \def (le_plus_plus TMP_136 
TMP_137 TMP_138 TMP_139 TMP_140 TMP_141) in (le_n_S TMP_132 TMP_135 
TMP_142)))))))))))))))))))))) in (K_ind TMP_12 TMP_129 TMP_143 k))))) in 
(T_ind TMP_3 TMP_6 TMP_7 TMP_144 t))))).

theorem weight_eq:
 \forall (t: T).(\forall (f: ((nat \to nat))).(\forall (g: ((nat \to 
nat))).(((\forall (n: nat).(eq nat (f n) (g n)))) \to (eq nat (weight_map f 
t) (weight_map g t)))))
\def
 \lambda (t: T).(\lambda (f: ((nat \to nat))).(\lambda (g: ((nat \to 
nat))).(\lambda (H: ((\forall (n: nat).(eq nat (f n) (g n))))).(let TMP_1 
\def (weight_map f t) in (let TMP_2 \def (weight_map g t) in (let TMP_10 \def 
(\lambda (n: nat).(let TMP_3 \def (g n) in (let TMP_5 \def (\lambda (n0: 
nat).(let TMP_4 \def (g n) in (le n0 TMP_4))) in (let TMP_6 \def (g n) in 
(let TMP_7 \def (le_n TMP_6) in (let TMP_8 \def (f n) in (let TMP_9 \def (H 
n) in (eq_ind_r nat TMP_3 TMP_5 TMP_7 TMP_8 TMP_9)))))))) in (let TMP_11 \def 
(weight_le t f g TMP_10) in (let TMP_19 \def (\lambda (n: nat).(let TMP_12 
\def (g n) in (let TMP_14 \def (\lambda (n0: nat).(let TMP_13 \def (g n) in 
(le TMP_13 n0))) in (let TMP_15 \def (g n) in (let TMP_16 \def (le_n TMP_15) 
in (let TMP_17 \def (f n) in (let TMP_18 \def (H n) in (eq_ind_r nat TMP_12 
TMP_14 TMP_16 TMP_17 TMP_18)))))))) in (let TMP_20 \def (weight_le t g f 
TMP_19) in (le_antisym TMP_1 TMP_2 TMP_11 TMP_20)))))))))).

theorem weight_add_O:
 \forall (t: T).(eq nat (weight_map (wadd (\lambda (_: nat).O) O) t) 
(weight_map (\lambda (_: nat).O) t))
\def
 \lambda (t: T).(let TMP_1 \def (\lambda (_: nat).O) in (let TMP_2 \def (wadd 
TMP_1 O) in (let TMP_3 \def (\lambda (_: nat).O) in (let TMP_4 \def (\lambda 
(n: nat).(wadd_O n)) in (weight_eq t TMP_2 TMP_3 TMP_4))))).

theorem weight_add_S:
 \forall (t: T).(\forall (m: nat).(le (weight_map (wadd (\lambda (_: nat).O) 
O) t) (weight_map (wadd (\lambda (_: nat).O) (S m)) t)))
\def
 \lambda (t: T).(\lambda (m: nat).(let TMP_1 \def (\lambda (_: nat).O) in 
(let TMP_2 \def (wadd TMP_1 O) in (let TMP_3 \def (\lambda (_: nat).O) in 
(let TMP_4 \def (S m) in (let TMP_5 \def (wadd TMP_3 TMP_4) in (let TMP_12 
\def (\lambda (n: nat).(let TMP_6 \def (\lambda (_: nat).O) in (let TMP_7 
\def (\lambda (_: nat).O) in (let TMP_8 \def (\lambda (_: nat).(le_O_n O)) in 
(let TMP_9 \def (S m) in (let TMP_10 \def (S m) in (let TMP_11 \def (le_O_n 
TMP_10) in (wadd_le TMP_6 TMP_7 TMP_8 O TMP_9 TMP_11 n)))))))) in (weight_le 
t TMP_2 TMP_5 TMP_12)))))))).

theorem tlt_trans:
 \forall (v: T).(\forall (u: T).(\forall (t: T).((tlt u v) \to ((tlt v t) \to 
(tlt u t)))))
\def
 \lambda (v: T).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (lt (weight u) 
(weight v))).(\lambda (H0: (lt (weight v) (weight t))).(let TMP_1 \def 
(weight u) in (let TMP_2 \def (weight v) in (let TMP_3 \def (weight t) in 
(lt_trans TMP_1 TMP_2 TMP_3 H H0)))))))).

theorem tlt_head_sx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt u (THead k u t))))
\def
 \lambda (k: K).(let TMP_6 \def (\lambda (k0: K).(\forall (u: T).(\forall (t: 
T).(let TMP_1 \def (\lambda (_: nat).O) in (let TMP_2 \def (weight_map TMP_1 
u) in (let TMP_3 \def (\lambda (_: nat).O) in (let TMP_4 \def (THead k0 u t) 
in (let TMP_5 \def (weight_map TMP_3 TMP_4) in (lt TMP_2 TMP_5))))))))) in 
(let TMP_83 \def (\lambda (b: B).(let TMP_31 \def (\lambda (b0: B).(\forall 
(u: T).(\forall (t: T).(let TMP_7 \def (\lambda (_: nat).O) in (let TMP_8 
\def (weight_map TMP_7 u) in (let TMP_30 \def (match b0 with [Abbr 
\Rightarrow (let TMP_21 \def (\lambda (_: nat).O) in (let TMP_22 \def 
(weight_map TMP_21 u) in (let TMP_23 \def (\lambda (_: nat).O) in (let TMP_24 
\def (\lambda (_: nat).O) in (let TMP_25 \def (weight_map TMP_24 u) in (let 
TMP_26 \def (S TMP_25) in (let TMP_27 \def (wadd TMP_23 TMP_26) in (let 
TMP_28 \def (weight_map TMP_27 t) in (let TMP_29 \def (plus TMP_22 TMP_28) in 
(S TMP_29)))))))))) | Abst \Rightarrow (let TMP_15 \def (\lambda (_: nat).O) 
in (let TMP_16 \def (weight_map TMP_15 u) in (let TMP_17 \def (\lambda (_: 
nat).O) in (let TMP_18 \def (wadd TMP_17 O) in (let TMP_19 \def (weight_map 
TMP_18 t) in (let TMP_20 \def (plus TMP_16 TMP_19) in (S TMP_20))))))) | Void 
\Rightarrow (let TMP_9 \def (\lambda (_: nat).O) in (let TMP_10 \def 
(weight_map TMP_9 u) in (let TMP_11 \def (\lambda (_: nat).O) in (let TMP_12 
\def (wadd TMP_11 O) in (let TMP_13 \def (weight_map TMP_12 t) in (let TMP_14 
\def (plus TMP_10 TMP_13) in (S TMP_14)))))))]) in (lt TMP_8 TMP_30))))))) in 
(let TMP_52 \def (\lambda (u: T).(\lambda (t: T).(let TMP_32 \def (\lambda 
(_: nat).O) in (let TMP_33 \def (weight_map TMP_32 u) in (let TMP_34 \def 
(\lambda (_: nat).O) in (let TMP_35 \def (weight_map TMP_34 u) in (let TMP_36 
\def (\lambda (_: nat).O) in (let TMP_37 \def (\lambda (_: nat).O) in (let 
TMP_38 \def (weight_map TMP_37 u) in (let TMP_39 \def (S TMP_38) in (let 
TMP_40 \def (wadd TMP_36 TMP_39) in (let TMP_41 \def (weight_map TMP_40 t) in 
(let TMP_42 \def (plus TMP_35 TMP_41) in (let TMP_43 \def (\lambda (_: 
nat).O) in (let TMP_44 \def (weight_map TMP_43 u) in (let TMP_45 \def 
(\lambda (_: nat).O) in (let TMP_46 \def (\lambda (_: nat).O) in (let TMP_47 
\def (weight_map TMP_46 u) in (let TMP_48 \def (S TMP_47) in (let TMP_49 \def 
(wadd TMP_45 TMP_48) in (let TMP_50 \def (weight_map TMP_49 t) in (let TMP_51 
\def (le_plus_l TMP_44 TMP_50) in (le_n_S TMP_33 TMP_42 
TMP_51))))))))))))))))))))))) in (let TMP_67 \def (\lambda (u: T).(\lambda 
(t: T).(let TMP_53 \def (\lambda (_: nat).O) in (let TMP_54 \def (weight_map 
TMP_53 u) in (let TMP_55 \def (\lambda (_: nat).O) in (let TMP_56 \def 
(weight_map TMP_55 u) in (let TMP_57 \def (\lambda (_: nat).O) in (let TMP_58 
\def (wadd TMP_57 O) in (let TMP_59 \def (weight_map TMP_58 t) in (let TMP_60 
\def (plus TMP_56 TMP_59) in (let TMP_61 \def (\lambda (_: nat).O) in (let 
TMP_62 \def (weight_map TMP_61 u) in (let TMP_63 \def (\lambda (_: nat).O) in 
(let TMP_64 \def (wadd TMP_63 O) in (let TMP_65 \def (weight_map TMP_64 t) in 
(let TMP_66 \def (le_plus_l TMP_62 TMP_65) in (le_n_S TMP_54 TMP_60 
TMP_66))))))))))))))))) in (let TMP_82 \def (\lambda (u: T).(\lambda (t: 
T).(let TMP_68 \def (\lambda (_: nat).O) in (let TMP_69 \def (weight_map 
TMP_68 u) in (let TMP_70 \def (\lambda (_: nat).O) in (let TMP_71 \def 
(weight_map TMP_70 u) in (let TMP_72 \def (\lambda (_: nat).O) in (let TMP_73 
\def (wadd TMP_72 O) in (let TMP_74 \def (weight_map TMP_73 t) in (let TMP_75 
\def (plus TMP_71 TMP_74) in (let TMP_76 \def (\lambda (_: nat).O) in (let 
TMP_77 \def (weight_map TMP_76 u) in (let TMP_78 \def (\lambda (_: nat).O) in 
(let TMP_79 \def (wadd TMP_78 O) in (let TMP_80 \def (weight_map TMP_79 t) in 
(let TMP_81 \def (le_plus_l TMP_77 TMP_80) in (le_n_S TMP_69 TMP_75 
TMP_81))))))))))))))))) in (B_ind TMP_31 TMP_52 TMP_67 TMP_82 b)))))) in (let 
TMP_96 \def (\lambda (_: F).(\lambda (u: T).(\lambda (t: T).(let TMP_84 \def 
(\lambda (_: nat).O) in (let TMP_85 \def (weight_map TMP_84 u) in (let TMP_86 
\def (\lambda (_: nat).O) in (let TMP_87 \def (weight_map TMP_86 u) in (let 
TMP_88 \def (\lambda (_: nat).O) in (let TMP_89 \def (weight_map TMP_88 t) in 
(let TMP_90 \def (plus TMP_87 TMP_89) in (let TMP_91 \def (\lambda (_: 
nat).O) in (let TMP_92 \def (weight_map TMP_91 u) in (let TMP_93 \def 
(\lambda (_: nat).O) in (let TMP_94 \def (weight_map TMP_93 t) in (let TMP_95 
\def (le_plus_l TMP_92 TMP_94) in (le_n_S TMP_85 TMP_90 
TMP_95)))))))))))))))) in (K_ind TMP_6 TMP_83 TMP_96 k)))).

theorem tlt_head_dx:
 \forall (k: K).(\forall (u: T).(\forall (t: T).(tlt t (THead k u t))))
\def
 \lambda (k: K).(let TMP_6 \def (\lambda (k0: K).(\forall (u: T).(\forall (t: 
T).(let TMP_1 \def (\lambda (_: nat).O) in (let TMP_2 \def (weight_map TMP_1 
t) in (let TMP_3 \def (\lambda (_: nat).O) in (let TMP_4 \def (THead k0 u t) 
in (let TMP_5 \def (weight_map TMP_3 TMP_4) in (lt TMP_2 TMP_5))))))))) in 
(let TMP_161 \def (\lambda (b: B).(let TMP_31 \def (\lambda (b0: B).(\forall 
(u: T).(\forall (t: T).(let TMP_7 \def (\lambda (_: nat).O) in (let TMP_8 
\def (weight_map TMP_7 t) in (let TMP_30 \def (match b0 with [Abbr 
\Rightarrow (let TMP_21 \def (\lambda (_: nat).O) in (let TMP_22 \def 
(weight_map TMP_21 u) in (let TMP_23 \def (\lambda (_: nat).O) in (let TMP_24 
\def (\lambda (_: nat).O) in (let TMP_25 \def (weight_map TMP_24 u) in (let 
TMP_26 \def (S TMP_25) in (let TMP_27 \def (wadd TMP_23 TMP_26) in (let 
TMP_28 \def (weight_map TMP_27 t) in (let TMP_29 \def (plus TMP_22 TMP_28) in 
(S TMP_29)))))))))) | Abst \Rightarrow (let TMP_15 \def (\lambda (_: nat).O) 
in (let TMP_16 \def (weight_map TMP_15 u) in (let TMP_17 \def (\lambda (_: 
nat).O) in (let TMP_18 \def (wadd TMP_17 O) in (let TMP_19 \def (weight_map 
TMP_18 t) in (let TMP_20 \def (plus TMP_16 TMP_19) in (S TMP_20))))))) | Void 
\Rightarrow (let TMP_9 \def (\lambda (_: nat).O) in (let TMP_10 \def 
(weight_map TMP_9 u) in (let TMP_11 \def (\lambda (_: nat).O) in (let TMP_12 
\def (wadd TMP_11 O) in (let TMP_13 \def (weight_map TMP_12 t) in (let TMP_14 
\def (plus TMP_10 TMP_13) in (S TMP_14)))))))]) in (lt TMP_8 TMP_30))))))) in 
(let TMP_106 \def (\lambda (u: T).(\lambda (t: T).(let TMP_32 \def (\lambda 
(_: nat).O) in (let TMP_33 \def (weight_map TMP_32 t) in (let TMP_34 \def 
(\lambda (_: nat).O) in (let TMP_35 \def (weight_map TMP_34 t) in (let TMP_36 
\def (S TMP_35) in (let TMP_37 \def (\lambda (_: nat).O) in (let TMP_38 \def 
(weight_map TMP_37 u) in (let TMP_39 \def (\lambda (_: nat).O) in (let TMP_40 
\def (\lambda (_: nat).O) in (let TMP_41 \def (weight_map TMP_40 u) in (let 
TMP_42 \def (S TMP_41) in (let TMP_43 \def (wadd TMP_39 TMP_42) in (let 
TMP_44 \def (weight_map TMP_43 t) in (let TMP_45 \def (plus TMP_38 TMP_44) in 
(let TMP_46 \def (S TMP_45) in (let TMP_47 \def (\lambda (_: nat).O) in (let 
TMP_48 \def (weight_map TMP_47 t) in (let TMP_49 \def (lt_n_Sn TMP_48) in 
(let TMP_50 \def (\lambda (_: nat).O) in (let TMP_51 \def (weight_map TMP_50 
t) in (let TMP_52 \def (\lambda (_: nat).O) in (let TMP_53 \def (weight_map 
TMP_52 u) in (let TMP_54 \def (\lambda (_: nat).O) in (let TMP_55 \def 
(\lambda (_: nat).O) in (let TMP_56 \def (weight_map TMP_55 u) in (let TMP_57 
\def (S TMP_56) in (let TMP_58 \def (wadd TMP_54 TMP_57) in (let TMP_59 \def 
(weight_map TMP_58 t) in (let TMP_60 \def (plus TMP_53 TMP_59) in (let TMP_61 
\def (\lambda (_: nat).O) in (let TMP_62 \def (weight_map TMP_61 t) in (let 
TMP_63 \def (\lambda (_: nat).O) in (let TMP_64 \def (\lambda (_: nat).O) in 
(let TMP_65 \def (weight_map TMP_64 u) in (let TMP_66 \def (S TMP_65) in (let 
TMP_67 \def (wadd TMP_63 TMP_66) in (let TMP_68 \def (weight_map TMP_67 t) in 
(let TMP_69 \def (\lambda (_: nat).O) in (let TMP_70 \def (weight_map TMP_69 
u) in (let TMP_71 \def (\lambda (_: nat).O) in (let TMP_72 \def (\lambda (_: 
nat).O) in (let TMP_73 \def (weight_map TMP_72 u) in (let TMP_74 \def (S 
TMP_73) in (let TMP_75 \def (wadd TMP_71 TMP_74) in (let TMP_76 \def 
(weight_map TMP_75 t) in (let TMP_77 \def (plus TMP_70 TMP_76) in (let TMP_78 
\def (\lambda (_: nat).O) in (let TMP_79 \def (wadd TMP_78 O) in (let TMP_80 
\def (weight_map TMP_79 t) in (let TMP_87 \def (\lambda (n: nat).(let TMP_81 
\def (\lambda (_: nat).O) in (let TMP_82 \def (\lambda (_: nat).O) in (let 
TMP_83 \def (weight_map TMP_82 u) in (let TMP_84 \def (S TMP_83) in (let 
TMP_85 \def (wadd TMP_81 TMP_84) in (let TMP_86 \def (weight_map TMP_85 t) in 
(le n TMP_86)))))))) in (let TMP_88 \def (\lambda (_: nat).O) in (let TMP_89 
\def (weight_map TMP_88 u) in (let TMP_90 \def (weight_add_S t TMP_89) in 
(let TMP_91 \def (\lambda (_: nat).O) in (let TMP_92 \def (weight_map TMP_91 
t) in (let TMP_93 \def (weight_add_O t) in (let TMP_94 \def (eq_ind nat 
TMP_80 TMP_87 TMP_90 TMP_92 TMP_93) in (let TMP_95 \def (\lambda (_: nat).O) 
in (let TMP_96 \def (weight_map TMP_95 u) in (let TMP_97 \def (\lambda (_: 
nat).O) in (let TMP_98 \def (\lambda (_: nat).O) in (let TMP_99 \def 
(weight_map TMP_98 u) in (let TMP_100 \def (S TMP_99) in (let TMP_101 \def 
(wadd TMP_97 TMP_100) in (let TMP_102 \def (weight_map TMP_101 t) in (let 
TMP_103 \def (le_plus_r TMP_96 TMP_102) in (let TMP_104 \def (le_trans TMP_62 
TMP_68 TMP_77 TMP_94 TMP_103) in (let TMP_105 \def (le_n_S TMP_51 TMP_60 
TMP_104) in (lt_le_trans TMP_33 TMP_36 TMP_46 TMP_49 
TMP_105)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 in (let TMP_133 \def (\lambda (u: T).(\lambda (t: T).(let TMP_107 \def 
(\lambda (_: nat).O) in (let TMP_108 \def (weight_map TMP_107 t) in (let 
TMP_115 \def (\lambda (n: nat).(let TMP_109 \def (\lambda (_: nat).O) in (let 
TMP_110 \def (weight_map TMP_109 t) in (let TMP_111 \def (\lambda (_: nat).O) 
in (let TMP_112 \def (weight_map TMP_111 u) in (let TMP_113 \def (plus 
TMP_112 n) in (let TMP_114 \def (S TMP_113) in (lt TMP_110 TMP_114)))))))) in 
(let TMP_116 \def (\lambda (_: nat).O) in (let TMP_117 \def (weight_map 
TMP_116 t) in (let TMP_118 \def (\lambda (_: nat).O) in (let TMP_119 \def 
(weight_map TMP_118 u) in (let TMP_120 \def (\lambda (_: nat).O) in (let 
TMP_121 \def (weight_map TMP_120 t) in (let TMP_122 \def (plus TMP_119 
TMP_121) in (let TMP_123 \def (\lambda (_: nat).O) in (let TMP_124 \def 
(weight_map TMP_123 u) in (let TMP_125 \def (\lambda (_: nat).O) in (let 
TMP_126 \def (weight_map TMP_125 t) in (let TMP_127 \def (le_plus_r TMP_124 
TMP_126) in (let TMP_128 \def (le_n_S TMP_117 TMP_122 TMP_127) in (let 
TMP_129 \def (\lambda (_: nat).O) in (let TMP_130 \def (wadd TMP_129 O) in 
(let TMP_131 \def (weight_map TMP_130 t) in (let TMP_132 \def (weight_add_O 
t) in (eq_ind_r nat TMP_108 TMP_115 TMP_128 TMP_131 
TMP_132))))))))))))))))))))))) in (let TMP_160 \def (\lambda (u: T).(\lambda 
(t: T).(let TMP_134 \def (\lambda (_: nat).O) in (let TMP_135 \def 
(weight_map TMP_134 t) in (let TMP_142 \def (\lambda (n: nat).(let TMP_136 
\def (\lambda (_: nat).O) in (let TMP_137 \def (weight_map TMP_136 t) in (let 
TMP_138 \def (\lambda (_: nat).O) in (let TMP_139 \def (weight_map TMP_138 u) 
in (let TMP_140 \def (plus TMP_139 n) in (let TMP_141 \def (S TMP_140) in (lt 
TMP_137 TMP_141)))))))) in (let TMP_143 \def (\lambda (_: nat).O) in (let 
TMP_144 \def (weight_map TMP_143 t) in (let TMP_145 \def (\lambda (_: nat).O) 
in (let TMP_146 \def (weight_map TMP_145 u) in (let TMP_147 \def (\lambda (_: 
nat).O) in (let TMP_148 \def (weight_map TMP_147 t) in (let TMP_149 \def 
(plus TMP_146 TMP_148) in (let TMP_150 \def (\lambda (_: nat).O) in (let 
TMP_151 \def (weight_map TMP_150 u) in (let TMP_152 \def (\lambda (_: nat).O) 
in (let TMP_153 \def (weight_map TMP_152 t) in (let TMP_154 \def (le_plus_r 
TMP_151 TMP_153) in (let TMP_155 \def (le_n_S TMP_144 TMP_149 TMP_154) in 
(let TMP_156 \def (\lambda (_: nat).O) in (let TMP_157 \def (wadd TMP_156 O) 
in (let TMP_158 \def (weight_map TMP_157 t) in (let TMP_159 \def 
(weight_add_O t) in (eq_ind_r nat TMP_135 TMP_142 TMP_155 TMP_158 
TMP_159))))))))))))))))))))))) in (B_ind TMP_31 TMP_106 TMP_133 TMP_160 
b)))))) in (let TMP_174 \def (\lambda (_: F).(\lambda (u: T).(\lambda (t: 
T).(let TMP_162 \def (\lambda (_: nat).O) in (let TMP_163 \def (weight_map 
TMP_162 t) in (let TMP_164 \def (\lambda (_: nat).O) in (let TMP_165 \def 
(weight_map TMP_164 u) in (let TMP_166 \def (\lambda (_: nat).O) in (let 
TMP_167 \def (weight_map TMP_166 t) in (let TMP_168 \def (plus TMP_165 
TMP_167) in (let TMP_169 \def (\lambda (_: nat).O) in (let TMP_170 \def 
(weight_map TMP_169 u) in (let TMP_171 \def (\lambda (_: nat).O) in (let 
TMP_172 \def (weight_map TMP_171 t) in (let TMP_173 \def (le_plus_r TMP_170 
TMP_172) in (le_n_S TMP_163 TMP_168 TMP_173)))))))))))))))) in (K_ind TMP_6 
TMP_161 TMP_174 k)))).

