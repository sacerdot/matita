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

include "legacy_1/coq/fwd.ma".

theorem f_equal:
 \forall (A: Type[0]).(\forall (B: Type[0]).(\forall (f: ((A \to 
B))).(\forall (x: A).(\forall (y: A).((eq A x y) \to (eq B (f x) (f y)))))))
\def
 \lambda (A: Type[0]).(\lambda (B: Type[0]).(\lambda (f: ((A \to 
B))).(\lambda (x: A).(\lambda (y: A).(\lambda (H: (eq A x y)).(let TMP_12 
\def (\lambda (a: A).(let TMP_11 \def (f x) in (let TMP_10 \def (f a) in (eq 
B TMP_11 TMP_10)))) in (let TMP_8 \def (f x) in (let TMP_9 \def (refl_equal B 
TMP_8) in (eq_ind A x TMP_12 TMP_9 y H))))))))).

theorem f_equal2:
 \forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall (B: Type[0]).(\forall 
(f: ((A1 \to (A2 \to B)))).(\forall (x1: A1).(\forall (y1: A1).(\forall (x2: 
A2).(\forall (y2: A2).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to (eq B (f x1 x2) 
(f y1 y2)))))))))))
\def
 \lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda (B: Type[0]).(\lambda 
(f: ((A1 \to (A2 \to B)))).(\lambda (x1: A1).(\lambda (y1: A1).(\lambda (x2: 
A2).(\lambda (y2: A2).(\lambda (H: (eq A1 x1 y1)).(let TMP_21 \def (\lambda 
(a: A1).((eq A2 x2 y2) \to (let TMP_20 \def (f x1 x2) in (let TMP_19 \def (f 
a y2) in (eq B TMP_20 TMP_19))))) in (let TMP_18 \def (\lambda (H0: (eq A2 x2 
y2)).(let TMP_17 \def (\lambda (a: A2).(let TMP_16 \def (f x1 x2) in (let 
TMP_15 \def (f x1 a) in (eq B TMP_16 TMP_15)))) in (let TMP_13 \def (f x1 x2) 
in (let TMP_14 \def (refl_equal B TMP_13) in (eq_ind A2 x2 TMP_17 TMP_14 y2 
H0))))) in (eq_ind A1 x1 TMP_21 TMP_18 y1 H))))))))))).

theorem f_equal3:
 \forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall (A3: Type[0]).(\forall 
(B: Type[0]).(\forall (f: ((A1 \to (A2 \to (A3 \to B))))).(\forall (x1: 
A1).(\forall (y1: A1).(\forall (x2: A2).(\forall (y2: A2).(\forall (x3: 
A3).(\forall (y3: A3).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to ((eq A3 x3 y3) 
\to (eq B (f x1 x2 x3) (f y1 y2 y3)))))))))))))))
\def
 \lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda (A3: Type[0]).(\lambda 
(B: Type[0]).(\lambda (f: ((A1 \to (A2 \to (A3 \to B))))).(\lambda (x1: 
A1).(\lambda (y1: A1).(\lambda (x2: A2).(\lambda (y2: A2).(\lambda (x3: 
A3).(\lambda (y3: A3).(\lambda (H: (eq A1 x1 y1)).(let TMP_34 \def (\lambda 
(a: A1).((eq A2 x2 y2) \to ((eq A3 x3 y3) \to (let TMP_33 \def (f x1 x2 x3) 
in (let TMP_32 \def (f a y2 y3) in (eq B TMP_33 TMP_32)))))) in (let TMP_31 
\def (\lambda (H0: (eq A2 x2 y2)).(let TMP_30 \def (\lambda (a: A2).((eq A3 
x3 y3) \to (let TMP_29 \def (f x1 x2 x3) in (let TMP_28 \def (f x1 a y3) in 
(eq B TMP_29 TMP_28))))) in (let TMP_27 \def (\lambda (H1: (eq A3 x3 
y3)).(let TMP_26 \def (\lambda (a: A3).(let TMP_25 \def (f x1 x2 x3) in (let 
TMP_24 \def (f x1 x2 a) in (eq B TMP_25 TMP_24)))) in (let TMP_22 \def (f x1 
x2 x3) in (let TMP_23 \def (refl_equal B TMP_22) in (eq_ind A3 x3 TMP_26 
TMP_23 y3 H1))))) in (eq_ind A2 x2 TMP_30 TMP_27 y2 H0)))) in (eq_ind A1 x1 
TMP_34 TMP_31 y1 H)))))))))))))).

theorem sym_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).((eq A x y) \to (eq A y 
x))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (H: (eq A x 
y)).(let TMP_36 \def (\lambda (a: A).(eq A a x)) in (let TMP_35 \def 
(refl_equal A x) in (eq_ind A x TMP_36 TMP_35 y H)))))).

theorem eq_ind_r:
 \forall (A: Type[0]).(\forall (x: A).(\forall (P: ((A \to Prop))).((P x) \to 
(\forall (y: A).((eq A y x) \to (P y))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (P: ((A \to Prop))).(\lambda 
(H: (P x)).(\lambda (y: A).(\lambda (H0: (eq A y x)).(match (sym_eq A y x H0) 
in eq with [refl_equal \Rightarrow H])))))).

theorem trans_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).(\forall (z: A).((eq A 
x y) \to ((eq A y z) \to (eq A x z))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (z: 
A).(\lambda (H: (eq A x y)).(\lambda (H0: (eq A y z)).(let TMP_37 \def 
(\lambda (a: A).(eq A x a)) in (eq_ind A y TMP_37 H z H0))))))).

theorem sym_not_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).((not (eq A x y)) \to 
(not (eq A y x)))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (h1: (not (eq 
A x y))).(\lambda (h2: (eq A y x)).(let TMP_39 \def (\lambda (a: A).(eq A a 
y)) in (let TMP_38 \def (refl_equal A y) in (let TMP_40 \def (eq_ind A y 
TMP_39 TMP_38 x h2) in (h1 TMP_40)))))))).

theorem nat_double_ind:
 \forall (R: ((nat \to (nat \to Prop)))).(((\forall (n: nat).(R O n))) \to 
(((\forall (n: nat).(R (S n) O))) \to (((\forall (n: nat).(\forall (m: 
nat).((R n m) \to (R (S n) (S m)))))) \to (\forall (n: nat).(\forall (m: 
nat).(R n m))))))
\def
 \lambda (R: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (n: nat).(R O 
n)))).(\lambda (H0: ((\forall (n: nat).(R (S n) O)))).(\lambda (H1: ((\forall 
(n: nat).(\forall (m: nat).((R n m) \to (R (S n) (S m))))))).(\lambda (n: 
nat).(let TMP_47 \def (\lambda (n0: nat).(\forall (m: nat).(R n0 m))) in (let 
TMP_46 \def (\lambda (n0: nat).(\lambda (H2: ((\forall (m: nat).(R n0 
m)))).(\lambda (m: nat).(let TMP_45 \def (\lambda (n1: nat).(let TMP_44 \def 
(S n0) in (R TMP_44 n1))) in (let TMP_43 \def (H0 n0) in (let TMP_42 \def 
(\lambda (n1: nat).(\lambda (_: (R (S n0) n1)).(let TMP_41 \def (H2 n1) in 
(H1 n0 n1 TMP_41)))) in (nat_ind TMP_45 TMP_43 TMP_42 m))))))) in (nat_ind 
TMP_47 H TMP_46 n))))))).

theorem eq_add_S:
 \forall (n: nat).(\forall (m: nat).((eq nat (S n) (S m)) \to (eq nat n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (eq nat (S n) (S m))).(let 
TMP_49 \def (S n) in (let TMP_48 \def (S m) in (f_equal nat nat pred TMP_49 
TMP_48 H))))).

theorem O_S:
 \forall (n: nat).(not (eq nat O (S n)))
\def
 \lambda (n: nat).(\lambda (H: (eq nat O (S n))).(let TMP_53 \def (S n) in 
(let TMP_52 \def (\lambda (n0: nat).(IsSucc n0)) in (let TMP_50 \def (S n) in 
(let TMP_51 \def (sym_eq nat O TMP_50 H) in (eq_ind nat TMP_53 TMP_52 I O 
TMP_51)))))).

theorem not_eq_S:
 \forall (n: nat).(\forall (m: nat).((not (eq nat n m)) \to (not (eq nat (S 
n) (S m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (not (eq nat n m))).(\lambda 
(H0: (eq nat (S n) (S m))).(let TMP_54 \def (eq_add_S n m H0) in (H 
TMP_54))))).

theorem pred_Sn:
 \forall (m: nat).(eq nat m (pred (S m)))
\def
 \lambda (m: nat).(let TMP_55 \def (S m) in (let TMP_56 \def (pred TMP_55) in 
(refl_equal nat TMP_56))).

theorem S_pred:
 \forall (n: nat).(\forall (m: nat).((lt m n) \to (eq nat n (S (pred n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt m n)).(let TMP_68 \def 
(S m) in (let TMP_67 \def (\lambda (n0: nat).(let TMP_65 \def (pred n0) in 
(let TMP_66 \def (S TMP_65) in (eq nat n0 TMP_66)))) in (let TMP_61 \def (S 
m) in (let TMP_62 \def (pred TMP_61) in (let TMP_63 \def (S TMP_62) in (let 
TMP_64 \def (refl_equal nat TMP_63) in (let TMP_60 \def (\lambda (m0: 
nat).(\lambda (_: (le (S m) m0)).(\lambda (_: (eq nat m0 (S (pred m0)))).(let 
TMP_57 \def (S m0) in (let TMP_58 \def (pred TMP_57) in (let TMP_59 \def (S 
TMP_58) in (refl_equal nat TMP_59))))))) in (le_ind TMP_68 TMP_67 TMP_64 
TMP_60 n H)))))))))).

theorem le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((le m p) 
\to (le n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (le m p)).(let TMP_70 \def (\lambda (n0: nat).(le n n0)) in 
(let TMP_69 \def (\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda (IHle: 
(le n m0)).(le_S n m0 IHle)))) in (le_ind m TMP_70 H TMP_69 p H0))))))).

theorem le_trans_S:
 \forall (n: nat).(\forall (m: nat).((le (S n) m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) m)).(let TMP_73 
\def (S n) in (let TMP_71 \def (le_n n) in (let TMP_72 \def (le_S n n TMP_71) 
in (le_trans n TMP_73 m TMP_72 H)))))).

theorem le_n_S:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_81 \def 
(\lambda (n0: nat).(let TMP_80 \def (S n) in (let TMP_79 \def (S n0) in (le 
TMP_80 TMP_79)))) in (let TMP_77 \def (S n) in (let TMP_78 \def (le_n TMP_77) 
in (let TMP_76 \def (\lambda (m0: nat).(\lambda (_: (le n m0)).(\lambda 
(IHle: (le (S n) (S m0))).(let TMP_75 \def (S n) in (let TMP_74 \def (S m0) 
in (le_S TMP_75 TMP_74 IHle)))))) in (le_ind n TMP_81 TMP_78 TMP_76 m 
H))))))).

theorem le_O_n:
 \forall (n: nat).(le O n)
\def
 \lambda (n: nat).(let TMP_84 \def (\lambda (n0: nat).(le O n0)) in (let 
TMP_83 \def (le_n O) in (let TMP_82 \def (\lambda (n0: nat).(\lambda (IHn: 
(le O n0)).(le_S O n0 IHn))) in (nat_ind TMP_84 TMP_83 TMP_82 n)))).

theorem le_S_n:
 \forall (n: nat).(\forall (m: nat).((le (S n) (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) (S m))).(let 
TMP_92 \def (S n) in (let TMP_91 \def (\lambda (n0: nat).(let TMP_89 \def (S 
n) in (let TMP_90 \def (pred TMP_89) in (let TMP_88 \def (pred n0) in (le 
TMP_90 TMP_88))))) in (let TMP_87 \def (le_n n) in (let TMP_86 \def (\lambda 
(m0: nat).(\lambda (H0: (le (S n) m0)).(\lambda (_: (le n (pred 
m0))).(le_trans_S n m0 H0)))) in (let TMP_85 \def (S m) in (le_ind TMP_92 
TMP_91 TMP_87 TMP_86 TMP_85 H)))))))).

theorem le_Sn_O:
 \forall (n: nat).(not (le (S n) O))
\def
 \lambda (n: nat).(\lambda (H: (le (S n) O)).(let TMP_95 \def (S n) in (let 
TMP_94 \def (\lambda (n0: nat).(IsSucc n0)) in (let TMP_93 \def (\lambda (m: 
nat).(\lambda (_: (le (S n) m)).(\lambda (_: (IsSucc m)).I))) in (le_ind 
TMP_95 TMP_94 I TMP_93 O H))))).

theorem le_Sn_n:
 \forall (n: nat).(not (le (S n) n))
\def
 \lambda (n: nat).(let TMP_102 \def (\lambda (n0: nat).(let TMP_100 \def (S 
n0) in (let TMP_101 \def (le TMP_100 n0) in (not TMP_101)))) in (let TMP_99 
\def (le_Sn_O O) in (let TMP_98 \def (\lambda (n0: nat).(\lambda (IHn: (not 
(le (S n0) n0))).(\lambda (H: (le (S (S n0)) (S n0))).(let TMP_96 \def (S n0) 
in (let TMP_97 \def (le_S_n TMP_96 n0 H) in (IHn TMP_97)))))) in (nat_ind 
TMP_102 TMP_99 TMP_98 n)))).

theorem le_antisym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to ((le m n) \to (eq nat n 
m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (h: (le n m)).(let TMP_110 \def 
(\lambda (n0: nat).((le n0 n) \to (eq nat n n0))) in (let TMP_109 \def 
(\lambda (_: (le n n)).(refl_equal nat n)) in (let TMP_108 \def (\lambda (m0: 
nat).(\lambda (H: (le n m0)).(\lambda (_: (((le m0 n) \to (eq nat n 
m0)))).(\lambda (H1: (le (S m0) n)).(let TMP_106 \def (S m0) in (let TMP_107 
\def (eq nat n TMP_106) in (let TMP_103 \def (S m0) in (let H2 \def (le_trans 
TMP_103 n m0 H1 H) in (let H3 \def (le_Sn_n m0) in (let TMP_104 \def (\lambda 
(H4: (le (S m0) m0)).(H3 H4)) in (let TMP_105 \def (TMP_104 H2) in (False_ind 
TMP_107 TMP_105)))))))))))) in (le_ind n TMP_110 TMP_109 TMP_108 m h)))))).

theorem le_n_O_eq:
 \forall (n: nat).((le n O) \to (eq nat O n))
\def
 \lambda (n: nat).(\lambda (H: (le n O)).(let TMP_111 \def (le_O_n n) in 
(le_antisym O n TMP_111 H))).

theorem le_elim_rel:
 \forall (P: ((nat \to (nat \to Prop)))).(((\forall (p: nat).(P O p))) \to 
(((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p q) \to (P (S p) (S 
q))))))) \to (\forall (n: nat).(\forall (m: nat).((le n m) \to (P n m))))))
\def
 \lambda (P: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (p: nat).(P O 
p)))).(\lambda (H0: ((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p 
q) \to (P (S p) (S q)))))))).(\lambda (n: nat).(let TMP_125 \def (\lambda 
(n0: nat).(\forall (m: nat).((le n0 m) \to (P n0 m)))) in (let TMP_124 \def 
(\lambda (m: nat).(\lambda (_: (le O m)).(H m))) in (let TMP_123 \def 
(\lambda (n0: nat).(\lambda (IHn: ((\forall (m: nat).((le n0 m) \to (P n0 
m))))).(\lambda (m: nat).(\lambda (Le: (le (S n0) m)).(let TMP_122 \def (S 
n0) in (let TMP_121 \def (\lambda (n1: nat).(let TMP_120 \def (S n0) in (P 
TMP_120 n1))) in (let TMP_118 \def (le_n n0) in (let TMP_116 \def (le_n n0) 
in (let TMP_117 \def (IHn n0 TMP_116) in (let TMP_119 \def (H0 n0 n0 TMP_118 
TMP_117) in (let TMP_115 \def (\lambda (m0: nat).(\lambda (H1: (le (S n0) 
m0)).(\lambda (_: (P (S n0) m0)).(let TMP_114 \def (le_trans_S n0 m0 H1) in 
(let TMP_112 \def (le_trans_S n0 m0 H1) in (let TMP_113 \def (IHn m0 TMP_112) 
in (H0 n0 m0 TMP_114 TMP_113))))))) in (le_ind TMP_122 TMP_121 TMP_119 
TMP_115 m Le)))))))))))) in (nat_ind TMP_125 TMP_124 TMP_123 n))))))).

theorem lt_n_n:
 \forall (n: nat).(not (lt n n))
\def
 le_Sn_n.

theorem lt_n_S:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (lt (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(let TMP_126 \def 
(S n) in (le_n_S TMP_126 m H)))).

theorem lt_n_Sn:
 \forall (n: nat).(lt n (S n))
\def
 \lambda (n: nat).(let TMP_127 \def (S n) in (le_n TMP_127)).

theorem lt_S_n:
 \forall (n: nat).(\forall (m: nat).((lt (S n) (S m)) \to (lt n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (S n) (S m))).(let 
TMP_128 \def (S n) in (le_S_n TMP_128 m H)))).

theorem lt_n_O:
 \forall (n: nat).(not (lt n O))
\def
 le_Sn_O.

theorem lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (lt m p)).(let TMP_134 \def (S m) in (let TMP_133 \def 
(\lambda (n0: nat).(lt n n0)) in (let TMP_131 \def (S n) in (let TMP_132 \def 
(le_S TMP_131 m H) in (let TMP_130 \def (\lambda (m0: nat).(\lambda (_: (le 
(S m) m0)).(\lambda (IHle: (lt n m0)).(let TMP_129 \def (S n) in (le_S 
TMP_129 m0 IHle))))) in (le_ind TMP_134 TMP_133 TMP_132 TMP_130 p 
H0)))))))))).

theorem lt_O_Sn:
 \forall (n: nat).(lt O (S n))
\def
 \lambda (n: nat).(let TMP_135 \def (le_O_n n) in (le_n_S O n TMP_135)).

theorem lt_le_S:
 \forall (n: nat).(\forall (p: nat).((lt n p) \to (le (S n) p)))
\def
 \lambda (n: nat).(\lambda (p: nat).(\lambda (H: (lt n p)).H)).

theorem le_not_lt:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (not (lt m n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_141 \def 
(\lambda (n0: nat).(let TMP_140 \def (lt n0 n) in (not TMP_140))) in (let 
TMP_139 \def (lt_n_n n) in (let TMP_138 \def (\lambda (m0: nat).(\lambda (_: 
(le n m0)).(\lambda (IHle: (not (lt m0 n))).(\lambda (H1: (lt (S m0) n)).(let 
TMP_136 \def (S m0) in (let TMP_137 \def (le_trans_S TMP_136 n H1) in (IHle 
TMP_137))))))) in (le_ind n TMP_141 TMP_139 TMP_138 m H)))))).

theorem le_lt_n_Sm:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (lt n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_n_S n m H))).

theorem le_lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (lt m p)).(let TMP_146 \def (S m) in (let TMP_145 \def 
(\lambda (n0: nat).(lt n n0)) in (let TMP_144 \def (le_n_S n m H) in (let 
TMP_143 \def (\lambda (m0: nat).(\lambda (_: (le (S m) m0)).(\lambda (IHle: 
(lt n m0)).(let TMP_142 \def (S n) in (le_S TMP_142 m0 IHle))))) in (le_ind 
TMP_146 TMP_145 TMP_144 TMP_143 p H0))))))))).

theorem lt_le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((le m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (le m p)).(let TMP_149 \def (\lambda (n0: nat).(lt n n0)) 
in (let TMP_148 \def (\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda 
(IHle: (lt n m0)).(let TMP_147 \def (S n) in (le_S TMP_147 m0 IHle))))) in 
(le_ind m TMP_149 H TMP_148 p H0))))))).

theorem lt_le_weak:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(le_trans_S n m 
H))).

theorem lt_n_Sm_le:
 \forall (n: nat).(\forall (m: nat).((lt n (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n (S m))).(le_S_n n m 
H))).

theorem le_lt_or_eq:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (or (lt n m) (eq nat n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_162 \def 
(\lambda (n0: nat).(let TMP_161 \def (lt n n0) in (let TMP_160 \def (eq nat n 
n0) in (or TMP_161 TMP_160)))) in (let TMP_158 \def (lt n n) in (let TMP_157 
\def (eq nat n n) in (let TMP_156 \def (refl_equal nat n) in (let TMP_159 
\def (or_intror TMP_158 TMP_157 TMP_156) in (let TMP_155 \def (\lambda (m0: 
nat).(\lambda (H0: (le n m0)).(\lambda (_: (or (lt n m0) (eq nat n m0))).(let 
TMP_153 \def (S m0) in (let TMP_154 \def (lt n TMP_153) in (let TMP_151 \def 
(S m0) in (let TMP_152 \def (eq nat n TMP_151) in (let TMP_150 \def (le_n_S n 
m0 H0) in (or_introl TMP_154 TMP_152 TMP_150))))))))) in (le_ind n TMP_162 
TMP_159 TMP_155 m H))))))))).

theorem le_or_lt:
 \forall (n: nat).(\forall (m: nat).(or (le n m) (lt m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_204 \def (\lambda (n0: 
nat).(\lambda (n1: nat).(let TMP_203 \def (le n0 n1) in (let TMP_202 \def (lt 
n1 n0) in (or TMP_203 TMP_202))))) in (let TMP_201 \def (\lambda (n0: 
nat).(let TMP_200 \def (le O n0) in (let TMP_199 \def (lt n0 O) in (let 
TMP_198 \def (le_O_n n0) in (or_introl TMP_200 TMP_199 TMP_198))))) in (let 
TMP_197 \def (\lambda (n0: nat).(let TMP_195 \def (S n0) in (let TMP_196 \def 
(le TMP_195 O) in (let TMP_193 \def (S n0) in (let TMP_194 \def (lt O 
TMP_193) in (let TMP_191 \def (S n0) in (let TMP_190 \def (lt_O_Sn n0) in 
(let TMP_192 \def (lt_le_S O TMP_191 TMP_190) in (or_intror TMP_196 TMP_194 
TMP_192))))))))) in (let TMP_189 \def (\lambda (n0: nat).(\lambda (m0: 
nat).(\lambda (H: (or (le n0 m0) (lt m0 n0))).(let TMP_188 \def (le n0 m0) in 
(let TMP_187 \def (lt m0 n0) in (let TMP_184 \def (S n0) in (let TMP_183 \def 
(S m0) in (let TMP_185 \def (le TMP_184 TMP_183) in (let TMP_181 \def (S m0) 
in (let TMP_180 \def (S n0) in (let TMP_182 \def (lt TMP_181 TMP_180) in (let 
TMP_186 \def (or TMP_185 TMP_182) in (let TMP_179 \def (\lambda (H0: (le n0 
m0)).(let TMP_177 \def (S n0) in (let TMP_176 \def (S m0) in (let TMP_178 
\def (le TMP_177 TMP_176) in (let TMP_174 \def (S m0) in (let TMP_173 \def (S 
n0) in (let TMP_175 \def (lt TMP_174 TMP_173) in (let TMP_172 \def (le_n_S n0 
m0 H0) in (or_introl TMP_178 TMP_175 TMP_172))))))))) in (let TMP_171 \def 
(\lambda (H0: (lt m0 n0)).(let TMP_169 \def (S n0) in (let TMP_168 \def (S 
m0) in (let TMP_170 \def (le TMP_169 TMP_168) in (let TMP_166 \def (S m0) in 
(let TMP_165 \def (S n0) in (let TMP_167 \def (lt TMP_166 TMP_165) in (let 
TMP_163 \def (S m0) in (let TMP_164 \def (le_n_S TMP_163 n0 H0) in (or_intror 
TMP_170 TMP_167 TMP_164)))))))))) in (or_ind TMP_188 TMP_187 TMP_186 TMP_179 
TMP_171 H))))))))))))))) in (nat_double_ind TMP_204 TMP_201 TMP_197 TMP_189 n 
m)))))).

theorem plus_n_O:
 \forall (n: nat).(eq nat n (plus n O))
\def
 \lambda (n: nat).(let TMP_209 \def (\lambda (n0: nat).(let TMP_208 \def 
(plus n0 O) in (eq nat n0 TMP_208))) in (let TMP_207 \def (refl_equal nat O) 
in (let TMP_206 \def (\lambda (n0: nat).(\lambda (H: (eq nat n0 (plus n0 
O))).(let TMP_205 \def (plus n0 O) in (f_equal nat nat S n0 TMP_205 H)))) in 
(nat_ind TMP_209 TMP_207 TMP_206 n)))).

theorem plus_n_Sm:
 \forall (n: nat).(\forall (m: nat).(eq nat (S (plus n m)) (plus n (S m))))
\def
 \lambda (m: nat).(\lambda (n: nat).(let TMP_221 \def (\lambda (n0: nat).(let 
TMP_219 \def (plus n0 n) in (let TMP_220 \def (S TMP_219) in (let TMP_217 
\def (S n) in (let TMP_218 \def (plus n0 TMP_217) in (eq nat TMP_220 
TMP_218)))))) in (let TMP_215 \def (S n) in (let TMP_216 \def (refl_equal nat 
TMP_215) in (let TMP_214 \def (\lambda (n0: nat).(\lambda (H: (eq nat (S 
(plus n0 n)) (plus n0 (S n)))).(let TMP_212 \def (plus n0 n) in (let TMP_213 
\def (S TMP_212) in (let TMP_210 \def (S n) in (let TMP_211 \def (plus n0 
TMP_210) in (f_equal nat nat S TMP_213 TMP_211 H))))))) in (nat_ind TMP_221 
TMP_216 TMP_214 m)))))).

theorem plus_sym:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus n m) (plus m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_237 \def (\lambda (n0: nat).(let 
TMP_236 \def (plus n0 m) in (let TMP_235 \def (plus m n0) in (eq nat TMP_236 
TMP_235)))) in (let TMP_234 \def (plus_n_O m) in (let TMP_233 \def (\lambda 
(y: nat).(\lambda (H: (eq nat (plus y m) (plus m y))).(let TMP_231 \def (plus 
m y) in (let TMP_232 \def (S TMP_231) in (let TMP_230 \def (\lambda (n0: 
nat).(let TMP_228 \def (plus y m) in (let TMP_229 \def (S TMP_228) in (eq nat 
TMP_229 n0)))) in (let TMP_226 \def (plus y m) in (let TMP_225 \def (plus m 
y) in (let TMP_227 \def (f_equal nat nat S TMP_226 TMP_225 H) in (let TMP_223 
\def (S y) in (let TMP_224 \def (plus m TMP_223) in (let TMP_222 \def 
(plus_n_Sm m y) in (eq_ind nat TMP_232 TMP_230 TMP_227 TMP_224 
TMP_222)))))))))))) in (nat_ind TMP_237 TMP_234 TMP_233 n))))).

theorem plus_Snm_nSm:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus (S n) m) (plus n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_257 \def (plus m n) in (let 
TMP_256 \def (\lambda (n0: nat).(let TMP_255 \def (S n0) in (let TMP_253 \def 
(S m) in (let TMP_254 \def (plus n TMP_253) in (eq nat TMP_255 TMP_254))))) 
in (let TMP_250 \def (S m) in (let TMP_251 \def (plus TMP_250 n) in (let 
TMP_249 \def (\lambda (n0: nat).(let TMP_247 \def (plus m n) in (let TMP_248 
\def (S TMP_247) in (eq nat TMP_248 n0)))) in (let TMP_244 \def (S m) in (let 
TMP_245 \def (plus TMP_244 n) in (let TMP_246 \def (refl_equal nat TMP_245) 
in (let TMP_242 \def (S m) in (let TMP_243 \def (plus n TMP_242) in (let 
TMP_240 \def (S m) in (let TMP_241 \def (plus_sym n TMP_240) in (let TMP_252 
\def (eq_ind_r nat TMP_251 TMP_249 TMP_246 TMP_243 TMP_241) in (let TMP_239 
\def (plus n m) in (let TMP_238 \def (plus_sym n m) in (eq_ind_r nat TMP_257 
TMP_256 TMP_252 TMP_239 TMP_238))))))))))))))))).

theorem plus_assoc_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus n (plus m 
p)) (plus (plus n m) p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_269 \def 
(\lambda (n0: nat).(let TMP_267 \def (plus m p) in (let TMP_268 \def (plus n0 
TMP_267) in (let TMP_265 \def (plus n0 m) in (let TMP_266 \def (plus TMP_265 
p) in (eq nat TMP_268 TMP_266)))))) in (let TMP_263 \def (plus m p) in (let 
TMP_264 \def (refl_equal nat TMP_263) in (let TMP_262 \def (\lambda (n0: 
nat).(\lambda (H: (eq nat (plus n0 (plus m p)) (plus (plus n0 m) p))).(let 
TMP_260 \def (plus m p) in (let TMP_261 \def (plus n0 TMP_260) in (let 
TMP_258 \def (plus n0 m) in (let TMP_259 \def (plus TMP_258 p) in (f_equal 
nat nat S TMP_261 TMP_259 H))))))) in (nat_ind TMP_269 TMP_264 TMP_262 
n))))))).

theorem plus_assoc_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus (plus n 
m) p) (plus n (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_273 \def (plus 
m p) in (let TMP_274 \def (plus n TMP_273) in (let TMP_271 \def (plus n m) in 
(let TMP_272 \def (plus TMP_271 p) in (let TMP_270 \def (plus_assoc_l n m p) 
in (sym_eq nat TMP_274 TMP_272 TMP_270)))))))).

theorem simpl_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus n m) 
(plus n p)) \to (eq nat m p))))
\def
 \lambda (n: nat).(let TMP_287 \def (\lambda (n0: nat).(\forall (m: 
nat).(\forall (p: nat).((eq nat (plus n0 m) (plus n0 p)) \to (eq nat m p))))) 
in (let TMP_286 \def (\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat 
m p)).H))) in (let TMP_285 \def (\lambda (n0: nat).(\lambda (IHn: ((\forall 
(m: nat).(\forall (p: nat).((eq nat (plus n0 m) (plus n0 p)) \to (eq nat m 
p)))))).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat (S (plus n0 
m)) (S (plus n0 p)))).(let TMP_283 \def (plus n0 m) in (let TMP_282 \def 
(plus n0 p) in (let TMP_280 \def (plus n0) in (let TMP_279 \def (plus n0 m) 
in (let TMP_278 \def (plus n0 p) in (let TMP_276 \def (plus n0 m) in (let 
TMP_275 \def (plus n0 p) in (let TMP_277 \def (eq_add_S TMP_276 TMP_275 H) in 
(let TMP_281 \def (f_equal nat nat TMP_280 TMP_279 TMP_278 TMP_277) in (let 
TMP_284 \def (IHn TMP_283 TMP_282 TMP_281) in (IHn m p 
TMP_284)))))))))))))))) in (nat_ind TMP_287 TMP_286 TMP_285 n)))).

theorem minus_n_O:
 \forall (n: nat).(eq nat n (minus n O))
\def
 \lambda (n: nat).(let TMP_292 \def (\lambda (n0: nat).(let TMP_291 \def 
(minus n0 O) in (eq nat n0 TMP_291))) in (let TMP_290 \def (refl_equal nat O) 
in (let TMP_289 \def (\lambda (n0: nat).(\lambda (_: (eq nat n0 (minus n0 
O))).(let TMP_288 \def (S n0) in (refl_equal nat TMP_288)))) in (nat_ind 
TMP_292 TMP_290 TMP_289 n)))).

theorem minus_n_n:
 \forall (n: nat).(eq nat O (minus n n))
\def
 \lambda (n: nat).(let TMP_296 \def (\lambda (n0: nat).(let TMP_295 \def 
(minus n0 n0) in (eq nat O TMP_295))) in (let TMP_294 \def (refl_equal nat O) 
in (let TMP_293 \def (\lambda (n0: nat).(\lambda (IHn: (eq nat O (minus n0 
n0))).IHn)) in (nat_ind TMP_296 TMP_294 TMP_293 n)))).

theorem minus_Sn_m:
 \forall (n: nat).(\forall (m: nat).((le m n) \to (eq nat (S (minus n m)) 
(minus (S n) m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le m n)).(let TMP_307 \def 
(\lambda (n0: nat).(\lambda (n1: nat).(let TMP_305 \def (minus n1 n0) in (let 
TMP_306 \def (S TMP_305) in (let TMP_303 \def (S n1) in (let TMP_304 \def 
(minus TMP_303 n0) in (eq nat TMP_306 TMP_304))))))) in (let TMP_302 \def 
(\lambda (p: nat).(let TMP_301 \def (minus p O) in (let TMP_299 \def (minus p 
O) in (let TMP_298 \def (minus_n_O p) in (let TMP_300 \def (sym_eq nat p 
TMP_299 TMP_298) in (f_equal nat nat S TMP_301 p TMP_300)))))) in (let 
TMP_297 \def (\lambda (p: nat).(\lambda (q: nat).(\lambda (_: (le p 
q)).(\lambda (H0: (eq nat (S (minus q p)) (match p with [O \Rightarrow (S q) 
| (S l) \Rightarrow (minus q l)]))).H0)))) in (le_elim_rel TMP_307 TMP_302 
TMP_297 m n Le)))))).

theorem plus_minus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat n (plus m p)) 
\to (eq nat p (minus n m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_322 \def 
(\lambda (n0: nat).(\lambda (n1: nat).((eq nat n1 (plus n0 p)) \to (let 
TMP_321 \def (minus n1 n0) in (eq nat p TMP_321))))) in (let TMP_320 \def 
(\lambda (n0: nat).(\lambda (H: (eq nat n0 p)).(let TMP_319 \def (\lambda 
(n1: nat).(eq nat p n1)) in (let TMP_318 \def (sym_eq nat n0 p H) in (let 
TMP_317 \def (minus n0 O) in (let TMP_316 \def (minus_n_O n0) in (eq_ind nat 
n0 TMP_319 TMP_318 TMP_317 TMP_316))))))) in (let TMP_315 \def (\lambda (n0: 
nat).(\lambda (H: (eq nat O (S (plus n0 p)))).(let TMP_314 \def (eq nat p O) 
in (let H0 \def H in (let TMP_311 \def (plus n0 p) in (let H1 \def (O_S 
TMP_311) in (let TMP_312 \def (\lambda (H2: (eq nat O (S (plus n0 p)))).(H1 
H2)) in (let TMP_313 \def (TMP_312 H0) in (False_ind TMP_314 TMP_313))))))))) 
in (let TMP_310 \def (\lambda (n0: nat).(\lambda (m0: nat).(\lambda (H: (((eq 
nat m0 (plus n0 p)) \to (eq nat p (minus m0 n0))))).(\lambda (H0: (eq nat (S 
m0) (S (plus n0 p)))).(let TMP_308 \def (plus n0 p) in (let TMP_309 \def 
(eq_add_S m0 TMP_308 H0) in (H TMP_309))))))) in (nat_double_ind TMP_322 
TMP_320 TMP_315 TMP_310 m n))))))).

theorem minus_plus:
 \forall (n: nat).(\forall (m: nat).(eq nat (minus (plus n m) n) m))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_327 \def (plus n m) in (let 
TMP_328 \def (minus TMP_327 n) in (let TMP_325 \def (plus n m) in (let 
TMP_323 \def (plus n m) in (let TMP_324 \def (refl_equal nat TMP_323) in (let 
TMP_326 \def (plus_minus TMP_325 n m TMP_324) in (sym_eq nat m TMP_328 
TMP_326)))))))).

theorem le_pred_n:
 \forall (n: nat).(le (pred n) n)
\def
 \lambda (n: nat).(let TMP_335 \def (\lambda (n0: nat).(let TMP_334 \def 
(pred n0) in (le TMP_334 n0))) in (let TMP_333 \def (le_n O) in (let TMP_332 
\def (\lambda (n0: nat).(\lambda (_: (le (pred n0) n0)).(let TMP_330 \def (S 
n0) in (let TMP_331 \def (pred TMP_330) in (let TMP_329 \def (le_n n0) in 
(le_S TMP_331 n0 TMP_329)))))) in (nat_ind TMP_335 TMP_333 TMP_332 n)))).

theorem le_plus_l:
 \forall (n: nat).(\forall (m: nat).(le n (plus n m)))
\def
 \lambda (n: nat).(let TMP_341 \def (\lambda (n0: nat).(\forall (m: nat).(let 
TMP_340 \def (plus n0 m) in (le n0 TMP_340)))) in (let TMP_339 \def (\lambda 
(m: nat).(le_O_n m)) in (let TMP_338 \def (\lambda (n0: nat).(\lambda (IHn: 
((\forall (m: nat).(le n0 (plus n0 m))))).(\lambda (m: nat).(let TMP_337 \def 
(plus n0 m) in (let TMP_336 \def (IHn m) in (le_n_S n0 TMP_337 TMP_336)))))) 
in (nat_ind TMP_341 TMP_339 TMP_338 n)))).

theorem le_plus_r:
 \forall (n: nat).(\forall (m: nat).(le m (plus n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_346 \def (\lambda (n0: nat).(let 
TMP_345 \def (plus n0 m) in (le m TMP_345))) in (let TMP_344 \def (le_n m) in 
(let TMP_343 \def (\lambda (n0: nat).(\lambda (H: (le m (plus n0 m))).(let 
TMP_342 \def (plus n0 m) in (le_S m TMP_342 H)))) in (nat_ind TMP_346 TMP_344 
TMP_343 n))))).

theorem simpl_le_plus_l:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((le (plus p n) (plus p 
m)) \to (le n m))))
\def
 \lambda (p: nat).(let TMP_352 \def (\lambda (n: nat).(\forall (n0: 
nat).(\forall (m: nat).((le (plus n n0) (plus n m)) \to (le n0 m))))) in (let 
TMP_351 \def (\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).H))) 
in (let TMP_350 \def (\lambda (p0: nat).(\lambda (IHp: ((\forall (n: 
nat).(\forall (m: nat).((le (plus p0 n) (plus p0 m)) \to (le n 
m)))))).(\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S (plus p0 n)) 
(S (plus p0 m)))).(let TMP_348 \def (plus p0 n) in (let TMP_347 \def (plus p0 
m) in (let TMP_349 \def (le_S_n TMP_348 TMP_347 H) in (IHp n m 
TMP_349))))))))) in (nat_ind TMP_352 TMP_351 TMP_350 p)))).

theorem le_plus_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le n 
(plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(let TMP_354 \def (plus m p) in (let TMP_353 \def (le_plus_l m p) in 
(le_trans n m TMP_354 H TMP_353)))))).

theorem le_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_362 \def 
(\lambda (n0: nat).((le n m) \to (let TMP_361 \def (plus n0 n) in (let 
TMP_360 \def (plus n0 m) in (le TMP_361 TMP_360))))) in (let TMP_359 \def 
(\lambda (H: (le n m)).H) in (let TMP_358 \def (\lambda (p0: nat).(\lambda 
(IHp: (((le n m) \to (le (plus p0 n) (plus p0 m))))).(\lambda (H: (le n 
m)).(let TMP_357 \def (plus p0 n) in (let TMP_356 \def (plus p0 m) in (let 
TMP_355 \def (IHp H) in (le_n_S TMP_357 TMP_356 TMP_355))))))) in (nat_ind 
TMP_362 TMP_359 TMP_358 p)))))).

theorem le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((le p q) \to (le (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le p q)).(let TMP_369 \def 
(\lambda (n0: nat).(let TMP_368 \def (plus n p) in (let TMP_367 \def (plus n0 
q) in (le TMP_368 TMP_367)))) in (let TMP_366 \def (le_reg_l p q n H0) in 
(let TMP_365 \def (\lambda (m0: nat).(\lambda (_: (le n m0)).(\lambda (H2: 
(le (plus n p) (plus m0 q))).(let TMP_364 \def (plus n p) in (let TMP_363 
\def (plus m0 q) in (le_S TMP_364 TMP_363 H2)))))) in (le_ind n TMP_369 
TMP_366 TMP_365 m H))))))))).

theorem le_plus_minus:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus n (minus m 
n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le n m)).(let TMP_376 \def 
(\lambda (n0: nat).(\lambda (n1: nat).(let TMP_374 \def (minus n1 n0) in (let 
TMP_375 \def (plus n0 TMP_374) in (eq nat n1 TMP_375))))) in (let TMP_373 
\def (\lambda (p: nat).(minus_n_O p)) in (let TMP_372 \def (\lambda (p: 
nat).(\lambda (q: nat).(\lambda (_: (le p q)).(\lambda (H0: (eq nat q (plus p 
(minus q p)))).(let TMP_370 \def (minus q p) in (let TMP_371 \def (plus p 
TMP_370) in (f_equal nat nat S q TMP_371 H0))))))) in (le_elim_rel TMP_376 
TMP_373 TMP_372 n m Le)))))).

theorem le_plus_minus_r:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat (plus n (minus m 
n)) m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_378 \def 
(minus m n) in (let TMP_379 \def (plus n TMP_378) in (let TMP_377 \def 
(le_plus_minus n m H) in (sym_eq nat m TMP_379 TMP_377)))))).

theorem simpl_lt_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt (plus p n) (plus p 
m)) \to (lt n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_386 \def 
(\lambda (n0: nat).((lt (plus n0 n) (plus n0 m)) \to (lt n m))) in (let 
TMP_385 \def (\lambda (H: (lt n m)).H) in (let TMP_384 \def (\lambda (p0: 
nat).(\lambda (IHp: (((lt (plus p0 n) (plus p0 m)) \to (lt n m)))).(\lambda 
(H: (lt (S (plus p0 n)) (S (plus p0 m)))).(let TMP_381 \def (plus p0 n) in 
(let TMP_382 \def (S TMP_381) in (let TMP_380 \def (plus p0 m) in (let 
TMP_383 \def (le_S_n TMP_382 TMP_380 H) in (IHp TMP_383)))))))) in (nat_ind 
TMP_386 TMP_385 TMP_384 p)))))).

theorem lt_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_394 \def 
(\lambda (n0: nat).((lt n m) \to (let TMP_393 \def (plus n0 n) in (let 
TMP_392 \def (plus n0 m) in (lt TMP_393 TMP_392))))) in (let TMP_391 \def 
(\lambda (H: (lt n m)).H) in (let TMP_390 \def (\lambda (p0: nat).(\lambda 
(IHp: (((lt n m) \to (lt (plus p0 n) (plus p0 m))))).(\lambda (H: (lt n 
m)).(let TMP_389 \def (plus p0 n) in (let TMP_388 \def (plus p0 m) in (let 
TMP_387 \def (IHp H) in (lt_n_S TMP_389 TMP_388 TMP_387))))))) in (nat_ind 
TMP_394 TMP_391 TMP_390 p)))))).

theorem lt_reg_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
n p) (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(let TMP_411 \def (plus p n) in (let TMP_410 \def (\lambda (n0: nat).(let 
TMP_409 \def (plus m p) in (lt n0 TMP_409))) in (let TMP_407 \def (plus p m) 
in (let TMP_406 \def (\lambda (n0: nat).(let TMP_405 \def (plus p n) in (lt 
TMP_405 n0))) in (let TMP_403 \def (\lambda (n0: nat).(let TMP_402 \def (plus 
n0 n) in (let TMP_401 \def (plus n0 m) in (lt TMP_402 TMP_401)))) in (let 
TMP_400 \def (\lambda (n0: nat).(\lambda (_: (lt (plus n0 n) (plus n0 
m))).(let TMP_399 \def (S n0) in (lt_reg_l n m TMP_399 H)))) in (let TMP_404 
\def (nat_ind TMP_403 H TMP_400 p) in (let TMP_398 \def (plus m p) in (let 
TMP_397 \def (plus_sym m p) in (let TMP_408 \def (eq_ind_r nat TMP_407 
TMP_406 TMP_404 TMP_398 TMP_397) in (let TMP_396 \def (plus n p) in (let 
TMP_395 \def (plus_sym n p) in (eq_ind_r nat TMP_411 TMP_410 TMP_408 TMP_396 
TMP_395)))))))))))))))).

theorem le_lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le (S p) q)).(let TMP_419 \def (S 
p) in (let TMP_420 \def (plus n TMP_419) in (let TMP_418 \def (\lambda (n0: 
nat).(let TMP_417 \def (plus m q) in (le n0 TMP_417))) in (let TMP_415 \def 
(S p) in (let TMP_416 \def (le_plus_plus n m TMP_415 q H H0) in (let TMP_413 
\def (S n) in (let TMP_414 \def (plus TMP_413 p) in (let TMP_412 \def 
(plus_Snm_nSm n p) in (eq_ind_r nat TMP_420 TMP_418 TMP_416 TMP_414 
TMP_412)))))))))))))).

theorem lt_le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((le p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le (S n) m)).(\lambda (H0: (le p q)).(let TMP_421 \def (S 
n) in (le_plus_plus TMP_421 m p q H H0))))))).

theorem lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (lt n m)).(\lambda (H0: (lt p q)).(let TMP_422 \def 
(lt_le_weak p q H0) in (lt_le_plus_plus n m p q H TMP_422))))))).

theorem well_founded_ltof:
 \forall (A: Type[0]).(\forall (f: ((A \to nat))).(well_founded A (ltof A f)))
\def
 \lambda (A: Type[0]).(\lambda (f: ((A \to nat))).(let H \def (\lambda (n: 
nat).(let TMP_438 \def (\lambda (n0: nat).(\forall (a: A).((lt (f a) n0) \to 
(let TMP_437 \def (ltof A f) in (Acc A TMP_437 a))))) in (let TMP_436 \def 
(\lambda (a: A).(\lambda (H: (lt (f a) O)).(let TMP_434 \def (ltof A f) in 
(let TMP_435 \def (Acc A TMP_434 a) in (let H0 \def H in (let TMP_431 \def (f 
a) in (let H1 \def (lt_n_O TMP_431) in (let TMP_432 \def (\lambda (H2: (lt (f 
a) O)).(H1 H2)) in (let TMP_433 \def (TMP_432 H0) in (False_ind TMP_435 
TMP_433)))))))))) in (let TMP_430 \def (\lambda (n0: nat).(\lambda (IHn: 
((\forall (a: A).((lt (f a) n0) \to (Acc A (ltof A f) a))))).(\lambda (a: 
A).(\lambda (ltSma: (lt (f a) (S n0))).(let TMP_429 \def (ltof A f) in (let 
TMP_428 \def (\lambda (b: A).(\lambda (ltfafb: (lt (f b) (f a))).(let TMP_426 
\def (f b) in (let TMP_425 \def (f a) in (let TMP_423 \def (f a) in (let 
TMP_424 \def (lt_n_Sm_le TMP_423 n0 ltSma) in (let TMP_427 \def (lt_le_trans 
TMP_426 TMP_425 n0 ltfafb TMP_424) in (IHn b TMP_427)))))))) in (Acc_intro A 
TMP_429 a TMP_428))))))) in (nat_ind TMP_438 TMP_436 TMP_430 n))))) in 
(\lambda (a: A).(let TMP_442 \def (f a) in (let TMP_443 \def (S TMP_442) in 
(let TMP_439 \def (f a) in (let TMP_440 \def (S TMP_439) in (let TMP_441 \def 
(le_n TMP_440) in (H TMP_443 a TMP_441))))))))).

theorem lt_wf:
 well_founded nat lt
\def
 let TMP_444 \def (\lambda (m: nat).m) in (well_founded_ltof nat TMP_444).

theorem lt_wf_ind:
 \forall (p: nat).(\forall (P: ((nat \to Prop))).(((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n)))) \to (P p)))
\def
 \lambda (p: nat).(\lambda (P: ((nat \to Prop))).(\lambda (H: ((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n))))).(let TMP_447 
\def (\lambda (n: nat).(P n)) in (let TMP_446 \def (\lambda (x: nat).(\lambda 
(_: ((\forall (y: nat).((lt y x) \to (Acc nat lt y))))).(\lambda (H1: 
((\forall (y: nat).((lt y x) \to (P y))))).(H x H1)))) in (let TMP_445 \def 
(lt_wf p) in (Acc_ind nat lt TMP_447 TMP_446 p TMP_445)))))).

