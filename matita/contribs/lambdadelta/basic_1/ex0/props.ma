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

include "basic_1/ex0/fwd.ma".

include "basic_1/leq/fwd.ma".

include "basic_1/aplus/props.ma".

theorem aplus_gz_le:
 \forall (k: nat).(\forall (h: nat).(\forall (n: nat).((le h k) \to (eq A 
(aplus gz (ASort h n) k) (ASort O (plus (minus k h) n))))))
\def
 \lambda (k: nat).(let TMP_6 \def (\lambda (n: nat).(\forall (h: 
nat).(\forall (n0: nat).((le h n) \to (let TMP_1 \def (ASort h n0) in (let 
TMP_2 \def (aplus gz TMP_1 n) in (let TMP_3 \def (minus n h) in (let TMP_4 
\def (plus TMP_3 n0) in (let TMP_5 \def (ASort O TMP_4) in (eq A TMP_2 
TMP_5)))))))))) in (let TMP_12 \def (\lambda (h: nat).(\lambda (n: 
nat).(\lambda (H: (le h O)).(let H_y \def (le_n_O_eq h H) in (let TMP_9 \def 
(\lambda (n0: nat).(let TMP_7 \def (ASort n0 n) in (let TMP_8 \def (ASort O 
n) in (eq A TMP_7 TMP_8)))) in (let TMP_10 \def (ASort O n) in (let TMP_11 
\def (refl_equal A TMP_10) in (eq_ind nat O TMP_9 TMP_11 h H_y)))))))) in 
(let TMP_103 \def (\lambda (k0: nat).(\lambda (IH: ((\forall (h: 
nat).(\forall (n: nat).((le h k0) \to (eq A (aplus gz (ASort h n) k0) (ASort 
O (plus (minus k0 h) n)))))))).(\lambda (h: nat).(let TMP_19 \def (\lambda 
(n: nat).(\forall (n0: nat).((le n (S k0)) \to (let TMP_13 \def (ASort n n0) 
in (let TMP_14 \def (aplus gz TMP_13 k0) in (let TMP_15 \def (asucc gz 
TMP_14) in (let TMP_16 \def (match n with [O \Rightarrow (S k0) | (S l) 
\Rightarrow (minus k0 l)]) in (let TMP_17 \def (plus TMP_16 n0) in (let 
TMP_18 \def (ASort O TMP_17) in (eq A TMP_15 TMP_18)))))))))) in (let TMP_72 
\def (\lambda (n: nat).(\lambda (_: (le O (S k0))).(let TMP_20 \def (ASort O 
n) in (let TMP_21 \def (asucc gz TMP_20) in (let TMP_22 \def (aplus gz TMP_21 
k0) in (let TMP_26 \def (\lambda (a: A).(let TMP_23 \def (plus k0 n) in (let 
TMP_24 \def (S TMP_23) in (let TMP_25 \def (ASort O TMP_24) in (eq A a 
TMP_25))))) in (let TMP_27 \def (minus k0 O) in (let TMP_28 \def (S n) in 
(let TMP_29 \def (plus TMP_27 TMP_28) in (let TMP_30 \def (ASort O TMP_29) in 
(let TMP_34 \def (\lambda (a: A).(let TMP_31 \def (plus k0 n) in (let TMP_32 
\def (S TMP_31) in (let TMP_33 \def (ASort O TMP_32) in (eq A a TMP_33))))) 
in (let TMP_41 \def (\lambda (n0: nat).(let TMP_35 \def (S n) in (let TMP_36 
\def (plus n0 TMP_35) in (let TMP_37 \def (ASort O TMP_36) in (let TMP_38 
\def (plus k0 n) in (let TMP_39 \def (S TMP_38) in (let TMP_40 \def (ASort O 
TMP_39) in (eq A TMP_37 TMP_40)))))))) in (let TMP_42 \def (plus k0 n) in 
(let TMP_43 \def (S TMP_42) in (let TMP_48 \def (\lambda (n0: nat).(let 
TMP_44 \def (ASort O n0) in (let TMP_45 \def (plus k0 n) in (let TMP_46 \def 
(S TMP_45) in (let TMP_47 \def (ASort O TMP_46) in (eq A TMP_44 TMP_47)))))) 
in (let TMP_49 \def (plus k0 n) in (let TMP_50 \def (S TMP_49) in (let TMP_51 
\def (ASort O TMP_50) in (let TMP_52 \def (refl_equal A TMP_51) in (let 
TMP_53 \def (S n) in (let TMP_54 \def (plus k0 TMP_53) in (let TMP_55 \def 
(plus_n_Sm k0 n) in (let TMP_56 \def (eq_ind nat TMP_43 TMP_48 TMP_52 TMP_54 
TMP_55) in (let TMP_57 \def (minus k0 O) in (let TMP_58 \def (minus_n_O k0) 
in (let TMP_59 \def (eq_ind nat k0 TMP_41 TMP_56 TMP_57 TMP_58) in (let 
TMP_60 \def (S n) in (let TMP_61 \def (ASort O TMP_60) in (let TMP_62 \def 
(aplus gz TMP_61 k0) in (let TMP_63 \def (S n) in (let TMP_64 \def (le_O_n 
k0) in (let TMP_65 \def (IH O TMP_63 TMP_64) in (let TMP_66 \def (eq_ind_r A 
TMP_30 TMP_34 TMP_59 TMP_62 TMP_65) in (let TMP_67 \def (ASort O n) in (let 
TMP_68 \def (aplus gz TMP_67 k0) in (let TMP_69 \def (asucc gz TMP_68) in 
(let TMP_70 \def (ASort O n) in (let TMP_71 \def (aplus_asucc gz k0 TMP_70) 
in (eq_ind A TMP_22 TMP_26 TMP_66 TMP_69 
TMP_71))))))))))))))))))))))))))))))))))))))) in (let TMP_102 \def (\lambda 
(n: nat).(\lambda (_: ((\forall (n0: nat).((le n (S k0)) \to (eq A (asucc gz 
(aplus gz (ASort n n0) k0)) (ASort O (plus (match n with [O \Rightarrow (S 
k0) | (S l) \Rightarrow (minus k0 l)]) n0))))))).(\lambda (n0: nat).(\lambda 
(H0: (le (S n) (S k0))).(let H_y \def (le_S_n n k0 H0) in (let TMP_73 \def 
(ASort n n0) in (let TMP_74 \def (aplus gz TMP_73 k0) in (let TMP_79 \def 
(\lambda (a: A).(let TMP_75 \def (S n) in (let TMP_76 \def (ASort TMP_75 n0) 
in (let TMP_77 \def (aplus gz TMP_76 k0) in (let TMP_78 \def (asucc gz 
TMP_77) in (eq A TMP_78 a)))))) in (let TMP_80 \def (S n) in (let TMP_81 \def 
(ASort TMP_80 n0) in (let TMP_82 \def (asucc gz TMP_81) in (let TMP_83 \def 
(aplus gz TMP_82 k0) in (let TMP_86 \def (\lambda (a: A).(let TMP_84 \def 
(ASort n n0) in (let TMP_85 \def (aplus gz TMP_84 k0) in (eq A a TMP_85)))) 
in (let TMP_87 \def (ASort n n0) in (let TMP_88 \def (aplus gz TMP_87 k0) in 
(let TMP_89 \def (refl_equal A TMP_88) in (let TMP_90 \def (S n) in (let 
TMP_91 \def (ASort TMP_90 n0) in (let TMP_92 \def (aplus gz TMP_91 k0) in 
(let TMP_93 \def (asucc gz TMP_92) in (let TMP_94 \def (S n) in (let TMP_95 
\def (ASort TMP_94 n0) in (let TMP_96 \def (aplus_asucc gz k0 TMP_95) in (let 
TMP_97 \def (eq_ind A TMP_83 TMP_86 TMP_89 TMP_93 TMP_96) in (let TMP_98 \def 
(minus k0 n) in (let TMP_99 \def (plus TMP_98 n0) in (let TMP_100 \def (ASort 
O TMP_99) in (let TMP_101 \def (IH n n0 H_y) in (eq_ind A TMP_74 TMP_79 
TMP_97 TMP_100 TMP_101))))))))))))))))))))))))))))) in (nat_ind TMP_19 TMP_72 
TMP_102 h))))))) in (nat_ind TMP_6 TMP_12 TMP_103 k)))).

theorem aplus_gz_ge:
 \forall (n: nat).(\forall (k: nat).(\forall (h: nat).((le k h) \to (eq A 
(aplus gz (ASort h n) k) (ASort (minus h k) n)))))
\def
 \lambda (n: nat).(\lambda (k: nat).(let TMP_5 \def (\lambda (n0: 
nat).(\forall (h: nat).((le n0 h) \to (let TMP_1 \def (ASort h n) in (let 
TMP_2 \def (aplus gz TMP_1 n0) in (let TMP_3 \def (minus h n0) in (let TMP_4 
\def (ASort TMP_3 n) in (eq A TMP_2 TMP_4)))))))) in (let TMP_13 \def 
(\lambda (h: nat).(\lambda (_: (le O h)).(let TMP_8 \def (\lambda (n0: 
nat).(let TMP_6 \def (ASort h n) in (let TMP_7 \def (ASort n0 n) in (eq A 
TMP_6 TMP_7)))) in (let TMP_9 \def (ASort h n) in (let TMP_10 \def 
(refl_equal A TMP_9) in (let TMP_11 \def (minus h O) in (let TMP_12 \def 
(minus_n_O h) in (eq_ind nat h TMP_8 TMP_10 TMP_11 TMP_12)))))))) in (let 
TMP_68 \def (\lambda (k0: nat).(\lambda (IH: ((\forall (h: nat).((le k0 h) 
\to (eq A (aplus gz (ASort h n) k0) (ASort (minus h k0) n)))))).(\lambda (h: 
nat).(let TMP_20 \def (\lambda (n0: nat).((le (S k0) n0) \to (let TMP_14 \def 
(ASort n0 n) in (let TMP_15 \def (aplus gz TMP_14 k0) in (let TMP_16 \def 
(asucc gz TMP_15) in (let TMP_17 \def (S k0) in (let TMP_18 \def (minus n0 
TMP_17) in (let TMP_19 \def (ASort TMP_18 n) in (eq A TMP_16 TMP_19))))))))) 
in (let TMP_38 \def (\lambda (H: (le (S k0) O)).(let TMP_22 \def (\lambda 
(n0: nat).(let TMP_21 \def (S n0) in (eq nat O TMP_21))) in (let TMP_23 \def 
(\lambda (n0: nat).(le k0 n0)) in (let TMP_24 \def (ASort O n) in (let TMP_25 
\def (aplus gz TMP_24 k0) in (let TMP_26 \def (asucc gz TMP_25) in (let 
TMP_27 \def (ASort O n) in (let TMP_28 \def (eq A TMP_26 TMP_27) in (let 
TMP_36 \def (\lambda (x: nat).(\lambda (H0: (eq nat O (S x))).(\lambda (_: 
(le k0 x)).(let TMP_29 \def (\lambda (ee: nat).(match ee with [O \Rightarrow 
True | (S _) \Rightarrow False])) in (let TMP_30 \def (S x) in (let H2 \def 
(eq_ind nat O TMP_29 I TMP_30 H0) in (let TMP_31 \def (ASort O n) in (let 
TMP_32 \def (aplus gz TMP_31 k0) in (let TMP_33 \def (asucc gz TMP_32) in 
(let TMP_34 \def (ASort O n) in (let TMP_35 \def (eq A TMP_33 TMP_34) in 
(False_ind TMP_35 H2)))))))))))) in (let TMP_37 \def (le_gen_S k0 O H) in 
(ex2_ind nat TMP_22 TMP_23 TMP_28 TMP_36 TMP_37))))))))))) in (let TMP_67 
\def (\lambda (n0: nat).(\lambda (_: (((le (S k0) n0) \to (eq A (asucc gz 
(aplus gz (ASort n0 n) k0)) (ASort (minus n0 (S k0)) n))))).(\lambda (H0: (le 
(S k0) (S n0))).(let H_y \def (le_S_n k0 n0 H0) in (let TMP_39 \def (ASort n0 
n) in (let TMP_40 \def (aplus gz TMP_39 k0) in (let TMP_45 \def (\lambda (a: 
A).(let TMP_41 \def (S n0) in (let TMP_42 \def (ASort TMP_41 n) in (let 
TMP_43 \def (aplus gz TMP_42 k0) in (let TMP_44 \def (asucc gz TMP_43) in (eq 
A TMP_44 a)))))) in (let TMP_46 \def (S n0) in (let TMP_47 \def (ASort TMP_46 
n) in (let TMP_48 \def (asucc gz TMP_47) in (let TMP_49 \def (aplus gz TMP_48 
k0) in (let TMP_52 \def (\lambda (a: A).(let TMP_50 \def (ASort n0 n) in (let 
TMP_51 \def (aplus gz TMP_50 k0) in (eq A a TMP_51)))) in (let TMP_53 \def 
(ASort n0 n) in (let TMP_54 \def (aplus gz TMP_53 k0) in (let TMP_55 \def 
(refl_equal A TMP_54) in (let TMP_56 \def (S n0) in (let TMP_57 \def (ASort 
TMP_56 n) in (let TMP_58 \def (aplus gz TMP_57 k0) in (let TMP_59 \def (asucc 
gz TMP_58) in (let TMP_60 \def (S n0) in (let TMP_61 \def (ASort TMP_60 n) in 
(let TMP_62 \def (aplus_asucc gz k0 TMP_61) in (let TMP_63 \def (eq_ind A 
TMP_49 TMP_52 TMP_55 TMP_59 TMP_62) in (let TMP_64 \def (minus n0 k0) in (let 
TMP_65 \def (ASort TMP_64 n) in (let TMP_66 \def (IH n0 H_y) in (eq_ind A 
TMP_40 TMP_45 TMP_63 TMP_65 TMP_66))))))))))))))))))))))))))) in (nat_ind 
TMP_20 TMP_38 TMP_67 h))))))) in (nat_ind TMP_5 TMP_13 TMP_68 k))))).

theorem next_plus_gz:
 \forall (n: nat).(\forall (h: nat).(eq nat (next_plus gz n h) (plus h n)))
\def
 \lambda (n: nat).(\lambda (h: nat).(let TMP_3 \def (\lambda (n0: nat).(let 
TMP_1 \def (next_plus gz n n0) in (let TMP_2 \def (plus n0 n) in (eq nat 
TMP_1 TMP_2)))) in (let TMP_4 \def (refl_equal nat n) in (let TMP_7 \def 
(\lambda (n0: nat).(\lambda (H: (eq nat (next_plus gz n n0) (plus n0 
n))).(let TMP_5 \def (next_plus gz n n0) in (let TMP_6 \def (plus n0 n) in 
(f_equal nat nat S TMP_5 TMP_6 H))))) in (nat_ind TMP_3 TMP_4 TMP_7 h))))).

theorem leqz_leq:
 \forall (a1: A).(\forall (a2: A).((leq gz a1 a2) \to (leqz a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq gz a1 a2)).(let TMP_1 
\def (\lambda (a: A).(\lambda (a0: A).(leqz a a0))) in (let TMP_225 \def 
(\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: 
nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus gz (ASort h1 n1) k) (aplus 
gz (ASort h2 n2) k))).(let TMP_2 \def (ASort h1 n1) in (let TMP_3 \def (ASort 
h2 n2) in (let TMP_4 \def (leqz TMP_2 TMP_3) in (let TMP_136 \def (\lambda 
(H1: (lt k h1)).(let TMP_5 \def (ASort h1 n1) in (let TMP_6 \def (ASort h2 
n2) in (let TMP_7 \def (leqz TMP_5 TMP_6) in (let TMP_86 \def (\lambda (H2: 
(lt k h2)).(let TMP_8 \def (ASort h1 n1) in (let TMP_9 \def (aplus gz TMP_8 
k) in (let TMP_12 \def (\lambda (a: A).(let TMP_10 \def (ASort h2 n2) in (let 
TMP_11 \def (aplus gz TMP_10 k) in (eq A a TMP_11)))) in (let TMP_13 \def 
(minus h1 k) in (let TMP_14 \def (ASort TMP_13 n1) in (let TMP_15 \def (S k) 
in (let TMP_16 \def (S h1) in (let TMP_17 \def (S k) in (let TMP_18 \def (S 
TMP_17) in (let TMP_19 \def (S h1) in (let TMP_20 \def (S k) in (let TMP_21 
\def (le_n_S TMP_20 h1 H1) in (let TMP_22 \def (le_S TMP_18 TMP_19 TMP_21) in 
(let TMP_23 \def (le_S_n TMP_15 TMP_16 TMP_22) in (let TMP_24 \def (le_S_n k 
h1 TMP_23) in (let TMP_25 \def (aplus_gz_ge n1 k h1 TMP_24) in (let H3 \def 
(eq_ind A TMP_9 TMP_12 H0 TMP_14 TMP_25) in (let TMP_26 \def (ASort h2 n2) in 
(let TMP_27 \def (aplus gz TMP_26 k) in (let TMP_30 \def (\lambda (a: A).(let 
TMP_28 \def (minus h1 k) in (let TMP_29 \def (ASort TMP_28 n1) in (eq A 
TMP_29 a)))) in (let TMP_31 \def (minus h2 k) in (let TMP_32 \def (ASort 
TMP_31 n2) in (let TMP_33 \def (S k) in (let TMP_34 \def (S h2) in (let 
TMP_35 \def (S k) in (let TMP_36 \def (S TMP_35) in (let TMP_37 \def (S h2) 
in (let TMP_38 \def (S k) in (let TMP_39 \def (le_n_S TMP_38 h2 H2) in (let 
TMP_40 \def (le_S TMP_36 TMP_37 TMP_39) in (let TMP_41 \def (le_S_n TMP_33 
TMP_34 TMP_40) in (let TMP_42 \def (le_S_n k h2 TMP_41) in (let TMP_43 \def 
(aplus_gz_ge n2 k h2 TMP_42) in (let H4 \def (eq_ind A TMP_27 TMP_30 H3 
TMP_32 TMP_43) in (let TMP_44 \def (\lambda (e: A).(match e with [(ASort n _) 
\Rightarrow n | (AHead _ _) \Rightarrow (minus h1 k)])) in (let TMP_45 \def 
(minus h1 k) in (let TMP_46 \def (ASort TMP_45 n1) in (let TMP_47 \def (minus 
h2 k) in (let TMP_48 \def (ASort TMP_47 n2) in (let H5 \def (f_equal A nat 
TMP_44 TMP_46 TMP_48 H4) in (let TMP_49 \def (\lambda (e: A).(match e with 
[(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow n1])) in (let TMP_50 
\def (minus h1 k) in (let TMP_51 \def (ASort TMP_50 n1) in (let TMP_52 \def 
(minus h2 k) in (let TMP_53 \def (ASort TMP_52 n2) in (let H6 \def (f_equal A 
nat TMP_49 TMP_51 TMP_53 H4) in (let TMP_85 \def (\lambda (H7: (eq nat (minus 
h1 k) (minus h2 k))).(let TMP_56 \def (\lambda (n: nat).(let TMP_54 \def 
(ASort h1 n1) in (let TMP_55 \def (ASort h2 n) in (leqz TMP_54 TMP_55)))) in 
(let TMP_59 \def (\lambda (n: nat).(let TMP_57 \def (ASort h1 n1) in (let 
TMP_58 \def (ASort n n1) in (leqz TMP_57 TMP_58)))) in (let TMP_60 \def (plus 
h1 n1) in (let TMP_61 \def (refl_equal nat TMP_60) in (let TMP_62 \def 
(leqz_sort h1 h1 n1 n1 TMP_61) in (let TMP_63 \def (S k) in (let TMP_64 \def 
(S h1) in (let TMP_65 \def (S k) in (let TMP_66 \def (S TMP_65) in (let 
TMP_67 \def (S h1) in (let TMP_68 \def (S k) in (let TMP_69 \def (le_n_S 
TMP_68 h1 H1) in (let TMP_70 \def (le_S TMP_66 TMP_67 TMP_69) in (let TMP_71 
\def (le_S_n TMP_63 TMP_64 TMP_70) in (let TMP_72 \def (le_S_n k h1 TMP_71) 
in (let TMP_73 \def (S k) in (let TMP_74 \def (S h2) in (let TMP_75 \def (S 
k) in (let TMP_76 \def (S TMP_75) in (let TMP_77 \def (S h2) in (let TMP_78 
\def (S k) in (let TMP_79 \def (le_n_S TMP_78 h2 H2) in (let TMP_80 \def 
(le_S TMP_76 TMP_77 TMP_79) in (let TMP_81 \def (le_S_n TMP_73 TMP_74 TMP_80) 
in (let TMP_82 \def (le_S_n k h2 TMP_81) in (let TMP_83 \def (minus_minus k 
h1 h2 TMP_72 TMP_82 H7) in (let TMP_84 \def (eq_ind nat h1 TMP_59 TMP_62 h2 
TMP_83) in (eq_ind nat n1 TMP_56 TMP_84 n2 H6))))))))))))))))))))))))))))) in 
(TMP_85 H5))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_135 
\def (\lambda (H2: (le h2 k)).(let TMP_87 \def (ASort h1 n1) in (let TMP_88 
\def (aplus gz TMP_87 k) in (let TMP_91 \def (\lambda (a: A).(let TMP_89 \def 
(ASort h2 n2) in (let TMP_90 \def (aplus gz TMP_89 k) in (eq A a TMP_90)))) 
in (let TMP_92 \def (minus h1 k) in (let TMP_93 \def (ASort TMP_92 n1) in 
(let TMP_94 \def (S k) in (let TMP_95 \def (S h1) in (let TMP_96 \def (S k) 
in (let TMP_97 \def (S TMP_96) in (let TMP_98 \def (S h1) in (let TMP_99 \def 
(S k) in (let TMP_100 \def (le_n_S TMP_99 h1 H1) in (let TMP_101 \def (le_S 
TMP_97 TMP_98 TMP_100) in (let TMP_102 \def (le_S_n TMP_94 TMP_95 TMP_101) in 
(let TMP_103 \def (le_S_n k h1 TMP_102) in (let TMP_104 \def (aplus_gz_ge n1 
k h1 TMP_103) in (let H3 \def (eq_ind A TMP_88 TMP_91 H0 TMP_93 TMP_104) in 
(let TMP_105 \def (ASort h2 n2) in (let TMP_106 \def (aplus gz TMP_105 k) in 
(let TMP_109 \def (\lambda (a: A).(let TMP_107 \def (minus h1 k) in (let 
TMP_108 \def (ASort TMP_107 n1) in (eq A TMP_108 a)))) in (let TMP_110 \def 
(minus k h2) in (let TMP_111 \def (plus TMP_110 n2) in (let TMP_112 \def 
(ASort O TMP_111) in (let TMP_113 \def (aplus_gz_le k h2 n2 H2) in (let H4 
\def (eq_ind A TMP_106 TMP_109 H3 TMP_112 TMP_113) in (let TMP_114 \def 
(minus h1 k) in (let TMP_119 \def (\lambda (n: nat).(let TMP_115 \def (ASort 
n n1) in (let TMP_116 \def (minus k h2) in (let TMP_117 \def (plus TMP_116 
n2) in (let TMP_118 \def (ASort O TMP_117) in (eq A TMP_115 TMP_118)))))) in 
(let TMP_120 \def (S k) in (let TMP_121 \def (minus h1 TMP_120) in (let 
TMP_122 \def (S TMP_121) in (let TMP_123 \def (minus_x_Sy h1 k H1) in (let H5 
\def (eq_ind nat TMP_114 TMP_119 H4 TMP_122 TMP_123) in (let TMP_124 \def (S 
k) in (let TMP_125 \def (minus h1 TMP_124) in (let TMP_126 \def (S TMP_125) 
in (let TMP_127 \def (ASort TMP_126 n1) in (let TMP_128 \def (\lambda (ee: 
A).(match ee with [(ASort n _) \Rightarrow (match n with [O \Rightarrow False 
| (S _) \Rightarrow True]) | (AHead _ _) \Rightarrow False])) in (let TMP_129 
\def (minus k h2) in (let TMP_130 \def (plus TMP_129 n2) in (let TMP_131 \def 
(ASort O TMP_130) in (let H6 \def (eq_ind A TMP_127 TMP_128 I TMP_131 H5) in 
(let TMP_132 \def (ASort h1 n1) in (let TMP_133 \def (ASort h2 n2) in (let 
TMP_134 \def (leqz TMP_132 TMP_133) in (False_ind TMP_134 
H6)))))))))))))))))))))))))))))))))))))))))))))) in (lt_le_e k h2 TMP_7 
TMP_86 TMP_135))))))) in (let TMP_224 \def (\lambda (H1: (le h1 k)).(let 
TMP_137 \def (ASort h1 n1) in (let TMP_138 \def (ASort h2 n2) in (let TMP_139 
\def (leqz TMP_137 TMP_138) in (let TMP_194 \def (\lambda (H2: (lt k 
h2)).(let TMP_140 \def (ASort h1 n1) in (let TMP_141 \def (aplus gz TMP_140 
k) in (let TMP_144 \def (\lambda (a: A).(let TMP_142 \def (ASort h2 n2) in 
(let TMP_143 \def (aplus gz TMP_142 k) in (eq A a TMP_143)))) in (let TMP_145 
\def (minus k h1) in (let TMP_146 \def (plus TMP_145 n1) in (let TMP_147 \def 
(ASort O TMP_146) in (let TMP_148 \def (aplus_gz_le k h1 n1 H1) in (let H3 
\def (eq_ind A TMP_141 TMP_144 H0 TMP_147 TMP_148) in (let TMP_149 \def 
(ASort h2 n2) in (let TMP_150 \def (aplus gz TMP_149 k) in (let TMP_154 \def 
(\lambda (a: A).(let TMP_151 \def (minus k h1) in (let TMP_152 \def (plus 
TMP_151 n1) in (let TMP_153 \def (ASort O TMP_152) in (eq A TMP_153 a))))) in 
(let TMP_155 \def (minus h2 k) in (let TMP_156 \def (ASort TMP_155 n2) in 
(let TMP_157 \def (S k) in (let TMP_158 \def (S h2) in (let TMP_159 \def (S 
k) in (let TMP_160 \def (S TMP_159) in (let TMP_161 \def (S h2) in (let 
TMP_162 \def (S k) in (let TMP_163 \def (le_n_S TMP_162 h2 H2) in (let 
TMP_164 \def (le_S TMP_160 TMP_161 TMP_163) in (let TMP_165 \def (le_S_n 
TMP_157 TMP_158 TMP_164) in (let TMP_166 \def (le_S_n k h2 TMP_165) in (let 
TMP_167 \def (aplus_gz_ge n2 k h2 TMP_166) in (let H4 \def (eq_ind A TMP_150 
TMP_154 H3 TMP_156 TMP_167) in (let TMP_168 \def (minus k h1) in (let TMP_169 
\def (plus TMP_168 n1) in (let TMP_170 \def (ASort O TMP_169) in (let TMP_171 
\def (minus h2 k) in (let TMP_172 \def (ASort TMP_171 n2) in (let H5 \def 
(sym_eq A TMP_170 TMP_172 H4) in (let TMP_173 \def (minus h2 k) in (let 
TMP_178 \def (\lambda (n: nat).(let TMP_174 \def (ASort n n2) in (let TMP_175 
\def (minus k h1) in (let TMP_176 \def (plus TMP_175 n1) in (let TMP_177 \def 
(ASort O TMP_176) in (eq A TMP_174 TMP_177)))))) in (let TMP_179 \def (S k) 
in (let TMP_180 \def (minus h2 TMP_179) in (let TMP_181 \def (S TMP_180) in 
(let TMP_182 \def (minus_x_Sy h2 k H2) in (let H6 \def (eq_ind nat TMP_173 
TMP_178 H5 TMP_181 TMP_182) in (let TMP_183 \def (S k) in (let TMP_184 \def 
(minus h2 TMP_183) in (let TMP_185 \def (S TMP_184) in (let TMP_186 \def 
(ASort TMP_185 n2) in (let TMP_187 \def (\lambda (ee: A).(match ee with 
[(ASort n _) \Rightarrow (match n with [O \Rightarrow False | (S _) 
\Rightarrow True]) | (AHead _ _) \Rightarrow False])) in (let TMP_188 \def 
(minus k h1) in (let TMP_189 \def (plus TMP_188 n1) in (let TMP_190 \def 
(ASort O TMP_189) in (let H7 \def (eq_ind A TMP_186 TMP_187 I TMP_190 H6) in 
(let TMP_191 \def (ASort h1 n1) in (let TMP_192 \def (ASort h2 n2) in (let 
TMP_193 \def (leqz TMP_191 TMP_192) in (False_ind TMP_193 
H7)))))))))))))))))))))))))))))))))))))))))))))))))))) in (let TMP_223 \def 
(\lambda (H2: (le h2 k)).(let TMP_195 \def (ASort h1 n1) in (let TMP_196 \def 
(aplus gz TMP_195 k) in (let TMP_199 \def (\lambda (a: A).(let TMP_197 \def 
(ASort h2 n2) in (let TMP_198 \def (aplus gz TMP_197 k) in (eq A a 
TMP_198)))) in (let TMP_200 \def (minus k h1) in (let TMP_201 \def (plus 
TMP_200 n1) in (let TMP_202 \def (ASort O TMP_201) in (let TMP_203 \def 
(aplus_gz_le k h1 n1 H1) in (let H3 \def (eq_ind A TMP_196 TMP_199 H0 TMP_202 
TMP_203) in (let TMP_204 \def (ASort h2 n2) in (let TMP_205 \def (aplus gz 
TMP_204 k) in (let TMP_209 \def (\lambda (a: A).(let TMP_206 \def (minus k 
h1) in (let TMP_207 \def (plus TMP_206 n1) in (let TMP_208 \def (ASort O 
TMP_207) in (eq A TMP_208 a))))) in (let TMP_210 \def (minus k h2) in (let 
TMP_211 \def (plus TMP_210 n2) in (let TMP_212 \def (ASort O TMP_211) in (let 
TMP_213 \def (aplus_gz_le k h2 n2 H2) in (let H4 \def (eq_ind A TMP_205 
TMP_209 H3 TMP_212 TMP_213) in (let TMP_216 \def (\lambda (e: A).(match e 
with [(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow (let TMP_215 \def 
(minus k h1) in (plus TMP_215 n1))])) in (let TMP_217 \def (minus k h1) in 
(let TMP_218 \def (plus TMP_217 n1) in (let TMP_219 \def (ASort O TMP_218) in 
(let TMP_220 \def (minus k h2) in (let TMP_221 \def (plus TMP_220 n2) in (let 
TMP_222 \def (ASort O TMP_221) in (let H5 \def (f_equal A nat TMP_216 TMP_219 
TMP_222 H4) in (let H_y \def (plus_plus k h1 h2 n1 n2 H1 H2 H5) in (leqz_sort 
h1 h2 n1 n2 H_y))))))))))))))))))))))))))) in (lt_le_e k h2 TMP_139 TMP_194 
TMP_223))))))) in (lt_le_e k h1 TMP_4 TMP_136 TMP_224)))))))))))) in (let 
TMP_226 \def (\lambda (a0: A).(\lambda (a3: A).(\lambda (_: (leq gz a0 
a3)).(\lambda (H1: (leqz a0 a3)).(\lambda (a4: A).(\lambda (a5: A).(\lambda 
(_: (leq gz a4 a5)).(\lambda (H3: (leqz a4 a5)).(leqz_head a0 a3 H1 a4 a5 
H3))))))))) in (leq_ind gz TMP_1 TMP_225 TMP_226 a1 a2 H)))))).

theorem leq_leqz:
 \forall (a1: A).(\forall (a2: A).((leqz a1 a2) \to (leq gz a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leqz a1 a2)).(let TMP_1 \def 
(\lambda (a: A).(\lambda (a0: A).(leq gz a a0))) in (let TMP_113 \def 
(\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: 
nat).(\lambda (H0: (eq nat (plus h1 n2) (plus h2 n1))).(let TMP_2 \def (plus 
h1 h2) in (let TMP_3 \def (plus h1 h2) in (let TMP_4 \def (minus h1 TMP_3) in 
(let TMP_5 \def (plus h1 h2) in (let TMP_6 \def (minus TMP_5 h1) in (let 
TMP_7 \def (next_plus gz n1 TMP_6) in (let TMP_8 \def (ASort TMP_4 TMP_7) in 
(let TMP_12 \def (\lambda (a: A).(let TMP_9 \def (ASort h2 n2) in (let TMP_10 
\def (plus h1 h2) in (let TMP_11 \def (aplus gz TMP_9 TMP_10) in (eq A a 
TMP_11))))) in (let TMP_13 \def (plus h1 h2) in (let TMP_14 \def (minus h2 
TMP_13) in (let TMP_15 \def (plus h1 h2) in (let TMP_16 \def (minus TMP_15 
h2) in (let TMP_17 \def (next_plus gz n2 TMP_16) in (let TMP_18 \def (ASort 
TMP_14 TMP_17) in (let TMP_25 \def (\lambda (a: A).(let TMP_19 \def (plus h1 
h2) in (let TMP_20 \def (minus h1 TMP_19) in (let TMP_21 \def (plus h1 h2) in 
(let TMP_22 \def (minus TMP_21 h1) in (let TMP_23 \def (next_plus gz n1 
TMP_22) in (let TMP_24 \def (ASort TMP_20 TMP_23) in (eq A TMP_24 a)))))))) 
in (let TMP_36 \def (\lambda (n: nat).(let TMP_26 \def (plus h1 h2) in (let 
TMP_27 \def (minus h1 TMP_26) in (let TMP_28 \def (next_plus gz n1 n) in (let 
TMP_29 \def (ASort TMP_27 TMP_28) in (let TMP_30 \def (plus h1 h2) in (let 
TMP_31 \def (minus h2 TMP_30) in (let TMP_32 \def (plus h1 h2) in (let TMP_33 
\def (minus TMP_32 h2) in (let TMP_34 \def (next_plus gz n2 TMP_33) in (let 
TMP_35 \def (ASort TMP_31 TMP_34) in (eq A TMP_29 TMP_35)))))))))))) in (let 
TMP_45 \def (\lambda (n: nat).(let TMP_37 \def (plus h1 h2) in (let TMP_38 
\def (minus h1 TMP_37) in (let TMP_39 \def (next_plus gz n1 h2) in (let 
TMP_40 \def (ASort TMP_38 TMP_39) in (let TMP_41 \def (plus h1 h2) in (let 
TMP_42 \def (minus h2 TMP_41) in (let TMP_43 \def (next_plus gz n2 n) in (let 
TMP_44 \def (ASort TMP_42 TMP_43) in (eq A TMP_40 TMP_44)))))))))) in (let 
TMP_52 \def (\lambda (n: nat).(let TMP_46 \def (next_plus gz n1 h2) in (let 
TMP_47 \def (ASort n TMP_46) in (let TMP_48 \def (plus h1 h2) in (let TMP_49 
\def (minus h2 TMP_48) in (let TMP_50 \def (next_plus gz n2 h1) in (let 
TMP_51 \def (ASort TMP_49 TMP_50) in (eq A TMP_47 TMP_51)))))))) in (let 
TMP_57 \def (\lambda (n: nat).(let TMP_53 \def (next_plus gz n1 h2) in (let 
TMP_54 \def (ASort O TMP_53) in (let TMP_55 \def (next_plus gz n2 h1) in (let 
TMP_56 \def (ASort n TMP_55) in (eq A TMP_54 TMP_56)))))) in (let TMP_58 \def 
(plus h2 n1) in (let TMP_62 \def (\lambda (n: nat).(let TMP_59 \def (ASort O 
n) in (let TMP_60 \def (next_plus gz n2 h1) in (let TMP_61 \def (ASort O 
TMP_60) in (eq A TMP_59 TMP_61))))) in (let TMP_63 \def (plus h1 n2) in (let 
TMP_67 \def (\lambda (n: nat).(let TMP_64 \def (plus h2 n1) in (let TMP_65 
\def (ASort O TMP_64) in (let TMP_66 \def (ASort O n) in (eq A TMP_65 
TMP_66))))) in (let TMP_68 \def (ASort O) in (let TMP_69 \def (plus h2 n1) in 
(let TMP_70 \def (plus h1 n2) in (let TMP_71 \def (plus h1 n2) in (let TMP_72 
\def (plus h2 n1) in (let TMP_73 \def (sym_eq nat TMP_71 TMP_72 H0) in (let 
TMP_74 \def (f_equal nat A TMP_68 TMP_69 TMP_70 TMP_73) in (let TMP_75 \def 
(next_plus gz n2 h1) in (let TMP_76 \def (next_plus_gz n2 h1) in (let TMP_77 
\def (eq_ind_r nat TMP_63 TMP_67 TMP_74 TMP_75 TMP_76) in (let TMP_78 \def 
(next_plus gz n1 h2) in (let TMP_79 \def (next_plus_gz n1 h2) in (let TMP_80 
\def (eq_ind_r nat TMP_58 TMP_62 TMP_77 TMP_78 TMP_79) in (let TMP_81 \def 
(plus h1 h2) in (let TMP_82 \def (minus h2 TMP_81) in (let TMP_83 \def (plus 
h1 h2) in (let TMP_84 \def (le_plus_r h1 h2) in (let TMP_85 \def (O_minus h2 
TMP_83 TMP_84) in (let TMP_86 \def (eq_ind_r nat O TMP_57 TMP_80 TMP_82 
TMP_85) in (let TMP_87 \def (plus h1 h2) in (let TMP_88 \def (minus h1 
TMP_87) in (let TMP_89 \def (plus h1 h2) in (let TMP_90 \def (le_plus_l h1 
h2) in (let TMP_91 \def (O_minus h1 TMP_89 TMP_90) in (let TMP_92 \def 
(eq_ind_r nat O TMP_52 TMP_86 TMP_88 TMP_91) in (let TMP_93 \def (plus h1 h2) 
in (let TMP_94 \def (minus TMP_93 h2) in (let TMP_95 \def (minus_plus_r h1 
h2) in (let TMP_96 \def (eq_ind_r nat h1 TMP_45 TMP_92 TMP_94 TMP_95) in (let 
TMP_97 \def (plus h1 h2) in (let TMP_98 \def (minus TMP_97 h1) in (let TMP_99 
\def (minus_plus h1 h2) in (let TMP_100 \def (eq_ind_r nat h2 TMP_36 TMP_96 
TMP_98 TMP_99) in (let TMP_101 \def (ASort h2 n2) in (let TMP_102 \def (plus 
h1 h2) in (let TMP_103 \def (aplus gz TMP_101 TMP_102) in (let TMP_104 \def 
(plus h1 h2) in (let TMP_105 \def (aplus_asort_simpl gz TMP_104 h2 n2) in 
(let TMP_106 \def (eq_ind_r A TMP_18 TMP_25 TMP_100 TMP_103 TMP_105) in (let 
TMP_107 \def (ASort h1 n1) in (let TMP_108 \def (plus h1 h2) in (let TMP_109 
\def (aplus gz TMP_107 TMP_108) in (let TMP_110 \def (plus h1 h2) in (let 
TMP_111 \def (aplus_asort_simpl gz TMP_110 h1 n1) in (let TMP_112 \def 
(eq_ind_r A TMP_8 TMP_12 TMP_106 TMP_109 TMP_111) in (leq_sort gz h1 h2 n1 n2 
TMP_2 
TMP_112)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))) in (let TMP_114 \def (\lambda (a0: A).(\lambda (a3: A).(\lambda (_: (leqz 
a0 a3)).(\lambda (H1: (leq gz a0 a3)).(\lambda (a4: A).(\lambda (a5: 
A).(\lambda (_: (leqz a4 a5)).(\lambda (H3: (leq gz a4 a5)).(leq_head gz a0 
a3 H1 a4 a5 H3))))))))) in (leqz_ind TMP_1 TMP_113 TMP_114 a1 a2 H)))))).

