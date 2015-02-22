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

include "basic_1/aplus/defs.ma".

include "basic_1/A/fwd.ma".

include "basic_1/next_plus/props.ma".

theorem aplus_reg_r:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (h1: nat).(\forall 
(h2: nat).((eq A (aplus g a1 h1) (aplus g a2 h2)) \to (\forall (h: nat).(eq A 
(aplus g a1 (plus h h1)) (aplus g a2 (plus h h2)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (H: (eq A (aplus g a1 h1) (aplus g a2 h2))).(\lambda (h: 
nat).(let TMP_5 \def (\lambda (n: nat).(let TMP_1 \def (plus n h1) in (let 
TMP_2 \def (aplus g a1 TMP_1) in (let TMP_3 \def (plus n h2) in (let TMP_4 
\def (aplus g a2 TMP_3) in (eq A TMP_2 TMP_4)))))) in (let TMP_11 \def 
(\lambda (n: nat).(\lambda (H0: (eq A (aplus g a1 (plus n h1)) (aplus g a2 
(plus n h2)))).(let TMP_6 \def (plus n h1) in (let TMP_7 \def (aplus g a1 
TMP_6) in (let TMP_8 \def (plus n h2) in (let TMP_9 \def (aplus g a2 TMP_8) 
in (let TMP_10 \def (refl_equal G g) in (f_equal2 G A A asucc g g TMP_7 TMP_9 
TMP_10 H0)))))))) in (nat_ind TMP_5 H TMP_11 h))))))))).

theorem aplus_assoc:
 \forall (g: G).(\forall (a: A).(\forall (h1: nat).(\forall (h2: nat).(eq A 
(aplus g (aplus g a h1) h2) (aplus g a (plus h1 h2))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (h1: nat).(let TMP_5 \def (\lambda 
(n: nat).(\forall (h2: nat).(let TMP_1 \def (aplus g a n) in (let TMP_2 \def 
(aplus g TMP_1 h2) in (let TMP_3 \def (plus n h2) in (let TMP_4 \def (aplus g 
a TMP_3) in (eq A TMP_2 TMP_4))))))) in (let TMP_7 \def (\lambda (h2: 
nat).(let TMP_6 \def (aplus g a h2) in (refl_equal A TMP_6))) in (let TMP_47 
\def (\lambda (n: nat).(\lambda (_: ((\forall (h2: nat).(eq A (aplus g (aplus 
g a n) h2) (aplus g a (plus n h2)))))).(\lambda (h2: nat).(let TMP_14 \def 
(\lambda (n0: nat).(let TMP_8 \def (aplus g a n) in (let TMP_9 \def (asucc g 
TMP_8) in (let TMP_10 \def (aplus g TMP_9 n0) in (let TMP_11 \def (plus n n0) 
in (let TMP_12 \def (aplus g a TMP_11) in (let TMP_13 \def (asucc g TMP_12) 
in (eq A TMP_10 TMP_13)))))))) in (let TMP_19 \def (\lambda (n0: nat).(let 
TMP_15 \def (aplus g a n) in (let TMP_16 \def (asucc g TMP_15) in (let TMP_17 
\def (aplus g a n0) in (let TMP_18 \def (asucc g TMP_17) in (eq A TMP_16 
TMP_18)))))) in (let TMP_20 \def (aplus g a n) in (let TMP_21 \def (asucc g 
TMP_20) in (let TMP_22 \def (refl_equal A TMP_21) in (let TMP_23 \def (plus n 
O) in (let TMP_24 \def (plus_n_O n) in (let TMP_25 \def (eq_ind nat n TMP_19 
TMP_22 TMP_23 TMP_24) in (let TMP_46 \def (\lambda (n0: nat).(\lambda (H0: 
(eq A (aplus g (asucc g (aplus g a n)) n0) (asucc g (aplus g a (plus n 
n0))))).(let TMP_26 \def (plus n n0) in (let TMP_27 \def (S TMP_26) in (let 
TMP_34 \def (\lambda (n1: nat).(let TMP_28 \def (aplus g a n) in (let TMP_29 
\def (asucc g TMP_28) in (let TMP_30 \def (aplus g TMP_29 n0) in (let TMP_31 
\def (asucc g TMP_30) in (let TMP_32 \def (aplus g a n1) in (let TMP_33 \def 
(asucc g TMP_32) in (eq A TMP_31 TMP_33)))))))) in (let TMP_35 \def (aplus g 
a n) in (let TMP_36 \def (asucc g TMP_35) in (let TMP_37 \def (aplus g TMP_36 
n0) in (let TMP_38 \def (plus n n0) in (let TMP_39 \def (aplus g a TMP_38) in 
(let TMP_40 \def (asucc g TMP_39) in (let TMP_41 \def (refl_equal G g) in 
(let TMP_42 \def (f_equal2 G A A asucc g g TMP_37 TMP_40 TMP_41 H0) in (let 
TMP_43 \def (S n0) in (let TMP_44 \def (plus n TMP_43) in (let TMP_45 \def 
(plus_n_Sm n n0) in (eq_ind nat TMP_27 TMP_34 TMP_42 TMP_44 
TMP_45))))))))))))))))) in (nat_ind TMP_14 TMP_25 TMP_46 h2))))))))))))) in 
(nat_ind TMP_5 TMP_7 TMP_47 h1)))))).

theorem aplus_asucc:
 \forall (g: G).(\forall (h: nat).(\forall (a: A).(eq A (aplus g (asucc g a) 
h) (asucc g (aplus g a h)))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (a: A).(let TMP_1 \def (S O) in 
(let TMP_2 \def (plus TMP_1 h) in (let TMP_3 \def (aplus g a TMP_2) in (let 
TMP_6 \def (\lambda (a0: A).(let TMP_4 \def (aplus g a h) in (let TMP_5 \def 
(asucc g TMP_4) in (eq A a0 TMP_5)))) in (let TMP_7 \def (aplus g a h) in 
(let TMP_8 \def (asucc g TMP_7) in (let TMP_9 \def (refl_equal A TMP_8) in 
(let TMP_10 \def (S O) in (let TMP_11 \def (aplus g a TMP_10) in (let TMP_12 
\def (aplus g TMP_11 h) in (let TMP_13 \def (S O) in (let TMP_14 \def 
(aplus_assoc g a TMP_13 h) in (eq_ind_r A TMP_3 TMP_6 TMP_9 TMP_12 
TMP_14))))))))))))))).

theorem aplus_sort_O_S_simpl:
 \forall (g: G).(\forall (n: nat).(\forall (k: nat).(eq A (aplus g (ASort O 
n) (S k)) (aplus g (ASort O (next g n)) k))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (k: nat).(let TMP_1 \def (ASort O 
n) in (let TMP_2 \def (asucc g TMP_1) in (let TMP_3 \def (aplus g TMP_2 k) in 
(let TMP_7 \def (\lambda (a: A).(let TMP_4 \def (next g n) in (let TMP_5 \def 
(ASort O TMP_4) in (let TMP_6 \def (aplus g TMP_5 k) in (eq A a TMP_6))))) in 
(let TMP_8 \def (next g n) in (let TMP_9 \def (ASort O TMP_8) in (let TMP_10 
\def (aplus g TMP_9 k) in (let TMP_11 \def (refl_equal A TMP_10) in (let 
TMP_12 \def (ASort O n) in (let TMP_13 \def (aplus g TMP_12 k) in (let TMP_14 
\def (asucc g TMP_13) in (let TMP_15 \def (ASort O n) in (let TMP_16 \def 
(aplus_asucc g k TMP_15) in (eq_ind A TMP_3 TMP_7 TMP_11 TMP_14 
TMP_16)))))))))))))))).

theorem aplus_sort_S_S_simpl:
 \forall (g: G).(\forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq A 
(aplus g (ASort (S h) n) (S k)) (aplus g (ASort h n) k)))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(let 
TMP_1 \def (S h) in (let TMP_2 \def (ASort TMP_1 n) in (let TMP_3 \def (asucc 
g TMP_2) in (let TMP_4 \def (aplus g TMP_3 k) in (let TMP_7 \def (\lambda (a: 
A).(let TMP_5 \def (ASort h n) in (let TMP_6 \def (aplus g TMP_5 k) in (eq A 
a TMP_6)))) in (let TMP_8 \def (ASort h n) in (let TMP_9 \def (aplus g TMP_8 
k) in (let TMP_10 \def (refl_equal A TMP_9) in (let TMP_11 \def (S h) in (let 
TMP_12 \def (ASort TMP_11 n) in (let TMP_13 \def (aplus g TMP_12 k) in (let 
TMP_14 \def (asucc g TMP_13) in (let TMP_15 \def (S h) in (let TMP_16 \def 
(ASort TMP_15 n) in (let TMP_17 \def (aplus_asucc g k TMP_16) in (eq_ind A 
TMP_4 TMP_7 TMP_10 TMP_14 TMP_17))))))))))))))))))).

theorem aplus_asort_O_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(eq A (aplus g (ASort O 
n) h) (ASort O (next_plus g n h)))))
\def
 \lambda (g: G).(\lambda (h: nat).(let TMP_5 \def (\lambda (n: nat).(\forall 
(n0: nat).(let TMP_1 \def (ASort O n0) in (let TMP_2 \def (aplus g TMP_1 n) 
in (let TMP_3 \def (next_plus g n0 n) in (let TMP_4 \def (ASort O TMP_3) in 
(eq A TMP_2 TMP_4))))))) in (let TMP_7 \def (\lambda (n: nat).(let TMP_6 \def 
(ASort O n) in (refl_equal A TMP_6))) in (let TMP_33 \def (\lambda (n: 
nat).(\lambda (H: ((\forall (n0: nat).(eq A (aplus g (ASort O n0) n) (ASort O 
(next_plus g n0 n)))))).(\lambda (n0: nat).(let TMP_8 \def (ASort O n0) in 
(let TMP_9 \def (asucc g TMP_8) in (let TMP_10 \def (aplus g TMP_9 n) in (let 
TMP_14 \def (\lambda (a: A).(let TMP_11 \def (next_plus g n0 n) in (let 
TMP_12 \def (next g TMP_11) in (let TMP_13 \def (ASort O TMP_12) in (eq A a 
TMP_13))))) in (let TMP_15 \def (next g n0) in (let TMP_16 \def (next_plus g 
TMP_15 n) in (let TMP_21 \def (\lambda (n1: nat).(let TMP_17 \def (next g n0) 
in (let TMP_18 \def (ASort O TMP_17) in (let TMP_19 \def (aplus g TMP_18 n) 
in (let TMP_20 \def (ASort O n1) in (eq A TMP_19 TMP_20)))))) in (let TMP_22 
\def (next g n0) in (let TMP_23 \def (H TMP_22) in (let TMP_24 \def 
(next_plus g n0 n) in (let TMP_25 \def (next g TMP_24) in (let TMP_26 \def 
(next_plus_next g n0 n) in (let TMP_27 \def (eq_ind nat TMP_16 TMP_21 TMP_23 
TMP_25 TMP_26) in (let TMP_28 \def (ASort O n0) in (let TMP_29 \def (aplus g 
TMP_28 n) in (let TMP_30 \def (asucc g TMP_29) in (let TMP_31 \def (ASort O 
n0) in (let TMP_32 \def (aplus_asucc g n TMP_31) in (eq_ind A TMP_10 TMP_14 
TMP_27 TMP_30 TMP_32)))))))))))))))))))))) in (nat_ind TMP_5 TMP_7 TMP_33 
h))))).

theorem aplus_asort_le_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).((le h 
k) \to (eq A (aplus g (ASort k n) h) (ASort (minus k h) n))))))
\def
 \lambda (g: G).(\lambda (h: nat).(let TMP_5 \def (\lambda (n: nat).(\forall 
(k: nat).(\forall (n0: nat).((le n k) \to (let TMP_1 \def (ASort k n0) in 
(let TMP_2 \def (aplus g TMP_1 n) in (let TMP_3 \def (minus k n) in (let 
TMP_4 \def (ASort TMP_3 n0) in (eq A TMP_2 TMP_4))))))))) in (let TMP_13 \def 
(\lambda (k: nat).(\lambda (n: nat).(\lambda (_: (le O k)).(let TMP_8 \def 
(\lambda (n0: nat).(let TMP_6 \def (ASort k n) in (let TMP_7 \def (ASort n0 
n) in (eq A TMP_6 TMP_7)))) in (let TMP_9 \def (ASort k n) in (let TMP_10 
\def (refl_equal A TMP_9) in (let TMP_11 \def (minus k O) in (let TMP_12 \def 
(minus_n_O k) in (eq_ind nat k TMP_8 TMP_10 TMP_11 TMP_12))))))))) in (let 
TMP_62 \def (\lambda (h0: nat).(\lambda (H: ((\forall (k: nat).(\forall (n: 
nat).((le h0 k) \to (eq A (aplus g (ASort k n) h0) (ASort (minus k h0) 
n))))))).(\lambda (k: nat).(let TMP_20 \def (\lambda (n: nat).(\forall (n0: 
nat).((le (S h0) n) \to (let TMP_14 \def (ASort n n0) in (let TMP_15 \def 
(aplus g TMP_14 h0) in (let TMP_16 \def (asucc g TMP_15) in (let TMP_17 \def 
(S h0) in (let TMP_18 \def (minus n TMP_17) in (let TMP_19 \def (ASort TMP_18 
n0) in (eq A TMP_16 TMP_19)))))))))) in (let TMP_42 \def (\lambda (n: 
nat).(\lambda (H0: (le (S h0) O)).(let TMP_22 \def (\lambda (n0: nat).(let 
TMP_21 \def (S n0) in (eq nat O TMP_21))) in (let TMP_23 \def (\lambda (n0: 
nat).(le h0 n0)) in (let TMP_24 \def (ASort O n) in (let TMP_25 \def (aplus g 
TMP_24 h0) in (let TMP_26 \def (asucc g TMP_25) in (let TMP_27 \def (S h0) in 
(let TMP_28 \def (minus O TMP_27) in (let TMP_29 \def (ASort TMP_28 n) in 
(let TMP_30 \def (eq A TMP_26 TMP_29) in (let TMP_40 \def (\lambda (x: 
nat).(\lambda (H1: (eq nat O (S x))).(\lambda (_: (le h0 x)).(let TMP_31 \def 
(\lambda (ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow 
False])) in (let TMP_32 \def (S x) in (let H3 \def (eq_ind nat O TMP_31 I 
TMP_32 H1) in (let TMP_33 \def (ASort O n) in (let TMP_34 \def (aplus g 
TMP_33 h0) in (let TMP_35 \def (asucc g TMP_34) in (let TMP_36 \def (S h0) in 
(let TMP_37 \def (minus O TMP_36) in (let TMP_38 \def (ASort TMP_37 n) in 
(let TMP_39 \def (eq A TMP_35 TMP_38) in (False_ind TMP_39 H3)))))))))))))) 
in (let TMP_41 \def (le_gen_S h0 O H0) in (ex2_ind nat TMP_22 TMP_23 TMP_30 
TMP_40 TMP_41)))))))))))))) in (let TMP_61 \def (\lambda (n: nat).(\lambda 
(_: ((\forall (n0: nat).((le (S h0) n) \to (eq A (asucc g (aplus g (ASort n 
n0) h0)) (ASort (minus n (S h0)) n0)))))).(\lambda (n0: nat).(\lambda (H1: 
(le (S h0) (S n))).(let TMP_43 \def (S n) in (let TMP_44 \def (ASort TMP_43 
n0) in (let TMP_45 \def (asucc g TMP_44) in (let TMP_46 \def (aplus g TMP_45 
h0) in (let TMP_51 \def (\lambda (a: A).(let TMP_47 \def (S n) in (let TMP_48 
\def (S h0) in (let TMP_49 \def (minus TMP_47 TMP_48) in (let TMP_50 \def 
(ASort TMP_49 n0) in (eq A a TMP_50)))))) in (let TMP_52 \def (le_S_n h0 n 
H1) in (let TMP_53 \def (H n n0 TMP_52) in (let TMP_54 \def (S n) in (let 
TMP_55 \def (ASort TMP_54 n0) in (let TMP_56 \def (aplus g TMP_55 h0) in (let 
TMP_57 \def (asucc g TMP_56) in (let TMP_58 \def (S n) in (let TMP_59 \def 
(ASort TMP_58 n0) in (let TMP_60 \def (aplus_asucc g h0 TMP_59) in (eq_ind A 
TMP_46 TMP_51 TMP_53 TMP_57 TMP_60))))))))))))))))))) in (nat_ind TMP_20 
TMP_42 TMP_61 k))))))) in (nat_ind TMP_5 TMP_13 TMP_62 h))))).

theorem aplus_asort_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).(eq A 
(aplus g (ASort k n) h) (ASort (minus k h) (next_plus g n (minus h k)))))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (k: nat).(\lambda (n: nat).(let 
TMP_1 \def (ASort k n) in (let TMP_2 \def (aplus g TMP_1 h) in (let TMP_3 
\def (minus k h) in (let TMP_4 \def (minus h k) in (let TMP_5 \def (next_plus 
g n TMP_4) in (let TMP_6 \def (ASort TMP_3 TMP_5) in (let TMP_7 \def (eq A 
TMP_2 TMP_6) in (let TMP_92 \def (\lambda (H: (lt k h)).(let TMP_8 \def 
(minus h k) in (let TMP_9 \def (plus k TMP_8) in (let TMP_16 \def (\lambda 
(n0: nat).(let TMP_10 \def (ASort k n) in (let TMP_11 \def (aplus g TMP_10 
n0) in (let TMP_12 \def (minus k h) in (let TMP_13 \def (minus h k) in (let 
TMP_14 \def (next_plus g n TMP_13) in (let TMP_15 \def (ASort TMP_12 TMP_14) 
in (eq A TMP_11 TMP_15)))))))) in (let TMP_17 \def (ASort k n) in (let TMP_18 
\def (aplus g TMP_17 k) in (let TMP_19 \def (minus h k) in (let TMP_20 \def 
(aplus g TMP_18 TMP_19) in (let TMP_25 \def (\lambda (a: A).(let TMP_21 \def 
(minus k h) in (let TMP_22 \def (minus h k) in (let TMP_23 \def (next_plus g 
n TMP_22) in (let TMP_24 \def (ASort TMP_21 TMP_23) in (eq A a TMP_24)))))) 
in (let TMP_26 \def (minus k k) in (let TMP_27 \def (ASort TMP_26 n) in (let 
TMP_34 \def (\lambda (a: A).(let TMP_28 \def (minus h k) in (let TMP_29 \def 
(aplus g a TMP_28) in (let TMP_30 \def (minus k h) in (let TMP_31 \def (minus 
h k) in (let TMP_32 \def (next_plus g n TMP_31) in (let TMP_33 \def (ASort 
TMP_30 TMP_32) in (eq A TMP_29 TMP_33)))))))) in (let TMP_42 \def (\lambda 
(n0: nat).(let TMP_35 \def (ASort n0 n) in (let TMP_36 \def (minus h k) in 
(let TMP_37 \def (aplus g TMP_35 TMP_36) in (let TMP_38 \def (minus k h) in 
(let TMP_39 \def (minus h k) in (let TMP_40 \def (next_plus g n TMP_39) in 
(let TMP_41 \def (ASort TMP_38 TMP_40) in (eq A TMP_37 TMP_41))))))))) in 
(let TMP_49 \def (\lambda (n0: nat).(let TMP_43 \def (ASort O n) in (let 
TMP_44 \def (minus h k) in (let TMP_45 \def (aplus g TMP_43 TMP_44) in (let 
TMP_46 \def (minus h k) in (let TMP_47 \def (next_plus g n TMP_46) in (let 
TMP_48 \def (ASort n0 TMP_47) in (eq A TMP_45 TMP_48)))))))) in (let TMP_50 
\def (minus h k) in (let TMP_51 \def (aplus_asort_O_simpl g TMP_50 n) in (let 
TMP_52 \def (minus k h) in (let TMP_53 \def (S k) in (let TMP_54 \def (S h) 
in (let TMP_55 \def (S k) in (let TMP_56 \def (S TMP_55) in (let TMP_57 \def 
(S h) in (let TMP_58 \def (S k) in (let TMP_59 \def (le_n_S TMP_58 h H) in 
(let TMP_60 \def (le_S TMP_56 TMP_57 TMP_59) in (let TMP_61 \def (le_S_n 
TMP_53 TMP_54 TMP_60) in (let TMP_62 \def (le_S_n k h TMP_61) in (let TMP_63 
\def (O_minus k h TMP_62) in (let TMP_64 \def (eq_ind_r nat O TMP_49 TMP_51 
TMP_52 TMP_63) in (let TMP_65 \def (minus k k) in (let TMP_66 \def (minus_n_n 
k) in (let TMP_67 \def (eq_ind nat O TMP_42 TMP_64 TMP_65 TMP_66) in (let 
TMP_68 \def (ASort k n) in (let TMP_69 \def (aplus g TMP_68 k) in (let TMP_70 
\def (le_n k) in (let TMP_71 \def (aplus_asort_le_simpl g k k n TMP_70) in 
(let TMP_72 \def (eq_ind_r A TMP_27 TMP_34 TMP_67 TMP_69 TMP_71) in (let 
TMP_73 \def (ASort k n) in (let TMP_74 \def (minus h k) in (let TMP_75 \def 
(plus k TMP_74) in (let TMP_76 \def (aplus g TMP_73 TMP_75) in (let TMP_77 
\def (ASort k n) in (let TMP_78 \def (minus h k) in (let TMP_79 \def 
(aplus_assoc g TMP_77 k TMP_78) in (let TMP_80 \def (eq_ind A TMP_20 TMP_25 
TMP_72 TMP_76 TMP_79) in (let TMP_81 \def (S k) in (let TMP_82 \def (S h) in 
(let TMP_83 \def (S k) in (let TMP_84 \def (S TMP_83) in (let TMP_85 \def (S 
h) in (let TMP_86 \def (S k) in (let TMP_87 \def (le_n_S TMP_86 h H) in (let 
TMP_88 \def (le_S TMP_84 TMP_85 TMP_87) in (let TMP_89 \def (le_S_n TMP_81 
TMP_82 TMP_88) in (let TMP_90 \def (le_S_n k h TMP_89) in (let TMP_91 \def 
(le_plus_minus k h TMP_90) in (eq_ind_r nat TMP_9 TMP_16 TMP_80 h 
TMP_91))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in (let 
TMP_116 \def (\lambda (H: (le h k)).(let TMP_93 \def (minus k h) in (let 
TMP_94 \def (ASort TMP_93 n) in (let TMP_99 \def (\lambda (a: A).(let TMP_95 
\def (minus k h) in (let TMP_96 \def (minus h k) in (let TMP_97 \def 
(next_plus g n TMP_96) in (let TMP_98 \def (ASort TMP_95 TMP_97) in (eq A a 
TMP_98)))))) in (let TMP_105 \def (\lambda (n0: nat).(let TMP_100 \def (minus 
k h) in (let TMP_101 \def (ASort TMP_100 n) in (let TMP_102 \def (minus k h) 
in (let TMP_103 \def (next_plus g n n0) in (let TMP_104 \def (ASort TMP_102 
TMP_103) in (eq A TMP_101 TMP_104))))))) in (let TMP_106 \def (minus k h) in 
(let TMP_107 \def (next_plus g n O) in (let TMP_108 \def (ASort TMP_106 
TMP_107) in (let TMP_109 \def (refl_equal A TMP_108) in (let TMP_110 \def 
(minus h k) in (let TMP_111 \def (O_minus h k H) in (let TMP_112 \def 
(eq_ind_r nat O TMP_105 TMP_109 TMP_110 TMP_111) in (let TMP_113 \def (ASort 
k n) in (let TMP_114 \def (aplus g TMP_113 h) in (let TMP_115 \def 
(aplus_asort_le_simpl g h k n H) in (eq_ind_r A TMP_94 TMP_99 TMP_112 TMP_114 
TMP_115)))))))))))))))) in (lt_le_e k h TMP_7 TMP_92 TMP_116))))))))))))).

theorem aplus_ahead_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (a1: A).(\forall (a2: A).(eq A 
(aplus g (AHead a1 a2) h) (AHead a1 (aplus g a2 h))))))
\def
 \lambda (g: G).(\lambda (h: nat).(let TMP_5 \def (\lambda (n: nat).(\forall 
(a1: A).(\forall (a2: A).(let TMP_1 \def (AHead a1 a2) in (let TMP_2 \def 
(aplus g TMP_1 n) in (let TMP_3 \def (aplus g a2 n) in (let TMP_4 \def (AHead 
a1 TMP_3) in (eq A TMP_2 TMP_4)))))))) in (let TMP_7 \def (\lambda (a1: 
A).(\lambda (a2: A).(let TMP_6 \def (AHead a1 a2) in (refl_equal A TMP_6)))) 
in (let TMP_33 \def (\lambda (n: nat).(\lambda (H: ((\forall (a1: A).(\forall 
(a2: A).(eq A (aplus g (AHead a1 a2) n) (AHead a1 (aplus g a2 
n))))))).(\lambda (a1: A).(\lambda (a2: A).(let TMP_8 \def (AHead a1 a2) in 
(let TMP_9 \def (asucc g TMP_8) in (let TMP_10 \def (aplus g TMP_9 n) in (let 
TMP_14 \def (\lambda (a: A).(let TMP_11 \def (aplus g a2 n) in (let TMP_12 
\def (asucc g TMP_11) in (let TMP_13 \def (AHead a1 TMP_12) in (eq A a 
TMP_13))))) in (let TMP_15 \def (asucc g a2) in (let TMP_16 \def (aplus g 
TMP_15 n) in (let TMP_21 \def (\lambda (a: A).(let TMP_17 \def (AHead a1 a2) 
in (let TMP_18 \def (asucc g TMP_17) in (let TMP_19 \def (aplus g TMP_18 n) 
in (let TMP_20 \def (AHead a1 a) in (eq A TMP_19 TMP_20)))))) in (let TMP_22 
\def (asucc g a2) in (let TMP_23 \def (H a1 TMP_22) in (let TMP_24 \def 
(aplus g a2 n) in (let TMP_25 \def (asucc g TMP_24) in (let TMP_26 \def 
(aplus_asucc g n a2) in (let TMP_27 \def (eq_ind A TMP_16 TMP_21 TMP_23 
TMP_25 TMP_26) in (let TMP_28 \def (AHead a1 a2) in (let TMP_29 \def (aplus g 
TMP_28 n) in (let TMP_30 \def (asucc g TMP_29) in (let TMP_31 \def (AHead a1 
a2) in (let TMP_32 \def (aplus_asucc g n TMP_31) in (eq_ind A TMP_10 TMP_14 
TMP_27 TMP_30 TMP_32))))))))))))))))))))))) in (nat_ind TMP_5 TMP_7 TMP_33 
h))))).

theorem aplus_asucc_false:
 \forall (g: G).(\forall (a: A).(\forall (h: nat).((eq A (aplus g (asucc g a) 
h) a) \to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_1 \def (\lambda (a0: A).(\forall (h: 
nat).((eq A (aplus g (asucc g a0) h) a0) \to (\forall (P: Prop).P)))) in (let 
TMP_70 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (h: nat).(\lambda 
(H: (eq A (aplus g (match n with [O \Rightarrow (ASort O (next g n0)) | (S 
h0) \Rightarrow (ASort h0 n0)]) h) (ASort n n0))).(\lambda (P: Prop).(let 
TMP_2 \def (\lambda (n1: nat).((eq A (aplus g (match n1 with [O \Rightarrow 
(ASort O (next g n0)) | (S h0) \Rightarrow (ASort h0 n0)]) h) (ASort n1 n0)) 
\to P)) in (let TMP_36 \def (\lambda (H0: (eq A (aplus g (ASort O (next g 
n0)) h) (ASort O n0))).(let TMP_3 \def (next g n0) in (let TMP_4 \def (ASort 
O TMP_3) in (let TMP_5 \def (aplus g TMP_4 h) in (let TMP_7 \def (\lambda 
(a0: A).(let TMP_6 \def (ASort O n0) in (eq A a0 TMP_6))) in (let TMP_8 \def 
(minus O h) in (let TMP_9 \def (next g n0) in (let TMP_10 \def (minus h O) in 
(let TMP_11 \def (next_plus g TMP_9 TMP_10) in (let TMP_12 \def (ASort TMP_8 
TMP_11) in (let TMP_13 \def (next g n0) in (let TMP_14 \def 
(aplus_asort_simpl g h O TMP_13) in (let H1 \def (eq_ind A TMP_5 TMP_7 H0 
TMP_12 TMP_14) in (let TMP_18 \def (\lambda (e: A).(match e with [(ASort _ 
n1) \Rightarrow n1 | (AHead _ _) \Rightarrow (let TMP_16 \def (next g n0) in 
(let TMP_17 \def (minus h O) in (next_plus g TMP_16 TMP_17)))])) in (let 
TMP_19 \def (minus O h) in (let TMP_20 \def (next g n0) in (let TMP_21 \def 
(minus h O) in (let TMP_22 \def (next_plus g TMP_20 TMP_21) in (let TMP_23 
\def (ASort TMP_19 TMP_22) in (let TMP_24 \def (ASort O n0) in (let H2 \def 
(f_equal A nat TMP_18 TMP_23 TMP_24 H1) in (let TMP_25 \def (minus h O) in 
(let TMP_28 \def (\lambda (n1: nat).(let TMP_26 \def (next g n0) in (let 
TMP_27 \def (next_plus g TMP_26 n1) in (eq nat TMP_27 n0)))) in (let TMP_29 
\def (minus_n_O h) in (let H3 \def (eq_ind_r nat TMP_25 TMP_28 H2 h TMP_29) 
in (let TMP_30 \def (le_n n0) in (let TMP_31 \def (next g n0) in (let TMP_32 
\def (next_plus g TMP_31 h) in (let TMP_33 \def (\lambda (n1: nat).(lt n0 
n1)) in (let TMP_34 \def (next_plus_lt g h n0) in (let TMP_35 \def (eq_ind 
nat TMP_32 TMP_33 TMP_34 n0 H3) in (le_lt_false n0 n0 TMP_30 TMP_35 
P)))))))))))))))))))))))))))))))) in (let TMP_69 \def (\lambda (n1: 
nat).(\lambda (_: (((eq A (aplus g (match n1 with [O \Rightarrow (ASort O 
(next g n0)) | (S h0) \Rightarrow (ASort h0 n0)]) h) (ASort n1 n0)) \to 
P))).(\lambda (H0: (eq A (aplus g (ASort n1 n0) h) (ASort (S n1) n0))).(let 
TMP_37 \def (ASort n1 n0) in (let TMP_38 \def (aplus g TMP_37 h) in (let 
TMP_41 \def (\lambda (a0: A).(let TMP_39 \def (S n1) in (let TMP_40 \def 
(ASort TMP_39 n0) in (eq A a0 TMP_40)))) in (let TMP_42 \def (minus n1 h) in 
(let TMP_43 \def (minus h n1) in (let TMP_44 \def (next_plus g n0 TMP_43) in 
(let TMP_45 \def (ASort TMP_42 TMP_44) in (let TMP_46 \def (aplus_asort_simpl 
g h n1 n0) in (let H1 \def (eq_ind A TMP_38 TMP_41 H0 TMP_45 TMP_46) in (let 
TMP_47 \def (\lambda (e: A).(match e with [(ASort n2 _) \Rightarrow n2 | 
(AHead _ _) \Rightarrow (minus n1 h)])) in (let TMP_48 \def (minus n1 h) in 
(let TMP_49 \def (minus h n1) in (let TMP_50 \def (next_plus g n0 TMP_49) in 
(let TMP_51 \def (ASort TMP_48 TMP_50) in (let TMP_52 \def (S n1) in (let 
TMP_53 \def (ASort TMP_52 n0) in (let H2 \def (f_equal A nat TMP_47 TMP_51 
TMP_53 H1) in (let TMP_56 \def (\lambda (e: A).(match e with [(ASort _ n2) 
\Rightarrow n2 | (AHead _ _) \Rightarrow (let TMP_55 \def (minus h n1) in 
(next_plus g n0 TMP_55))])) in (let TMP_57 \def (minus n1 h) in (let TMP_58 
\def (minus h n1) in (let TMP_59 \def (next_plus g n0 TMP_58) in (let TMP_60 
\def (ASort TMP_57 TMP_59) in (let TMP_61 \def (S n1) in (let TMP_62 \def 
(ASort TMP_61 n0) in (let H3 \def (f_equal A nat TMP_56 TMP_60 TMP_62 H1) in 
(let TMP_68 \def (\lambda (H4: (eq nat (minus n1 h) (S n1))).(let TMP_63 \def 
(minus n1 h) in (let TMP_64 \def (\lambda (n2: nat).(le n2 n1)) in (let 
TMP_65 \def (minus_le n1 h) in (let TMP_66 \def (S n1) in (let TMP_67 \def 
(eq_ind nat TMP_63 TMP_64 TMP_65 TMP_66 H4) in (le_Sx_x n1 TMP_67 P))))))) in 
(TMP_68 H2)))))))))))))))))))))))))))))) in (nat_ind TMP_2 TMP_36 TMP_69 n 
H))))))))) in (let TMP_88 \def (\lambda (a0: A).(\lambda (_: ((\forall (h: 
nat).((eq A (aplus g (asucc g a0) h) a0) \to (\forall (P: 
Prop).P))))).(\lambda (a1: A).(\lambda (H0: ((\forall (h: nat).((eq A (aplus 
g (asucc g a1) h) a1) \to (\forall (P: Prop).P))))).(\lambda (h: 
nat).(\lambda (H1: (eq A (aplus g (AHead a0 (asucc g a1)) h) (AHead a0 
a1))).(\lambda (P: Prop).(let TMP_71 \def (asucc g a1) in (let TMP_72 \def 
(AHead a0 TMP_71) in (let TMP_73 \def (aplus g TMP_72 h) in (let TMP_75 \def 
(\lambda (a2: A).(let TMP_74 \def (AHead a0 a1) in (eq A a2 TMP_74))) in (let 
TMP_76 \def (asucc g a1) in (let TMP_77 \def (aplus g TMP_76 h) in (let 
TMP_78 \def (AHead a0 TMP_77) in (let TMP_79 \def (asucc g a1) in (let TMP_80 
\def (aplus_ahead_simpl g h a0 TMP_79) in (let H2 \def (eq_ind A TMP_73 
TMP_75 H1 TMP_78 TMP_80) in (let TMP_83 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow (let TMP_82 \def (asucc g a1) in (aplus g TMP_82 h)) 
| (AHead _ a2) \Rightarrow a2])) in (let TMP_84 \def (asucc g a1) in (let 
TMP_85 \def (aplus g TMP_84 h) in (let TMP_86 \def (AHead a0 TMP_85) in (let 
TMP_87 \def (AHead a0 a1) in (let H3 \def (f_equal A A TMP_83 TMP_86 TMP_87 
H2) in (H0 h H3 P)))))))))))))))))))))))) in (A_ind TMP_1 TMP_70 TMP_88 
a))))).

theorem aplus_inj:
 \forall (g: G).(\forall (h1: nat).(\forall (h2: nat).(\forall (a: A).((eq A 
(aplus g a h1) (aplus g a h2)) \to (eq nat h1 h2)))))
\def
 \lambda (g: G).(\lambda (h1: nat).(let TMP_1 \def (\lambda (n: nat).(\forall 
(h2: nat).(\forall (a: A).((eq A (aplus g a n) (aplus g a h2)) \to (eq nat n 
h2))))) in (let TMP_16 \def (\lambda (h2: nat).(let TMP_2 \def (\lambda (n: 
nat).(\forall (a: A).((eq A (aplus g a O) (aplus g a n)) \to (eq nat O n)))) 
in (let TMP_3 \def (\lambda (a: A).(\lambda (_: (eq A a a)).(refl_equal nat 
O))) in (let TMP_15 \def (\lambda (n: nat).(\lambda (_: ((\forall (a: A).((eq 
A a (aplus g a n)) \to (eq nat O n))))).(\lambda (a: A).(\lambda (H0: (eq A a 
(asucc g (aplus g a n)))).(let TMP_4 \def (aplus g a n) in (let TMP_5 \def 
(asucc g TMP_4) in (let TMP_6 \def (\lambda (a0: A).(eq A a a0)) in (let 
TMP_7 \def (asucc g a) in (let TMP_8 \def (aplus g TMP_7 n) in (let TMP_9 
\def (aplus_asucc g n a) in (let H1 \def (eq_ind_r A TMP_5 TMP_6 H0 TMP_8 
TMP_9) in (let TMP_10 \def (asucc g a) in (let TMP_11 \def (aplus g TMP_10 n) 
in (let TMP_12 \def (sym_eq A a TMP_11 H1) in (let TMP_13 \def (S n) in (let 
TMP_14 \def (eq nat O TMP_13) in (aplus_asucc_false g a n TMP_12 
TMP_14))))))))))))))))) in (nat_ind TMP_2 TMP_3 TMP_15 h2))))) in (let TMP_47 
\def (\lambda (n: nat).(\lambda (H: ((\forall (h2: nat).(\forall (a: A).((eq 
A (aplus g a n) (aplus g a h2)) \to (eq nat n h2)))))).(\lambda (h2: 
nat).(let TMP_18 \def (\lambda (n0: nat).(\forall (a: A).((eq A (aplus g a (S 
n)) (aplus g a n0)) \to (let TMP_17 \def (S n) in (eq nat TMP_17 n0))))) in 
(let TMP_27 \def (\lambda (a: A).(\lambda (H0: (eq A (asucc g (aplus g a n)) 
a)).(let TMP_19 \def (aplus g a n) in (let TMP_20 \def (asucc g TMP_19) in 
(let TMP_21 \def (\lambda (a0: A).(eq A a0 a)) in (let TMP_22 \def (asucc g 
a) in (let TMP_23 \def (aplus g TMP_22 n) in (let TMP_24 \def (aplus_asucc g 
n a) in (let H1 \def (eq_ind_r A TMP_20 TMP_21 H0 TMP_23 TMP_24) in (let 
TMP_25 \def (S n) in (let TMP_26 \def (eq nat TMP_25 O) in (aplus_asucc_false 
g a n H1 TMP_26)))))))))))) in (let TMP_46 \def (\lambda (n0: nat).(\lambda 
(_: ((\forall (a: A).((eq A (asucc g (aplus g a n)) (aplus g a n0)) \to (eq 
nat (S n) n0))))).(\lambda (a: A).(\lambda (H1: (eq A (asucc g (aplus g a n)) 
(asucc g (aplus g a n0)))).(let TMP_28 \def (aplus g a n) in (let TMP_29 \def 
(asucc g TMP_28) in (let TMP_32 \def (\lambda (a0: A).(let TMP_30 \def (aplus 
g a n0) in (let TMP_31 \def (asucc g TMP_30) in (eq A a0 TMP_31)))) in (let 
TMP_33 \def (asucc g a) in (let TMP_34 \def (aplus g TMP_33 n) in (let TMP_35 
\def (aplus_asucc g n a) in (let H2 \def (eq_ind_r A TMP_29 TMP_32 H1 TMP_34 
TMP_35) in (let TMP_36 \def (aplus g a n0) in (let TMP_37 \def (asucc g 
TMP_36) in (let TMP_40 \def (\lambda (a0: A).(let TMP_38 \def (asucc g a) in 
(let TMP_39 \def (aplus g TMP_38 n) in (eq A TMP_39 a0)))) in (let TMP_41 
\def (asucc g a) in (let TMP_42 \def (aplus g TMP_41 n0) in (let TMP_43 \def 
(aplus_asucc g n0 a) in (let H3 \def (eq_ind_r A TMP_37 TMP_40 H2 TMP_42 
TMP_43) in (let TMP_44 \def (asucc g a) in (let TMP_45 \def (H n0 TMP_44 H3) 
in (f_equal nat nat S n n0 TMP_45))))))))))))))))))))) in (nat_ind TMP_18 
TMP_27 TMP_46 h2))))))) in (nat_ind TMP_1 TMP_16 TMP_47 h1))))).

