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

include "ground_1/preamble.ma".

theorem nat_dec:
 \forall (n1: nat).(\forall (n2: nat).(or (eq nat n1 n2) ((eq nat n1 n2) \to 
(\forall (P: Prop).P))))
\def
 \lambda (n1: nat).(let TMP_3 \def (\lambda (n: nat).(\forall (n2: nat).(let 
TMP_1 \def (eq nat n n2) in (let TMP_2 \def ((eq nat n n2) \to (\forall (P: 
Prop).P)) in (or TMP_1 TMP_2))))) in (let TMP_18 \def (\lambda (n2: nat).(let 
TMP_6 \def (\lambda (n: nat).(let TMP_4 \def (eq nat O n) in (let TMP_5 \def 
((eq nat O n) \to (\forall (P: Prop).P)) in (or TMP_4 TMP_5)))) in (let TMP_7 
\def (eq nat O O) in (let TMP_8 \def ((eq nat O O) \to (\forall (P: Prop).P)) 
in (let TMP_9 \def (refl_equal nat O) in (let TMP_10 \def (or_introl TMP_7 
TMP_8 TMP_9) in (let TMP_17 \def (\lambda (n: nat).(\lambda (_: (or (eq nat O 
n) ((eq nat O n) \to (\forall (P: Prop).P)))).(let TMP_11 \def (S n) in (let 
TMP_12 \def (eq nat O TMP_11) in (let TMP_13 \def ((eq nat O (S n)) \to 
(\forall (P: Prop).P)) in (let TMP_16 \def (\lambda (H0: (eq nat O (S 
n))).(\lambda (P: Prop).(let TMP_14 \def (\lambda (ee: nat).(match ee with [O 
\Rightarrow True | (S _) \Rightarrow False])) in (let TMP_15 \def (S n) in 
(let H1 \def (eq_ind nat O TMP_14 I TMP_15 H0) in (False_ind P H1)))))) in 
(or_intror TMP_12 TMP_13 TMP_16))))))) in (nat_ind TMP_6 TMP_10 TMP_17 
n2)))))))) in (let TMP_71 \def (\lambda (n: nat).(\lambda (H: ((\forall (n2: 
nat).(or (eq nat n n2) ((eq nat n n2) \to (\forall (P: Prop).P)))))).(\lambda 
(n2: nat).(let TMP_22 \def (\lambda (n0: nat).(let TMP_19 \def (S n) in (let 
TMP_20 \def (eq nat TMP_19 n0) in (let TMP_21 \def ((eq nat (S n) n0) \to 
(\forall (P: Prop).P)) in (or TMP_20 TMP_21))))) in (let TMP_23 \def (S n) in 
(let TMP_24 \def (eq nat TMP_23 O) in (let TMP_25 \def ((eq nat (S n) O) \to 
(\forall (P: Prop).P)) in (let TMP_28 \def (\lambda (H0: (eq nat (S n) 
O)).(\lambda (P: Prop).(let TMP_26 \def (S n) in (let TMP_27 \def (\lambda 
(ee: nat).(match ee with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H1 \def (eq_ind nat TMP_26 TMP_27 I O H0) in (False_ind P H1)))))) in 
(let TMP_29 \def (or_intror TMP_24 TMP_25 TMP_28) in (let TMP_70 \def 
(\lambda (n0: nat).(\lambda (H0: (or (eq nat (S n) n0) ((eq nat (S n) n0) \to 
(\forall (P: Prop).P)))).(let TMP_30 \def (eq nat n n0) in (let TMP_31 \def 
((eq nat n n0) \to (\forall (P: Prop).P)) in (let TMP_32 \def (S n) in (let 
TMP_33 \def (S n0) in (let TMP_34 \def (eq nat TMP_32 TMP_33) in (let TMP_35 
\def ((eq nat (S n) (S n0)) \to (\forall (P: Prop).P)) in (let TMP_36 \def 
(or TMP_34 TMP_35) in (let TMP_53 \def (\lambda (H1: (eq nat n n0)).(let 
TMP_40 \def (\lambda (n3: nat).(let TMP_37 \def (S n) in (let TMP_38 \def (eq 
nat TMP_37 n3) in (let TMP_39 \def ((eq nat (S n) n3) \to (\forall (P: 
Prop).P)) in (or TMP_38 TMP_39))))) in (let H2 \def (eq_ind_r nat n0 TMP_40 
H0 n H1) in (let TMP_45 \def (\lambda (n3: nat).(let TMP_41 \def (S n) in 
(let TMP_42 \def (S n3) in (let TMP_43 \def (eq nat TMP_41 TMP_42) in (let 
TMP_44 \def ((eq nat (S n) (S n3)) \to (\forall (P: Prop).P)) in (or TMP_43 
TMP_44)))))) in (let TMP_46 \def (S n) in (let TMP_47 \def (S n) in (let 
TMP_48 \def (eq nat TMP_46 TMP_47) in (let TMP_49 \def ((eq nat (S n) (S n)) 
\to (\forall (P: Prop).P)) in (let TMP_50 \def (S n) in (let TMP_51 \def 
(refl_equal nat TMP_50) in (let TMP_52 \def (or_introl TMP_48 TMP_49 TMP_51) 
in (eq_ind nat n TMP_45 TMP_52 n0 H1)))))))))))) in (let TMP_68 \def (\lambda 
(H1: (((eq nat n n0) \to (\forall (P: Prop).P)))).(let TMP_54 \def (S n) in 
(let TMP_55 \def (S n0) in (let TMP_56 \def (eq nat TMP_54 TMP_55) in (let 
TMP_57 \def ((eq nat (S n) (S n0)) \to (\forall (P: Prop).P)) in (let TMP_67 
\def (\lambda (H2: (eq nat (S n) (S n0))).(\lambda (P: Prop).(let TMP_58 \def 
(\lambda (e: nat).(match e with [O \Rightarrow n | (S n3) \Rightarrow n3])) 
in (let TMP_59 \def (S n) in (let TMP_60 \def (S n0) in (let H3 \def (f_equal 
nat nat TMP_58 TMP_59 TMP_60 H2) in (let TMP_61 \def (\lambda (n3: nat).((eq 
nat n n3) \to (\forall (P0: Prop).P0))) in (let H4 \def (eq_ind_r nat n0 
TMP_61 H1 n H3) in (let TMP_65 \def (\lambda (n3: nat).(let TMP_62 \def (S n) 
in (let TMP_63 \def (eq nat TMP_62 n3) in (let TMP_64 \def ((eq nat (S n) n3) 
\to (\forall (P0: Prop).P0)) in (or TMP_63 TMP_64))))) in (let H5 \def 
(eq_ind_r nat n0 TMP_65 H0 n H3) in (let TMP_66 \def (refl_equal nat n) in 
(H4 TMP_66 P)))))))))))) in (or_intror TMP_56 TMP_57 TMP_67))))))) in (let 
TMP_69 \def (H n0) in (or_ind TMP_30 TMP_31 TMP_36 TMP_53 TMP_68 
TMP_69))))))))))))) in (nat_ind TMP_22 TMP_29 TMP_70 n2))))))))))) in 
(nat_ind TMP_3 TMP_18 TMP_71 n1)))).

theorem simpl_plus_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus m n) 
(plus p n)) \to (eq nat m p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat 
(plus m n) (plus p n))).(let TMP_1 \def (plus m n) in (let TMP_3 \def 
(\lambda (n0: nat).(let TMP_2 \def (plus n p) in (eq nat n0 TMP_2))) in (let 
TMP_4 \def (plus p n) in (let TMP_6 \def (\lambda (n0: nat).(let TMP_5 \def 
(plus n p) in (eq nat n0 TMP_5))) in (let TMP_7 \def (plus_sym p n) in (let 
TMP_8 \def (plus m n) in (let TMP_9 \def (eq_ind_r nat TMP_4 TMP_6 TMP_7 
TMP_8 H) in (let TMP_10 \def (plus n m) in (let TMP_11 \def (plus_sym n m) in 
(let TMP_12 \def (eq_ind_r nat TMP_1 TMP_3 TMP_9 TMP_10 TMP_11) in 
(simpl_plus_l n m p TMP_12)))))))))))))).

theorem minus_Sx_Sy:
 \forall (x: nat).(\forall (y: nat).(eq nat (minus (S x) (S y)) (minus x y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_1 \def (minus x y) in 
(refl_equal nat TMP_1))).

theorem minus_plus_r:
 \forall (m: nat).(\forall (n: nat).(eq nat (minus (plus m n) n) m))
\def
 \lambda (m: nat).(\lambda (n: nat).(let TMP_1 \def (plus n m) in (let TMP_3 
\def (\lambda (n0: nat).(let TMP_2 \def (minus n0 n) in (eq nat TMP_2 m))) in 
(let TMP_4 \def (minus_plus n m) in (let TMP_5 \def (plus m n) in (let TMP_6 
\def (plus_sym m n) in (eq_ind_r nat TMP_1 TMP_3 TMP_4 TMP_5 TMP_6))))))).

theorem plus_permute_2_in_3:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).(eq nat (plus (plus x 
y) z) (plus (plus x z) y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(let TMP_1 \def (plus y 
z) in (let TMP_2 \def (plus x TMP_1) in (let TMP_5 \def (\lambda (n: 
nat).(let TMP_3 \def (plus x z) in (let TMP_4 \def (plus TMP_3 y) in (eq nat 
n TMP_4)))) in (let TMP_6 \def (plus z y) in (let TMP_10 \def (\lambda (n: 
nat).(let TMP_7 \def (plus x n) in (let TMP_8 \def (plus x z) in (let TMP_9 
\def (plus TMP_8 y) in (eq nat TMP_7 TMP_9))))) in (let TMP_11 \def (plus x 
z) in (let TMP_12 \def (plus TMP_11 y) in (let TMP_15 \def (\lambda (n: 
nat).(let TMP_13 \def (plus x z) in (let TMP_14 \def (plus TMP_13 y) in (eq 
nat n TMP_14)))) in (let TMP_16 \def (plus x z) in (let TMP_17 \def (plus 
TMP_16 y) in (let TMP_18 \def (refl_equal nat TMP_17) in (let TMP_19 \def 
(plus z y) in (let TMP_20 \def (plus x TMP_19) in (let TMP_21 \def 
(plus_assoc_r x z y) in (let TMP_22 \def (eq_ind nat TMP_12 TMP_15 TMP_18 
TMP_20 TMP_21) in (let TMP_23 \def (plus y z) in (let TMP_24 \def (plus_sym y 
z) in (let TMP_25 \def (eq_ind_r nat TMP_6 TMP_10 TMP_22 TMP_23 TMP_24) in 
(let TMP_26 \def (plus x y) in (let TMP_27 \def (plus TMP_26 z) in (let 
TMP_28 \def (plus_assoc_r x y z) in (eq_ind_r nat TMP_2 TMP_5 TMP_25 TMP_27 
TMP_28)))))))))))))))))))))))).

theorem plus_permute_2_in_3_assoc:
 \forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq nat (plus (plus n 
h) k) (plus n (plus k h)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(let TMP_1 \def (plus n 
k) in (let TMP_2 \def (plus TMP_1 h) in (let TMP_5 \def (\lambda (n0: 
nat).(let TMP_3 \def (plus k h) in (let TMP_4 \def (plus n TMP_3) in (eq nat 
n0 TMP_4)))) in (let TMP_6 \def (plus n k) in (let TMP_7 \def (plus TMP_6 h) 
in (let TMP_10 \def (\lambda (n0: nat).(let TMP_8 \def (plus n k) in (let 
TMP_9 \def (plus TMP_8 h) in (eq nat TMP_9 n0)))) in (let TMP_11 \def (plus n 
k) in (let TMP_12 \def (plus TMP_11 h) in (let TMP_13 \def (refl_equal nat 
TMP_12) in (let TMP_14 \def (plus k h) in (let TMP_15 \def (plus n TMP_14) in 
(let TMP_16 \def (plus_assoc_l n k h) in (let TMP_17 \def (eq_ind_r nat TMP_7 
TMP_10 TMP_13 TMP_15 TMP_16) in (let TMP_18 \def (plus n h) in (let TMP_19 
\def (plus TMP_18 k) in (let TMP_20 \def (plus_permute_2_in_3 n h k) in 
(eq_ind_r nat TMP_2 TMP_5 TMP_17 TMP_19 TMP_20))))))))))))))))))).

theorem plus_O:
 \forall (x: nat).(\forall (y: nat).((eq nat (plus x y) O) \to (land (eq nat 
x O) (eq nat y O))))
\def
 \lambda (x: nat).(let TMP_3 \def (\lambda (n: nat).(\forall (y: nat).((eq 
nat (plus n y) O) \to (let TMP_1 \def (eq nat n O) in (let TMP_2 \def (eq nat 
y O) in (land TMP_1 TMP_2)))))) in (let TMP_7 \def (\lambda (y: nat).(\lambda 
(H: (eq nat (plus O y) O)).(let TMP_4 \def (eq nat O O) in (let TMP_5 \def 
(eq nat y O) in (let TMP_6 \def (refl_equal nat O) in (conj TMP_4 TMP_5 TMP_6 
H)))))) in (let TMP_16 \def (\lambda (n: nat).(\lambda (_: ((\forall (y: 
nat).((eq nat (plus n y) O) \to (land (eq nat n O) (eq nat y O)))))).(\lambda 
(y: nat).(\lambda (H0: (eq nat (plus (S n) y) O)).(let H1 \def (match H0 with 
[refl_equal \Rightarrow (\lambda (H1: (eq nat (plus (S n) y) O)).(let TMP_8 
\def (S n) in (let TMP_9 \def (plus TMP_8 y) in (let TMP_10 \def (\lambda (e: 
nat).(match e with [O \Rightarrow False | (S _) \Rightarrow True])) in (let 
H2 \def (eq_ind nat TMP_9 TMP_10 I O H1) in (let TMP_11 \def (S n) in (let 
TMP_12 \def (eq nat TMP_11 O) in (let TMP_13 \def (eq nat y O) in (let TMP_14 
\def (land TMP_12 TMP_13) in (False_ind TMP_14 H2))))))))))]) in (let TMP_15 
\def (refl_equal nat O) in (H1 TMP_15))))))) in (nat_ind TMP_3 TMP_7 TMP_16 
x)))).

theorem minus_Sx_SO:
 \forall (x: nat).(eq nat (minus (S x) (S O)) x)
\def
 \lambda (x: nat).(let TMP_1 \def (\lambda (n: nat).(eq nat n x)) in (let 
TMP_2 \def (refl_equal nat x) in (let TMP_3 \def (minus x O) in (let TMP_4 
\def (minus_n_O x) in (eq_ind nat x TMP_1 TMP_2 TMP_3 TMP_4))))).

theorem nat_dec_neg:
 \forall (i: nat).(\forall (j: nat).(or (not (eq nat i j)) (eq nat i j)))
\def
 \lambda (i: nat).(let TMP_4 \def (\lambda (n: nat).(\forall (j: nat).(let 
TMP_1 \def (eq nat n j) in (let TMP_2 \def (not TMP_1) in (let TMP_3 \def (eq 
nat n j) in (or TMP_2 TMP_3)))))) in (let TMP_21 \def (\lambda (j: nat).(let 
TMP_8 \def (\lambda (n: nat).(let TMP_5 \def (eq nat O n) in (let TMP_6 \def 
(not TMP_5) in (let TMP_7 \def (eq nat O n) in (or TMP_6 TMP_7))))) in (let 
TMP_9 \def (eq nat O O) in (let TMP_10 \def (not TMP_9) in (let TMP_11 \def 
(eq nat O O) in (let TMP_12 \def (refl_equal nat O) in (let TMP_13 \def 
(or_intror TMP_10 TMP_11 TMP_12) in (let TMP_20 \def (\lambda (n: 
nat).(\lambda (_: (or (not (eq nat O n)) (eq nat O n))).(let TMP_14 \def (S 
n) in (let TMP_15 \def (eq nat O TMP_14) in (let TMP_16 \def (not TMP_15) in 
(let TMP_17 \def (S n) in (let TMP_18 \def (eq nat O TMP_17) in (let TMP_19 
\def (O_S n) in (or_introl TMP_16 TMP_18 TMP_19))))))))) in (nat_ind TMP_8 
TMP_13 TMP_20 j))))))))) in (let TMP_68 \def (\lambda (n: nat).(\lambda (H: 
((\forall (j: nat).(or (not (eq nat n j)) (eq nat n j))))).(\lambda (j: 
nat).(let TMP_27 \def (\lambda (n0: nat).(let TMP_22 \def (S n) in (let 
TMP_23 \def (eq nat TMP_22 n0) in (let TMP_24 \def (not TMP_23) in (let 
TMP_25 \def (S n) in (let TMP_26 \def (eq nat TMP_25 n0) in (or TMP_24 
TMP_26))))))) in (let TMP_28 \def (S n) in (let TMP_29 \def (eq nat TMP_28 O) 
in (let TMP_30 \def (not TMP_29) in (let TMP_31 \def (S n) in (let TMP_32 
\def (eq nat TMP_31 O) in (let TMP_33 \def (S n) in (let TMP_34 \def (O_S n) 
in (let TMP_35 \def (sym_not_eq nat O TMP_33 TMP_34) in (let TMP_36 \def 
(or_introl TMP_30 TMP_32 TMP_35) in (let TMP_67 \def (\lambda (n0: 
nat).(\lambda (_: (or (not (eq nat (S n) n0)) (eq nat (S n) n0))).(let TMP_37 
\def (eq nat n n0) in (let TMP_38 \def (not TMP_37) in (let TMP_39 \def (eq 
nat n n0) in (let TMP_40 \def (S n) in (let TMP_41 \def (S n0) in (let TMP_42 
\def (eq nat TMP_40 TMP_41) in (let TMP_43 \def (not TMP_42) in (let TMP_44 
\def (S n) in (let TMP_45 \def (S n0) in (let TMP_46 \def (eq nat TMP_44 
TMP_45) in (let TMP_47 \def (or TMP_43 TMP_46) in (let TMP_56 \def (\lambda 
(H1: (not (eq nat n n0))).(let TMP_48 \def (S n) in (let TMP_49 \def (S n0) 
in (let TMP_50 \def (eq nat TMP_48 TMP_49) in (let TMP_51 \def (not TMP_50) 
in (let TMP_52 \def (S n) in (let TMP_53 \def (S n0) in (let TMP_54 \def (eq 
nat TMP_52 TMP_53) in (let TMP_55 \def (not_eq_S n n0 H1) in (or_introl 
TMP_51 TMP_54 TMP_55)))))))))) in (let TMP_65 \def (\lambda (H1: (eq nat n 
n0)).(let TMP_57 \def (S n) in (let TMP_58 \def (S n0) in (let TMP_59 \def 
(eq nat TMP_57 TMP_58) in (let TMP_60 \def (not TMP_59) in (let TMP_61 \def 
(S n) in (let TMP_62 \def (S n0) in (let TMP_63 \def (eq nat TMP_61 TMP_62) 
in (let TMP_64 \def (f_equal nat nat S n n0 H1) in (or_intror TMP_60 TMP_63 
TMP_64)))))))))) in (let TMP_66 \def (H n0) in (or_ind TMP_38 TMP_39 TMP_47 
TMP_56 TMP_65 TMP_66))))))))))))))))) in (nat_ind TMP_27 TMP_36 TMP_67 
j))))))))))))))) in (nat_ind TMP_4 TMP_21 TMP_68 i)))).

theorem neq_eq_e:
 \forall (i: nat).(\forall (j: nat).(\forall (P: Prop).((((not (eq nat i j)) 
\to P)) \to ((((eq nat i j) \to P)) \to P))))
\def
 \lambda (i: nat).(\lambda (j: nat).(\lambda (P: Prop).(\lambda (H: (((not 
(eq nat i j)) \to P))).(\lambda (H0: (((eq nat i j) \to P))).(let o \def 
(nat_dec_neg i j) in (let TMP_1 \def (eq nat i j) in (let TMP_2 \def (not 
TMP_1) in (let TMP_3 \def (eq nat i j) in (or_ind TMP_2 TMP_3 P H H0 
o))))))))).

theorem le_false:
 \forall (m: nat).(\forall (n: nat).(\forall (P: Prop).((le m n) \to ((le (S 
n) m) \to P))))
\def
 \lambda (m: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (n0: 
nat).(\forall (P: Prop).((le n n0) \to ((le (S n0) n) \to P))))) in (let 
TMP_9 \def (\lambda (n: nat).(\lambda (P: Prop).(\lambda (_: (le O 
n)).(\lambda (H0: (le (S n) O)).(let H1 \def (match H0 with [le_n \Rightarrow 
(\lambda (H1: (eq nat (S n) O)).(let TMP_6 \def (S n) in (let TMP_7 \def 
(\lambda (e: nat).(match e with [O \Rightarrow False | (S _) \Rightarrow 
True])) in (let H2 \def (eq_ind nat TMP_6 TMP_7 I O H1) in (False_ind P 
H2))))) | (le_S m0 H1) \Rightarrow (\lambda (H2: (eq nat (S m0) O)).(let 
TMP_2 \def (S m0) in (let TMP_3 \def (\lambda (e: nat).(match e with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H3 \def (eq_ind nat 
TMP_2 TMP_3 I O H2) in (let TMP_4 \def ((le (S n) m0) \to P) in (let TMP_5 
\def (False_ind TMP_4 H3) in (TMP_5 H1)))))))]) in (let TMP_8 \def 
(refl_equal nat O) in (H1 TMP_8))))))) in (let TMP_23 \def (\lambda (n: 
nat).(\lambda (H: ((\forall (n0: nat).(\forall (P: Prop).((le n n0) \to ((le 
(S n0) n) \to P)))))).(\lambda (n0: nat).(let TMP_10 \def (\lambda (n1: 
nat).(\forall (P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) \to P)))) in 
(let TMP_18 \def (\lambda (P: Prop).(\lambda (H0: (le (S n) O)).(\lambda (_: 
(le (S O) (S n))).(let H2 \def (match H0 with [le_n \Rightarrow (\lambda (H2: 
(eq nat (S n) O)).(let TMP_15 \def (S n) in (let TMP_16 \def (\lambda (e: 
nat).(match e with [O \Rightarrow False | (S _) \Rightarrow True])) in (let 
H3 \def (eq_ind nat TMP_15 TMP_16 I O H2) in (False_ind P H3))))) | (le_S m0 
H2) \Rightarrow (\lambda (H3: (eq nat (S m0) O)).(let TMP_11 \def (S m0) in 
(let TMP_12 \def (\lambda (e: nat).(match e with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H4 \def (eq_ind nat TMP_11 TMP_12 I O H3) in (let 
TMP_13 \def ((le (S n) m0) \to P) in (let TMP_14 \def (False_ind TMP_13 H4) 
in (TMP_14 H2)))))))]) in (let TMP_17 \def (refl_equal nat O) in (H2 
TMP_17)))))) in (let TMP_22 \def (\lambda (n1: nat).(\lambda (_: ((\forall 
(P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) \to P))))).(\lambda (P: 
Prop).(\lambda (H1: (le (S n) (S n1))).(\lambda (H2: (le (S (S n1)) (S 
n))).(let TMP_19 \def (le_S_n n n1 H1) in (let TMP_20 \def (S n1) in (let 
TMP_21 \def (le_S_n TMP_20 n H2) in (H n1 P TMP_19 TMP_21))))))))) in 
(nat_ind TMP_10 TMP_18 TMP_22 n0))))))) in (nat_ind TMP_1 TMP_9 TMP_23 m)))).

theorem le_Sx_x:
 \forall (x: nat).((le (S x) x) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) x)).(\lambda (P: Prop).(let H0 \def 
le_Sn_n in (let TMP_1 \def (H0 x H) in (False_ind P TMP_1))))).

theorem le_n_pred:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (pred n) (pred m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_3 \def 
(\lambda (n0: nat).(let TMP_1 \def (pred n) in (let TMP_2 \def (pred n0) in 
(le TMP_1 TMP_2)))) in (let TMP_4 \def (pred n) in (let TMP_5 \def (le_n 
TMP_4) in (let TMP_9 \def (\lambda (m0: nat).(\lambda (_: (le n m0)).(\lambda 
(H1: (le (pred n) (pred m0))).(let TMP_6 \def (pred n) in (let TMP_7 \def 
(pred m0) in (let TMP_8 \def (le_pred_n m0) in (le_trans TMP_6 TMP_7 m0 H1 
TMP_8))))))) in (le_ind n TMP_3 TMP_5 TMP_9 m H))))))).

theorem minus_le:
 \forall (x: nat).(\forall (y: nat).(le (minus x y) x))
\def
 \lambda (x: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (y: nat).(let 
TMP_1 \def (minus n y) in (le TMP_1 n)))) in (let TMP_3 \def (\lambda (_: 
nat).(le_O_n O)) in (let TMP_13 \def (\lambda (n: nat).(\lambda (H: ((\forall 
(y: nat).(le (minus n y) n)))).(\lambda (y: nat).(let TMP_7 \def (\lambda 
(n0: nat).(let TMP_4 \def (S n) in (let TMP_5 \def (minus TMP_4 n0) in (let 
TMP_6 \def (S n) in (le TMP_5 TMP_6))))) in (let TMP_8 \def (S n) in (let 
TMP_9 \def (le_n TMP_8) in (let TMP_12 \def (\lambda (n0: nat).(\lambda (_: 
(le (match n0 with [O \Rightarrow (S n) | (S l) \Rightarrow (minus n l)]) (S 
n))).(let TMP_10 \def (minus n n0) in (let TMP_11 \def (H n0) in (le_S TMP_10 
n TMP_11))))) in (nat_ind TMP_7 TMP_9 TMP_12 y)))))))) in (nat_ind TMP_2 
TMP_3 TMP_13 x)))).

theorem le_plus_minus_sym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus (minus m n) 
n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_1 \def 
(minus m n) in (let TMP_2 \def (plus n TMP_1) in (let TMP_3 \def (\lambda 
(n0: nat).(eq nat m n0)) in (let TMP_4 \def (le_plus_minus n m H) in (let 
TMP_5 \def (minus m n) in (let TMP_6 \def (plus TMP_5 n) in (let TMP_7 \def 
(minus m n) in (let TMP_8 \def (plus_sym TMP_7 n) in (eq_ind_r nat TMP_2 
TMP_3 TMP_4 TMP_6 TMP_8))))))))))).

theorem le_minus_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (\forall (z: nat).((le y z) 
\to (le (minus y x) (minus z x))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (z: 
nat).(\lambda (H0: (le y z)).(let TMP_1 \def (minus y x) in (let TMP_2 \def 
(minus z x) in (let TMP_5 \def (\lambda (n: nat).(let TMP_3 \def (minus z x) 
in (let TMP_4 \def (plus x TMP_3) in (le n TMP_4)))) in (let TMP_6 \def 
(\lambda (n: nat).(le y n)) in (let TMP_7 \def (minus z x) in (let TMP_8 \def 
(plus x TMP_7) in (let TMP_9 \def (le_trans x y z H H0) in (let TMP_10 \def 
(le_plus_minus_r x z TMP_9) in (let TMP_11 \def (eq_ind_r nat z TMP_6 H0 
TMP_8 TMP_10) in (let TMP_12 \def (minus y x) in (let TMP_13 \def (plus x 
TMP_12) in (let TMP_14 \def (le_plus_minus_r x y H) in (let TMP_15 \def 
(eq_ind_r nat y TMP_5 TMP_11 TMP_13 TMP_14) in (simpl_le_plus_l x TMP_1 TMP_2 
TMP_15)))))))))))))))))).

theorem le_minus_plus:
 \forall (z: nat).(\forall (x: nat).((le z x) \to (\forall (y: nat).(eq nat 
(minus (plus x y) z) (plus (minus x z) y)))))
\def
 \lambda (z: nat).(let TMP_5 \def (\lambda (n: nat).(\forall (x: nat).((le n 
x) \to (\forall (y: nat).(let TMP_1 \def (plus x y) in (let TMP_2 \def (minus 
TMP_1 n) in (let TMP_3 \def (minus x n) in (let TMP_4 \def (plus TMP_3 y) in 
(eq nat TMP_2 TMP_4))))))))) in (let TMP_29 \def (\lambda (x: nat).(\lambda 
(H: (le O x)).(let H0 \def (match H with [le_n \Rightarrow (\lambda (H0: (eq 
nat O x)).(let TMP_20 \def (\lambda (n: nat).(\forall (y: nat).(let TMP_16 
\def (plus n y) in (let TMP_17 \def (minus TMP_16 O) in (let TMP_18 \def 
(minus n O) in (let TMP_19 \def (plus TMP_18 y) in (eq nat TMP_17 
TMP_19))))))) in (let TMP_27 \def (\lambda (y: nat).(let TMP_21 \def (minus O 
O) in (let TMP_22 \def (plus TMP_21 y) in (let TMP_23 \def (plus O y) in (let 
TMP_24 \def (minus TMP_23 O) in (let TMP_25 \def (plus O y) in (let TMP_26 
\def (minus_n_O TMP_25) in (sym_eq nat TMP_22 TMP_24 TMP_26)))))))) in 
(eq_ind nat O TMP_20 TMP_27 x H0)))) | (le_S m H0) \Rightarrow (\lambda (H1: 
(eq nat (S m) x)).(let TMP_6 \def (S m) in (let TMP_11 \def (\lambda (n: 
nat).((le O m) \to (\forall (y: nat).(let TMP_7 \def (plus n y) in (let TMP_8 
\def (minus TMP_7 O) in (let TMP_9 \def (minus n O) in (let TMP_10 \def (plus 
TMP_9 y) in (eq nat TMP_8 TMP_10)))))))) in (let TMP_15 \def (\lambda (_: (le 
O m)).(\lambda (y: nat).(let TMP_12 \def (S m) in (let TMP_13 \def (minus 
TMP_12 O) in (let TMP_14 \def (plus TMP_13 y) in (refl_equal nat TMP_14)))))) 
in (eq_ind nat TMP_6 TMP_11 TMP_15 x H1 H0)))))]) in (let TMP_28 \def 
(refl_equal nat x) in (H0 TMP_28))))) in (let TMP_60 \def (\lambda (z0: 
nat).(\lambda (H: ((\forall (x: nat).((le z0 x) \to (\forall (y: nat).(eq nat 
(minus (plus x y) z0) (plus (minus x z0) y))))))).(\lambda (x: nat).(let 
TMP_36 \def (\lambda (n: nat).((le (S z0) n) \to (\forall (y: nat).(let 
TMP_30 \def (plus n y) in (let TMP_31 \def (S z0) in (let TMP_32 \def (minus 
TMP_30 TMP_31) in (let TMP_33 \def (S z0) in (let TMP_34 \def (minus n 
TMP_33) in (let TMP_35 \def (plus TMP_34 y) in (eq nat TMP_32 
TMP_35)))))))))) in (let TMP_57 \def (\lambda (H0: (le (S z0) O)).(\lambda 
(y: nat).(let H1 \def (match H0 with [le_n \Rightarrow (\lambda (H1: (eq nat 
(S z0) O)).(let TMP_47 \def (S z0) in (let TMP_48 \def (\lambda (e: 
nat).(match e with [O \Rightarrow False | (S _) \Rightarrow True])) in (let 
H2 \def (eq_ind nat TMP_47 TMP_48 I O H1) in (let TMP_49 \def (plus O y) in 
(let TMP_50 \def (S z0) in (let TMP_51 \def (minus TMP_49 TMP_50) in (let 
TMP_52 \def (S z0) in (let TMP_53 \def (minus O TMP_52) in (let TMP_54 \def 
(plus TMP_53 y) in (let TMP_55 \def (eq nat TMP_51 TMP_54) in (False_ind 
TMP_55 H2)))))))))))) | (le_S m H1) \Rightarrow (\lambda (H2: (eq nat (S m) 
O)).(let TMP_37 \def (S m) in (let TMP_38 \def (\lambda (e: nat).(match e 
with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H3 \def (eq_ind 
nat TMP_37 TMP_38 I O H2) in (let TMP_45 \def ((le (S z0) m) \to (let TMP_39 
\def (plus O y) in (let TMP_40 \def (S z0) in (let TMP_41 \def (minus TMP_39 
TMP_40) in (let TMP_42 \def (S z0) in (let TMP_43 \def (minus O TMP_42) in 
(let TMP_44 \def (plus TMP_43 y) in (eq nat TMP_41 TMP_44)))))))) in (let 
TMP_46 \def (False_ind TMP_45 H3) in (TMP_46 H1)))))))]) in (let TMP_56 \def 
(refl_equal nat O) in (H1 TMP_56))))) in (let TMP_59 \def (\lambda (n: 
nat).(\lambda (_: (((le (S z0) n) \to (\forall (y: nat).(eq nat (minus (plus 
n y) (S z0)) (plus (minus n (S z0)) y)))))).(\lambda (H1: (le (S z0) (S 
n))).(\lambda (y: nat).(let TMP_58 \def (le_S_n z0 n H1) in (H n TMP_58 
y)))))) in (nat_ind TMP_36 TMP_57 TMP_59 x))))))) in (nat_ind TMP_5 TMP_29 
TMP_60 z)))).

theorem le_minus:
 \forall (x: nat).(\forall (z: nat).(\forall (y: nat).((le (plus x y) z) \to 
(le x (minus z y)))))
\def
 \lambda (x: nat).(\lambda (z: nat).(\lambda (y: nat).(\lambda (H: (le (plus 
x y) z)).(let TMP_1 \def (plus x y) in (let TMP_2 \def (minus TMP_1 y) in 
(let TMP_4 \def (\lambda (n: nat).(let TMP_3 \def (minus z y) in (le n 
TMP_3))) in (let TMP_5 \def (plus x y) in (let TMP_6 \def (le_plus_r x y) in 
(let TMP_7 \def (le_minus_minus y TMP_5 TMP_6 z H) in (let TMP_8 \def 
(minus_plus_r x y) in (eq_ind nat TMP_2 TMP_4 TMP_7 x TMP_8))))))))))).

theorem le_trans_plus_r:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).((le (plus x y) z) \to 
(le y z))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(\lambda (H: (le (plus 
x y) z)).(let TMP_1 \def (plus x y) in (let TMP_2 \def (le_plus_r x y) in 
(le_trans y TMP_1 z TMP_2 H)))))).

theorem lt_x_O:
 \forall (x: nat).((lt x O) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) O)).(\lambda (P: Prop).(let TMP_1 
\def (S x) in (let H_y \def (le_n_O_eq TMP_1 H) in (let TMP_2 \def (\lambda 
(ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) in 
(let TMP_3 \def (S x) in (let H0 \def (eq_ind nat O TMP_2 I TMP_3 H_y) in 
(False_ind P H0)))))))).

theorem le_gen_S:
 \forall (m: nat).(\forall (x: nat).((le (S m) x) \to (ex2 nat (\lambda (n: 
nat).(eq nat x (S n))) (\lambda (n: nat).(le m n)))))
\def
 \lambda (m: nat).(\lambda (x: nat).(\lambda (H: (le (S m) x)).(let H0 \def 
(match H with [le_n \Rightarrow (\lambda (H0: (eq nat (S m) x)).(let TMP_16 
\def (S m) in (let TMP_20 \def (\lambda (n: nat).(let TMP_18 \def (\lambda 
(n0: nat).(let TMP_17 \def (S n0) in (eq nat n TMP_17))) in (let TMP_19 \def 
(\lambda (n0: nat).(le m n0)) in (ex2 nat TMP_18 TMP_19)))) in (let TMP_23 
\def (\lambda (n: nat).(let TMP_21 \def (S m) in (let TMP_22 \def (S n) in 
(eq nat TMP_21 TMP_22)))) in (let TMP_24 \def (\lambda (n: nat).(le m n)) in 
(let TMP_25 \def (S m) in (let TMP_26 \def (refl_equal nat TMP_25) in (let 
TMP_27 \def (le_n m) in (let TMP_28 \def (ex_intro2 nat TMP_23 TMP_24 m 
TMP_26 TMP_27) in (eq_ind nat TMP_16 TMP_20 TMP_28 x H0)))))))))) | (le_S m0 
H0) \Rightarrow (\lambda (H1: (eq nat (S m0) x)).(let TMP_1 \def (S m0) in 
(let TMP_5 \def (\lambda (n: nat).((le (S m) m0) \to (let TMP_3 \def (\lambda 
(n0: nat).(let TMP_2 \def (S n0) in (eq nat n TMP_2))) in (let TMP_4 \def 
(\lambda (n0: nat).(le m n0)) in (ex2 nat TMP_3 TMP_4))))) in (let TMP_15 
\def (\lambda (H2: (le (S m) m0)).(let TMP_8 \def (\lambda (n: nat).(let 
TMP_6 \def (S m0) in (let TMP_7 \def (S n) in (eq nat TMP_6 TMP_7)))) in (let 
TMP_9 \def (\lambda (n: nat).(le m n)) in (let TMP_10 \def (S m0) in (let 
TMP_11 \def (refl_equal nat TMP_10) in (let TMP_12 \def (S m) in (let TMP_13 
\def (le_S TMP_12 m0 H2) in (let TMP_14 \def (le_S_n m m0 TMP_13) in 
(ex_intro2 nat TMP_8 TMP_9 m0 TMP_11 TMP_14))))))))) in (eq_ind nat TMP_1 
TMP_5 TMP_15 x H1 H0)))))]) in (let TMP_29 \def (refl_equal nat x) in (H0 
TMP_29))))).

theorem lt_x_plus_x_Sy:
 \forall (x: nat).(\forall (y: nat).(lt x (plus x (S y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_1 \def (S y) in (let TMP_2 \def 
(plus TMP_1 x) in (let TMP_3 \def (\lambda (n: nat).(lt x n)) in (let TMP_4 
\def (S x) in (let TMP_5 \def (plus y x) in (let TMP_6 \def (S TMP_5) in (let 
TMP_7 \def (S x) in (let TMP_8 \def (plus y x) in (let TMP_9 \def (S TMP_8) 
in (let TMP_10 \def (plus y x) in (let TMP_11 \def (le_plus_r y x) in (let 
TMP_12 \def (le_n_S x TMP_10 TMP_11) in (let TMP_13 \def (le_n_S TMP_7 TMP_9 
TMP_12) in (let TMP_14 \def (le_S_n TMP_4 TMP_6 TMP_13) in (let TMP_15 \def 
(S y) in (let TMP_16 \def (plus x TMP_15) in (let TMP_17 \def (S y) in (let 
TMP_18 \def (plus_sym x TMP_17) in (eq_ind_r nat TMP_2 TMP_3 TMP_14 TMP_16 
TMP_18)))))))))))))))))))).

theorem simpl_lt_plus_r:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((lt (plus n p) (plus m 
p)) \to (lt n m))))
\def
 \lambda (p: nat).(\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (plus 
n p) (plus m p))).(let TMP_1 \def (plus n p) in (let TMP_3 \def (\lambda (n0: 
nat).(let TMP_2 \def (plus m p) in (lt n0 TMP_2))) in (let TMP_4 \def (plus p 
n) in (let TMP_5 \def (plus_sym n p) in (let H0 \def (eq_ind nat TMP_1 TMP_3 
H TMP_4 TMP_5) in (let TMP_6 \def (plus m p) in (let TMP_8 \def (\lambda (n0: 
nat).(let TMP_7 \def (plus p n) in (lt TMP_7 n0))) in (let TMP_9 \def (plus p 
m) in (let TMP_10 \def (plus_sym m p) in (let H1 \def (eq_ind nat TMP_6 TMP_8 
H0 TMP_9 TMP_10) in (simpl_lt_plus_l n m p H1)))))))))))))).

theorem minus_x_Sy:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq nat (minus x y) (S 
(minus x (S y))))))
\def
 \lambda (x: nat).(let TMP_5 \def (\lambda (n: nat).(\forall (y: nat).((lt y 
n) \to (let TMP_1 \def (minus n y) in (let TMP_2 \def (S y) in (let TMP_3 
\def (minus n TMP_2) in (let TMP_4 \def (S TMP_3) in (eq nat TMP_1 
TMP_4)))))))) in (let TMP_22 \def (\lambda (y: nat).(\lambda (H: (lt y 
O)).(let H0 \def (match H with [le_n \Rightarrow (\lambda (H0: (eq nat (S y) 
O)).(let TMP_14 \def (S y) in (let TMP_15 \def (\lambda (e: nat).(match e 
with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H1 \def (eq_ind 
nat TMP_14 TMP_15 I O H0) in (let TMP_16 \def (minus O y) in (let TMP_17 \def 
(S y) in (let TMP_18 \def (minus O TMP_17) in (let TMP_19 \def (S TMP_18) in 
(let TMP_20 \def (eq nat TMP_16 TMP_19) in (False_ind TMP_20 H1)))))))))) | 
(le_S m H0) \Rightarrow (\lambda (H1: (eq nat (S m) O)).(let TMP_6 \def (S m) 
in (let TMP_7 \def (\lambda (e: nat).(match e with [O \Rightarrow False | (S 
_) \Rightarrow True])) in (let H2 \def (eq_ind nat TMP_6 TMP_7 I O H1) in 
(let TMP_12 \def ((le (S y) m) \to (let TMP_8 \def (minus O y) in (let TMP_9 
\def (S y) in (let TMP_10 \def (minus O TMP_9) in (let TMP_11 \def (S TMP_10) 
in (eq nat TMP_8 TMP_11)))))) in (let TMP_13 \def (False_ind TMP_12 H2) in 
(TMP_13 H0)))))))]) in (let TMP_21 \def (refl_equal nat O) in (H0 TMP_21))))) 
in (let TMP_40 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y 
n) \to (eq nat (minus n y) (S (minus n (S y)))))))).(\lambda (y: nat).(let 
TMP_29 \def (\lambda (n0: nat).((lt n0 (S n)) \to (let TMP_23 \def (S n) in 
(let TMP_24 \def (minus TMP_23 n0) in (let TMP_25 \def (S n) in (let TMP_26 
\def (S n0) in (let TMP_27 \def (minus TMP_25 TMP_26) in (let TMP_28 \def (S 
TMP_27) in (eq nat TMP_24 TMP_28))))))))) in (let TMP_37 \def (\lambda (_: 
(lt O (S n))).(let TMP_32 \def (\lambda (n0: nat).(let TMP_30 \def (S n) in 
(let TMP_31 \def (S n0) in (eq nat TMP_30 TMP_31)))) in (let TMP_33 \def (S 
n) in (let TMP_34 \def (refl_equal nat TMP_33) in (let TMP_35 \def (minus n 
O) in (let TMP_36 \def (minus_n_O n) in (eq_ind nat n TMP_32 TMP_34 TMP_35 
TMP_36))))))) in (let TMP_39 \def (\lambda (n0: nat).(\lambda (_: (((lt n0 (S 
n)) \to (eq nat (minus (S n) n0) (S (minus (S n) (S n0))))))).(\lambda (H1: 
(lt (S n0) (S n))).(let TMP_38 \def (S n0) in (let H2 \def (le_S_n TMP_38 n 
H1) in (H n0 H2)))))) in (nat_ind TMP_29 TMP_37 TMP_39 y))))))) in (nat_ind 
TMP_5 TMP_22 TMP_40 x)))).

theorem lt_plus_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus x (minus 
y (S x)))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_1 \def (S 
x) in (le_plus_minus TMP_1 y H)))).

theorem lt_plus_minus_r:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus (minus y 
(S x)) x)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_1 \def (S 
x) in (let TMP_2 \def (minus y TMP_1) in (let TMP_3 \def (plus x TMP_2) in 
(let TMP_5 \def (\lambda (n: nat).(let TMP_4 \def (S n) in (eq nat y TMP_4))) 
in (let TMP_6 \def (lt_plus_minus x y H) in (let TMP_7 \def (S x) in (let 
TMP_8 \def (minus y TMP_7) in (let TMP_9 \def (plus TMP_8 x) in (let TMP_10 
\def (S x) in (let TMP_11 \def (minus y TMP_10) in (let TMP_12 \def (plus_sym 
TMP_11 x) in (eq_ind_r nat TMP_3 TMP_5 TMP_6 TMP_9 TMP_12)))))))))))))).

theorem minus_x_SO:
 \forall (x: nat).((lt O x) \to (eq nat x (S (minus x (S O)))))
\def
 \lambda (x: nat).(\lambda (H: (lt O x)).(let TMP_1 \def (minus x O) in (let 
TMP_2 \def (\lambda (n: nat).(eq nat x n)) in (let TMP_3 \def (\lambda (n: 
nat).(eq nat x n)) in (let TMP_4 \def (refl_equal nat x) in (let TMP_5 \def 
(minus x O) in (let TMP_6 \def (minus_n_O x) in (let TMP_7 \def (eq_ind nat x 
TMP_3 TMP_4 TMP_5 TMP_6) in (let TMP_8 \def (S O) in (let TMP_9 \def (minus x 
TMP_8) in (let TMP_10 \def (S TMP_9) in (let TMP_11 \def (minus_x_Sy x O H) 
in (eq_ind nat TMP_1 TMP_2 TMP_7 TMP_10 TMP_11))))))))))))).

theorem le_x_pred_y:
 \forall (y: nat).(\forall (x: nat).((lt x y) \to (le x (pred y))))
\def
 \lambda (y: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (x: nat).((lt x 
n) \to (let TMP_1 \def (pred n) in (le x TMP_1))))) in (let TMP_11 \def 
(\lambda (x: nat).(\lambda (H: (lt x O)).(let H0 \def (match H with [le_n 
\Rightarrow (\lambda (H0: (eq nat (S x) O)).(let TMP_7 \def (S x) in (let 
TMP_8 \def (\lambda (e: nat).(match e with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H1 \def (eq_ind nat TMP_7 TMP_8 I O H0) in (let 
TMP_9 \def (le x O) in (False_ind TMP_9 H1)))))) | (le_S m H0) \Rightarrow 
(\lambda (H1: (eq nat (S m) O)).(let TMP_3 \def (S m) in (let TMP_4 \def 
(\lambda (e: nat).(match e with [O \Rightarrow False | (S _) \Rightarrow 
True])) in (let H2 \def (eq_ind nat TMP_3 TMP_4 I O H1) in (let TMP_5 \def 
((le (S x) m) \to (le x O)) in (let TMP_6 \def (False_ind TMP_5 H2) in (TMP_6 
H0)))))))]) in (let TMP_10 \def (refl_equal nat O) in (H0 TMP_10))))) in (let 
TMP_12 \def (\lambda (n: nat).(\lambda (_: ((\forall (x: nat).((lt x n) \to 
(le x (pred n)))))).(\lambda (x: nat).(\lambda (H0: (lt x (S n))).(le_S_n x n 
H0))))) in (nat_ind TMP_2 TMP_11 TMP_12 y)))).

theorem lt_le_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (le x (minus y (S O)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(let TMP_1 \def (S 
O) in (let TMP_2 \def (S O) in (let TMP_3 \def (plus TMP_2 x) in (let TMP_4 
\def (\lambda (n: nat).(le n y)) in (let TMP_5 \def (S O) in (let TMP_6 \def 
(plus x TMP_5) in (let TMP_7 \def (S O) in (let TMP_8 \def (plus_sym x TMP_7) 
in (let TMP_9 \def (eq_ind_r nat TMP_3 TMP_4 H TMP_6 TMP_8) in (le_minus x y 
TMP_1 TMP_9)))))))))))).

theorem lt_le_e:
 \forall (n: nat).(\forall (d: nat).(\forall (P: Prop).((((lt n d) \to P)) 
\to ((((le d n) \to P)) \to P))))
\def
 \lambda (n: nat).(\lambda (d: nat).(\lambda (P: Prop).(\lambda (H: (((lt n 
d) \to P))).(\lambda (H0: (((le d n) \to P))).(let H1 \def (le_or_lt d n) in 
(let TMP_1 \def (le d n) in (let TMP_2 \def (lt n d) in (or_ind TMP_1 TMP_2 P 
H0 H H1)))))))).

theorem lt_eq_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((le x y) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (le x 
y)).(let TMP_1 \def (lt x y) in (let TMP_2 \def (eq nat x y) in (let TMP_3 
\def (le_lt_or_eq x y H1) in (or_ind TMP_1 TMP_2 P H H0 TMP_3))))))))).

theorem lt_eq_gt_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((((lt y x) \to P)) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (((lt y x) 
\to P))).(let TMP_3 \def (\lambda (H2: (le y x)).(let TMP_2 \def (\lambda 
(H3: (eq nat y x)).(let TMP_1 \def (sym_eq nat y x H3) in (H0 TMP_1))) in 
(lt_eq_e y x P H1 TMP_2 H2))) in (lt_le_e x y P H TMP_3))))))).

theorem lt_gen_xS:
 \forall (x: nat).(\forall (n: nat).((lt x (S n)) \to (or (eq nat x O) (ex2 
nat (\lambda (m: nat).(eq nat x (S m))) (\lambda (m: nat).(lt m n))))))
\def
 \lambda (x: nat).(let TMP_6 \def (\lambda (n: nat).(\forall (n0: nat).((lt n 
(S n0)) \to (let TMP_1 \def (eq nat n O) in (let TMP_3 \def (\lambda (m: 
nat).(let TMP_2 \def (S m) in (eq nat n TMP_2))) in (let TMP_4 \def (\lambda 
(m: nat).(lt m n0)) in (let TMP_5 \def (ex2 nat TMP_3 TMP_4) in (or TMP_1 
TMP_5)))))))) in (let TMP_13 \def (\lambda (n: nat).(\lambda (_: (lt O (S 
n))).(let TMP_7 \def (eq nat O O) in (let TMP_9 \def (\lambda (m: nat).(let 
TMP_8 \def (S m) in (eq nat O TMP_8))) in (let TMP_10 \def (\lambda (m: 
nat).(lt m n)) in (let TMP_11 \def (ex2 nat TMP_9 TMP_10) in (let TMP_12 \def 
(refl_equal nat O) in (or_introl TMP_7 TMP_11 TMP_12)))))))) in (let TMP_30 
\def (\lambda (n: nat).(\lambda (_: ((\forall (n0: nat).((lt n (S n0)) \to 
(or (eq nat n O) (ex2 nat (\lambda (m: nat).(eq nat n (S m))) (\lambda (m: 
nat).(lt m n0)))))))).(\lambda (n0: nat).(\lambda (H0: (lt (S n) (S 
n0))).(let TMP_14 \def (S n) in (let TMP_15 \def (eq nat TMP_14 O) in (let 
TMP_18 \def (\lambda (m: nat).(let TMP_16 \def (S n) in (let TMP_17 \def (S 
m) in (eq nat TMP_16 TMP_17)))) in (let TMP_19 \def (\lambda (m: nat).(lt m 
n0)) in (let TMP_20 \def (ex2 nat TMP_18 TMP_19) in (let TMP_23 \def (\lambda 
(m: nat).(let TMP_21 \def (S n) in (let TMP_22 \def (S m) in (eq nat TMP_21 
TMP_22)))) in (let TMP_24 \def (\lambda (m: nat).(lt m n0)) in (let TMP_25 
\def (S n) in (let TMP_26 \def (refl_equal nat TMP_25) in (let TMP_27 \def (S 
n) in (let TMP_28 \def (le_S_n TMP_27 n0 H0) in (let TMP_29 \def (ex_intro2 
nat TMP_23 TMP_24 n TMP_26 TMP_28) in (or_intror TMP_15 TMP_20 
TMP_29))))))))))))))))) in (nat_ind TMP_6 TMP_13 TMP_30 x)))).

theorem le_lt_false:
 \forall (x: nat).(\forall (y: nat).((le x y) \to ((lt y x) \to (\forall (P: 
Prop).P))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (H0: (lt 
y x)).(\lambda (P: Prop).(let TMP_1 \def (le_not_lt x y H H0) in (False_ind P 
TMP_1)))))).

theorem lt_neq:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (not (eq nat x y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(\lambda (H0: (eq 
nat x y)).(let TMP_1 \def (\lambda (n: nat).(lt n y)) in (let H1 \def (eq_ind 
nat x TMP_1 H y H0) in (lt_n_n y H1)))))).

theorem arith0:
 \forall (h2: nat).(\forall (d2: nat).(\forall (n: nat).((le (plus d2 h2) n) 
\to (\forall (h1: nat).(le (plus d2 h1) (minus (plus n h1) h2))))))
\def
 \lambda (h2: nat).(\lambda (d2: nat).(\lambda (n: nat).(\lambda (H: (le 
(plus d2 h2) n)).(\lambda (h1: nat).(let TMP_1 \def (plus d2 h1) in (let 
TMP_2 \def (plus h2 TMP_1) in (let TMP_3 \def (minus TMP_2 h2) in (let TMP_6 
\def (\lambda (n0: nat).(let TMP_4 \def (plus n h1) in (let TMP_5 \def (minus 
TMP_4 h2) in (le n0 TMP_5)))) in (let TMP_7 \def (plus d2 h1) in (let TMP_8 
\def (plus h2 TMP_7) in (let TMP_9 \def (plus d2 h1) in (let TMP_10 \def 
(le_plus_l h2 TMP_9) in (let TMP_11 \def (plus n h1) in (let TMP_12 \def 
(plus h2 d2) in (let TMP_13 \def (plus TMP_12 h1) in (let TMP_15 \def 
(\lambda (n0: nat).(let TMP_14 \def (plus n h1) in (le n0 TMP_14))) in (let 
TMP_16 \def (plus d2 h2) in (let TMP_19 \def (\lambda (n0: nat).(let TMP_17 
\def (plus n0 h1) in (let TMP_18 \def (plus n h1) in (le TMP_17 TMP_18)))) in 
(let TMP_20 \def (plus d2 h2) in (let TMP_21 \def (plus TMP_20 h1) in (let 
TMP_22 \def (plus n h1) in (let TMP_23 \def (plus d2 h2) in (let TMP_24 \def 
(plus TMP_23 h1) in (let TMP_25 \def (plus n h1) in (let TMP_26 \def (plus d2 
h2) in (let TMP_27 \def (le_n h1) in (let TMP_28 \def (le_plus_plus TMP_26 n 
h1 h1 H TMP_27) in (let TMP_29 \def (le_n_S TMP_24 TMP_25 TMP_28) in (let 
TMP_30 \def (le_S_n TMP_21 TMP_22 TMP_29) in (let TMP_31 \def (plus h2 d2) in 
(let TMP_32 \def (plus_sym h2 d2) in (let TMP_33 \def (eq_ind_r nat TMP_16 
TMP_19 TMP_30 TMP_31 TMP_32) in (let TMP_34 \def (plus d2 h1) in (let TMP_35 
\def (plus h2 TMP_34) in (let TMP_36 \def (plus_assoc_l h2 d2 h1) in (let 
TMP_37 \def (eq_ind_r nat TMP_13 TMP_15 TMP_33 TMP_35 TMP_36) in (let TMP_38 
\def (le_minus_minus h2 TMP_8 TMP_10 TMP_11 TMP_37) in (let TMP_39 \def (plus 
d2 h1) in (let TMP_40 \def (plus d2 h1) in (let TMP_41 \def (minus_plus h2 
TMP_40) in (eq_ind nat TMP_3 TMP_6 TMP_38 TMP_39 
TMP_41))))))))))))))))))))))))))))))))))))))))).

theorem O_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq nat (minus x y) O)))
\def
 \lambda (x: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (y: nat).((le n 
y) \to (let TMP_1 \def (minus n y) in (eq nat TMP_1 O))))) in (let TMP_3 \def 
(\lambda (y: nat).(\lambda (_: (le O y)).(refl_equal nat O))) in (let TMP_20 
\def (\lambda (x0: nat).(\lambda (H: ((\forall (y: nat).((le x0 y) \to (eq 
nat (minus x0 y) O))))).(\lambda (y: nat).(let TMP_5 \def (\lambda (n: 
nat).((le (S x0) n) \to (let TMP_4 \def (match n with [O \Rightarrow (S x0) | 
(S l) \Rightarrow (minus x0 l)]) in (eq nat TMP_4 O)))) in (let TMP_17 \def 
(\lambda (H0: (le (S x0) O)).(let TMP_7 \def (\lambda (n: nat).(let TMP_6 
\def (S n) in (eq nat O TMP_6))) in (let TMP_8 \def (\lambda (n: nat).(le x0 
n)) in (let TMP_9 \def (S x0) in (let TMP_10 \def (eq nat TMP_9 O) in (let 
TMP_15 \def (\lambda (x1: nat).(\lambda (H1: (eq nat O (S x1))).(\lambda (_: 
(le x0 x1)).(let TMP_11 \def (\lambda (ee: nat).(match ee with [O \Rightarrow 
True | (S _) \Rightarrow False])) in (let TMP_12 \def (S x1) in (let H3 \def 
(eq_ind nat O TMP_11 I TMP_12 H1) in (let TMP_13 \def (S x0) in (let TMP_14 
\def (eq nat TMP_13 O) in (False_ind TMP_14 H3))))))))) in (let TMP_16 \def 
(le_gen_S x0 O H0) in (ex2_ind nat TMP_7 TMP_8 TMP_10 TMP_15 TMP_16)))))))) 
in (let TMP_19 \def (\lambda (n: nat).(\lambda (_: (((le (S x0) n) \to (eq 
nat (match n with [O \Rightarrow (S x0) | (S l) \Rightarrow (minus x0 l)]) 
O)))).(\lambda (H1: (le (S x0) (S n))).(let TMP_18 \def (le_S_n x0 n H1) in 
(H n TMP_18))))) in (nat_ind TMP_5 TMP_17 TMP_19 y))))))) in (nat_ind TMP_2 
TMP_3 TMP_20 x)))).

theorem minus_minus:
 \forall (z: nat).(\forall (x: nat).(\forall (y: nat).((le z x) \to ((le z y) 
\to ((eq nat (minus x z) (minus y z)) \to (eq nat x y))))))
\def
 \lambda (z: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (x: 
nat).(\forall (y: nat).((le n x) \to ((le n y) \to ((eq nat (minus x n) 
(minus y n)) \to (eq nat x y))))))) in (let TMP_9 \def (\lambda (x: 
nat).(\lambda (y: nat).(\lambda (_: (le O x)).(\lambda (_: (le O y)).(\lambda 
(H1: (eq nat (minus x O) (minus y O))).(let TMP_2 \def (minus x O) in (let 
TMP_4 \def (\lambda (n: nat).(let TMP_3 \def (minus y O) in (eq nat n 
TMP_3))) in (let TMP_5 \def (minus_n_O x) in (let H2 \def (eq_ind_r nat TMP_2 
TMP_4 H1 x TMP_5) in (let TMP_6 \def (minus y O) in (let TMP_7 \def (\lambda 
(n: nat).(eq nat x n)) in (let TMP_8 \def (minus_n_O y) in (let H3 \def 
(eq_ind_r nat TMP_6 TMP_7 H2 y TMP_8) in H3))))))))))))) in (let TMP_40 \def 
(\lambda (z0: nat).(\lambda (IH: ((\forall (x: nat).(\forall (y: nat).((le z0 
x) \to ((le z0 y) \to ((eq nat (minus x z0) (minus y z0)) \to (eq nat x 
y)))))))).(\lambda (x: nat).(let TMP_10 \def (\lambda (n: nat).(\forall (y: 
nat).((le (S z0) n) \to ((le (S z0) y) \to ((eq nat (minus n (S z0)) (minus y 
(S z0))) \to (eq nat n y)))))) in (let TMP_20 \def (\lambda (y: nat).(\lambda 
(H: (le (S z0) O)).(\lambda (_: (le (S z0) y)).(\lambda (_: (eq nat (minus O 
(S z0)) (minus y (S z0)))).(let TMP_12 \def (\lambda (n: nat).(let TMP_11 
\def (S n) in (eq nat O TMP_11))) in (let TMP_13 \def (\lambda (n: nat).(le 
z0 n)) in (let TMP_14 \def (eq nat O y) in (let TMP_18 \def (\lambda (x0: 
nat).(\lambda (H2: (eq nat O (S x0))).(\lambda (_: (le z0 x0)).(let TMP_15 
\def (\lambda (ee: nat).(match ee with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_16 \def (S x0) in (let H4 \def (eq_ind nat O 
TMP_15 I TMP_16 H2) in (let TMP_17 \def (eq nat O y) in (False_ind TMP_17 
H4)))))))) in (let TMP_19 \def (le_gen_S z0 O H) in (ex2_ind nat TMP_12 
TMP_13 TMP_14 TMP_18 TMP_19)))))))))) in (let TMP_39 \def (\lambda (x0: 
nat).(\lambda (_: ((\forall (y: nat).((le (S z0) x0) \to ((le (S z0) y) \to 
((eq nat (minus x0 (S z0)) (minus y (S z0))) \to (eq nat x0 y))))))).(\lambda 
(y: nat).(let TMP_22 \def (\lambda (n: nat).((le (S z0) (S x0)) \to ((le (S 
z0) n) \to ((eq nat (minus (S x0) (S z0)) (minus n (S z0))) \to (let TMP_21 
\def (S x0) in (eq nat TMP_21 n)))))) in (let TMP_34 \def (\lambda (H: (le (S 
z0) (S x0))).(\lambda (H0: (le (S z0) O)).(\lambda (_: (eq nat (minus (S x0) 
(S z0)) (minus O (S z0)))).(let H_y \def (le_S_n z0 x0 H) in (let TMP_24 \def 
(\lambda (n: nat).(let TMP_23 \def (S n) in (eq nat O TMP_23))) in (let 
TMP_25 \def (\lambda (n: nat).(le z0 n)) in (let TMP_26 \def (S x0) in (let 
TMP_27 \def (eq nat TMP_26 O) in (let TMP_32 \def (\lambda (x1: nat).(\lambda 
(H2: (eq nat O (S x1))).(\lambda (_: (le z0 x1)).(let TMP_28 \def (\lambda 
(ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) in 
(let TMP_29 \def (S x1) in (let H4 \def (eq_ind nat O TMP_28 I TMP_29 H2) in 
(let TMP_30 \def (S x0) in (let TMP_31 \def (eq nat TMP_30 O) in (False_ind 
TMP_31 H4))))))))) in (let TMP_33 \def (le_gen_S z0 O H0) in (ex2_ind nat 
TMP_24 TMP_25 TMP_27 TMP_32 TMP_33))))))))))) in (let TMP_38 \def (\lambda 
(y0: nat).(\lambda (_: (((le (S z0) (S x0)) \to ((le (S z0) y0) \to ((eq nat 
(minus (S x0) (S z0)) (minus y0 (S z0))) \to (eq nat (S x0) y0)))))).(\lambda 
(H: (le (S z0) (S x0))).(\lambda (H0: (le (S z0) (S y0))).(\lambda (H1: (eq 
nat (minus (S x0) (S z0)) (minus (S y0) (S z0)))).(let TMP_35 \def (le_S_n z0 
x0 H) in (let TMP_36 \def (le_S_n z0 y0 H0) in (let TMP_37 \def (IH x0 y0 
TMP_35 TMP_36 H1) in (f_equal nat nat S x0 y0 TMP_37))))))))) in (nat_ind 
TMP_22 TMP_34 TMP_38 y))))))) in (nat_ind TMP_10 TMP_20 TMP_39 x))))))) in 
(nat_ind TMP_1 TMP_9 TMP_40 z)))).

theorem plus_plus:
 \forall (z: nat).(\forall (x1: nat).(\forall (x2: nat).(\forall (y1: 
nat).(\forall (y2: nat).((le x1 z) \to ((le x2 z) \to ((eq nat (plus (minus z 
x1) y1) (plus (minus z x2) y2)) \to (eq nat (plus x1 y2) (plus x2 y1)))))))))
\def
 \lambda (z: nat).(let TMP_3 \def (\lambda (n: nat).(\forall (x1: 
nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 n) \to 
((le x2 n) \to ((eq nat (plus (minus n x1) y1) (plus (minus n x2) y2)) \to 
(let TMP_1 \def (plus x1 y2) in (let TMP_2 \def (plus x2 y1) in (eq nat TMP_1 
TMP_2))))))))))) in (let TMP_17 \def (\lambda (x1: nat).(\lambda (x2: 
nat).(\lambda (y1: nat).(\lambda (y2: nat).(\lambda (H: (le x1 O)).(\lambda 
(H0: (le x2 O)).(\lambda (H1: (eq nat y1 y2)).(let TMP_6 \def (\lambda (n: 
nat).(let TMP_4 \def (plus x1 n) in (let TMP_5 \def (plus x2 y1) in (eq nat 
TMP_4 TMP_5)))) in (let H_y \def (le_n_O_eq x2 H0) in (let TMP_9 \def 
(\lambda (n: nat).(let TMP_7 \def (plus x1 y1) in (let TMP_8 \def (plus n y1) 
in (eq nat TMP_7 TMP_8)))) in (let H_y0 \def (le_n_O_eq x1 H) in (let TMP_12 
\def (\lambda (n: nat).(let TMP_10 \def (plus n y1) in (let TMP_11 \def (plus 
O y1) in (eq nat TMP_10 TMP_11)))) in (let TMP_13 \def (plus O y1) in (let 
TMP_14 \def (refl_equal nat TMP_13) in (let TMP_15 \def (eq_ind nat O TMP_12 
TMP_14 x1 H_y0) in (let TMP_16 \def (eq_ind nat O TMP_9 TMP_15 x2 H_y) in 
(eq_ind nat y1 TMP_6 TMP_16 y2 H1))))))))))))))))) in (let TMP_91 \def 
(\lambda (z0: nat).(\lambda (IH: ((\forall (x1: nat).(\forall (x2: 
nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 z0) \to ((le x2 z0) \to 
((eq nat (plus (minus z0 x1) y1) (plus (minus z0 x2) y2)) \to (eq nat (plus 
x1 y2) (plus x2 y1))))))))))).(\lambda (x1: nat).(let TMP_20 \def (\lambda 
(n: nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: nat).((le n (S 
z0)) \to ((le x2 (S z0)) \to ((eq nat (plus (minus (S z0) n) y1) (plus (minus 
(S z0) x2) y2)) \to (let TMP_18 \def (plus n y2) in (let TMP_19 \def (plus x2 
y1) in (eq nat TMP_18 TMP_19)))))))))) in (let TMP_56 \def (\lambda (x2: 
nat).(let TMP_23 \def (\lambda (n: nat).(\forall (y1: nat).(\forall (y2: 
nat).((le O (S z0)) \to ((le n (S z0)) \to ((eq nat (plus (minus (S z0) O) 
y1) (plus (minus (S z0) n) y2)) \to (let TMP_21 \def (plus O y2) in (let 
TMP_22 \def (plus n y1) in (eq nat TMP_21 TMP_22))))))))) in (let TMP_32 \def 
(\lambda (y1: nat).(\lambda (y2: nat).(\lambda (_: (le O (S z0))).(\lambda 
(_: (le O (S z0))).(\lambda (H1: (eq nat (S (plus z0 y1)) (S (plus z0 
y2)))).(let H_y \def (IH O O) in (let TMP_24 \def (minus z0 O) in (let TMP_25 
\def (\lambda (n: nat).(\forall (y3: nat).(\forall (y4: nat).((le O z0) \to 
((le O z0) \to ((eq nat (plus n y3) (plus n y4)) \to (eq nat y4 y3))))))) in 
(let TMP_26 \def (minus_n_O z0) in (let H2 \def (eq_ind_r nat TMP_24 TMP_25 
H_y z0 TMP_26) in (let TMP_27 \def (le_O_n z0) in (let TMP_28 \def (le_O_n 
z0) in (let TMP_29 \def (plus z0 y1) in (let TMP_30 \def (plus z0 y2) in (let 
TMP_31 \def (eq_add_S TMP_29 TMP_30 H1) in (H2 y1 y2 TMP_27 TMP_28 
TMP_31)))))))))))))))) in (let TMP_55 \def (\lambda (x3: nat).(\lambda (_: 
((\forall (y1: nat).(\forall (y2: nat).((le O (S z0)) \to ((le x3 (S z0)) \to 
((eq nat (S (plus z0 y1)) (plus (match x3 with [O \Rightarrow (S z0) | (S l) 
\Rightarrow (minus z0 l)]) y2)) \to (eq nat y2 (plus x3 y1))))))))).(\lambda 
(y1: nat).(\lambda (y2: nat).(\lambda (_: (le O (S z0))).(\lambda (H0: (le (S 
x3) (S z0))).(\lambda (H1: (eq nat (S (plus z0 y1)) (plus (minus z0 x3) 
y2))).(let TMP_33 \def (S y1) in (let H_y \def (IH O x3 TMP_33) in (let 
TMP_34 \def (minus z0 O) in (let TMP_37 \def (\lambda (n: nat).(\forall (y3: 
nat).((le O z0) \to ((le x3 z0) \to ((eq nat (plus n (S y1)) (plus (minus z0 
x3) y3)) \to (let TMP_35 \def (S y1) in (let TMP_36 \def (plus x3 TMP_35) in 
(eq nat y3 TMP_36)))))))) in (let TMP_38 \def (minus_n_O z0) in (let H2 \def 
(eq_ind_r nat TMP_34 TMP_37 H_y z0 TMP_38) in (let TMP_39 \def (S y1) in (let 
TMP_40 \def (plus z0 TMP_39) in (let TMP_43 \def (\lambda (n: nat).(\forall 
(y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat n (plus (minus z0 x3) y3)) 
\to (let TMP_41 \def (S y1) in (let TMP_42 \def (plus x3 TMP_41) in (eq nat 
y3 TMP_42)))))))) in (let TMP_44 \def (plus z0 y1) in (let TMP_45 \def (S 
TMP_44) in (let TMP_46 \def (plus_n_Sm z0 y1) in (let H3 \def (eq_ind_r nat 
TMP_40 TMP_43 H2 TMP_45 TMP_46) in (let TMP_47 \def (S y1) in (let TMP_48 
\def (plus x3 TMP_47) in (let TMP_49 \def (\lambda (n: nat).(\forall (y3: 
nat).((le O z0) \to ((le x3 z0) \to ((eq nat (S (plus z0 y1)) (plus (minus z0 
x3) y3)) \to (eq nat y3 n)))))) in (let TMP_50 \def (plus x3 y1) in (let 
TMP_51 \def (S TMP_50) in (let TMP_52 \def (plus_n_Sm x3 y1) in (let H4 \def 
(eq_ind_r nat TMP_48 TMP_49 H3 TMP_51 TMP_52) in (let TMP_53 \def (le_O_n z0) 
in (let TMP_54 \def (le_S_n x3 z0 H0) in (H4 y2 TMP_53 TMP_54 
H1)))))))))))))))))))))))))))))) in (nat_ind TMP_23 TMP_32 TMP_55 x2))))) in 
(let TMP_90 \def (\lambda (x2: nat).(\lambda (_: ((\forall (x3: nat).(\forall 
(y1: nat).(\forall (y2: nat).((le x2 (S z0)) \to ((le x3 (S z0)) \to ((eq nat 
(plus (minus (S z0) x2) y1) (plus (minus (S z0) x3) y2)) \to (eq nat (plus x2 
y2) (plus x3 y1)))))))))).(\lambda (x3: nat).(let TMP_60 \def (\lambda (n: 
nat).(\forall (y1: nat).(\forall (y2: nat).((le (S x2) (S z0)) \to ((le n (S 
z0)) \to ((eq nat (plus (minus (S z0) (S x2)) y1) (plus (minus (S z0) n) y2)) 
\to (let TMP_57 \def (S x2) in (let TMP_58 \def (plus TMP_57 y2) in (let 
TMP_59 \def (plus n y1) in (eq nat TMP_58 TMP_59)))))))))) in (let TMP_83 
\def (\lambda (y1: nat).(\lambda (y2: nat).(\lambda (H: (le (S x2) (S 
z0))).(\lambda (_: (le O (S z0))).(\lambda (H1: (eq nat (plus (minus z0 x2) 
y1) (S (plus z0 y2)))).(let TMP_61 \def (S y2) in (let H_y \def (IH x2 O y1 
TMP_61) in (let TMP_62 \def (minus z0 O) in (let TMP_65 \def (\lambda (n: 
nat).((le x2 z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) (plus n 
(S y2))) \to (let TMP_63 \def (S y2) in (let TMP_64 \def (plus x2 TMP_63) in 
(eq nat TMP_64 y1))))))) in (let TMP_66 \def (minus_n_O z0) in (let H2 \def 
(eq_ind_r nat TMP_62 TMP_65 H_y z0 TMP_66) in (let TMP_67 \def (S y2) in (let 
TMP_68 \def (plus z0 TMP_67) in (let TMP_71 \def (\lambda (n: nat).((le x2 
z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) n) \to (let TMP_69 
\def (S y2) in (let TMP_70 \def (plus x2 TMP_69) in (eq nat TMP_70 y1))))))) 
in (let TMP_72 \def (plus z0 y2) in (let TMP_73 \def (S TMP_72) in (let 
TMP_74 \def (plus_n_Sm z0 y2) in (let H3 \def (eq_ind_r nat TMP_68 TMP_71 H2 
TMP_73 TMP_74) in (let TMP_75 \def (S y2) in (let TMP_76 \def (plus x2 
TMP_75) in (let TMP_77 \def (\lambda (n: nat).((le x2 z0) \to ((le O z0) \to 
((eq nat (plus (minus z0 x2) y1) (S (plus z0 y2))) \to (eq nat n y1))))) in 
(let TMP_78 \def (plus x2 y2) in (let TMP_79 \def (S TMP_78) in (let TMP_80 
\def (plus_n_Sm x2 y2) in (let H4 \def (eq_ind_r nat TMP_76 TMP_77 H3 TMP_79 
TMP_80) in (let TMP_81 \def (le_S_n x2 z0 H) in (let TMP_82 \def (le_O_n z0) 
in (H4 TMP_81 TMP_82 H1)))))))))))))))))))))))))))) in (let TMP_89 \def 
(\lambda (x4: nat).(\lambda (_: ((\forall (y1: nat).(\forall (y2: nat).((le 
(S x2) (S z0)) \to ((le x4 (S z0)) \to ((eq nat (plus (minus z0 x2) y1) (plus 
(match x4 with [O \Rightarrow (S z0) | (S l) \Rightarrow (minus z0 l)]) y2)) 
\to (eq nat (S (plus x2 y2)) (plus x4 y1))))))))).(\lambda (y1: nat).(\lambda 
(y2: nat).(\lambda (H: (le (S x2) (S z0))).(\lambda (H0: (le (S x4) (S 
z0))).(\lambda (H1: (eq nat (plus (minus z0 x2) y1) (plus (minus z0 x4) 
y2))).(let TMP_84 \def (plus x2 y2) in (let TMP_85 \def (plus x4 y1) in (let 
TMP_86 \def (le_S_n x2 z0 H) in (let TMP_87 \def (le_S_n x4 z0 H0) in (let 
TMP_88 \def (IH x2 x4 y1 y2 TMP_86 TMP_87 H1) in (f_equal nat nat S TMP_84 
TMP_85 TMP_88))))))))))))) in (nat_ind TMP_60 TMP_83 TMP_89 x3))))))) in 
(nat_ind TMP_20 TMP_56 TMP_90 x1))))))) in (nat_ind TMP_3 TMP_17 TMP_91 z)))).

theorem le_S_minus:
 \forall (d: nat).(\forall (h: nat).(\forall (n: nat).((le (plus d h) n) \to 
(le d (S (minus n h))))))
\def
 \lambda (d: nat).(\lambda (h: nat).(\lambda (n: nat).(\lambda (H: (le (plus 
d h) n)).(let TMP_1 \def (plus d h) in (let TMP_2 \def (le_plus_l d h) in 
(let H0 \def (le_trans d TMP_1 n TMP_2 H) in (let TMP_3 \def (\lambda (n0: 
nat).(le d n0)) in (let TMP_4 \def (minus n h) in (let TMP_5 \def (plus TMP_4 
h) in (let TMP_6 \def (plus d h) in (let TMP_7 \def (le_plus_r d h) in (let 
TMP_8 \def (le_trans h TMP_6 n TMP_7 H) in (let TMP_9 \def (le_plus_minus_sym 
h n TMP_8) in (let H1 \def (eq_ind nat n TMP_3 H0 TMP_5 TMP_9) in (let TMP_10 
\def (minus n h) in (let TMP_11 \def (le_minus d n h H) in (le_S d TMP_10 
TMP_11))))))))))))))))).

theorem lt_x_pred_y:
 \forall (x: nat).(\forall (y: nat).((lt x (pred y)) \to (lt (S x) y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(let TMP_2 \def (\lambda (n: nat).((lt x 
(pred n)) \to (let TMP_1 \def (S x) in (lt TMP_1 n)))) in (let TMP_5 \def 
(\lambda (H: (lt x O)).(let TMP_3 \def (S x) in (let TMP_4 \def (lt TMP_3 O) 
in (lt_x_O x H TMP_4)))) in (let TMP_6 \def (\lambda (n: nat).(\lambda (_: 
(((lt x (pred n)) \to (lt (S x) n)))).(\lambda (H0: (lt x n)).(lt_n_S x n 
H0)))) in (nat_ind TMP_2 TMP_5 TMP_6 y))))).

