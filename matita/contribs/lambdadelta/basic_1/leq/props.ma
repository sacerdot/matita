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

include "basic_1/leq/fwd.ma".

include "basic_1/aplus/props.ma".

theorem leq_refl:
 \forall (g: G).(\forall (a: A).(leq g a a))
\def
 \lambda (g: G).(\lambda (a: A).(let TMP_1 \def (\lambda (a0: A).(leq g a0 
a0)) in (let TMP_5 \def (\lambda (n: nat).(\lambda (n0: nat).(let TMP_2 \def 
(ASort n n0) in (let TMP_3 \def (aplus g TMP_2 O) in (let TMP_4 \def 
(refl_equal A TMP_3) in (leq_sort g n n n0 n0 O TMP_4)))))) in (let TMP_6 
\def (\lambda (a0: A).(\lambda (H: (leq g a0 a0)).(\lambda (a1: A).(\lambda 
(H0: (leq g a1 a1)).(leq_head g a0 a0 H a1 a1 H0))))) in (A_ind TMP_1 TMP_5 
TMP_6 a))))).

theorem leq_eq:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((eq A a1 a2) \to (leq g a1 
a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (eq A a1 
a2)).(let TMP_1 \def (\lambda (a: A).(leq g a1 a)) in (let TMP_2 \def 
(leq_refl g a1) in (eq_ind A a1 TMP_1 TMP_2 a2 H)))))).

theorem leq_sym:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
a2 a1))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(let TMP_1 \def (\lambda (a: A).(\lambda (a0: A).(leq g a0 a))) in (let 
TMP_7 \def (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda 
(n2: nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort h1 n1) k) 
(aplus g (ASort h2 n2) k))).(let TMP_2 \def (ASort h1 n1) in (let TMP_3 \def 
(aplus g TMP_2 k) in (let TMP_4 \def (ASort h2 n2) in (let TMP_5 \def (aplus 
g TMP_4 k) in (let TMP_6 \def (sym_eq A TMP_3 TMP_5 H0) in (leq_sort g h2 h1 
n2 n1 k TMP_6)))))))))))) in (let TMP_8 \def (\lambda (a3: A).(\lambda (a4: 
A).(\lambda (_: (leq g a3 a4)).(\lambda (H1: (leq g a4 a3)).(\lambda (a5: 
A).(\lambda (a6: A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: (leq g a6 
a5)).(leq_head g a4 a3 H1 a6 a5 H3))))))))) in (leq_ind g TMP_1 TMP_7 TMP_8 
a1 a2 H))))))).

theorem leq_trans:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((leq g a2 a3) \to (leq g a1 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(let TMP_1 \def (\lambda (a: A).(\lambda (a0: A).(\forall (a3: A).((leq 
g a0 a3) \to (leq g a a3))))) in (let TMP_63 \def (\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda 
(H0: (eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda 
(a3: A).(\lambda (H1: (leq g (ASort h2 n2) a3)).(let H_x \def (leq_gen_sort1 
g h2 n2 a3 H1) in (let H2 \def H_x in (let TMP_6 \def (\lambda (n3: 
nat).(\lambda (h3: nat).(\lambda (k0: nat).(let TMP_2 \def (ASort h2 n2) in 
(let TMP_3 \def (aplus g TMP_2 k0) in (let TMP_4 \def (ASort h3 n3) in (let 
TMP_5 \def (aplus g TMP_4 k0) in (eq A TMP_3 TMP_5)))))))) in (let TMP_8 \def 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(let TMP_7 \def 
(ASort h3 n3) in (eq A a3 TMP_7))))) in (let TMP_9 \def (ASort h1 n1) in (let 
TMP_10 \def (leq g TMP_9 a3) in (let TMP_62 \def (\lambda (x0: nat).(\lambda 
(x1: nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort h2 n2) x2) 
(aplus g (ASort x1 x0) x2))).(\lambda (H4: (eq A a3 (ASort x1 x0))).(let 
TMP_11 \def (\lambda (e: A).e) in (let TMP_12 \def (ASort x1 x0) in (let H5 
\def (f_equal A A TMP_11 a3 TMP_12 H4) in (let TMP_13 \def (ASort x1 x0) in 
(let TMP_15 \def (\lambda (a: A).(let TMP_14 \def (ASort h1 n1) in (leq g 
TMP_14 a))) in (let TMP_16 \def (ASort h1 n1) in (let TMP_17 \def (ASort x1 
x0) in (let TMP_18 \def (leq g TMP_16 TMP_17) in (let TMP_41 \def (\lambda 
(H6: (lt k x2)).(let TMP_19 \def (ASort h1 n1) in (let TMP_20 \def (ASort h2 
n2) in (let TMP_21 \def (minus x2 k) in (let H_y \def (aplus_reg_r g TMP_19 
TMP_20 k k H0 TMP_21) in (let TMP_22 \def (minus x2 k) in (let TMP_23 \def 
(plus TMP_22 k) in (let TMP_28 \def (\lambda (n: nat).(let TMP_24 \def (ASort 
h1 n1) in (let TMP_25 \def (aplus g TMP_24 n) in (let TMP_26 \def (ASort h2 
n2) in (let TMP_27 \def (aplus g TMP_26 n) in (eq A TMP_25 TMP_27)))))) in 
(let TMP_29 \def (S k) in (let TMP_30 \def (le_n k) in (let TMP_31 \def (le_S 
k k TMP_30) in (let TMP_32 \def (le_trans k TMP_29 x2 TMP_31 H6) in (let 
TMP_33 \def (le_plus_minus_sym k x2 TMP_32) in (let H7 \def (eq_ind_r nat 
TMP_23 TMP_28 H_y x2 TMP_33) in (let TMP_34 \def (ASort h1 n1) in (let TMP_35 
\def (aplus g TMP_34 x2) in (let TMP_36 \def (ASort h2 n2) in (let TMP_37 
\def (aplus g TMP_36 x2) in (let TMP_38 \def (ASort x1 x0) in (let TMP_39 
\def (aplus g TMP_38 x2) in (let TMP_40 \def (trans_eq A TMP_35 TMP_37 TMP_39 
H7 H3) in (leq_sort g h1 x1 n1 x0 x2 TMP_40)))))))))))))))))))))) in (let 
TMP_60 \def (\lambda (H6: (le x2 k)).(let TMP_42 \def (ASort h2 n2) in (let 
TMP_43 \def (ASort x1 x0) in (let TMP_44 \def (minus k x2) in (let H_y \def 
(aplus_reg_r g TMP_42 TMP_43 x2 x2 H3 TMP_44) in (let TMP_45 \def (minus k 
x2) in (let TMP_46 \def (plus TMP_45 x2) in (let TMP_51 \def (\lambda (n: 
nat).(let TMP_47 \def (ASort h2 n2) in (let TMP_48 \def (aplus g TMP_47 n) in 
(let TMP_49 \def (ASort x1 x0) in (let TMP_50 \def (aplus g TMP_49 n) in (eq 
A TMP_48 TMP_50)))))) in (let TMP_52 \def (le_plus_minus_sym x2 k H6) in (let 
H7 \def (eq_ind_r nat TMP_46 TMP_51 H_y k TMP_52) in (let TMP_53 \def (ASort 
h1 n1) in (let TMP_54 \def (aplus g TMP_53 k) in (let TMP_55 \def (ASort h2 
n2) in (let TMP_56 \def (aplus g TMP_55 k) in (let TMP_57 \def (ASort x1 x0) 
in (let TMP_58 \def (aplus g TMP_57 k) in (let TMP_59 \def (trans_eq A TMP_54 
TMP_56 TMP_58 H0 H7) in (leq_sort g h1 x1 n1 x0 k TMP_59)))))))))))))))))) in 
(let TMP_61 \def (lt_le_e k x2 TMP_18 TMP_41 TMP_60) in (eq_ind_r A TMP_13 
TMP_15 TMP_61 a3 H5))))))))))))))))) in (ex2_3_ind nat nat nat TMP_6 TMP_8 
TMP_10 TMP_62 H2)))))))))))))))) in (let TMP_79 \def (\lambda (a3: 
A).(\lambda (a4: A).(\lambda (_: (leq g a3 a4)).(\lambda (H1: ((\forall (a5: 
A).((leq g a4 a5) \to (leq g a3 a5))))).(\lambda (a5: A).(\lambda (a6: 
A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: ((\forall (a7: A).((leq g a6 a7) 
\to (leq g a5 a7))))).(\lambda (a0: A).(\lambda (H4: (leq g (AHead a4 a6) 
a0)).(let H_x \def (leq_gen_head1 g a4 a6 a0 H4) in (let H5 \def H_x in (let 
TMP_64 \def (\lambda (a7: A).(\lambda (_: A).(leq g a4 a7))) in (let TMP_65 
\def (\lambda (_: A).(\lambda (a8: A).(leq g a6 a8))) in (let TMP_67 \def 
(\lambda (a7: A).(\lambda (a8: A).(let TMP_66 \def (AHead a7 a8) in (eq A a0 
TMP_66)))) in (let TMP_68 \def (AHead a3 a5) in (let TMP_69 \def (leq g 
TMP_68 a0) in (let TMP_78 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H6: (leq g a4 x0)).(\lambda (H7: (leq g a6 x1)).(\lambda (H8: (eq A a0 
(AHead x0 x1))).(let TMP_70 \def (\lambda (e: A).e) in (let TMP_71 \def 
(AHead x0 x1) in (let H9 \def (f_equal A A TMP_70 a0 TMP_71 H8) in (let 
TMP_72 \def (AHead x0 x1) in (let TMP_74 \def (\lambda (a: A).(let TMP_73 
\def (AHead a3 a5) in (leq g TMP_73 a))) in (let TMP_75 \def (H1 x0 H6) in 
(let TMP_76 \def (H3 x1 H7) in (let TMP_77 \def (leq_head g a3 x0 TMP_75 a5 
x1 TMP_76) in (eq_ind_r A TMP_72 TMP_74 TMP_77 a0 H9)))))))))))))) in 
(ex3_2_ind A A TMP_64 TMP_65 TMP_67 TMP_69 TMP_78 H5))))))))))))))))))) in 
(leq_ind g TMP_1 TMP_63 TMP_79 a1 a2 H))))))).

theorem leq_ahead_false_1:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) a1) 
\to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a1: A).(let TMP_1 \def (\lambda (a: A).(\forall 
(a2: A).((leq g (AHead a a2) a) \to (\forall (P: Prop).P)))) in (let TMP_34 
\def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (a2: A).(\lambda (H: (leq 
g (AHead (ASort n n0) a2) (ASort n n0))).(\lambda (P: Prop).(let TMP_2 \def 
(\lambda (n1: nat).((leq g (AHead (ASort n1 n0) a2) (ASort n1 n0)) \to P)) in 
(let TMP_15 \def (\lambda (H0: (leq g (AHead (ASort O n0) a2) (ASort O 
n0))).(let TMP_3 \def (ASort O n0) in (let TMP_4 \def (ASort O n0) in (let 
H_x \def (leq_gen_head1 g TMP_3 a2 TMP_4 H0) in (let H1 \def H_x in (let 
TMP_6 \def (\lambda (a3: A).(\lambda (_: A).(let TMP_5 \def (ASort O n0) in 
(leq g TMP_5 a3)))) in (let TMP_7 \def (\lambda (_: A).(\lambda (a4: A).(leq 
g a2 a4))) in (let TMP_10 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_8 
\def (ASort O n0) in (let TMP_9 \def (AHead a3 a4) in (eq A TMP_8 TMP_9))))) 
in (let TMP_14 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g 
(ASort O n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H4: (eq A (ASort O 
n0) (AHead x0 x1))).(let TMP_11 \def (ASort O n0) in (let TMP_12 \def 
(\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) in (let TMP_13 \def (AHead x0 x1) in (let H5 \def 
(eq_ind A TMP_11 TMP_12 I TMP_13 H4) in (False_ind P H5)))))))))) in 
(ex3_2_ind A A TMP_6 TMP_7 TMP_10 P TMP_14 H1)))))))))) in (let TMP_33 \def 
(\lambda (n1: nat).(\lambda (_: (((leq g (AHead (ASort n1 n0) a2) (ASort n1 
n0)) \to P))).(\lambda (H0: (leq g (AHead (ASort (S n1) n0) a2) (ASort (S n1) 
n0))).(let TMP_16 \def (S n1) in (let TMP_17 \def (ASort TMP_16 n0) in (let 
TMP_18 \def (S n1) in (let TMP_19 \def (ASort TMP_18 n0) in (let H_x \def 
(leq_gen_head1 g TMP_17 a2 TMP_19 H0) in (let H1 \def H_x in (let TMP_22 \def 
(\lambda (a3: A).(\lambda (_: A).(let TMP_20 \def (S n1) in (let TMP_21 \def 
(ASort TMP_20 n0) in (leq g TMP_21 a3))))) in (let TMP_23 \def (\lambda (_: 
A).(\lambda (a4: A).(leq g a2 a4))) in (let TMP_27 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_24 \def (S n1) in (let TMP_25 \def (ASort TMP_24 
n0) in (let TMP_26 \def (AHead a3 a4) in (eq A TMP_25 TMP_26)))))) in (let 
TMP_32 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g (ASort (S 
n1) n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H4: (eq A (ASort (S n1) 
n0) (AHead x0 x1))).(let TMP_28 \def (S n1) in (let TMP_29 \def (ASort TMP_28 
n0) in (let TMP_30 \def (\lambda (ee: A).(match ee with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) in (let TMP_31 \def 
(AHead x0 x1) in (let H5 \def (eq_ind A TMP_29 TMP_30 I TMP_31 H4) in 
(False_ind P H5))))))))))) in (ex3_2_ind A A TMP_22 TMP_23 TMP_27 P TMP_32 
H1)))))))))))))) in (nat_ind TMP_2 TMP_15 TMP_33 n H))))))))) in (let TMP_54 
\def (\lambda (a: A).(\lambda (H: ((\forall (a2: A).((leq g (AHead a a2) a) 
\to (\forall (P: Prop).P))))).(\lambda (a0: A).(\lambda (_: ((\forall (a2: 
A).((leq g (AHead a0 a2) a0) \to (\forall (P: Prop).P))))).(\lambda (a2: 
A).(\lambda (H1: (leq g (AHead (AHead a a0) a2) (AHead a a0))).(\lambda (P: 
Prop).(let TMP_35 \def (AHead a a0) in (let TMP_36 \def (AHead a a0) in (let 
H_x \def (leq_gen_head1 g TMP_35 a2 TMP_36 H1) in (let H2 \def H_x in (let 
TMP_38 \def (\lambda (a3: A).(\lambda (_: A).(let TMP_37 \def (AHead a a0) in 
(leq g TMP_37 a3)))) in (let TMP_39 \def (\lambda (_: A).(\lambda (a4: 
A).(leq g a2 a4))) in (let TMP_42 \def (\lambda (a3: A).(\lambda (a4: A).(let 
TMP_40 \def (AHead a a0) in (let TMP_41 \def (AHead a3 a4) in (eq A TMP_40 
TMP_41))))) in (let TMP_53 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H3: (leq g (AHead a a0) x0)).(\lambda (H4: (leq g a2 x1)).(\lambda (H5: (eq 
A (AHead a a0) (AHead x0 x1))).(let TMP_43 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a | (AHead a3 _) \Rightarrow a3])) in (let TMP_44 
\def (AHead a a0) in (let TMP_45 \def (AHead x0 x1) in (let H6 \def (f_equal 
A A TMP_43 TMP_44 TMP_45 H5) in (let TMP_46 \def (\lambda (e: A).(match e 
with [(ASort _ _) \Rightarrow a0 | (AHead _ a3) \Rightarrow a3])) in (let 
TMP_47 \def (AHead a a0) in (let TMP_48 \def (AHead x0 x1) in (let H7 \def 
(f_equal A A TMP_46 TMP_47 TMP_48 H5) in (let TMP_52 \def (\lambda (H8: (eq A 
a x0)).(let TMP_49 \def (\lambda (a3: A).(leq g a2 a3)) in (let H9 \def 
(eq_ind_r A x1 TMP_49 H4 a0 H7) in (let TMP_51 \def (\lambda (a3: A).(let 
TMP_50 \def (AHead a a0) in (leq g TMP_50 a3))) in (let H10 \def (eq_ind_r A 
x0 TMP_51 H3 a H8) in (H a0 H10 P)))))) in (TMP_52 H6))))))))))))))) in 
(ex3_2_ind A A TMP_38 TMP_39 TMP_42 P TMP_53 H2)))))))))))))))) in (A_ind 
TMP_1 TMP_34 TMP_54 a1))))).

theorem leq_ahead_false_2:
 \forall (g: G).(\forall (a2: A).(\forall (a1: A).((leq g (AHead a1 a2) a2) 
\to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a2: A).(let TMP_1 \def (\lambda (a: A).(\forall 
(a1: A).((leq g (AHead a1 a) a) \to (\forall (P: Prop).P)))) in (let TMP_34 
\def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (a1: A).(\lambda (H: (leq 
g (AHead a1 (ASort n n0)) (ASort n n0))).(\lambda (P: Prop).(let TMP_2 \def 
(\lambda (n1: nat).((leq g (AHead a1 (ASort n1 n0)) (ASort n1 n0)) \to P)) in 
(let TMP_15 \def (\lambda (H0: (leq g (AHead a1 (ASort O n0)) (ASort O 
n0))).(let TMP_3 \def (ASort O n0) in (let TMP_4 \def (ASort O n0) in (let 
H_x \def (leq_gen_head1 g a1 TMP_3 TMP_4 H0) in (let H1 \def H_x in (let 
TMP_5 \def (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) in (let TMP_7 
\def (\lambda (_: A).(\lambda (a4: A).(let TMP_6 \def (ASort O n0) in (leq g 
TMP_6 a4)))) in (let TMP_10 \def (\lambda (a3: A).(\lambda (a4: A).(let TMP_8 
\def (ASort O n0) in (let TMP_9 \def (AHead a3 a4) in (eq A TMP_8 TMP_9))))) 
in (let TMP_14 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g a1 
x0)).(\lambda (_: (leq g (ASort O n0) x1)).(\lambda (H4: (eq A (ASort O n0) 
(AHead x0 x1))).(let TMP_11 \def (ASort O n0) in (let TMP_12 \def (\lambda 
(ee: A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) in (let TMP_13 \def (AHead x0 x1) in (let H5 \def 
(eq_ind A TMP_11 TMP_12 I TMP_13 H4) in (False_ind P H5)))))))))) in 
(ex3_2_ind A A TMP_5 TMP_7 TMP_10 P TMP_14 H1)))))))))) in (let TMP_33 \def 
(\lambda (n1: nat).(\lambda (_: (((leq g (AHead a1 (ASort n1 n0)) (ASort n1 
n0)) \to P))).(\lambda (H0: (leq g (AHead a1 (ASort (S n1) n0)) (ASort (S n1) 
n0))).(let TMP_16 \def (S n1) in (let TMP_17 \def (ASort TMP_16 n0) in (let 
TMP_18 \def (S n1) in (let TMP_19 \def (ASort TMP_18 n0) in (let H_x \def 
(leq_gen_head1 g a1 TMP_17 TMP_19 H0) in (let H1 \def H_x in (let TMP_20 \def 
(\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) in (let TMP_23 \def (\lambda 
(_: A).(\lambda (a4: A).(let TMP_21 \def (S n1) in (let TMP_22 \def (ASort 
TMP_21 n0) in (leq g TMP_22 a4))))) in (let TMP_27 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_24 \def (S n1) in (let TMP_25 \def (ASort TMP_24 
n0) in (let TMP_26 \def (AHead a3 a4) in (eq A TMP_25 TMP_26)))))) in (let 
TMP_32 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g a1 
x0)).(\lambda (_: (leq g (ASort (S n1) n0) x1)).(\lambda (H4: (eq A (ASort (S 
n1) n0) (AHead x0 x1))).(let TMP_28 \def (S n1) in (let TMP_29 \def (ASort 
TMP_28 n0) in (let TMP_30 \def (\lambda (ee: A).(match ee with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) in (let TMP_31 \def 
(AHead x0 x1) in (let H5 \def (eq_ind A TMP_29 TMP_30 I TMP_31 H4) in 
(False_ind P H5))))))))))) in (ex3_2_ind A A TMP_20 TMP_23 TMP_27 P TMP_32 
H1)))))))))))))) in (nat_ind TMP_2 TMP_15 TMP_33 n H))))))))) in (let TMP_54 
\def (\lambda (a: A).(\lambda (_: ((\forall (a1: A).((leq g (AHead a1 a) a) 
\to (\forall (P: Prop).P))))).(\lambda (a0: A).(\lambda (H0: ((\forall (a1: 
A).((leq g (AHead a1 a0) a0) \to (\forall (P: Prop).P))))).(\lambda (a1: 
A).(\lambda (H1: (leq g (AHead a1 (AHead a a0)) (AHead a a0))).(\lambda (P: 
Prop).(let TMP_35 \def (AHead a a0) in (let TMP_36 \def (AHead a a0) in (let 
H_x \def (leq_gen_head1 g a1 TMP_35 TMP_36 H1) in (let H2 \def H_x in (let 
TMP_37 \def (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) in (let TMP_39 
\def (\lambda (_: A).(\lambda (a4: A).(let TMP_38 \def (AHead a a0) in (leq g 
TMP_38 a4)))) in (let TMP_42 \def (\lambda (a3: A).(\lambda (a4: A).(let 
TMP_40 \def (AHead a a0) in (let TMP_41 \def (AHead a3 a4) in (eq A TMP_40 
TMP_41))))) in (let TMP_53 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H3: (leq g a1 x0)).(\lambda (H4: (leq g (AHead a a0) x1)).(\lambda (H5: (eq 
A (AHead a a0) (AHead x0 x1))).(let TMP_43 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a | (AHead a3 _) \Rightarrow a3])) in (let TMP_44 
\def (AHead a a0) in (let TMP_45 \def (AHead x0 x1) in (let H6 \def (f_equal 
A A TMP_43 TMP_44 TMP_45 H5) in (let TMP_46 \def (\lambda (e: A).(match e 
with [(ASort _ _) \Rightarrow a0 | (AHead _ a3) \Rightarrow a3])) in (let 
TMP_47 \def (AHead a a0) in (let TMP_48 \def (AHead x0 x1) in (let H7 \def 
(f_equal A A TMP_46 TMP_47 TMP_48 H5) in (let TMP_52 \def (\lambda (H8: (eq A 
a x0)).(let TMP_50 \def (\lambda (a3: A).(let TMP_49 \def (AHead a a0) in 
(leq g TMP_49 a3))) in (let H9 \def (eq_ind_r A x1 TMP_50 H4 a0 H7) in (let 
TMP_51 \def (\lambda (a3: A).(leq g a1 a3)) in (let H10 \def (eq_ind_r A x0 
TMP_51 H3 a H8) in (H0 a H9 P)))))) in (TMP_52 H6))))))))))))))) in 
(ex3_2_ind A A TMP_37 TMP_39 TMP_42 P TMP_53 H2)))))))))))))))) in (A_ind 
TMP_1 TMP_34 TMP_54 a2))))).

