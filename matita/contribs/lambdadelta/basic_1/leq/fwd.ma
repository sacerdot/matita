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

include "basic_1/leq/defs.ma".

let rec leq_ind (g: G) (P: (A \to (A \to Prop))) (f: (\forall (h1: 
nat).(\forall (h2: nat).(\forall (n1: nat).(\forall (n2: nat).(\forall (k: 
nat).((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k)) \to (P 
(ASort h1 n1) (ASort h2 n2))))))))) (f0: (\forall (a1: A).(\forall (a2: 
A).((leq g a1 a2) \to ((P a1 a2) \to (\forall (a3: A).(\forall (a4: A).((leq 
g a3 a4) \to ((P a3 a4) \to (P (AHead a1 a3) (AHead a2 a4))))))))))) (a: A) 
(a0: A) (l: leq g a a0) on l: P a a0 \def match l with [(leq_sort h1 h2 n1 n2 
k e) \Rightarrow (f h1 h2 n1 n2 k e) | (leq_head a1 a2 l0 a3 a4 l1) 
\Rightarrow (let TMP_1 \def ((leq_ind g P f f0) a1 a2 l0) in (let TMP_2 \def 
((leq_ind g P f f0) a3 a4 l1) in (f0 a1 a2 l0 TMP_1 a3 a4 l1 TMP_2)))].

theorem leq_gen_sort1:
 \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq 
g (ASort h1 n1) a2) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a2 
(ASort h2 n2))))))))))
\def
 \lambda (g: G).(\lambda (h1: nat).(\lambda (n1: nat).(\lambda (a2: 
A).(\lambda (H: (leq g (ASort h1 n1) a2)).(let TMP_1 \def (ASort h1 n1) in 
(let TMP_2 \def (\lambda (a: A).(leq g a a2)) in (let TMP_9 \def (\lambda (a: 
A).(let TMP_6 \def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(let TMP_3 \def (aplus g a k) in (let TMP_4 \def (ASort h2 n2) in (let 
TMP_5 \def (aplus g TMP_4 k) in (eq A TMP_3 TMP_5))))))) in (let TMP_8 \def 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_7 \def 
(ASort h2 n2) in (eq A a2 TMP_7))))) in (ex2_3 nat nat nat TMP_6 TMP_8)))) in 
(let TMP_78 \def (\lambda (y: A).(\lambda (H0: (leq g y a2)).(let TMP_16 \def 
(\lambda (a: A).(\lambda (a0: A).((eq A a (ASort h1 n1)) \to (let TMP_13 \def 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_10 \def 
(aplus g a k) in (let TMP_11 \def (ASort h2 n2) in (let TMP_12 \def (aplus g 
TMP_11 k) in (eq A TMP_10 TMP_12))))))) in (let TMP_15 \def (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_14 \def (ASort h2 n2) in 
(eq A a0 TMP_14))))) in (ex2_3 nat nat nat TMP_13 TMP_15)))))) in (let TMP_64 
\def (\lambda (h0: nat).(\lambda (h2: nat).(\lambda (n0: nat).(\lambda (n2: 
nat).(\lambda (k: nat).(\lambda (H1: (eq A (aplus g (ASort h0 n0) k) (aplus g 
(ASort h2 n2) k))).(\lambda (H2: (eq A (ASort h0 n0) (ASort h1 n1))).(let 
TMP_17 \def (\lambda (e: A).(match e with [(ASort n _) \Rightarrow n | (AHead 
_ _) \Rightarrow h0])) in (let TMP_18 \def (ASort h0 n0) in (let TMP_19 \def 
(ASort h1 n1) in (let H3 \def (f_equal A nat TMP_17 TMP_18 TMP_19 H2) in (let 
TMP_20 \def (\lambda (e: A).(match e with [(ASort _ n) \Rightarrow n | (AHead 
_ _) \Rightarrow n0])) in (let TMP_21 \def (ASort h0 n0) in (let TMP_22 \def 
(ASort h1 n1) in (let H4 \def (f_equal A nat TMP_20 TMP_21 TMP_22 H2) in (let 
TMP_63 \def (\lambda (H5: (eq nat h0 h1)).(let TMP_27 \def (\lambda (n: 
nat).(let TMP_23 \def (ASort h0 n) in (let TMP_24 \def (aplus g TMP_23 k) in 
(let TMP_25 \def (ASort h2 n2) in (let TMP_26 \def (aplus g TMP_25 k) in (eq 
A TMP_24 TMP_26)))))) in (let H6 \def (eq_ind nat n0 TMP_27 H1 n1 H4) in (let 
TMP_36 \def (\lambda (n: nat).(let TMP_32 \def (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (k0: nat).(let TMP_28 \def (ASort h0 n) in (let TMP_29 
\def (aplus g TMP_28 k0) in (let TMP_30 \def (ASort h3 n3) in (let TMP_31 
\def (aplus g TMP_30 k0) in (eq A TMP_29 TMP_31)))))))) in (let TMP_35 \def 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(let TMP_33 \def 
(ASort h2 n2) in (let TMP_34 \def (ASort h3 n3) in (eq A TMP_33 TMP_34)))))) 
in (ex2_3 nat nat nat TMP_32 TMP_35)))) in (let TMP_41 \def (\lambda (n: 
nat).(let TMP_37 \def (ASort n n1) in (let TMP_38 \def (aplus g TMP_37 k) in 
(let TMP_39 \def (ASort h2 n2) in (let TMP_40 \def (aplus g TMP_39 k) in (eq 
A TMP_38 TMP_40)))))) in (let H7 \def (eq_ind nat h0 TMP_41 H6 h1 H5) in (let 
TMP_50 \def (\lambda (n: nat).(let TMP_46 \def (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (k0: nat).(let TMP_42 \def (ASort n n1) in (let TMP_43 
\def (aplus g TMP_42 k0) in (let TMP_44 \def (ASort h3 n3) in (let TMP_45 
\def (aplus g TMP_44 k0) in (eq A TMP_43 TMP_45)))))))) in (let TMP_49 \def 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(let TMP_47 \def 
(ASort h2 n2) in (let TMP_48 \def (ASort h3 n3) in (eq A TMP_47 TMP_48)))))) 
in (ex2_3 nat nat nat TMP_46 TMP_49)))) in (let TMP_55 \def (\lambda (n3: 
nat).(\lambda (h3: nat).(\lambda (k0: nat).(let TMP_51 \def (ASort h1 n1) in 
(let TMP_52 \def (aplus g TMP_51 k0) in (let TMP_53 \def (ASort h3 n3) in 
(let TMP_54 \def (aplus g TMP_53 k0) in (eq A TMP_52 TMP_54)))))))) in (let 
TMP_58 \def (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(let 
TMP_56 \def (ASort h2 n2) in (let TMP_57 \def (ASort h3 n3) in (eq A TMP_56 
TMP_57)))))) in (let TMP_59 \def (ASort h2 n2) in (let TMP_60 \def 
(refl_equal A TMP_59) in (let TMP_61 \def (ex2_3_intro nat nat nat TMP_55 
TMP_58 n2 h2 k H7 TMP_60) in (let TMP_62 \def (eq_ind_r nat h1 TMP_50 TMP_61 
h0 H5) in (eq_ind_r nat n1 TMP_36 TMP_62 n0 H4)))))))))))))) in (TMP_63 
H3))))))))))))))))) in (let TMP_77 \def (\lambda (a1: A).(\lambda (a3: 
A).(\lambda (_: (leq g a1 a3)).(\lambda (_: (((eq A a1 (ASort h1 n1)) \to 
(ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(eq A (aplus g a1 k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a3 (ASort h2 
n2))))))))).(\lambda (a4: A).(\lambda (a5: A).(\lambda (_: (leq g a4 
a5)).(\lambda (_: (((eq A a4 (ASort h1 n1)) \to (ex2_3 nat nat nat (\lambda 
(n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g a4 k) (aplus g 
(ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: 
nat).(eq A a5 (ASort h2 n2))))))))).(\lambda (H5: (eq A (AHead a1 a4) (ASort 
h1 n1))).(let TMP_65 \def (AHead a1 a4) in (let TMP_66 \def (\lambda (ee: 
A).(match ee with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) in (let TMP_67 \def (ASort h1 n1) in (let H6 \def (eq_ind A TMP_65 
TMP_66 I TMP_67 H5) in (let TMP_72 \def (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(let TMP_68 \def (AHead a1 a4) in (let TMP_69 \def 
(aplus g TMP_68 k) in (let TMP_70 \def (ASort h2 n2) in (let TMP_71 \def 
(aplus g TMP_70 k) in (eq A TMP_69 TMP_71)))))))) in (let TMP_75 \def 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_73 \def 
(AHead a3 a5) in (let TMP_74 \def (ASort h2 n2) in (eq A TMP_73 TMP_74)))))) 
in (let TMP_76 \def (ex2_3 nat nat nat TMP_72 TMP_75) in (False_ind TMP_76 
H6))))))))))))))))) in (leq_ind g TMP_16 TMP_64 TMP_77 y a2 H0)))))) in 
(insert_eq A TMP_1 TMP_2 TMP_9 TMP_78 H))))))))).

theorem leq_gen_head1:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g 
(AHead a1 a2) a) \to (ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g a1 
a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(\lambda 
(H: (leq g (AHead a1 a2) a)).(let TMP_1 \def (AHead a1 a2) in (let TMP_2 \def 
(\lambda (a0: A).(leq g a0 a)) in (let TMP_7 \def (\lambda (_: A).(let TMP_3 
\def (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) in (let TMP_4 \def 
(\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) in (let TMP_6 \def (\lambda 
(a3: A).(\lambda (a4: A).(let TMP_5 \def (AHead a3 a4) in (eq A a TMP_5)))) 
in (ex3_2 A A TMP_3 TMP_4 TMP_6))))) in (let TMP_50 \def (\lambda (y: 
A).(\lambda (H0: (leq g y a)).(let TMP_12 \def (\lambda (a0: A).(\lambda (a3: 
A).((eq A a0 (AHead a1 a2)) \to (let TMP_8 \def (\lambda (a4: A).(\lambda (_: 
A).(leq g a1 a4))) in (let TMP_9 \def (\lambda (_: A).(\lambda (a5: A).(leq g 
a2 a5))) in (let TMP_11 \def (\lambda (a4: A).(\lambda (a5: A).(let TMP_10 
\def (AHead a4 a5) in (eq A a3 TMP_10)))) in (ex3_2 A A TMP_8 TMP_9 
TMP_11))))))) in (let TMP_22 \def (\lambda (h1: nat).(\lambda (h2: 
nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq 
A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (H2: (eq A 
(ASort h1 n1) (AHead a1 a2))).(let TMP_13 \def (ASort h1 n1) in (let TMP_14 
\def (\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ 
_) \Rightarrow False])) in (let TMP_15 \def (AHead a1 a2) in (let H3 \def 
(eq_ind A TMP_13 TMP_14 I TMP_15 H2) in (let TMP_16 \def (\lambda (a3: 
A).(\lambda (_: A).(leq g a1 a3))) in (let TMP_17 \def (\lambda (_: 
A).(\lambda (a4: A).(leq g a2 a4))) in (let TMP_20 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_18 \def (ASort h2 n2) in (let TMP_19 \def (AHead 
a3 a4) in (eq A TMP_18 TMP_19))))) in (let TMP_21 \def (ex3_2 A A TMP_16 
TMP_17 TMP_20) in (False_ind TMP_21 H3)))))))))))))))) in (let TMP_49 \def 
(\lambda (a0: A).(\lambda (a3: A).(\lambda (H1: (leq g a0 a3)).(\lambda (H2: 
(((eq A a0 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a4: A).(\lambda (_: 
A).(leq g a1 a4))) (\lambda (_: A).(\lambda (a5: A).(leq g a2 a5))) (\lambda 
(a4: A).(\lambda (a5: A).(eq A a3 (AHead a4 a5)))))))).(\lambda (a4: 
A).(\lambda (a5: A).(\lambda (H3: (leq g a4 a5)).(\lambda (H4: (((eq A a4 
(AHead a1 a2)) \to (ex3_2 A A (\lambda (a6: A).(\lambda (_: A).(leq g a1 
a6))) (\lambda (_: A).(\lambda (a7: A).(leq g a2 a7))) (\lambda (a6: 
A).(\lambda (a7: A).(eq A a5 (AHead a6 a7)))))))).(\lambda (H5: (eq A (AHead 
a0 a4) (AHead a1 a2))).(let TMP_23 \def (\lambda (e: A).(match e with [(ASort 
_ _) \Rightarrow a0 | (AHead a6 _) \Rightarrow a6])) in (let TMP_24 \def 
(AHead a0 a4) in (let TMP_25 \def (AHead a1 a2) in (let H6 \def (f_equal A A 
TMP_23 TMP_24 TMP_25 H5) in (let TMP_26 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a4 | (AHead _ a6) \Rightarrow a6])) in (let TMP_27 
\def (AHead a0 a4) in (let TMP_28 \def (AHead a1 a2) in (let H7 \def (f_equal 
A A TMP_26 TMP_27 TMP_28 H5) in (let TMP_48 \def (\lambda (H8: (eq A a0 
a1)).(let TMP_33 \def (\lambda (a6: A).((eq A a6 (AHead a1 a2)) \to (let 
TMP_29 \def (\lambda (a7: A).(\lambda (_: A).(leq g a1 a7))) in (let TMP_30 
\def (\lambda (_: A).(\lambda (a8: A).(leq g a2 a8))) in (let TMP_32 \def 
(\lambda (a7: A).(\lambda (a8: A).(let TMP_31 \def (AHead a7 a8) in (eq A a5 
TMP_31)))) in (ex3_2 A A TMP_29 TMP_30 TMP_32)))))) in (let H9 \def (eq_ind A 
a4 TMP_33 H4 a2 H7) in (let TMP_34 \def (\lambda (a6: A).(leq g a6 a5)) in 
(let H10 \def (eq_ind A a4 TMP_34 H3 a2 H7) in (let TMP_39 \def (\lambda (a6: 
A).((eq A a6 (AHead a1 a2)) \to (let TMP_35 \def (\lambda (a7: A).(\lambda 
(_: A).(leq g a1 a7))) in (let TMP_36 \def (\lambda (_: A).(\lambda (a8: 
A).(leq g a2 a8))) in (let TMP_38 \def (\lambda (a7: A).(\lambda (a8: A).(let 
TMP_37 \def (AHead a7 a8) in (eq A a3 TMP_37)))) in (ex3_2 A A TMP_35 TMP_36 
TMP_38)))))) in (let H11 \def (eq_ind A a0 TMP_39 H2 a1 H8) in (let TMP_40 
\def (\lambda (a6: A).(leq g a6 a3)) in (let H12 \def (eq_ind A a0 TMP_40 H1 
a1 H8) in (let TMP_41 \def (\lambda (a6: A).(\lambda (_: A).(leq g a1 a6))) 
in (let TMP_42 \def (\lambda (_: A).(\lambda (a7: A).(leq g a2 a7))) in (let 
TMP_45 \def (\lambda (a6: A).(\lambda (a7: A).(let TMP_43 \def (AHead a3 a5) 
in (let TMP_44 \def (AHead a6 a7) in (eq A TMP_43 TMP_44))))) in (let TMP_46 
\def (AHead a3 a5) in (let TMP_47 \def (refl_equal A TMP_46) in (ex3_2_intro 
A A TMP_41 TMP_42 TMP_45 a3 a5 H12 H10 TMP_47))))))))))))))) in (TMP_48 
H6))))))))))))))))))) in (leq_ind g TMP_12 TMP_22 TMP_49 y a H0)))))) in 
(insert_eq A TMP_1 TMP_2 TMP_7 TMP_50 H))))))))).

theorem leq_gen_sort2:
 \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq 
g a2 (ASort h1 n1)) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort h2 n2) k) (aplus g (ASort h1 n1) 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a2 
(ASort h2 n2))))))))))
\def
 \lambda (g: G).(\lambda (h1: nat).(\lambda (n1: nat).(\lambda (a2: 
A).(\lambda (H: (leq g a2 (ASort h1 n1))).(let TMP_1 \def (ASort h1 n1) in 
(let TMP_2 \def (\lambda (a: A).(leq g a2 a)) in (let TMP_9 \def (\lambda (a: 
A).(let TMP_6 \def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(let TMP_3 \def (ASort h2 n2) in (let TMP_4 \def (aplus g TMP_3 k) in 
(let TMP_5 \def (aplus g a k) in (eq A TMP_4 TMP_5))))))) in (let TMP_8 \def 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_7 \def 
(ASort h2 n2) in (eq A a2 TMP_7))))) in (ex2_3 nat nat nat TMP_6 TMP_8)))) in 
(let TMP_78 \def (\lambda (y: A).(\lambda (H0: (leq g a2 y)).(let TMP_16 \def 
(\lambda (a: A).(\lambda (a0: A).((eq A a0 (ASort h1 n1)) \to (let TMP_13 
\def (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(let TMP_10 \def 
(ASort h2 n2) in (let TMP_11 \def (aplus g TMP_10 k) in (let TMP_12 \def 
(aplus g a0 k) in (eq A TMP_11 TMP_12))))))) in (let TMP_15 \def (\lambda 
(n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_14 \def (ASort h2 n2) 
in (eq A a TMP_14))))) in (ex2_3 nat nat nat TMP_13 TMP_15)))))) in (let 
TMP_64 \def (\lambda (h0: nat).(\lambda (h2: nat).(\lambda (n0: nat).(\lambda 
(n2: nat).(\lambda (k: nat).(\lambda (H1: (eq A (aplus g (ASort h0 n0) k) 
(aplus g (ASort h2 n2) k))).(\lambda (H2: (eq A (ASort h2 n2) (ASort h1 
n1))).(let TMP_17 \def (\lambda (e: A).(match e with [(ASort n _) \Rightarrow 
n | (AHead _ _) \Rightarrow h2])) in (let TMP_18 \def (ASort h2 n2) in (let 
TMP_19 \def (ASort h1 n1) in (let H3 \def (f_equal A nat TMP_17 TMP_18 TMP_19 
H2) in (let TMP_20 \def (\lambda (e: A).(match e with [(ASort _ n) 
\Rightarrow n | (AHead _ _) \Rightarrow n2])) in (let TMP_21 \def (ASort h2 
n2) in (let TMP_22 \def (ASort h1 n1) in (let H4 \def (f_equal A nat TMP_20 
TMP_21 TMP_22 H2) in (let TMP_63 \def (\lambda (H5: (eq nat h2 h1)).(let 
TMP_27 \def (\lambda (n: nat).(let TMP_23 \def (ASort h0 n0) in (let TMP_24 
\def (aplus g TMP_23 k) in (let TMP_25 \def (ASort h2 n) in (let TMP_26 \def 
(aplus g TMP_25 k) in (eq A TMP_24 TMP_26)))))) in (let H6 \def (eq_ind nat 
n2 TMP_27 H1 n1 H4) in (let TMP_36 \def (\lambda (n: nat).(let TMP_32 \def 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (k0: nat).(let TMP_28 \def 
(ASort h3 n3) in (let TMP_29 \def (aplus g TMP_28 k0) in (let TMP_30 \def 
(ASort h2 n) in (let TMP_31 \def (aplus g TMP_30 k0) in (eq A TMP_29 
TMP_31)))))))) in (let TMP_35 \def (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (_: nat).(let TMP_33 \def (ASort h0 n0) in (let TMP_34 \def 
(ASort h3 n3) in (eq A TMP_33 TMP_34)))))) in (ex2_3 nat nat nat TMP_32 
TMP_35)))) in (let TMP_41 \def (\lambda (n: nat).(let TMP_37 \def (ASort h0 
n0) in (let TMP_38 \def (aplus g TMP_37 k) in (let TMP_39 \def (ASort n n1) 
in (let TMP_40 \def (aplus g TMP_39 k) in (eq A TMP_38 TMP_40)))))) in (let 
H7 \def (eq_ind nat h2 TMP_41 H6 h1 H5) in (let TMP_50 \def (\lambda (n: 
nat).(let TMP_46 \def (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (k0: 
nat).(let TMP_42 \def (ASort h3 n3) in (let TMP_43 \def (aplus g TMP_42 k0) 
in (let TMP_44 \def (ASort n n1) in (let TMP_45 \def (aplus g TMP_44 k0) in 
(eq A TMP_43 TMP_45)))))))) in (let TMP_49 \def (\lambda (n3: nat).(\lambda 
(h3: nat).(\lambda (_: nat).(let TMP_47 \def (ASort h0 n0) in (let TMP_48 
\def (ASort h3 n3) in (eq A TMP_47 TMP_48)))))) in (ex2_3 nat nat nat TMP_46 
TMP_49)))) in (let TMP_55 \def (\lambda (n3: nat).(\lambda (h3: nat).(\lambda 
(k0: nat).(let TMP_51 \def (ASort h3 n3) in (let TMP_52 \def (aplus g TMP_51 
k0) in (let TMP_53 \def (ASort h1 n1) in (let TMP_54 \def (aplus g TMP_53 k0) 
in (eq A TMP_52 TMP_54)))))))) in (let TMP_58 \def (\lambda (n3: 
nat).(\lambda (h3: nat).(\lambda (_: nat).(let TMP_56 \def (ASort h0 n0) in 
(let TMP_57 \def (ASort h3 n3) in (eq A TMP_56 TMP_57)))))) in (let TMP_59 
\def (ASort h0 n0) in (let TMP_60 \def (refl_equal A TMP_59) in (let TMP_61 
\def (ex2_3_intro nat nat nat TMP_55 TMP_58 n0 h0 k H7 TMP_60) in (let TMP_62 
\def (eq_ind_r nat h1 TMP_50 TMP_61 h2 H5) in (eq_ind_r nat n1 TMP_36 TMP_62 
n2 H4)))))))))))))) in (TMP_63 H3))))))))))))))))) in (let TMP_77 \def 
(\lambda (a1: A).(\lambda (a3: A).(\lambda (_: (leq g a1 a3)).(\lambda (_: 
(((eq A a3 (ASort h1 n1)) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda 
(h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h2 n2) k) (aplus g a3 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a1 
(ASort h2 n2))))))))).(\lambda (a4: A).(\lambda (a5: A).(\lambda (_: (leq g 
a4 a5)).(\lambda (_: (((eq A a5 (ASort h1 n1)) \to (ex2_3 nat nat nat 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
h2 n2) k) (aplus g a5 k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A a4 (ASort h2 n2))))))))).(\lambda (H5: (eq A (AHead a3 a5) 
(ASort h1 n1))).(let TMP_65 \def (AHead a3 a5) in (let TMP_66 \def (\lambda 
(ee: A).(match ee with [(ASort _ _) \Rightarrow False | (AHead _ _) 
\Rightarrow True])) in (let TMP_67 \def (ASort h1 n1) in (let H6 \def (eq_ind 
A TMP_65 TMP_66 I TMP_67 H5) in (let TMP_72 \def (\lambda (n2: nat).(\lambda 
(h2: nat).(\lambda (k: nat).(let TMP_68 \def (ASort h2 n2) in (let TMP_69 
\def (aplus g TMP_68 k) in (let TMP_70 \def (AHead a3 a5) in (let TMP_71 \def 
(aplus g TMP_70 k) in (eq A TMP_69 TMP_71)))))))) in (let TMP_75 \def 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(let TMP_73 \def 
(AHead a1 a4) in (let TMP_74 \def (ASort h2 n2) in (eq A TMP_73 TMP_74)))))) 
in (let TMP_76 \def (ex2_3 nat nat nat TMP_72 TMP_75) in (False_ind TMP_76 
H6))))))))))))))))) in (leq_ind g TMP_16 TMP_64 TMP_77 a2 y H0)))))) in 
(insert_eq A TMP_1 TMP_2 TMP_9 TMP_78 H))))))))).

theorem leq_gen_head2:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g a 
(AHead a1 a2)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g a3 
a1))) (\lambda (_: A).(\lambda (a4: A).(leq g a4 a2))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(\lambda 
(H: (leq g a (AHead a1 a2))).(let TMP_1 \def (AHead a1 a2) in (let TMP_2 \def 
(\lambda (a0: A).(leq g a a0)) in (let TMP_7 \def (\lambda (_: A).(let TMP_3 
\def (\lambda (a3: A).(\lambda (_: A).(leq g a3 a1))) in (let TMP_4 \def 
(\lambda (_: A).(\lambda (a4: A).(leq g a4 a2))) in (let TMP_6 \def (\lambda 
(a3: A).(\lambda (a4: A).(let TMP_5 \def (AHead a3 a4) in (eq A a TMP_5)))) 
in (ex3_2 A A TMP_3 TMP_4 TMP_6))))) in (let TMP_50 \def (\lambda (y: 
A).(\lambda (H0: (leq g a y)).(let TMP_12 \def (\lambda (a0: A).(\lambda (a3: 
A).((eq A a3 (AHead a1 a2)) \to (let TMP_8 \def (\lambda (a4: A).(\lambda (_: 
A).(leq g a4 a1))) in (let TMP_9 \def (\lambda (_: A).(\lambda (a5: A).(leq g 
a5 a2))) in (let TMP_11 \def (\lambda (a4: A).(\lambda (a5: A).(let TMP_10 
\def (AHead a4 a5) in (eq A a0 TMP_10)))) in (ex3_2 A A TMP_8 TMP_9 
TMP_11))))))) in (let TMP_22 \def (\lambda (h1: nat).(\lambda (h2: 
nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq 
A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (H2: (eq A 
(ASort h2 n2) (AHead a1 a2))).(let TMP_13 \def (ASort h2 n2) in (let TMP_14 
\def (\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ 
_) \Rightarrow False])) in (let TMP_15 \def (AHead a1 a2) in (let H3 \def 
(eq_ind A TMP_13 TMP_14 I TMP_15 H2) in (let TMP_16 \def (\lambda (a3: 
A).(\lambda (_: A).(leq g a3 a1))) in (let TMP_17 \def (\lambda (_: 
A).(\lambda (a4: A).(leq g a4 a2))) in (let TMP_20 \def (\lambda (a3: 
A).(\lambda (a4: A).(let TMP_18 \def (ASort h1 n1) in (let TMP_19 \def (AHead 
a3 a4) in (eq A TMP_18 TMP_19))))) in (let TMP_21 \def (ex3_2 A A TMP_16 
TMP_17 TMP_20) in (False_ind TMP_21 H3)))))))))))))))) in (let TMP_49 \def 
(\lambda (a0: A).(\lambda (a3: A).(\lambda (H1: (leq g a0 a3)).(\lambda (H2: 
(((eq A a3 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a4: A).(\lambda (_: 
A).(leq g a4 a1))) (\lambda (_: A).(\lambda (a5: A).(leq g a5 a2))) (\lambda 
(a4: A).(\lambda (a5: A).(eq A a0 (AHead a4 a5)))))))).(\lambda (a4: 
A).(\lambda (a5: A).(\lambda (H3: (leq g a4 a5)).(\lambda (H4: (((eq A a5 
(AHead a1 a2)) \to (ex3_2 A A (\lambda (a6: A).(\lambda (_: A).(leq g a6 
a1))) (\lambda (_: A).(\lambda (a7: A).(leq g a7 a2))) (\lambda (a6: 
A).(\lambda (a7: A).(eq A a4 (AHead a6 a7)))))))).(\lambda (H5: (eq A (AHead 
a3 a5) (AHead a1 a2))).(let TMP_23 \def (\lambda (e: A).(match e with [(ASort 
_ _) \Rightarrow a3 | (AHead a6 _) \Rightarrow a6])) in (let TMP_24 \def 
(AHead a3 a5) in (let TMP_25 \def (AHead a1 a2) in (let H6 \def (f_equal A A 
TMP_23 TMP_24 TMP_25 H5) in (let TMP_26 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a5 | (AHead _ a6) \Rightarrow a6])) in (let TMP_27 
\def (AHead a3 a5) in (let TMP_28 \def (AHead a1 a2) in (let H7 \def (f_equal 
A A TMP_26 TMP_27 TMP_28 H5) in (let TMP_48 \def (\lambda (H8: (eq A a3 
a1)).(let TMP_33 \def (\lambda (a6: A).((eq A a6 (AHead a1 a2)) \to (let 
TMP_29 \def (\lambda (a7: A).(\lambda (_: A).(leq g a7 a1))) in (let TMP_30 
\def (\lambda (_: A).(\lambda (a8: A).(leq g a8 a2))) in (let TMP_32 \def 
(\lambda (a7: A).(\lambda (a8: A).(let TMP_31 \def (AHead a7 a8) in (eq A a4 
TMP_31)))) in (ex3_2 A A TMP_29 TMP_30 TMP_32)))))) in (let H9 \def (eq_ind A 
a5 TMP_33 H4 a2 H7) in (let TMP_34 \def (\lambda (a6: A).(leq g a4 a6)) in 
(let H10 \def (eq_ind A a5 TMP_34 H3 a2 H7) in (let TMP_39 \def (\lambda (a6: 
A).((eq A a6 (AHead a1 a2)) \to (let TMP_35 \def (\lambda (a7: A).(\lambda 
(_: A).(leq g a7 a1))) in (let TMP_36 \def (\lambda (_: A).(\lambda (a8: 
A).(leq g a8 a2))) in (let TMP_38 \def (\lambda (a7: A).(\lambda (a8: A).(let 
TMP_37 \def (AHead a7 a8) in (eq A a0 TMP_37)))) in (ex3_2 A A TMP_35 TMP_36 
TMP_38)))))) in (let H11 \def (eq_ind A a3 TMP_39 H2 a1 H8) in (let TMP_40 
\def (\lambda (a6: A).(leq g a0 a6)) in (let H12 \def (eq_ind A a3 TMP_40 H1 
a1 H8) in (let TMP_41 \def (\lambda (a6: A).(\lambda (_: A).(leq g a6 a1))) 
in (let TMP_42 \def (\lambda (_: A).(\lambda (a7: A).(leq g a7 a2))) in (let 
TMP_45 \def (\lambda (a6: A).(\lambda (a7: A).(let TMP_43 \def (AHead a0 a4) 
in (let TMP_44 \def (AHead a6 a7) in (eq A TMP_43 TMP_44))))) in (let TMP_46 
\def (AHead a0 a4) in (let TMP_47 \def (refl_equal A TMP_46) in (ex3_2_intro 
A A TMP_41 TMP_42 TMP_45 a0 a4 H12 H10 TMP_47))))))))))))))) in (TMP_48 
H6))))))))))))))))))) in (leq_ind g TMP_12 TMP_22 TMP_49 a y H0)))))) in 
(insert_eq A TMP_1 TMP_2 TMP_7 TMP_50 H))))))))).

theorem ahead_inj_snd:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a3: A).(\forall 
(a4: A).((leq g (AHead a1 a2) (AHead a3 a4)) \to (leq g a2 a4))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda 
(a4: A).(\lambda (H: (leq g (AHead a1 a2) (AHead a3 a4))).(let TMP_1 \def 
(AHead a3 a4) in (let H_x \def (leq_gen_head1 g a1 a2 TMP_1 H) in (let H0 
\def H_x in (let TMP_2 \def (\lambda (a5: A).(\lambda (_: A).(leq g a1 a5))) 
in (let TMP_3 \def (\lambda (_: A).(\lambda (a6: A).(leq g a2 a6))) in (let 
TMP_6 \def (\lambda (a5: A).(\lambda (a6: A).(let TMP_4 \def (AHead a3 a4) in 
(let TMP_5 \def (AHead a5 a6) in (eq A TMP_4 TMP_5))))) in (let TMP_7 \def 
(leq g a2 a4) in (let TMP_17 \def (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H1: (leq g a1 x0)).(\lambda (H2: (leq g a2 x1)).(\lambda (H3: (eq A (AHead 
a3 a4) (AHead x0 x1))).(let TMP_8 \def (\lambda (e: A).(match e with [(ASort 
_ _) \Rightarrow a3 | (AHead a _) \Rightarrow a])) in (let TMP_9 \def (AHead 
a3 a4) in (let TMP_10 \def (AHead x0 x1) in (let H4 \def (f_equal A A TMP_8 
TMP_9 TMP_10 H3) in (let TMP_11 \def (\lambda (e: A).(match e with [(ASort _ 
_) \Rightarrow a4 | (AHead _ a) \Rightarrow a])) in (let TMP_12 \def (AHead 
a3 a4) in (let TMP_13 \def (AHead x0 x1) in (let H5 \def (f_equal A A TMP_11 
TMP_12 TMP_13 H3) in (let TMP_16 \def (\lambda (H6: (eq A a3 x0)).(let TMP_14 
\def (\lambda (a: A).(leq g a2 a)) in (let H7 \def (eq_ind_r A x1 TMP_14 H2 
a4 H5) in (let TMP_15 \def (\lambda (a: A).(leq g a1 a)) in (let H8 \def 
(eq_ind_r A x0 TMP_15 H1 a3 H6) in H7))))) in (TMP_16 H4))))))))))))))) in 
(ex3_2_ind A A TMP_2 TMP_3 TMP_6 TMP_7 TMP_17 H0)))))))))))))).

