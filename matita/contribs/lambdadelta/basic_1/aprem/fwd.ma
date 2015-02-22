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

include "basic_1/aprem/defs.ma".

let rec aprem_ind (P: (nat \to (A \to (A \to Prop)))) (f: (\forall (a1: 
A).(\forall (a2: A).(P O (AHead a1 a2) a1)))) (f0: (\forall (a2: A).(\forall 
(a: A).(\forall (i: nat).((aprem i a2 a) \to ((P i a2 a) \to (\forall (a1: 
A).(P (S i) (AHead a1 a2) a)))))))) (n: nat) (a: A) (a0: A) (a1: aprem n a 
a0) on a1: P n a a0 \def match a1 with [(aprem_zero a2 a3) \Rightarrow (f a2 
a3) | (aprem_succ a2 a3 i a4 a5) \Rightarrow (let TMP_1 \def ((aprem_ind P f 
f0) i a2 a3 a4) in (f0 a2 a3 i a4 TMP_1 a5))].

theorem aprem_gen_sort:
 \forall (x: A).(\forall (i: nat).(\forall (h: nat).(\forall (n: nat).((aprem 
i (ASort h n) x) \to False))))
\def
 \lambda (x: A).(\lambda (i: nat).(\lambda (h: nat).(\lambda (n: 
nat).(\lambda (H: (aprem i (ASort h n) x)).(let TMP_1 \def (ASort h n) in 
(let TMP_2 \def (\lambda (a: A).(aprem i a x)) in (let TMP_3 \def (\lambda 
(_: A).False) in (let TMP_13 \def (\lambda (y: A).(\lambda (H0: (aprem i y 
x)).(let TMP_4 \def (\lambda (_: nat).(\lambda (a: A).(\lambda (_: A).((eq A 
a (ASort h n)) \to False)))) in (let TMP_8 \def (\lambda (a1: A).(\lambda 
(a2: A).(\lambda (H1: (eq A (AHead a1 a2) (ASort h n))).(let TMP_5 \def 
(AHead a1 a2) in (let TMP_6 \def (\lambda (ee: A).(match ee with [(ASort _ _) 
\Rightarrow False | (AHead _ _) \Rightarrow True])) in (let TMP_7 \def (ASort 
h n) in (let H2 \def (eq_ind A TMP_5 TMP_6 I TMP_7 H1) in (False_ind False 
H2)))))))) in (let TMP_12 \def (\lambda (a2: A).(\lambda (a: A).(\lambda (i0: 
nat).(\lambda (_: (aprem i0 a2 a)).(\lambda (_: (((eq A a2 (ASort h n)) \to 
False))).(\lambda (a1: A).(\lambda (H3: (eq A (AHead a1 a2) (ASort h 
n))).(let TMP_9 \def (AHead a1 a2) in (let TMP_10 \def (\lambda (ee: 
A).(match ee with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) in (let TMP_11 \def (ASort h n) in (let H4 \def (eq_ind A TMP_9 
TMP_10 I TMP_11 H3) in (False_ind False H4)))))))))))) in (aprem_ind TMP_4 
TMP_8 TMP_12 i y x H0)))))) in (insert_eq A TMP_1 TMP_2 TMP_3 TMP_13 
H))))))))).

theorem aprem_gen_head_O:
 \forall (a1: A).(\forall (a2: A).(\forall (x: A).((aprem O (AHead a1 a2) x) 
\to (eq A x a1))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (x: A).(\lambda (H: (aprem O 
(AHead a1 a2) x)).(let TMP_1 \def (AHead a1 a2) in (let TMP_2 \def (\lambda 
(a: A).(aprem O a x)) in (let TMP_3 \def (\lambda (_: A).(eq A x a1)) in (let 
TMP_29 \def (\lambda (y: A).(\lambda (H0: (aprem O y x)).(let TMP_4 \def 
(\lambda (n: nat).(aprem n y x)) in (let TMP_5 \def (\lambda (_: nat).((eq A 
y (AHead a1 a2)) \to (eq A x a1))) in (let TMP_28 \def (\lambda (y0: 
nat).(\lambda (H1: (aprem y0 y x)).(let TMP_6 \def (\lambda (n: nat).(\lambda 
(a: A).(\lambda (a0: A).((eq nat n O) \to ((eq A a (AHead a1 a2)) \to (eq A 
a0 a1)))))) in (let TMP_14 \def (\lambda (a0: A).(\lambda (a3: A).(\lambda 
(_: (eq nat O O)).(\lambda (H3: (eq A (AHead a0 a3) (AHead a1 a2))).(let 
TMP_7 \def (\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a0 | (AHead 
a _) \Rightarrow a])) in (let TMP_8 \def (AHead a0 a3) in (let TMP_9 \def 
(AHead a1 a2) in (let H4 \def (f_equal A A TMP_7 TMP_8 TMP_9 H3) in (let 
TMP_10 \def (\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a3 | 
(AHead _ a) \Rightarrow a])) in (let TMP_11 \def (AHead a0 a3) in (let TMP_12 
\def (AHead a1 a2) in (let H5 \def (f_equal A A TMP_10 TMP_11 TMP_12 H3) in 
(let TMP_13 \def (\lambda (H6: (eq A a0 a1)).H6) in (TMP_13 H4)))))))))))))) 
in (let TMP_27 \def (\lambda (a0: A).(\lambda (a: A).(\lambda (i: 
nat).(\lambda (H2: (aprem i a0 a)).(\lambda (H3: (((eq nat i O) \to ((eq A a0 
(AHead a1 a2)) \to (eq A a a1))))).(\lambda (a3: A).(\lambda (H4: (eq nat (S 
i) O)).(\lambda (H5: (eq A (AHead a3 a0) (AHead a1 a2))).(let TMP_15 \def 
(\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a3 | (AHead a4 _) 
\Rightarrow a4])) in (let TMP_16 \def (AHead a3 a0) in (let TMP_17 \def 
(AHead a1 a2) in (let H6 \def (f_equal A A TMP_15 TMP_16 TMP_17 H5) in (let 
TMP_18 \def (\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a0 | 
(AHead _ a4) \Rightarrow a4])) in (let TMP_19 \def (AHead a3 a0) in (let 
TMP_20 \def (AHead a1 a2) in (let H7 \def (f_equal A A TMP_18 TMP_19 TMP_20 
H5) in (let TMP_26 \def (\lambda (_: (eq A a3 a1)).(let TMP_21 \def (\lambda 
(a4: A).((eq nat i O) \to ((eq A a4 (AHead a1 a2)) \to (eq A a a1)))) in (let 
H9 \def (eq_ind A a0 TMP_21 H3 a2 H7) in (let TMP_22 \def (\lambda (a4: 
A).(aprem i a4 a)) in (let H10 \def (eq_ind A a0 TMP_22 H2 a2 H7) in (let 
TMP_23 \def (S i) in (let TMP_24 \def (\lambda (ee: nat).(match ee with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H11 \def (eq_ind nat 
TMP_23 TMP_24 I O H4) in (let TMP_25 \def (eq A a a1) in (False_ind TMP_25 
H11)))))))))) in (TMP_26 H6)))))))))))))))))) in (aprem_ind TMP_6 TMP_14 
TMP_27 y0 y x H1)))))) in (insert_eq nat O TMP_4 TMP_5 TMP_28 H0)))))) in 
(insert_eq A TMP_1 TMP_2 TMP_3 TMP_29 H)))))))).

theorem aprem_gen_head_S:
 \forall (a1: A).(\forall (a2: A).(\forall (x: A).(\forall (i: nat).((aprem 
(S i) (AHead a1 a2) x) \to (aprem i a2 x)))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (x: A).(\lambda (i: nat).(\lambda 
(H: (aprem (S i) (AHead a1 a2) x)).(let TMP_1 \def (AHead a1 a2) in (let 
TMP_3 \def (\lambda (a: A).(let TMP_2 \def (S i) in (aprem TMP_2 a x))) in 
(let TMP_4 \def (\lambda (_: A).(aprem i a2 x)) in (let TMP_38 \def (\lambda 
(y: A).(\lambda (H0: (aprem (S i) y x)).(let TMP_5 \def (S i) in (let TMP_6 
\def (\lambda (n: nat).(aprem n y x)) in (let TMP_7 \def (\lambda (_: 
nat).((eq A y (AHead a1 a2)) \to (aprem i a2 x))) in (let TMP_37 \def 
(\lambda (y0: nat).(\lambda (H1: (aprem y0 y x)).(let TMP_8 \def (\lambda (n: 
nat).(\lambda (a: A).(\lambda (a0: A).((eq nat n (S i)) \to ((eq A a (AHead 
a1 a2)) \to (aprem i a2 a0)))))) in (let TMP_21 \def (\lambda (a0: 
A).(\lambda (a3: A).(\lambda (H2: (eq nat O (S i))).(\lambda (H3: (eq A 
(AHead a0 a3) (AHead a1 a2))).(let TMP_9 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a0 | (AHead a _) \Rightarrow a])) in (let TMP_10 
\def (AHead a0 a3) in (let TMP_11 \def (AHead a1 a2) in (let H4 \def (f_equal 
A A TMP_9 TMP_10 TMP_11 H3) in (let TMP_12 \def (\lambda (e: A).(match e with 
[(ASort _ _) \Rightarrow a3 | (AHead _ a) \Rightarrow a])) in (let TMP_13 
\def (AHead a0 a3) in (let TMP_14 \def (AHead a1 a2) in (let H5 \def (f_equal 
A A TMP_12 TMP_13 TMP_14 H3) in (let TMP_20 \def (\lambda (H6: (eq A a0 
a1)).(let TMP_15 \def (\lambda (a: A).(aprem i a2 a)) in (let TMP_16 \def 
(\lambda (ee: nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow 
False])) in (let TMP_17 \def (S i) in (let H7 \def (eq_ind nat O TMP_16 I 
TMP_17 H2) in (let TMP_18 \def (aprem i a2 a1) in (let TMP_19 \def (False_ind 
TMP_18 H7) in (eq_ind_r A a1 TMP_15 TMP_19 a0 H6)))))))) in (TMP_20 
H4)))))))))))))) in (let TMP_36 \def (\lambda (a0: A).(\lambda (a: 
A).(\lambda (i0: nat).(\lambda (H2: (aprem i0 a0 a)).(\lambda (H3: (((eq nat 
i0 (S i)) \to ((eq A a0 (AHead a1 a2)) \to (aprem i a2 a))))).(\lambda (a3: 
A).(\lambda (H4: (eq nat (S i0) (S i))).(\lambda (H5: (eq A (AHead a3 a0) 
(AHead a1 a2))).(let TMP_22 \def (\lambda (e: A).(match e with [(ASort _ _) 
\Rightarrow a3 | (AHead a4 _) \Rightarrow a4])) in (let TMP_23 \def (AHead a3 
a0) in (let TMP_24 \def (AHead a1 a2) in (let H6 \def (f_equal A A TMP_22 
TMP_23 TMP_24 H5) in (let TMP_25 \def (\lambda (e: A).(match e with [(ASort _ 
_) \Rightarrow a0 | (AHead _ a4) \Rightarrow a4])) in (let TMP_26 \def (AHead 
a3 a0) in (let TMP_27 \def (AHead a1 a2) in (let H7 \def (f_equal A A TMP_25 
TMP_26 TMP_27 H5) in (let TMP_35 \def (\lambda (_: (eq A a3 a1)).(let TMP_28 
\def (\lambda (a4: A).((eq nat i0 (S i)) \to ((eq A a4 (AHead a1 a2)) \to 
(aprem i a2 a)))) in (let H9 \def (eq_ind A a0 TMP_28 H3 a2 H7) in (let 
TMP_29 \def (\lambda (a4: A).(aprem i0 a4 a)) in (let H10 \def (eq_ind A a0 
TMP_29 H2 a2 H7) in (let TMP_30 \def (\lambda (e: nat).(match e with [O 
\Rightarrow i0 | (S n) \Rightarrow n])) in (let TMP_31 \def (S i0) in (let 
TMP_32 \def (S i) in (let H11 \def (f_equal nat nat TMP_30 TMP_31 TMP_32 H4) 
in (let TMP_33 \def (\lambda (n: nat).((eq nat n (S i)) \to ((eq A a2 (AHead 
a1 a2)) \to (aprem i a2 a)))) in (let H12 \def (eq_ind nat i0 TMP_33 H9 i 
H11) in (let TMP_34 \def (\lambda (n: nat).(aprem n a2 a)) in (let H13 \def 
(eq_ind nat i0 TMP_34 H10 i H11) in H13))))))))))))) in (TMP_35 
H6)))))))))))))))))) in (aprem_ind TMP_8 TMP_21 TMP_36 y0 y x H1)))))) in 
(insert_eq nat TMP_5 TMP_6 TMP_7 TMP_37 H0))))))) in (insert_eq A TMP_1 TMP_3 
TMP_4 TMP_38 H))))))))).

