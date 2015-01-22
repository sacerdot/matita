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

include "Basic-1/aprem/defs.ma".

theorem aprem_gen_sort:
 \forall (x: A).(\forall (i: nat).(\forall (h: nat).(\forall (n: nat).((aprem 
i (ASort h n) x) \to False))))
\def
 \lambda (x: A).(\lambda (i: nat).(\lambda (h: nat).(\lambda (n: 
nat).(\lambda (H: (aprem i (ASort h n) x)).(insert_eq A (ASort h n) (\lambda 
(a: A).(aprem i a x)) (\lambda (_: A).False) (\lambda (y: A).(\lambda (H0: 
(aprem i y x)).(aprem_ind (\lambda (_: nat).(\lambda (a: A).(\lambda (_: 
A).((eq A a (ASort h n)) \to False)))) (\lambda (a1: A).(\lambda (a2: 
A).(\lambda (H1: (eq A (AHead a1 a2) (ASort h n))).(let H2 \def (eq_ind A 
(AHead a1 a2) (\lambda (ee: A).(match ee in A return (\lambda (_: A).Prop) 
with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I 
(ASort h n) H1) in (False_ind False H2))))) (\lambda (a2: A).(\lambda (a: 
A).(\lambda (i0: nat).(\lambda (_: (aprem i0 a2 a)).(\lambda (_: (((eq A a2 
(ASort h n)) \to False))).(\lambda (a1: A).(\lambda (H3: (eq A (AHead a1 a2) 
(ASort h n))).(let H4 \def (eq_ind A (AHead a1 a2) (\lambda (ee: A).(match ee 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) I (ASort h n) H3) in (False_ind False 
H4))))))))) i y x H0))) H))))).
(* COMMENTS
Initial nodes: 227
END *)

theorem aprem_gen_head_O:
 \forall (a1: A).(\forall (a2: A).(\forall (x: A).((aprem O (AHead a1 a2) x) 
\to (eq A x a1))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (x: A).(\lambda (H: (aprem O 
(AHead a1 a2) x)).(insert_eq A (AHead a1 a2) (\lambda (a: A).(aprem O a x)) 
(\lambda (_: A).(eq A x a1)) (\lambda (y: A).(\lambda (H0: (aprem O y 
x)).(insert_eq nat O (\lambda (n: nat).(aprem n y x)) (\lambda (_: nat).((eq 
A y (AHead a1 a2)) \to (eq A x a1))) (\lambda (y0: nat).(\lambda (H1: (aprem 
y0 y x)).(aprem_ind (\lambda (n: nat).(\lambda (a: A).(\lambda (a0: A).((eq 
nat n O) \to ((eq A a (AHead a1 a2)) \to (eq A a0 a1)))))) (\lambda (a0: 
A).(\lambda (a3: A).(\lambda (_: (eq nat O O)).(\lambda (H3: (eq A (AHead a0 
a3) (AHead a1 a2))).(let H4 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead a _) 
\Rightarrow a])) (AHead a0 a3) (AHead a1 a2) H3) in ((let H5 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a3 | (AHead _ a) \Rightarrow a])) (AHead a0 a3) (AHead a1 a2) H3) 
in (\lambda (H6: (eq A a0 a1)).H6)) H4)))))) (\lambda (a0: A).(\lambda (a: 
A).(\lambda (i: nat).(\lambda (H2: (aprem i a0 a)).(\lambda (H3: (((eq nat i 
O) \to ((eq A a0 (AHead a1 a2)) \to (eq A a a1))))).(\lambda (a3: A).(\lambda 
(H4: (eq nat (S i) O)).(\lambda (H5: (eq A (AHead a3 a0) (AHead a1 a2))).(let 
H6 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a3 | (AHead a4 _) \Rightarrow a4])) (AHead a3 
a0) (AHead a1 a2) H5) in ((let H7 \def (f_equal A A (\lambda (e: A).(match e 
in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead _ 
a4) \Rightarrow a4])) (AHead a3 a0) (AHead a1 a2) H5) in (\lambda (_: (eq A 
a3 a1)).(let H9 \def (eq_ind A a0 (\lambda (a4: A).((eq nat i O) \to ((eq A 
a4 (AHead a1 a2)) \to (eq A a a1)))) H3 a2 H7) in (let H10 \def (eq_ind A a0 
(\lambda (a4: A).(aprem i a4 a)) H2 a2 H7) in (let H11 \def (eq_ind nat (S i) 
(\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H4) in (False_ind (eq A a 
a1) H11)))))) H6)))))))))) y0 y x H1))) H0))) H)))).
(* COMMENTS
Initial nodes: 500
END *)

theorem aprem_gen_head_S:
 \forall (a1: A).(\forall (a2: A).(\forall (x: A).(\forall (i: nat).((aprem 
(S i) (AHead a1 a2) x) \to (aprem i a2 x)))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (x: A).(\lambda (i: nat).(\lambda 
(H: (aprem (S i) (AHead a1 a2) x)).(insert_eq A (AHead a1 a2) (\lambda (a: 
A).(aprem (S i) a x)) (\lambda (_: A).(aprem i a2 x)) (\lambda (y: 
A).(\lambda (H0: (aprem (S i) y x)).(insert_eq nat (S i) (\lambda (n: 
nat).(aprem n y x)) (\lambda (_: nat).((eq A y (AHead a1 a2)) \to (aprem i a2 
x))) (\lambda (y0: nat).(\lambda (H1: (aprem y0 y x)).(aprem_ind (\lambda (n: 
nat).(\lambda (a: A).(\lambda (a0: A).((eq nat n (S i)) \to ((eq A a (AHead 
a1 a2)) \to (aprem i a2 a0)))))) (\lambda (a0: A).(\lambda (a3: A).(\lambda 
(H2: (eq nat O (S i))).(\lambda (H3: (eq A (AHead a0 a3) (AHead a1 a2))).(let 
H4 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a0 | (AHead a _) \Rightarrow a])) (AHead a0 a3) 
(AHead a1 a2) H3) in ((let H5 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead _ a) 
\Rightarrow a])) (AHead a0 a3) (AHead a1 a2) H3) in (\lambda (H6: (eq A a0 
a1)).(eq_ind_r A a1 (\lambda (a: A).(aprem i a2 a)) (let H7 \def (eq_ind nat 
O (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow True | (S _) \Rightarrow False])) I (S i) H2) in (False_ind 
(aprem i a2 a1) H7)) a0 H6))) H4)))))) (\lambda (a0: A).(\lambda (a: 
A).(\lambda (i0: nat).(\lambda (H2: (aprem i0 a0 a)).(\lambda (H3: (((eq nat 
i0 (S i)) \to ((eq A a0 (AHead a1 a2)) \to (aprem i a2 a))))).(\lambda (a3: 
A).(\lambda (H4: (eq nat (S i0) (S i))).(\lambda (H5: (eq A (AHead a3 a0) 
(AHead a1 a2))).(let H6 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead a4 _) 
\Rightarrow a4])) (AHead a3 a0) (AHead a1 a2) H5) in ((let H7 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a0 | (AHead _ a4) \Rightarrow a4])) (AHead a3 a0) (AHead a1 a2) 
H5) in (\lambda (_: (eq A a3 a1)).(let H9 \def (eq_ind A a0 (\lambda (a4: 
A).((eq nat i0 (S i)) \to ((eq A a4 (AHead a1 a2)) \to (aprem i a2 a)))) H3 
a2 H7) in (let H10 \def (eq_ind A a0 (\lambda (a4: A).(aprem i0 a4 a)) H2 a2 
H7) in (let H11 \def (f_equal nat nat (\lambda (e: nat).(match e in nat 
return (\lambda (_: nat).nat) with [O \Rightarrow i0 | (S n) \Rightarrow n])) 
(S i0) (S i) H4) in (let H12 \def (eq_ind nat i0 (\lambda (n: nat).((eq nat n 
(S i)) \to ((eq A a2 (AHead a1 a2)) \to (aprem i a2 a)))) H9 i H11) in (let 
H13 \def (eq_ind nat i0 (\lambda (n: nat).(aprem n a2 a)) H10 i H11) in 
H13))))))) H6)))))))))) y0 y x H1))) H0))) H))))).
(* COMMENTS
Initial nodes: 631
END *)

