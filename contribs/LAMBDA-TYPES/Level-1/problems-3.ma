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

(* Problematic objects for disambiguation/typechecking ********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "LambdaDelta/theory.ma".

theorem asucc_inj:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (asucc g a1) (asucc 
g a2)) \to (leq g a1 a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(A_ind (\lambda (a: A).(\forall (a2: 
A).((leq g (asucc g a) (asucc g a2)) \to (leq g a a2)))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (a2: A).(A_ind (\lambda (a: A).((leq g 
(asucc g (ASort n n0)) (asucc g a)) \to (leq g (ASort n n0) a))) (\lambda 
(n1: nat).(\lambda (n2: nat).(\lambda (H: (leq g (asucc g (ASort n n0)) 
(asucc g (ASort n1 n2)))).((match n in nat return (\lambda (n3: nat).((leq g 
(asucc g (ASort n3 n0)) (asucc g (ASort n1 n2))) \to (leq g (ASort n3 n0) 
(ASort n1 n2)))) with [O \Rightarrow (\lambda (H0: (leq g (asucc g (ASort O 
n0)) (asucc g (ASort n1 n2)))).((match n1 in nat return (\lambda (n3: 
nat).((leq g (asucc g (ASort O n0)) (asucc g (ASort n3 n2))) \to (leq g 
(ASort O n0) (ASort n3 n2)))) with [O \Rightarrow (\lambda (H1: (leq g (asucc 
g (ASort O n0)) (asucc g (ASort O n2)))).(let H2 \def (match H1 in leq return 
(\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a (ASort O 
(next g n0))) \to ((eq A a0 (ASort O (next g n2))) \to (leq g (ASort O n0) 
(ASort O n2))))))) with [(leq_sort h1 h2 n1 n3 k H0) \Rightarrow (\lambda 
(H1: (eq A (ASort h1 n1) (ASort O (next g n0)))).(\lambda (H2: (eq A (ASort 
h2 n3) (ASort O (next g n2)))).((let H3 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n 
| (AHead _ _) \Rightarrow n1])) (ASort h1 n1) (ASort O (next g n0)) H1) in 
((let H4 \def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda 
(_: A).nat) with [(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h1])) 
(ASort h1 n1) (ASort O (next g n0)) H1) in (eq_ind nat O (\lambda (n: 
nat).((eq nat n1 (next g n0)) \to ((eq A (ASort h2 n3) (ASort O (next g n2))) 
\to ((eq A (aplus g (ASort n n1) k) (aplus g (ASort h2 n3) k)) \to (leq g 
(ASort O n0) (ASort O n2)))))) (\lambda (H5: (eq nat n1 (next g n0))).(eq_ind 
nat (next g n0) (\lambda (n: nat).((eq A (ASort h2 n3) (ASort O (next g n2))) 
\to ((eq A (aplus g (ASort O n) k) (aplus g (ASort h2 n3) k)) \to (leq g 
(ASort O n0) (ASort O n2))))) (\lambda (H6: (eq A (ASort h2 n3) (ASort O 
(next g n2)))).(let H7 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n3])) (ASort h2 n3) (ASort O (next g n2)) H6) in ((let H8 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h2])) (ASort h2 n3) 
(ASort O (next g n2)) H6) in (eq_ind nat O (\lambda (n: nat).((eq nat n3 
(next g n2)) \to ((eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort n 
n3) k)) \to (leq g (ASort O n0) (ASort O n2))))) (\lambda (H9: (eq nat n3 
(next g n2))).(eq_ind nat (next g n2) (\lambda (n: nat).((eq A (aplus g 
(ASort O (next g n0)) k) (aplus g (ASort O n) k)) \to (leq g (ASort O n0) 
(ASort O n2)))) (\lambda (H10: (eq A (aplus g (ASort O (next g n0)) k) (aplus 
g (ASort O (next g n2)) k))).(let H \def (eq_ind_r A (aplus g (ASort O (next 
g n0)) k) (\lambda (a: A).(eq A a (aplus g (ASort O (next g n2)) k))) H10 
(aplus g (ASort O n0) (S k)) (aplus_sort_O_S_simpl g n0 k)) in (let H11 \def 
(eq_ind_r A (aplus g (ASort O (next g n2)) k) (\lambda (a: A).(eq A (aplus g 
(ASort O n0) (S k)) a)) H (aplus g (ASort O n2) (S k)) (aplus_sort_O_S_simpl 
g n2 k)) in (leq_sort g O O n0 n2 (S k) H11)))) n3 (sym_eq nat n3 (next g n2) 
H9))) h2 (sym_eq nat h2 O H8))) H7))) n1 (sym_eq nat n1 (next g n0) H5))) h1 
(sym_eq nat h1 O H4))) H3)) H2 H0))) | (leq_head a1 a2 H0 a3 a4 H1) 
\Rightarrow (\lambda (H2: (eq A (AHead a1 a3) (ASort O (next g 
n0)))).(\lambda (H3: (eq A (AHead a2 a4) (ASort O (next g n2)))).((let H4 
\def (eq_ind A (AHead a1 a3) (\lambda (e: A).(match e in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort O (next g n0)) H2) in (False_ind ((eq A (AHead a2 a4) (ASort 
O (next g n2))) \to ((leq g a1 a2) \to ((leq g a3 a4) \to (leq g (ASort O n0) 
(ASort O n2))))) H4)) H3 H0 H1)))]) in (H2 (refl_equal A (ASort O (next g 
n0))) (refl_equal A (ASort O (next g n2)))))) | (S n3) \Rightarrow (\lambda 
(H1: (leq g (asucc g (ASort O n0)) (asucc g (ASort (S n3) n2)))).(let H2 \def 
(match H1 in leq return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? 
a a0)).((eq A a (ASort O (next g n0))) \to ((eq A a0 (ASort n3 n2)) \to (leq 
g (ASort O n0) (ASort (S n3) n2))))))) with [(leq_sort h1 h2 n1 n3 k H0) 
\Rightarrow (\lambda (H1: (eq A (ASort h1 n1) (ASort O (next g 
n0)))).(\lambda (H2: (eq A (ASort h2 n3) (ASort n3 n2))).((let H3 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow n1])) (ASort h1 n1) 
(ASort O (next g n0)) H1) in ((let H4 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort n _) \Rightarrow n 
| (AHead _ _) \Rightarrow h1])) (ASort h1 n1) (ASort O (next g n0)) H1) in 
(eq_ind nat O (\lambda (n: nat).((eq nat n1 (next g n0)) \to ((eq A (ASort h2 
n3) (ASort n3 n2)) \to ((eq A (aplus g (ASort n n1) k) (aplus g (ASort h2 n3) 
k)) \to (leq g (ASort O n0) (ASort (S n3) n2)))))) (\lambda (H5: (eq nat n1 
(next g n0))).(eq_ind nat (next g n0) (\lambda (n: nat).((eq A (ASort h2 n3) 
(ASort n3 n2)) \to ((eq A (aplus g (ASort O n) k) (aplus g (ASort h2 n3) k)) 
\to (leq g (ASort O n0) (ASort (S n3) n2))))) (\lambda (H6: (eq A (ASort h2 
n3) (ASort n3 n2))).(let H7 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n3])) (ASort h2 n3) (ASort n3 n2) H6) in ((let H8 \def (f_equal A 
nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort n 
_) \Rightarrow n | (AHead _ _) \Rightarrow h2])) (ASort h2 n3) (ASort n3 n2) 
H6) in (eq_ind nat n3 (\lambda (n: nat).((eq nat n3 n2) \to ((eq A (aplus g 
(ASort O (next g n0)) k) (aplus g (ASort n n3) k)) \to (leq g (ASort O n0) 
(ASort (S n3) n2))))) (\lambda (H9: (eq nat n3 n2)).(eq_ind nat n2 (\lambda 
(n: nat).((eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort n3 n) k)) 
\to (leq g (ASort O n0) (ASort (S n3) n2)))) (\lambda (H10: (eq A (aplus g 
(ASort O (next g n0)) k) (aplus g (ASort n3 n2) k))).(let H \def (eq_ind_r A 
(aplus g (ASort O (next g n0)) k) (\lambda (a: A).(eq A a (aplus g (ASort n3 
n2) k))) H10 (aplus g (ASort O n0) (S k)) (aplus_sort_O_S_simpl g n0 k)) in 
(let H11 \def (eq_ind_r A (aplus g (ASort n3 n2) k) (\lambda (a: A).(eq A 
(aplus g (ASort O n0) (S k)) a)) H (aplus g (ASort (S n3) n2) (S k)) 
(aplus_sort_S_S_simpl g n2 n3 k)) in (leq_sort g O (S n3) n0 n2 (S k) H11)))) 
n3 (sym_eq nat n3 n2 H9))) h2 (sym_eq nat h2 n3 H8))) H7))) n1 (sym_eq nat n1 
(next g n0) H5))) h1 (sym_eq nat h1 O H4))) H3)) H2 H0))) | (leq_head a1 a2 
H0 a3 a4 H1) \Rightarrow (\lambda (H2: (eq A (AHead a1 a3) (ASort O (next g 
n0)))).(\lambda (H3: (eq A (AHead a2 a4) (ASort n3 n2))).((let H4 \def 
(eq_ind A (AHead a1 a3) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort O (next g n0)) H2) in (False_ind ((eq A (AHead a2 a4) (ASort 
n3 n2)) \to ((leq g a1 a2) \to ((leq g a3 a4) \to (leq g (ASort O n0) (ASort 
(S n3) n2))))) H4)) H3 H0 H1)))]) in (H2 (refl_equal A (ASort O (next g n0))) 
(refl_equal A (ASort n3 n2)))))]) H0)) | (S n3) \Rightarrow (\lambda (H0: 
(leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n1 n2)))).((match n1 in 
nat return (\lambda (n4: nat).((leq g (asucc g (ASort (S n3) n0)) (asucc g 
(ASort n4 n2))) \to (leq g (ASort (S n3) n0) (ASort n4 n2)))) with [O 
\Rightarrow (\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort 
O n2)))).(let H2 \def (match H1 in leq return (\lambda (a: A).(\lambda (a0: 
A).(\lambda (_: (leq ? a a0)).((eq A a (ASort n3 n0)) \to ((eq A a0 (ASort O 
(next g n2))) \to (leq g (ASort (S n3) n0) (ASort O n2))))))) with [(leq_sort 
h1 h2 n1 n3 k H0) \Rightarrow (\lambda (H1: (eq A (ASort h1 n1) (ASort n3 
n0))).(\lambda (H2: (eq A (ASort h2 n3) (ASort O (next g n2)))).((let H3 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow n1])) (ASort h1 n1) 
(ASort n3 n0) H1) in ((let H4 \def (f_equal A nat (\lambda (e: A).(match e in 
A return (\lambda (_: A).nat) with [(ASort n _) \Rightarrow n | (AHead _ _) 
\Rightarrow h1])) (ASort h1 n1) (ASort n3 n0) H1) in (eq_ind nat n3 (\lambda 
(n: nat).((eq nat n1 n0) \to ((eq A (ASort h2 n3) (ASort O (next g n2))) \to 
((eq A (aplus g (ASort n n1) k) (aplus g (ASort h2 n3) k)) \to (leq g (ASort 
(S n3) n0) (ASort O n2)))))) (\lambda (H5: (eq nat n1 n0)).(eq_ind nat n0 
(\lambda (n: nat).((eq A (ASort h2 n3) (ASort O (next g n2))) \to ((eq A 
(aplus g (ASort n3 n) k) (aplus g (ASort h2 n3) k)) \to (leq g (ASort (S n3) 
n0) (ASort O n2))))) (\lambda (H6: (eq A (ASort h2 n3) (ASort O (next g 
n2)))).(let H7 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n3])) (ASort h2 n3) (ASort O (next g n2)) H6) in ((let H8 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h2])) (ASort h2 n3) 
(ASort O (next g n2)) H6) in (eq_ind nat O (\lambda (n: nat).((eq nat n3 
(next g n2)) \to ((eq A (aplus g (ASort n3 n0) k) (aplus g (ASort n n3) k)) 
\to (leq g (ASort (S n3) n0) (ASort O n2))))) (\lambda (H9: (eq nat n3 (next 
g n2))).(eq_ind nat (next g n2) (\lambda (n: nat).((eq A (aplus g (ASort n3 
n0) k) (aplus g (ASort O n) k)) \to (leq g (ASort (S n3) n0) (ASort O n2)))) 
(\lambda (H10: (eq A (aplus g (ASort n3 n0) k) (aplus g (ASort O (next g n2)) 
k))).(let H \def (eq_ind_r A (aplus g (ASort n3 n0) k) (\lambda (a: A).(eq A 
a (aplus g (ASort O (next g n2)) k))) H10 (aplus g (ASort (S n3) n0) (S k)) 
(aplus_sort_S_S_simpl g n0 n3 k)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort O (next g n2)) k) (\lambda (a: A).(eq A (aplus g (ASort (S n3) n0) (S 
k)) a)) H (aplus g (ASort O n2) (S k)) (aplus_sort_O_S_simpl g n2 k)) in 
(leq_sort g (S n3) O n0 n2 (S k) H11)))) n3 (sym_eq nat n3 (next g n2) H9))) 
h2 (sym_eq nat h2 O H8))) H7))) n1 (sym_eq nat n1 n0 H5))) h1 (sym_eq nat h1 
n3 H4))) H3)) H2 H0))) | (leq_head a1 a2 H0 a3 a4 H1) \Rightarrow (\lambda 
(H2: (eq A (AHead a1 a3) (ASort n3 n0))).(\lambda (H3: (eq A (AHead a2 a4) 
(ASort O (next g n2)))).((let H4 \def (eq_ind A (AHead a1 a3) (\lambda (e: 
A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow 
False | (AHead _ _) \Rightarrow True])) I (ASort n3 n0) H2) in (False_ind 
((eq A (AHead a2 a4) (ASort O (next g n2))) \to ((leq g a1 a2) \to ((leq g a3 
a4) \to (leq g (ASort (S n3) n0) (ASort O n2))))) H4)) H3 H0 H1)))]) in (H2 
(refl_equal A (ASort n3 n0)) (refl_equal A (ASort O (next g n2)))))) | (S n4) 
\Rightarrow (\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort 
(S n4) n2)))).(let H2 \def (match H1 in leq return (\lambda (a: A).(\lambda 
(a0: A).(\lambda (_: (leq ? a a0)).((eq A a (ASort n3 n0)) \to ((eq A a0 
(ASort n4 n2)) \to (leq g (ASort (S n3) n0) (ASort (S n4) n2))))))) with 
[(leq_sort h1 h2 n3 n4 k H0) \Rightarrow (\lambda (H1: (eq A (ASort h1 n3) 
(ASort n3 n0))).(\lambda (H2: (eq A (ASort h2 n4) (ASort n4 n2))).((let H3 
\def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) 
with [(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow n3])) (ASort h1 n3) 
(ASort n3 n0) H1) in ((let H4 \def (f_equal A nat (\lambda (e: A).(match e in 
A return (\lambda (_: A).nat) with [(ASort n _) \Rightarrow n | (AHead _ _) 
\Rightarrow h1])) (ASort h1 n3) (ASort n3 n0) H1) in (eq_ind nat n3 (\lambda 
(n: nat).((eq nat n3 n0) \to ((eq A (ASort h2 n4) (ASort n4 n2)) \to ((eq A 
(aplus g (ASort n n3) k) (aplus g (ASort h2 n4) k)) \to (leq g (ASort (S n3) 
n0) (ASort (S n4) n2)))))) (\lambda (H5: (eq nat n3 n0)).(eq_ind nat n0 
(\lambda (n: nat).((eq A (ASort h2 n4) (ASort n4 n2)) \to ((eq A (aplus g 
(ASort n3 n) k) (aplus g (ASort h2 n4) k)) \to (leq g (ASort (S n3) n0) 
(ASort (S n4) n2))))) (\lambda (H6: (eq A (ASort h2 n4) (ASort n4 n2))).(let 
H7 \def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: 
A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) \Rightarrow n4])) 
(ASort h2 n4) (ASort n4 n2) H6) in ((let H8 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort n _) \Rightarrow n 
| (AHead _ _) \Rightarrow h2])) (ASort h2 n4) (ASort n4 n2) H6) in (eq_ind 
nat n4 (\lambda (n: nat).((eq nat n4 n2) \to ((eq A (aplus g (ASort n3 n0) k) 
(aplus g (ASort n n4) k)) \to (leq g (ASort (S n3) n0) (ASort (S n4) n2))))) 
(\lambda (H9: (eq nat n4 n2)).(eq_ind nat n2 (\lambda (n: nat).((eq A (aplus 
g (ASort n3 n0) k) (aplus g (ASort n4 n) k)) \to (leq g (ASort (S n3) n0) 
(ASort (S n4) n2)))) (\lambda (H10: (eq A (aplus g (ASort n3 n0) k) (aplus g 
(ASort n4 n2) k))).(let H \def (eq_ind_r A (aplus g (ASort n3 n0) k) (\lambda 
(a: A).(eq A a (aplus g (ASort n4 n2) k))) H10 (aplus g (ASort (S n3) n0) (S 
k)) (aplus_sort_S_S_simpl g n0 n3 k)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort n4 n2) k) (\lambda (a: A).(eq A (aplus g (ASort (S n3) n0) (S k)) a)) 
H (aplus g (ASort (S n4) n2) (S k)) (aplus_sort_S_S_simpl g n2 n4 k)) in 
(leq_sort g (S n3) (S n4) n0 n2 (S k) H11)))) n4 (sym_eq nat n4 n2 H9))) h2 
(sym_eq nat h2 n4 H8))) H7))) n3 (sym_eq nat n3 n0 H5))) h1 (sym_eq nat h1 n3 
H4))) H3)) H2 H0))) | (leq_head a1 a2 H0 a3 a4 H1) \Rightarrow (\lambda (H2: 
(eq A (AHead a1 a3) (ASort n3 n0))).(\lambda (H3: (eq A (AHead a2 a4) (ASort 
n4 n2))).((let H4 \def (eq_ind A (AHead a1 a3) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort n3 n0) H2) in (False_ind ((eq A (AHead a2 a4) 
(ASort n4 n2)) \to ((leq g a1 a2) \to ((leq g a3 a4) \to (leq g (ASort (S n3) 
n0) (ASort (S n4) n2))))) H4)) H3 H0 H1)))]) in (H2 (refl_equal A (ASort n3 
n0)) (refl_equal A (ASort n4 n2)))))]) H0))]) H)))) (\lambda (a: A).(\lambda 
(H: (((leq g (asucc g (ASort n n0)) (asucc g a)) \to (leq g (ASort n n0) 
a)))).(\lambda (a0: A).(\lambda (H0: (((leq g (asucc g (ASort n n0)) (asucc g 
a0)) \to (leq g (ASort n n0) a0)))).(\lambda (H1: (leq g (asucc g (ASort n 
n0)) (asucc g (AHead a a0)))).((match n in nat return (\lambda (n1: 
nat).((((leq g (asucc g (ASort n1 n0)) (asucc g a)) \to (leq g (ASort n1 n0) 
a))) \to ((((leq g (asucc g (ASort n1 n0)) (asucc g a0)) \to (leq g (ASort n1 
n0) a0))) \to ((leq g (asucc g (ASort n1 n0)) (asucc g (AHead a a0))) \to 
(leq g (ASort n1 n0) (AHead a a0)))))) with [O \Rightarrow (\lambda (_: 
(((leq g (asucc g (ASort O n0)) (asucc g a)) \to (leq g (ASort O n0) 
a)))).(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g a0)) \to (leq g 
(ASort O n0) a0)))).(\lambda (H4: (leq g (asucc g (ASort O n0)) (asucc g 
(AHead a a0)))).(let H5 \def (match H4 in leq return (\lambda (a1: 
A).(\lambda (a2: A).(\lambda (_: (leq ? a1 a2)).((eq A a1 (ASort O (next g 
n0))) \to ((eq A a2 (AHead a (asucc g a0))) \to (leq g (ASort O n0) (AHead a 
a0))))))) with [(leq_sort h1 h2 n1 n2 k H2) \Rightarrow (\lambda (H3: (eq A 
(ASort h1 n1) (ASort O (next g n0)))).(\lambda (H4: (eq A (ASort h2 n2) 
(AHead a (asucc g a0)))).((let H5 \def (f_equal A nat (\lambda (e: A).(match 
e in A return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ 
_) \Rightarrow n1])) (ASort h1 n1) (ASort O (next g n0)) H3) in ((let H6 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow h1])) (ASort h1 n1) 
(ASort O (next g n0)) H3) in (eq_ind nat O (\lambda (n: nat).((eq nat n1 
(next g n0)) \to ((eq A (ASort h2 n2) (AHead a (asucc g a0))) \to ((eq A 
(aplus g (ASort n n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort O n0) 
(AHead a a0)))))) (\lambda (H7: (eq nat n1 (next g n0))).(eq_ind nat (next g 
n0) (\lambda (n: nat).((eq A (ASort h2 n2) (AHead a (asucc g a0))) \to ((eq A 
(aplus g (ASort O n) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort O n0) 
(AHead a a0))))) (\lambda (H8: (eq A (ASort h2 n2) (AHead a (asucc g 
a0)))).(let H9 \def (eq_ind A (ASort h2 n2) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a (asucc g a0)) H8) in (False_ind ((eq A (aplus 
g (ASort O (next g n0)) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort O n0) 
(AHead a a0))) H9))) n1 (sym_eq nat n1 (next g n0) H7))) h1 (sym_eq nat h1 O 
H6))) H5)) H4 H2))) | (leq_head a1 a2 H2 a3 a4 H3) \Rightarrow (\lambda (H4: 
(eq A (AHead a1 a3) (ASort O (next g n0)))).(\lambda (H5: (eq A (AHead a2 a4) 
(AHead a (asucc g a0)))).((let H6 \def (eq_ind A (AHead a1 a3) (\lambda (e: 
A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow 
False | (AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) H4) in 
(False_ind ((eq A (AHead a2 a4) (AHead a (asucc g a0))) \to ((leq g a1 a2) 
\to ((leq g a3 a4) \to (leq g (ASort O n0) (AHead a a0))))) H6)) H5 H2 
H3)))]) in (H5 (refl_equal A (ASort O (next g n0))) (refl_equal A (AHead a 
(asucc g a0)))))))) | (S n1) \Rightarrow (\lambda (_: (((leq g (asucc g 
(ASort (S n1) n0)) (asucc g a)) \to (leq g (ASort (S n1) n0) a)))).(\lambda 
(_: (((leq g (asucc g (ASort (S n1) n0)) (asucc g a0)) \to (leq g (ASort (S 
n1) n0) a0)))).(\lambda (H4: (leq g (asucc g (ASort (S n1) n0)) (asucc g 
(AHead a a0)))).(let H5 \def (match H4 in leq return (\lambda (a1: 
A).(\lambda (a2: A).(\lambda (_: (leq ? a1 a2)).((eq A a1 (ASort n1 n0)) \to 
((eq A a2 (AHead a (asucc g a0))) \to (leq g (ASort (S n1) n0) (AHead a 
a0))))))) with [(leq_sort h1 h2 n1 n2 k H2) \Rightarrow (\lambda (H3: (eq A 
(ASort h1 n1) (ASort n1 n0))).(\lambda (H4: (eq A (ASort h2 n2) (AHead a 
(asucc g a0)))).((let H5 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n1])) (ASort h1 n1) (ASort n1 n0) H3) in ((let H6 \def (f_equal A 
nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort n 
_) \Rightarrow n | (AHead _ _) \Rightarrow h1])) (ASort h1 n1) (ASort n1 n0) 
H3) in (eq_ind nat n1 (\lambda (n: nat).((eq nat n1 n0) \to ((eq A (ASort h2 
n2) (AHead a (asucc g a0))) \to ((eq A (aplus g (ASort n n1) k) (aplus g 
(ASort h2 n2) k)) \to (leq g (ASort (S n1) n0) (AHead a a0)))))) (\lambda 
(H7: (eq nat n1 n0)).(eq_ind nat n0 (\lambda (n: nat).((eq A (ASort h2 n2) 
(AHead a (asucc g a0))) \to ((eq A (aplus g (ASort n1 n) k) (aplus g (ASort 
h2 n2) k)) \to (leq g (ASort (S n1) n0) (AHead a a0))))) (\lambda (H8: (eq A 
(ASort h2 n2) (AHead a (asucc g a0)))).(let H9 \def (eq_ind A (ASort h2 n2) 
(\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead a (asucc g a0)) 
H8) in (False_ind ((eq A (aplus g (ASort n1 n0) k) (aplus g (ASort h2 n2) k)) 
\to (leq g (ASort (S n1) n0) (AHead a a0))) H9))) n1 (sym_eq nat n1 n0 H7))) 
h1 (sym_eq nat h1 n1 H6))) H5)) H4 H2))) | (leq_head a1 a2 H2 a3 a4 H3) 
\Rightarrow (\lambda (H4: (eq A (AHead a1 a3) (ASort n1 n0))).(\lambda (H5: 
(eq A (AHead a2 a4) (AHead a (asucc g a0)))).((let H6 \def (eq_ind A (AHead 
a1 a3) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort n1 
n0) H4) in (False_ind ((eq A (AHead a2 a4) (AHead a (asucc g a0))) \to ((leq 
g a1 a2) \to ((leq g a3 a4) \to (leq g (ASort (S n1) n0) (AHead a a0))))) 
H6)) H5 H2 H3)))]) in (H5 (refl_equal A (ASort n1 n0)) (refl_equal A (AHead a 
(asucc g a0))))))))]) H H0 H1)))))) a2)))) (\lambda (a: A).(\lambda (_: 
((\forall (a2: A).((leq g (asucc g a) (asucc g a2)) \to (leq g a 
a2))))).(\lambda (a0: A).(\lambda (H0: ((\forall (a2: A).((leq g (asucc g a0) 
(asucc g a2)) \to (leq g a0 a2))))).(\lambda (a2: A).(A_ind (\lambda (a3: 
A).((leq g (asucc g (AHead a a0)) (asucc g a3)) \to (leq g (AHead a a0) a3))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (H1: (leq g (asucc g (AHead a 
a0)) (asucc g (ASort n n0)))).((match n in nat return (\lambda (n1: 
nat).((leq g (asucc g (AHead a a0)) (asucc g (ASort n1 n0))) \to (leq g 
(AHead a a0) (ASort n1 n0)))) with [O \Rightarrow (\lambda (H2: (leq g (asucc 
g (AHead a a0)) (asucc g (ASort O n0)))).(let H3 \def (match H2 in leq return 
(\lambda (a1: A).(\lambda (a2: A).(\lambda (_: (leq ? a1 a2)).((eq A a1 
(AHead a (asucc g a0))) \to ((eq A a2 (ASort O (next g n0))) \to (leq g 
(AHead a a0) (ASort O n0))))))) with [(leq_sort h1 h2 n1 n2 k H2) \Rightarrow 
(\lambda (H3: (eq A (ASort h1 n1) (AHead a (asucc g a0)))).(\lambda (H4: (eq 
A (ASort h2 n2) (ASort O (next g n0)))).((let H5 \def (eq_ind A (ASort h1 n1) 
(\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead a (asucc g a0)) 
H3) in (False_ind ((eq A (ASort h2 n2) (ASort O (next g n0))) \to ((eq A 
(aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (AHead a a0) 
(ASort O n0)))) H5)) H4 H2))) | (leq_head a1 a2 H2 a3 a4 H3) \Rightarrow 
(\lambda (H4: (eq A (AHead a1 a3) (AHead a (asucc g a0)))).(\lambda (H5: (eq 
A (AHead a2 a4) (ASort O (next g n0)))).((let H6 \def (f_equal A A (\lambda 
(e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow 
a3 | (AHead _ a) \Rightarrow a])) (AHead a1 a3) (AHead a (asucc g a0)) H4) in 
((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: 
A).A) with [(ASort _ _) \Rightarrow a1 | (AHead a _) \Rightarrow a])) (AHead 
a1 a3) (AHead a (asucc g a0)) H4) in (eq_ind A a (\lambda (a5: A).((eq A a3 
(asucc g a0)) \to ((eq A (AHead a2 a4) (ASort O (next g n0))) \to ((leq g a5 
a2) \to ((leq g a3 a4) \to (leq g (AHead a a0) (ASort O n0))))))) (\lambda 
(H8: (eq A a3 (asucc g a0))).(eq_ind A (asucc g a0) (\lambda (a5: A).((eq A 
(AHead a2 a4) (ASort O (next g n0))) \to ((leq g a a2) \to ((leq g a5 a4) \to 
(leq g (AHead a a0) (ASort O n0)))))) (\lambda (H9: (eq A (AHead a2 a4) 
(ASort O (next g n0)))).(let H10 \def (eq_ind A (AHead a2 a4) (\lambda (e: 
A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow 
False | (AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) H9) in 
(False_ind ((leq g a a2) \to ((leq g (asucc g a0) a4) \to (leq g (AHead a a0) 
(ASort O n0)))) H10))) a3 (sym_eq A a3 (asucc g a0) H8))) a1 (sym_eq A a1 a 
H7))) H6)) H5 H2 H3)))]) in (H3 (refl_equal A (AHead a (asucc g a0))) 
(refl_equal A (ASort O (next g n0)))))) | (S n1) \Rightarrow (\lambda (H2: 
(leq g (asucc g (AHead a a0)) (asucc g (ASort (S n1) n0)))).(let H3 \def 
(match H2 in leq return (\lambda (a1: A).(\lambda (a2: A).(\lambda (_: (leq ? 
a1 a2)).((eq A a1 (AHead a (asucc g a0))) \to ((eq A a2 (ASort n1 n0)) \to 
(leq g (AHead a a0) (ASort (S n1) n0))))))) with [(leq_sort h1 h2 n1 n2 k H2) 
\Rightarrow (\lambda (H3: (eq A (ASort h1 n1) (AHead a (asucc g 
a0)))).(\lambda (H4: (eq A (ASort h2 n2) (ASort n1 n0))).((let H5 \def 
(eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead a (asucc g a0)) H3) in (False_ind ((eq A (ASort h2 n2) 
(ASort n1 n0)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k)) \to (leq g (AHead a a0) (ASort (S n1) n0)))) H5)) H4 H2))) | (leq_head a1 
a2 H2 a3 a4 H3) \Rightarrow (\lambda (H4: (eq A (AHead a1 a3) (AHead a (asucc 
g a0)))).(\lambda (H5: (eq A (AHead a2 a4) (ASort n1 n0))).((let H6 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a3 | (AHead _ a) \Rightarrow a])) (AHead a1 a3) 
(AHead a (asucc g a0)) H4) in ((let H7 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a1 | 
(AHead a _) \Rightarrow a])) (AHead a1 a3) (AHead a (asucc g a0)) H4) in 
(eq_ind A a (\lambda (a5: A).((eq A a3 (asucc g a0)) \to ((eq A (AHead a2 a4) 
(ASort n1 n0)) \to ((leq g a5 a2) \to ((leq g a3 a4) \to (leq g (AHead a a0) 
(ASort (S n1) n0))))))) (\lambda (H8: (eq A a3 (asucc g a0))).(eq_ind A 
(asucc g a0) (\lambda (a5: A).((eq A (AHead a2 a4) (ASort n1 n0)) \to ((leq g 
a a2) \to ((leq g a5 a4) \to (leq g (AHead a a0) (ASort (S n1) n0)))))) 
(\lambda (H9: (eq A (AHead a2 a4) (ASort n1 n0))).(let H10 \def (eq_ind A 
(AHead a2 a4) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort n1 
n0) H9) in (False_ind ((leq g a a2) \to ((leq g (asucc g a0) a4) \to (leq g 
(AHead a a0) (ASort (S n1) n0)))) H10))) a3 (sym_eq A a3 (asucc g a0) H8))) 
a1 (sym_eq A a1 a H7))) H6)) H5 H2 H3)))]) in (H3 (refl_equal A (AHead a 
(asucc g a0))) (refl_equal A (ASort n1 n0)))))]) H1)))) (\lambda (a3: 
A).(\lambda (_: (((leq g (asucc g (AHead a a0)) (asucc g a3)) \to (leq g 
(AHead a a0) a3)))).(\lambda (a4: A).(\lambda (_: (((leq g (asucc g (AHead a 
a0)) (asucc g a4)) \to (leq g (AHead a a0) a4)))).(\lambda (H3: (leq g (asucc 
g (AHead a a0)) (asucc g (AHead a3 a4)))).(let H4 \def (match H3 in leq 
return (\lambda (a1: A).(\lambda (a2: A).(\lambda (_: (leq ? a1 a2)).((eq A 
a1 (AHead a (asucc g a0))) \to ((eq A a2 (AHead a3 (asucc g a4))) \to (leq g 
(AHead a a0) (AHead a3 a4))))))) with [(leq_sort h1 h2 n1 n2 k H4) 
\Rightarrow (\lambda (H5: (eq A (ASort h1 n1) (AHead a (asucc g 
a0)))).(\lambda (H6: (eq A (ASort h2 n2) (AHead a3 (asucc g a4)))).((let H7 
\def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead a (asucc g a0)) H5) in (False_ind ((eq A (ASort h2 n2) 
(AHead a3 (asucc g a4))) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort 
h2 n2) k)) \to (leq g (AHead a a0) (AHead a3 a4)))) H7)) H6 H4))) | (leq_head 
a3 a4 H4 a5 a6 H5) \Rightarrow (\lambda (H6: (eq A (AHead a3 a5) (AHead a 
(asucc g a0)))).(\lambda (H7: (eq A (AHead a4 a6) (AHead a3 (asucc g 
a4)))).((let H8 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a5 | (AHead _ a) \Rightarrow 
a])) (AHead a3 a5) (AHead a (asucc g a0)) H6) in ((let H9 \def (f_equal A A 
(\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a3 | (AHead a _) \Rightarrow a])) (AHead a3 a5) (AHead a (asucc g 
a0)) H6) in (eq_ind A a (\lambda (a1: A).((eq A a5 (asucc g a0)) \to ((eq A 
(AHead a4 a6) (AHead a3 (asucc g a4))) \to ((leq g a1 a4) \to ((leq g a5 a6) 
\to (leq g (AHead a a0) (AHead a3 a4))))))) (\lambda (H10: (eq A a5 (asucc g 
a0))).(eq_ind A (asucc g a0) (\lambda (a1: A).((eq A (AHead a4 a6) (AHead a3 
(asucc g a4))) \to ((leq g a a4) \to ((leq g a1 a6) \to (leq g (AHead a a0) 
(AHead a3 a4)))))) (\lambda (H11: (eq A (AHead a4 a6) (AHead a3 (asucc g 
a4)))).(let H12 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a6 | (AHead _ a) \Rightarrow 
a])) (AHead a4 a6) (AHead a3 (asucc g a4)) H11) in ((let H13 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a4 | (AHead a _) \Rightarrow a])) (AHead a4 a6) (AHead a3 (asucc 
g a4)) H11) in (eq_ind A a3 (\lambda (a1: A).((eq A a6 (asucc g a4)) \to 
((leq g a a1) \to ((leq g (asucc g a0) a6) \to (leq g (AHead a a0) (AHead a3 
a4)))))) (\lambda (H14: (eq A a6 (asucc g a4))).(eq_ind A (asucc g a4) 
(\lambda (a1: A).((leq g a a3) \to ((leq g (asucc g a0) a1) \to (leq g (AHead 
a a0) (AHead a3 a4))))) (\lambda (H15: (leq g a a3)).(\lambda (H16: (leq g 
(asucc g a0) (asucc g a4))).(leq_head g a a3 H15 a0 a4 (H0 a4 H16)))) a6 
(sym_eq A a6 (asucc g a4) H14))) a4 (sym_eq A a4 a3 H13))) H12))) a5 (sym_eq 
A a5 (asucc g a0) H10))) a3 (sym_eq A a3 a H9))) H8)) H7 H4 H5)))]) in (H4 
(refl_equal A (AHead a (asucc g a0))) (refl_equal A (AHead a3 (asucc g 
a4)))))))))) a2)))))) a1)).

