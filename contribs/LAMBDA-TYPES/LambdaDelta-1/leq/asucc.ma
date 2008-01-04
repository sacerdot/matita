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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/leq/asucc".

include "leq/props.ma".

include "aplus/props.ma".

theorem asucc_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
(asucc g a1) (asucc g a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(leq g (asucc g a) (asucc g 
a0)))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: 
nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k))).(nat_ind (\lambda (n: nat).((eq A (aplus g (ASort n n1) k) 
(aplus g (ASort h2 n2) k)) \to (leq g (match n with [O \Rightarrow (ASort O 
(next g n1)) | (S h) \Rightarrow (ASort h n1)]) (match h2 with [O \Rightarrow 
(ASort O (next g n2)) | (S h) \Rightarrow (ASort h n2)])))) (\lambda (H1: (eq 
A (aplus g (ASort O n1) k) (aplus g (ASort h2 n2) k))).(nat_ind (\lambda (n: 
nat).((eq A (aplus g (ASort O n1) k) (aplus g (ASort n n2) k)) \to (leq g 
(ASort O (next g n1)) (match n with [O \Rightarrow (ASort O (next g n2)) | (S 
h) \Rightarrow (ASort h n2)])))) (\lambda (H2: (eq A (aplus g (ASort O n1) k) 
(aplus g (ASort O n2) k))).(leq_sort g O O (next g n1) (next g n2) k (eq_ind 
A (aplus g (ASort O n1) (S k)) (\lambda (a: A).(eq A a (aplus g (ASort O 
(next g n2)) k))) (eq_ind A (aplus g (ASort O n2) (S k)) (\lambda (a: A).(eq 
A (aplus g (ASort O n1) (S k)) a)) (eq_ind_r A (aplus g (ASort O n2) k) 
(\lambda (a: A).(eq A (asucc g a) (asucc g (aplus g (ASort O n2) k)))) 
(refl_equal A (asucc g (aplus g (ASort O n2) k))) (aplus g (ASort O n1) k) 
H2) (aplus g (ASort O (next g n2)) k) (aplus_sort_O_S_simpl g n2 k)) (aplus g 
(ASort O (next g n1)) k) (aplus_sort_O_S_simpl g n1 k)))) (\lambda (h3: 
nat).(\lambda (_: (((eq A (aplus g (ASort O n1) k) (aplus g (ASort h3 n2) k)) 
\to (leq g (ASort O (next g n1)) (match h3 with [O \Rightarrow (ASort O (next 
g n2)) | (S h) \Rightarrow (ASort h n2)]))))).(\lambda (H2: (eq A (aplus g 
(ASort O n1) k) (aplus g (ASort (S h3) n2) k))).(leq_sort g O h3 (next g n1) 
n2 k (eq_ind A (aplus g (ASort O n1) (S k)) (\lambda (a: A).(eq A a (aplus g 
(ASort h3 n2) k))) (eq_ind A (aplus g (ASort (S h3) n2) (S k)) (\lambda (a: 
A).(eq A (aplus g (ASort O n1) (S k)) a)) (eq_ind_r A (aplus g (ASort (S h3) 
n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc g (aplus g (ASort (S h3) n2) 
k)))) (refl_equal A (asucc g (aplus g (ASort (S h3) n2) k))) (aplus g (ASort 
O n1) k) H2) (aplus g (ASort h3 n2) k) (aplus_sort_S_S_simpl g n2 h3 k)) 
(aplus g (ASort O (next g n1)) k) (aplus_sort_O_S_simpl g n1 k)))))) h2 H1)) 
(\lambda (h3: nat).(\lambda (IHh1: (((eq A (aplus g (ASort h3 n1) k) (aplus g 
(ASort h2 n2) k)) \to (leq g (match h3 with [O \Rightarrow (ASort O (next g 
n1)) | (S h) \Rightarrow (ASort h n1)]) (match h2 with [O \Rightarrow (ASort 
O (next g n2)) | (S h) \Rightarrow (ASort h n2)]))))).(\lambda (H1: (eq A 
(aplus g (ASort (S h3) n1) k) (aplus g (ASort h2 n2) k))).(nat_ind (\lambda 
(n: nat).((eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort n n2) k)) \to 
((((eq A (aplus g (ASort h3 n1) k) (aplus g (ASort n n2) k)) \to (leq g 
(match h3 with [O \Rightarrow (ASort O (next g n1)) | (S h) \Rightarrow 
(ASort h n1)]) (match n with [O \Rightarrow (ASort O (next g n2)) | (S h) 
\Rightarrow (ASort h n2)])))) \to (leq g (ASort h3 n1) (match n with [O 
\Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow (ASort h n2)]))))) 
(\lambda (H2: (eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort O n2) 
k))).(\lambda (_: (((eq A (aplus g (ASort h3 n1) k) (aplus g (ASort O n2) k)) 
\to (leq g (match h3 with [O \Rightarrow (ASort O (next g n1)) | (S h) 
\Rightarrow (ASort h n1)]) (ASort O (next g n2)))))).(leq_sort g h3 O n1 
(next g n2) k (eq_ind A (aplus g (ASort O n2) (S k)) (\lambda (a: A).(eq A 
(aplus g (ASort h3 n1) k) a)) (eq_ind A (aplus g (ASort (S h3) n1) (S k)) 
(\lambda (a: A).(eq A a (aplus g (ASort O n2) (S k)))) (eq_ind_r A (aplus g 
(ASort O n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc g (aplus g (ASort O 
n2) k)))) (refl_equal A (asucc g (aplus g (ASort O n2) k))) (aplus g (ASort 
(S h3) n1) k) H2) (aplus g (ASort h3 n1) k) (aplus_sort_S_S_simpl g n1 h3 k)) 
(aplus g (ASort O (next g n2)) k) (aplus_sort_O_S_simpl g n2 k))))) (\lambda 
(h4: nat).(\lambda (_: (((eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort 
h4 n2) k)) \to ((((eq A (aplus g (ASort h3 n1) k) (aplus g (ASort h4 n2) k)) 
\to (leq g (match h3 with [O \Rightarrow (ASort O (next g n1)) | (S h) 
\Rightarrow (ASort h n1)]) (match h4 with [O \Rightarrow (ASort O (next g 
n2)) | (S h) \Rightarrow (ASort h n2)])))) \to (leq g (ASort h3 n1) (match h4 
with [O \Rightarrow (ASort O (next g n2)) | (S h) \Rightarrow (ASort h 
n2)])))))).(\lambda (H2: (eq A (aplus g (ASort (S h3) n1) k) (aplus g (ASort 
(S h4) n2) k))).(\lambda (_: (((eq A (aplus g (ASort h3 n1) k) (aplus g 
(ASort (S h4) n2) k)) \to (leq g (match h3 with [O \Rightarrow (ASort O (next 
g n1)) | (S h) \Rightarrow (ASort h n1)]) (ASort h4 n2))))).(leq_sort g h3 h4 
n1 n2 k (eq_ind A (aplus g (ASort (S h3) n1) (S k)) (\lambda (a: A).(eq A a 
(aplus g (ASort h4 n2) k))) (eq_ind A (aplus g (ASort (S h4) n2) (S k)) 
(\lambda (a: A).(eq A (aplus g (ASort (S h3) n1) (S k)) a)) (eq_ind_r A 
(aplus g (ASort (S h4) n2) k) (\lambda (a: A).(eq A (asucc g a) (asucc g 
(aplus g (ASort (S h4) n2) k)))) (refl_equal A (asucc g (aplus g (ASort (S 
h4) n2) k))) (aplus g (ASort (S h3) n1) k) H2) (aplus g (ASort h4 n2) k) 
(aplus_sort_S_S_simpl g n2 h4 k)) (aplus g (ASort h3 n1) k) 
(aplus_sort_S_S_simpl g n1 h3 k))))))) h2 H1 IHh1)))) h1 H0))))))) (\lambda 
(a3: A).(\lambda (a4: A).(\lambda (H0: (leq g a3 a4)).(\lambda (_: (leq g 
(asucc g a3) (asucc g a4))).(\lambda (a5: A).(\lambda (a6: A).(\lambda (_: 
(leq g a5 a6)).(\lambda (H3: (leq g (asucc g a5) (asucc g a6))).(leq_head g 
a3 a4 H0 (asucc g a5) (asucc g a6) H3))))))))) a1 a2 H)))).

theorem asucc_inj:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (asucc g a1) (asucc 
g a2)) \to (leq g a1 a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(A_ind (\lambda (a: A).(\forall (a2: 
A).((leq g (asucc g a) (asucc g a2)) \to (leq g a a2)))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (a2: A).(A_ind (\lambda (a: A).((leq g 
(asucc g (ASort n n0)) (asucc g a)) \to (leq g (ASort n n0) a))) (\lambda 
(n1: nat).(\lambda (n2: nat).(\lambda (H: (leq g (asucc g (ASort n n0)) 
(asucc g (ASort n1 n2)))).(nat_ind (\lambda (n3: nat).((leq g (asucc g (ASort 
n3 n0)) (asucc g (ASort n1 n2))) \to (leq g (ASort n3 n0) (ASort n1 n2)))) 
(\lambda (H0: (leq g (asucc g (ASort O n0)) (asucc g (ASort n1 
n2)))).(nat_ind (\lambda (n3: nat).((leq g (asucc g (ASort O n0)) (asucc g 
(ASort n3 n2))) \to (leq g (ASort O n0) (ASort n3 n2)))) (\lambda (H1: (leq g 
(asucc g (ASort O n0)) (asucc g (ASort O n2)))).(let H2 \def (match H1 in leq 
return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a 
(ASort O (next g n0))) \to ((eq A a0 (ASort O (next g n2))) \to (leq g (ASort 
O n0) (ASort O n2))))))) with [(leq_sort h1 h2 n3 n4 k H2) \Rightarrow 
(\lambda (H3: (eq A (ASort h1 n3) (ASort O (next g n0)))).(\lambda (H4: (eq A 
(ASort h2 n4) (ASort O (next g n2)))).((let H5 \def (f_equal A nat (\lambda 
(e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n5) 
\Rightarrow n5 | (AHead _ _) \Rightarrow n3])) (ASort h1 n3) (ASort O (next g 
n0)) H3) in ((let H6 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort n5 _) \Rightarrow n5 | (AHead _ _) 
\Rightarrow h1])) (ASort h1 n3) (ASort O (next g n0)) H3) in (eq_ind nat O 
(\lambda (n5: nat).((eq nat n3 (next g n0)) \to ((eq A (ASort h2 n4) (ASort O 
(next g n2))) \to ((eq A (aplus g (ASort n5 n3) k) (aplus g (ASort h2 n4) k)) 
\to (leq g (ASort O n0) (ASort O n2)))))) (\lambda (H7: (eq nat n3 (next g 
n0))).(eq_ind nat (next g n0) (\lambda (n5: nat).((eq A (ASort h2 n4) (ASort 
O (next g n2))) \to ((eq A (aplus g (ASort O n5) k) (aplus g (ASort h2 n4) 
k)) \to (leq g (ASort O n0) (ASort O n2))))) (\lambda (H8: (eq A (ASort h2 
n4) (ASort O (next g n2)))).(let H9 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n5) \Rightarrow 
n5 | (AHead _ _) \Rightarrow n4])) (ASort h2 n4) (ASort O (next g n2)) H8) in 
((let H10 \def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda 
(_: A).nat) with [(ASort n5 _) \Rightarrow n5 | (AHead _ _) \Rightarrow h2])) 
(ASort h2 n4) (ASort O (next g n2)) H8) in (eq_ind nat O (\lambda (n5: 
nat).((eq nat n4 (next g n2)) \to ((eq A (aplus g (ASort O (next g n0)) k) 
(aplus g (ASort n5 n4) k)) \to (leq g (ASort O n0) (ASort O n2))))) (\lambda 
(H11: (eq nat n4 (next g n2))).(eq_ind nat (next g n2) (\lambda (n5: 
nat).((eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort O n5) k)) \to 
(leq g (ASort O n0) (ASort O n2)))) (\lambda (H12: (eq A (aplus g (ASort O 
(next g n0)) k) (aplus g (ASort O (next g n2)) k))).(let H13 \def (eq_ind_r A 
(aplus g (ASort O (next g n0)) k) (\lambda (a: A).(eq A a (aplus g (ASort O 
(next g n2)) k))) H12 (aplus g (ASort O n0) (S k)) (aplus_sort_O_S_simpl g n0 
k)) in (let H14 \def (eq_ind_r A (aplus g (ASort O (next g n2)) k) (\lambda 
(a: A).(eq A (aplus g (ASort O n0) (S k)) a)) H13 (aplus g (ASort O n2) (S 
k)) (aplus_sort_O_S_simpl g n2 k)) in (leq_sort g O O n0 n2 (S k) H14)))) n4 
(sym_eq nat n4 (next g n2) H11))) h2 (sym_eq nat h2 O H10))) H9))) n3 (sym_eq 
nat n3 (next g n0) H7))) h1 (sym_eq nat h1 O H6))) H5)) H4 H2))) | (leq_head 
a0 a3 H2 a4 a5 H3) \Rightarrow (\lambda (H4: (eq A (AHead a0 a4) (ASort O 
(next g n0)))).(\lambda (H5: (eq A (AHead a3 a5) (ASort O (next g 
n2)))).((let H6 \def (eq_ind A (AHead a0 a4) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort O (next g n0)) H4) in (False_ind ((eq A 
(AHead a3 a5) (ASort O (next g n2))) \to ((leq g a0 a3) \to ((leq g a4 a5) 
\to (leq g (ASort O n0) (ASort O n2))))) H6)) H5 H2 H3)))]) in (H2 
(refl_equal A (ASort O (next g n0))) (refl_equal A (ASort O (next g n2)))))) 
(\lambda (n3: nat).(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g 
(ASort n3 n2))) \to (leq g (ASort O n0) (ASort n3 n2))))).(\lambda (H1: (leq 
g (asucc g (ASort O n0)) (asucc g (ASort (S n3) n2)))).(let H2 \def (match H1 
in leq return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a 
a0)).((eq A a (ASort O (next g n0))) \to ((eq A a0 (ASort n3 n2)) \to (leq g 
(ASort O n0) (ASort (S n3) n2))))))) with [(leq_sort h1 h2 n4 n5 k H2) 
\Rightarrow (\lambda (H3: (eq A (ASort h1 n4) (ASort O (next g 
n0)))).(\lambda (H4: (eq A (ASort h2 n5) (ASort n3 n2))).((let H5 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n6) \Rightarrow n6 | (AHead _ _) \Rightarrow n4])) (ASort h1 n4) 
(ASort O (next g n0)) H3) in ((let H6 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort n6 _) \Rightarrow 
n6 | (AHead _ _) \Rightarrow h1])) (ASort h1 n4) (ASort O (next g n0)) H3) in 
(eq_ind nat O (\lambda (n6: nat).((eq nat n4 (next g n0)) \to ((eq A (ASort 
h2 n5) (ASort n3 n2)) \to ((eq A (aplus g (ASort n6 n4) k) (aplus g (ASort h2 
n5) k)) \to (leq g (ASort O n0) (ASort (S n3) n2)))))) (\lambda (H7: (eq nat 
n4 (next g n0))).(eq_ind nat (next g n0) (\lambda (n6: nat).((eq A (ASort h2 
n5) (ASort n3 n2)) \to ((eq A (aplus g (ASort O n6) k) (aplus g (ASort h2 n5) 
k)) \to (leq g (ASort O n0) (ASort (S n3) n2))))) (\lambda (H8: (eq A (ASort 
h2 n5) (ASort n3 n2))).(let H9 \def (f_equal A nat (\lambda (e: A).(match e 
in A return (\lambda (_: A).nat) with [(ASort _ n6) \Rightarrow n6 | (AHead _ 
_) \Rightarrow n5])) (ASort h2 n5) (ASort n3 n2) H8) in ((let H10 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n6 _) \Rightarrow n6 | (AHead _ _) \Rightarrow h2])) (ASort h2 n5) 
(ASort n3 n2) H8) in (eq_ind nat n3 (\lambda (n6: nat).((eq nat n5 n2) \to 
((eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort n6 n5) k)) \to (leq 
g (ASort O n0) (ASort (S n3) n2))))) (\lambda (H11: (eq nat n5 n2)).(eq_ind 
nat n2 (\lambda (n6: nat).((eq A (aplus g (ASort O (next g n0)) k) (aplus g 
(ASort n3 n6) k)) \to (leq g (ASort O n0) (ASort (S n3) n2)))) (\lambda (H12: 
(eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort n3 n2) k))).(let H13 
\def (eq_ind_r A (aplus g (ASort O (next g n0)) k) (\lambda (a: A).(eq A a 
(aplus g (ASort n3 n2) k))) H12 (aplus g (ASort O n0) (S k)) 
(aplus_sort_O_S_simpl g n0 k)) in (let H14 \def (eq_ind_r A (aplus g (ASort 
n3 n2) k) (\lambda (a: A).(eq A (aplus g (ASort O n0) (S k)) a)) H13 (aplus g 
(ASort (S n3) n2) (S k)) (aplus_sort_S_S_simpl g n2 n3 k)) in (leq_sort g O 
(S n3) n0 n2 (S k) H14)))) n5 (sym_eq nat n5 n2 H11))) h2 (sym_eq nat h2 n3 
H10))) H9))) n4 (sym_eq nat n4 (next g n0) H7))) h1 (sym_eq nat h1 O H6))) 
H5)) H4 H2))) | (leq_head a0 a3 H2 a4 a5 H3) \Rightarrow (\lambda (H4: (eq A 
(AHead a0 a4) (ASort O (next g n0)))).(\lambda (H5: (eq A (AHead a3 a5) 
(ASort n3 n2))).((let H6 \def (eq_ind A (AHead a0 a4) (\lambda (e: A).(match 
e in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) H4) in (False_ind 
((eq A (AHead a3 a5) (ASort n3 n2)) \to ((leq g a0 a3) \to ((leq g a4 a5) \to 
(leq g (ASort O n0) (ASort (S n3) n2))))) H6)) H5 H2 H3)))]) in (H2 
(refl_equal A (ASort O (next g n0))) (refl_equal A (ASort n3 n2))))))) n1 
H0)) (\lambda (n3: nat).(\lambda (IHn: (((leq g (asucc g (ASort n3 n0)) 
(asucc g (ASort n1 n2))) \to (leq g (ASort n3 n0) (ASort n1 n2))))).(\lambda 
(H0: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n1 n2)))).(nat_ind 
(\lambda (n4: nat).((leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n4 
n2))) \to ((((leq g (asucc g (ASort n3 n0)) (asucc g (ASort n4 n2))) \to (leq 
g (ASort n3 n0) (ASort n4 n2)))) \to (leq g (ASort (S n3) n0) (ASort n4 
n2))))) (\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort O 
n2)))).(\lambda (_: (((leq g (asucc g (ASort n3 n0)) (asucc g (ASort O n2))) 
\to (leq g (ASort n3 n0) (ASort O n2))))).(let H2 \def (match H1 in leq 
return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a 
(ASort n3 n0)) \to ((eq A a0 (ASort O (next g n2))) \to (leq g (ASort (S n3) 
n0) (ASort O n2))))))) with [(leq_sort h1 h2 n4 n5 k H2) \Rightarrow (\lambda 
(H3: (eq A (ASort h1 n4) (ASort n3 n0))).(\lambda (H4: (eq A (ASort h2 n5) 
(ASort O (next g n2)))).((let H5 \def (f_equal A nat (\lambda (e: A).(match e 
in A return (\lambda (_: A).nat) with [(ASort _ n6) \Rightarrow n6 | (AHead _ 
_) \Rightarrow n4])) (ASort h1 n4) (ASort n3 n0) H3) in ((let H6 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n6 _) \Rightarrow n6 | (AHead _ _) \Rightarrow h1])) (ASort h1 n4) 
(ASort n3 n0) H3) in (eq_ind nat n3 (\lambda (n6: nat).((eq nat n4 n0) \to 
((eq A (ASort h2 n5) (ASort O (next g n2))) \to ((eq A (aplus g (ASort n6 n4) 
k) (aplus g (ASort h2 n5) k)) \to (leq g (ASort (S n3) n0) (ASort O n2)))))) 
(\lambda (H7: (eq nat n4 n0)).(eq_ind nat n0 (\lambda (n6: nat).((eq A (ASort 
h2 n5) (ASort O (next g n2))) \to ((eq A (aplus g (ASort n3 n6) k) (aplus g 
(ASort h2 n5) k)) \to (leq g (ASort (S n3) n0) (ASort O n2))))) (\lambda (H8: 
(eq A (ASort h2 n5) (ASort O (next g n2)))).(let H9 \def (f_equal A nat 
(\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n6) 
\Rightarrow n6 | (AHead _ _) \Rightarrow n5])) (ASort h2 n5) (ASort O (next g 
n2)) H8) in ((let H10 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort n6 _) \Rightarrow n6 | (AHead _ _) 
\Rightarrow h2])) (ASort h2 n5) (ASort O (next g n2)) H8) in (eq_ind nat O 
(\lambda (n6: nat).((eq nat n5 (next g n2)) \to ((eq A (aplus g (ASort n3 n0) 
k) (aplus g (ASort n6 n5) k)) \to (leq g (ASort (S n3) n0) (ASort O n2))))) 
(\lambda (H11: (eq nat n5 (next g n2))).(eq_ind nat (next g n2) (\lambda (n6: 
nat).((eq A (aplus g (ASort n3 n0) k) (aplus g (ASort O n6) k)) \to (leq g 
(ASort (S n3) n0) (ASort O n2)))) (\lambda (H12: (eq A (aplus g (ASort n3 n0) 
k) (aplus g (ASort O (next g n2)) k))).(let H13 \def (eq_ind_r A (aplus g 
(ASort n3 n0) k) (\lambda (a: A).(eq A a (aplus g (ASort O (next g n2)) k))) 
H12 (aplus g (ASort (S n3) n0) (S k)) (aplus_sort_S_S_simpl g n0 n3 k)) in 
(let H14 \def (eq_ind_r A (aplus g (ASort O (next g n2)) k) (\lambda (a: 
A).(eq A (aplus g (ASort (S n3) n0) (S k)) a)) H13 (aplus g (ASort O n2) (S 
k)) (aplus_sort_O_S_simpl g n2 k)) in (leq_sort g (S n3) O n0 n2 (S k) 
H14)))) n5 (sym_eq nat n5 (next g n2) H11))) h2 (sym_eq nat h2 O H10))) H9))) 
n4 (sym_eq nat n4 n0 H7))) h1 (sym_eq nat h1 n3 H6))) H5)) H4 H2))) | 
(leq_head a0 a3 H2 a4 a5 H3) \Rightarrow (\lambda (H4: (eq A (AHead a0 a4) 
(ASort n3 n0))).(\lambda (H5: (eq A (AHead a3 a5) (ASort O (next g 
n2)))).((let H6 \def (eq_ind A (AHead a0 a4) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort n3 n0) H4) in (False_ind ((eq A (AHead a3 a5) 
(ASort O (next g n2))) \to ((leq g a0 a3) \to ((leq g a4 a5) \to (leq g 
(ASort (S n3) n0) (ASort O n2))))) H6)) H5 H2 H3)))]) in (H2 (refl_equal A 
(ASort n3 n0)) (refl_equal A (ASort O (next g n2))))))) (\lambda (n4: 
nat).(\lambda (_: (((leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n4 
n2))) \to ((((leq g (asucc g (ASort n3 n0)) (asucc g (ASort n4 n2))) \to (leq 
g (ASort n3 n0) (ASort n4 n2)))) \to (leq g (ASort (S n3) n0) (ASort n4 
n2)))))).(\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort (S 
n4) n2)))).(\lambda (_: (((leq g (asucc g (ASort n3 n0)) (asucc g (ASort (S 
n4) n2))) \to (leq g (ASort n3 n0) (ASort (S n4) n2))))).(let H2 \def (match 
H1 in leq return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a 
a0)).((eq A a (ASort n3 n0)) \to ((eq A a0 (ASort n4 n2)) \to (leq g (ASort 
(S n3) n0) (ASort (S n4) n2))))))) with [(leq_sort h1 h2 n5 n6 k H2) 
\Rightarrow (\lambda (H3: (eq A (ASort h1 n5) (ASort n3 n0))).(\lambda (H4: 
(eq A (ASort h2 n6) (ASort n4 n2))).((let H5 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n7) \Rightarrow 
n7 | (AHead _ _) \Rightarrow n5])) (ASort h1 n5) (ASort n3 n0) H3) in ((let 
H6 \def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: 
A).nat) with [(ASort n7 _) \Rightarrow n7 | (AHead _ _) \Rightarrow h1])) 
(ASort h1 n5) (ASort n3 n0) H3) in (eq_ind nat n3 (\lambda (n7: nat).((eq nat 
n5 n0) \to ((eq A (ASort h2 n6) (ASort n4 n2)) \to ((eq A (aplus g (ASort n7 
n5) k) (aplus g (ASort h2 n6) k)) \to (leq g (ASort (S n3) n0) (ASort (S n4) 
n2)))))) (\lambda (H7: (eq nat n5 n0)).(eq_ind nat n0 (\lambda (n7: nat).((eq 
A (ASort h2 n6) (ASort n4 n2)) \to ((eq A (aplus g (ASort n3 n7) k) (aplus g 
(ASort h2 n6) k)) \to (leq g (ASort (S n3) n0) (ASort (S n4) n2))))) (\lambda 
(H8: (eq A (ASort h2 n6) (ASort n4 n2))).(let H9 \def (f_equal A nat (\lambda 
(e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n7) 
\Rightarrow n7 | (AHead _ _) \Rightarrow n6])) (ASort h2 n6) (ASort n4 n2) 
H8) in ((let H10 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort n7 _) \Rightarrow n7 | (AHead _ _) 
\Rightarrow h2])) (ASort h2 n6) (ASort n4 n2) H8) in (eq_ind nat n4 (\lambda 
(n7: nat).((eq nat n6 n2) \to ((eq A (aplus g (ASort n3 n0) k) (aplus g 
(ASort n7 n6) k)) \to (leq g (ASort (S n3) n0) (ASort (S n4) n2))))) (\lambda 
(H11: (eq nat n6 n2)).(eq_ind nat n2 (\lambda (n7: nat).((eq A (aplus g 
(ASort n3 n0) k) (aplus g (ASort n4 n7) k)) \to (leq g (ASort (S n3) n0) 
(ASort (S n4) n2)))) (\lambda (H12: (eq A (aplus g (ASort n3 n0) k) (aplus g 
(ASort n4 n2) k))).(let H13 \def (eq_ind_r A (aplus g (ASort n3 n0) k) 
(\lambda (a: A).(eq A a (aplus g (ASort n4 n2) k))) H12 (aplus g (ASort (S 
n3) n0) (S k)) (aplus_sort_S_S_simpl g n0 n3 k)) in (let H14 \def (eq_ind_r A 
(aplus g (ASort n4 n2) k) (\lambda (a: A).(eq A (aplus g (ASort (S n3) n0) (S 
k)) a)) H13 (aplus g (ASort (S n4) n2) (S k)) (aplus_sort_S_S_simpl g n2 n4 
k)) in (leq_sort g (S n3) (S n4) n0 n2 (S k) H14)))) n6 (sym_eq nat n6 n2 
H11))) h2 (sym_eq nat h2 n4 H10))) H9))) n5 (sym_eq nat n5 n0 H7))) h1 
(sym_eq nat h1 n3 H6))) H5)) H4 H2))) | (leq_head a0 a3 H2 a4 a5 H3) 
\Rightarrow (\lambda (H4: (eq A (AHead a0 a4) (ASort n3 n0))).(\lambda (H5: 
(eq A (AHead a3 a5) (ASort n4 n2))).((let H6 \def (eq_ind A (AHead a0 a4) 
(\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort n3 n0) H4) in 
(False_ind ((eq A (AHead a3 a5) (ASort n4 n2)) \to ((leq g a0 a3) \to ((leq g 
a4 a5) \to (leq g (ASort (S n3) n0) (ASort (S n4) n2))))) H6)) H5 H2 H3)))]) 
in (H2 (refl_equal A (ASort n3 n0)) (refl_equal A (ASort n4 n2)))))))) n1 H0 
IHn)))) n H)))) (\lambda (a: A).(\lambda (H: (((leq g (asucc g (ASort n n0)) 
(asucc g a)) \to (leq g (ASort n n0) a)))).(\lambda (a0: A).(\lambda (H0: 
(((leq g (asucc g (ASort n n0)) (asucc g a0)) \to (leq g (ASort n n0) 
a0)))).(\lambda (H1: (leq g (asucc g (ASort n n0)) (asucc g (AHead a 
a0)))).(nat_ind (\lambda (n1: nat).((((leq g (asucc g (ASort n1 n0)) (asucc g 
a)) \to (leq g (ASort n1 n0) a))) \to ((((leq g (asucc g (ASort n1 n0)) 
(asucc g a0)) \to (leq g (ASort n1 n0) a0))) \to ((leq g (asucc g (ASort n1 
n0)) (asucc g (AHead a a0))) \to (leq g (ASort n1 n0) (AHead a a0)))))) 
(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g a)) \to (leq g (ASort O 
n0) a)))).(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g a0)) \to (leq 
g (ASort O n0) a0)))).(\lambda (H4: (leq g (asucc g (ASort O n0)) (asucc g 
(AHead a a0)))).(let H5 \def (match H4 in leq return (\lambda (a3: 
A).(\lambda (a4: A).(\lambda (_: (leq ? a3 a4)).((eq A a3 (ASort O (next g 
n0))) \to ((eq A a4 (AHead a (asucc g a0))) \to (leq g (ASort O n0) (AHead a 
a0))))))) with [(leq_sort h1 h2 n1 n2 k H5) \Rightarrow (\lambda (H6: (eq A 
(ASort h1 n1) (ASort O (next g n0)))).(\lambda (H7: (eq A (ASort h2 n2) 
(AHead a (asucc g a0)))).((let H8 \def (f_equal A nat (\lambda (e: A).(match 
e in A return (\lambda (_: A).nat) with [(ASort _ n3) \Rightarrow n3 | (AHead 
_ _) \Rightarrow n1])) (ASort h1 n1) (ASort O (next g n0)) H6) in ((let H9 
\def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) 
with [(ASort n3 _) \Rightarrow n3 | (AHead _ _) \Rightarrow h1])) (ASort h1 
n1) (ASort O (next g n0)) H6) in (eq_ind nat O (\lambda (n3: nat).((eq nat n1 
(next g n0)) \to ((eq A (ASort h2 n2) (AHead a (asucc g a0))) \to ((eq A 
(aplus g (ASort n3 n1) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort O n0) 
(AHead a a0)))))) (\lambda (H10: (eq nat n1 (next g n0))).(eq_ind nat (next g 
n0) (\lambda (n3: nat).((eq A (ASort h2 n2) (AHead a (asucc g a0))) \to ((eq 
A (aplus g (ASort O n3) k) (aplus g (ASort h2 n2) k)) \to (leq g (ASort O n0) 
(AHead a a0))))) (\lambda (H11: (eq A (ASort h2 n2) (AHead a (asucc g 
a0)))).(let H12 \def (eq_ind A (ASort h2 n2) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a (asucc g a0)) H11) in (False_ind ((eq A 
(aplus g (ASort O (next g n0)) k) (aplus g (ASort h2 n2) k)) \to (leq g 
(ASort O n0) (AHead a a0))) H12))) n1 (sym_eq nat n1 (next g n0) H10))) h1 
(sym_eq nat h1 O H9))) H8)) H7 H5))) | (leq_head a3 a4 H5 a5 a6 H6) 
\Rightarrow (\lambda (H7: (eq A (AHead a3 a5) (ASort O (next g 
n0)))).(\lambda (H8: (eq A (AHead a4 a6) (AHead a (asucc g a0)))).((let H9 
\def (eq_ind A (AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort O (next g n0)) H7) in (False_ind ((eq A (AHead a4 a6) (AHead 
a (asucc g a0))) \to ((leq g a3 a4) \to ((leq g a5 a6) \to (leq g (ASort O 
n0) (AHead a a0))))) H9)) H8 H5 H6)))]) in (H5 (refl_equal A (ASort O (next g 
n0))) (refl_equal A (AHead a (asucc g a0)))))))) (\lambda (n1: nat).(\lambda 
(_: (((((leq g (asucc g (ASort n1 n0)) (asucc g a)) \to (leq g (ASort n1 n0) 
a))) \to ((((leq g (asucc g (ASort n1 n0)) (asucc g a0)) \to (leq g (ASort n1 
n0) a0))) \to ((leq g (asucc g (ASort n1 n0)) (asucc g (AHead a a0))) \to 
(leq g (ASort n1 n0) (AHead a a0))))))).(\lambda (_: (((leq g (asucc g (ASort 
(S n1) n0)) (asucc g a)) \to (leq g (ASort (S n1) n0) a)))).(\lambda (_: 
(((leq g (asucc g (ASort (S n1) n0)) (asucc g a0)) \to (leq g (ASort (S n1) 
n0) a0)))).(\lambda (H4: (leq g (asucc g (ASort (S n1) n0)) (asucc g (AHead a 
a0)))).(let H5 \def (match H4 in leq return (\lambda (a3: A).(\lambda (a4: 
A).(\lambda (_: (leq ? a3 a4)).((eq A a3 (ASort n1 n0)) \to ((eq A a4 (AHead 
a (asucc g a0))) \to (leq g (ASort (S n1) n0) (AHead a a0))))))) with 
[(leq_sort h1 h2 n2 n3 k H5) \Rightarrow (\lambda (H6: (eq A (ASort h1 n2) 
(ASort n1 n0))).(\lambda (H7: (eq A (ASort h2 n3) (AHead a (asucc g 
a0)))).((let H8 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n4) \Rightarrow n4 | (AHead _ _) 
\Rightarrow n2])) (ASort h1 n2) (ASort n1 n0) H6) in ((let H9 \def (f_equal A 
nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort n4 
_) \Rightarrow n4 | (AHead _ _) \Rightarrow h1])) (ASort h1 n2) (ASort n1 n0) 
H6) in (eq_ind nat n1 (\lambda (n4: nat).((eq nat n2 n0) \to ((eq A (ASort h2 
n3) (AHead a (asucc g a0))) \to ((eq A (aplus g (ASort n4 n2) k) (aplus g 
(ASort h2 n3) k)) \to (leq g (ASort (S n1) n0) (AHead a a0)))))) (\lambda 
(H10: (eq nat n2 n0)).(eq_ind nat n0 (\lambda (n4: nat).((eq A (ASort h2 n3) 
(AHead a (asucc g a0))) \to ((eq A (aplus g (ASort n1 n4) k) (aplus g (ASort 
h2 n3) k)) \to (leq g (ASort (S n1) n0) (AHead a a0))))) (\lambda (H11: (eq A 
(ASort h2 n3) (AHead a (asucc g a0)))).(let H12 \def (eq_ind A (ASort h2 n3) 
(\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead a (asucc g a0)) 
H11) in (False_ind ((eq A (aplus g (ASort n1 n0) k) (aplus g (ASort h2 n3) 
k)) \to (leq g (ASort (S n1) n0) (AHead a a0))) H12))) n2 (sym_eq nat n2 n0 
H10))) h1 (sym_eq nat h1 n1 H9))) H8)) H7 H5))) | (leq_head a3 a4 H5 a5 a6 
H6) \Rightarrow (\lambda (H7: (eq A (AHead a3 a5) (ASort n1 n0))).(\lambda 
(H8: (eq A (AHead a4 a6) (AHead a (asucc g a0)))).((let H9 \def (eq_ind A 
(AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort n1 
n0) H7) in (False_ind ((eq A (AHead a4 a6) (AHead a (asucc g a0))) \to ((leq 
g a3 a4) \to ((leq g a5 a6) \to (leq g (ASort (S n1) n0) (AHead a a0))))) 
H9)) H8 H5 H6)))]) in (H5 (refl_equal A (ASort n1 n0)) (refl_equal A (AHead a 
(asucc g a0)))))))))) n H H0 H1)))))) a2)))) (\lambda (a: A).(\lambda (_: 
((\forall (a2: A).((leq g (asucc g a) (asucc g a2)) \to (leq g a 
a2))))).(\lambda (a0: A).(\lambda (H0: ((\forall (a2: A).((leq g (asucc g a0) 
(asucc g a2)) \to (leq g a0 a2))))).(\lambda (a2: A).(A_ind (\lambda (a3: 
A).((leq g (asucc g (AHead a a0)) (asucc g a3)) \to (leq g (AHead a a0) a3))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (H1: (leq g (asucc g (AHead a 
a0)) (asucc g (ASort n n0)))).(nat_ind (\lambda (n1: nat).((leq g (asucc g 
(AHead a a0)) (asucc g (ASort n1 n0))) \to (leq g (AHead a a0) (ASort n1 
n0)))) (\lambda (H2: (leq g (asucc g (AHead a a0)) (asucc g (ASort O 
n0)))).(let H3 \def (match H2 in leq return (\lambda (a3: A).(\lambda (a4: 
A).(\lambda (_: (leq ? a3 a4)).((eq A a3 (AHead a (asucc g a0))) \to ((eq A 
a4 (ASort O (next g n0))) \to (leq g (AHead a a0) (ASort O n0))))))) with 
[(leq_sort h1 h2 n1 n2 k H3) \Rightarrow (\lambda (H4: (eq A (ASort h1 n1) 
(AHead a (asucc g a0)))).(\lambda (H5: (eq A (ASort h2 n2) (ASort O (next g 
n0)))).((let H6 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a (asucc g a0)) H4) in (False_ind ((eq A (ASort 
h2 n2) (ASort O (next g n0))) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k)) \to (leq g (AHead a a0) (ASort O n0)))) H6)) H5 H3))) | 
(leq_head a3 a4 H3 a5 a6 H4) \Rightarrow (\lambda (H5: (eq A (AHead a3 a5) 
(AHead a (asucc g a0)))).(\lambda (H6: (eq A (AHead a4 a6) (ASort O (next g 
n0)))).((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a5 | (AHead _ a7) 
\Rightarrow a7])) (AHead a3 a5) (AHead a (asucc g a0)) H5) in ((let H8 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a3 | (AHead a7 _) \Rightarrow a7])) (AHead a3 a5) 
(AHead a (asucc g a0)) H5) in (eq_ind A a (\lambda (a7: A).((eq A a5 (asucc g 
a0)) \to ((eq A (AHead a4 a6) (ASort O (next g n0))) \to ((leq g a7 a4) \to 
((leq g a5 a6) \to (leq g (AHead a a0) (ASort O n0))))))) (\lambda (H9: (eq A 
a5 (asucc g a0))).(eq_ind A (asucc g a0) (\lambda (a7: A).((eq A (AHead a4 
a6) (ASort O (next g n0))) \to ((leq g a a4) \to ((leq g a7 a6) \to (leq g 
(AHead a a0) (ASort O n0)))))) (\lambda (H10: (eq A (AHead a4 a6) (ASort O 
(next g n0)))).(let H11 \def (eq_ind A (AHead a4 a6) (\lambda (e: A).(match e 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) H10) in (False_ind 
((leq g a a4) \to ((leq g (asucc g a0) a6) \to (leq g (AHead a a0) (ASort O 
n0)))) H11))) a5 (sym_eq A a5 (asucc g a0) H9))) a3 (sym_eq A a3 a H8))) H7)) 
H6 H3 H4)))]) in (H3 (refl_equal A (AHead a (asucc g a0))) (refl_equal A 
(ASort O (next g n0)))))) (\lambda (n1: nat).(\lambda (_: (((leq g (asucc g 
(AHead a a0)) (asucc g (ASort n1 n0))) \to (leq g (AHead a a0) (ASort n1 
n0))))).(\lambda (H2: (leq g (asucc g (AHead a a0)) (asucc g (ASort (S n1) 
n0)))).(let H3 \def (match H2 in leq return (\lambda (a3: A).(\lambda (a4: 
A).(\lambda (_: (leq ? a3 a4)).((eq A a3 (AHead a (asucc g a0))) \to ((eq A 
a4 (ASort n1 n0)) \to (leq g (AHead a a0) (ASort (S n1) n0))))))) with 
[(leq_sort h1 h2 n2 n3 k H3) \Rightarrow (\lambda (H4: (eq A (ASort h1 n2) 
(AHead a (asucc g a0)))).(\lambda (H5: (eq A (ASort h2 n3) (ASort n1 
n0))).((let H6 \def (eq_ind A (ASort h1 n2) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a (asucc g a0)) H4) in (False_ind ((eq A (ASort 
h2 n3) (ASort n1 n0)) \to ((eq A (aplus g (ASort h1 n2) k) (aplus g (ASort h2 
n3) k)) \to (leq g (AHead a a0) (ASort (S n1) n0)))) H6)) H5 H3))) | 
(leq_head a3 a4 H3 a5 a6 H4) \Rightarrow (\lambda (H5: (eq A (AHead a3 a5) 
(AHead a (asucc g a0)))).(\lambda (H6: (eq A (AHead a4 a6) (ASort n1 
n0))).((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a5 | (AHead _ a7) 
\Rightarrow a7])) (AHead a3 a5) (AHead a (asucc g a0)) H5) in ((let H8 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a3 | (AHead a7 _) \Rightarrow a7])) (AHead a3 a5) 
(AHead a (asucc g a0)) H5) in (eq_ind A a (\lambda (a7: A).((eq A a5 (asucc g 
a0)) \to ((eq A (AHead a4 a6) (ASort n1 n0)) \to ((leq g a7 a4) \to ((leq g 
a5 a6) \to (leq g (AHead a a0) (ASort (S n1) n0))))))) (\lambda (H9: (eq A a5 
(asucc g a0))).(eq_ind A (asucc g a0) (\lambda (a7: A).((eq A (AHead a4 a6) 
(ASort n1 n0)) \to ((leq g a a4) \to ((leq g a7 a6) \to (leq g (AHead a a0) 
(ASort (S n1) n0)))))) (\lambda (H10: (eq A (AHead a4 a6) (ASort n1 
n0))).(let H11 \def (eq_ind A (AHead a4 a6) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort n1 n0) H10) in (False_ind ((leq g a a4) \to 
((leq g (asucc g a0) a6) \to (leq g (AHead a a0) (ASort (S n1) n0)))) H11))) 
a5 (sym_eq A a5 (asucc g a0) H9))) a3 (sym_eq A a3 a H8))) H7)) H6 H3 H4)))]) 
in (H3 (refl_equal A (AHead a (asucc g a0))) (refl_equal A (ASort n1 
n0))))))) n H1)))) (\lambda (a3: A).(\lambda (_: (((leq g (asucc g (AHead a 
a0)) (asucc g a3)) \to (leq g (AHead a a0) a3)))).(\lambda (a4: A).(\lambda 
(_: (((leq g (asucc g (AHead a a0)) (asucc g a4)) \to (leq g (AHead a a0) 
a4)))).(\lambda (H3: (leq g (asucc g (AHead a a0)) (asucc g (AHead a3 
a4)))).(let H4 \def (match H3 in leq return (\lambda (a5: A).(\lambda (a6: 
A).(\lambda (_: (leq ? a5 a6)).((eq A a5 (AHead a (asucc g a0))) \to ((eq A 
a6 (AHead a3 (asucc g a4))) \to (leq g (AHead a a0) (AHead a3 a4))))))) with 
[(leq_sort h1 h2 n1 n2 k H4) \Rightarrow (\lambda (H5: (eq A (ASort h1 n1) 
(AHead a (asucc g a0)))).(\lambda (H6: (eq A (ASort h2 n2) (AHead a3 (asucc g 
a4)))).((let H7 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a (asucc g a0)) H5) in (False_ind ((eq A (ASort 
h2 n2) (AHead a3 (asucc g a4))) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k)) \to (leq g (AHead a a0) (AHead a3 a4)))) H7)) H6 H4))) | 
(leq_head a5 a6 H4 a7 a8 H5) \Rightarrow (\lambda (H6: (eq A (AHead a5 a7) 
(AHead a (asucc g a0)))).(\lambda (H7: (eq A (AHead a6 a8) (AHead a3 (asucc g 
a4)))).((let H8 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a7 | (AHead _ a9) 
\Rightarrow a9])) (AHead a5 a7) (AHead a (asucc g a0)) H6) in ((let H9 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a5 | (AHead a9 _) \Rightarrow a9])) (AHead a5 a7) 
(AHead a (asucc g a0)) H6) in (eq_ind A a (\lambda (a9: A).((eq A a7 (asucc g 
a0)) \to ((eq A (AHead a6 a8) (AHead a3 (asucc g a4))) \to ((leq g a9 a6) \to 
((leq g a7 a8) \to (leq g (AHead a a0) (AHead a3 a4))))))) (\lambda (H10: (eq 
A a7 (asucc g a0))).(eq_ind A (asucc g a0) (\lambda (a9: A).((eq A (AHead a6 
a8) (AHead a3 (asucc g a4))) \to ((leq g a a6) \to ((leq g a9 a8) \to (leq g 
(AHead a a0) (AHead a3 a4)))))) (\lambda (H11: (eq A (AHead a6 a8) (AHead a3 
(asucc g a4)))).(let H12 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a8 | (AHead _ a9) 
\Rightarrow a9])) (AHead a6 a8) (AHead a3 (asucc g a4)) H11) in ((let H13 
\def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a6 | (AHead a9 _) \Rightarrow a9])) (AHead a6 
a8) (AHead a3 (asucc g a4)) H11) in (eq_ind A a3 (\lambda (a9: A).((eq A a8 
(asucc g a4)) \to ((leq g a a9) \to ((leq g (asucc g a0) a8) \to (leq g 
(AHead a a0) (AHead a3 a4)))))) (\lambda (H14: (eq A a8 (asucc g 
a4))).(eq_ind A (asucc g a4) (\lambda (a9: A).((leq g a a3) \to ((leq g 
(asucc g a0) a9) \to (leq g (AHead a a0) (AHead a3 a4))))) (\lambda (H15: 
(leq g a a3)).(\lambda (H16: (leq g (asucc g a0) (asucc g a4))).(leq_head g a 
a3 H15 a0 a4 (H0 a4 H16)))) a8 (sym_eq A a8 (asucc g a4) H14))) a6 (sym_eq A 
a6 a3 H13))) H12))) a7 (sym_eq A a7 (asucc g a0) H10))) a5 (sym_eq A a5 a 
H9))) H8)) H7 H4 H5)))]) in (H4 (refl_equal A (AHead a (asucc g a0))) 
(refl_equal A (AHead a3 (asucc g a4)))))))))) a2)))))) a1)).

theorem leq_asucc:
 \forall (g: G).(\forall (a: A).(ex A (\lambda (a0: A).(leq g a (asucc g 
a0)))))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(ex A (\lambda (a1: 
A).(leq g a0 (asucc g a1))))) (\lambda (n: nat).(\lambda (n0: nat).(ex_intro 
A (\lambda (a0: A).(leq g (ASort n n0) (asucc g a0))) (ASort (S n) n0) 
(leq_refl g (ASort n n0))))) (\lambda (a0: A).(\lambda (_: (ex A (\lambda 
(a1: A).(leq g a0 (asucc g a1))))).(\lambda (a1: A).(\lambda (H0: (ex A 
(\lambda (a2: A).(leq g a1 (asucc g a2))))).(let H1 \def H0 in (ex_ind A 
(\lambda (a2: A).(leq g a1 (asucc g a2))) (ex A (\lambda (a2: A).(leq g 
(AHead a0 a1) (asucc g a2)))) (\lambda (x: A).(\lambda (H2: (leq g a1 (asucc 
g x))).(ex_intro A (\lambda (a2: A).(leq g (AHead a0 a1) (asucc g a2))) 
(AHead a0 x) (leq_head g a0 a0 (leq_refl g a0) a1 (asucc g x) H2)))) H1)))))) 
a)).

theorem leq_ahead_asucc_false:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) 
(asucc g a1)) \to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a1: A).(A_ind (\lambda (a: A).(\forall (a2: 
A).((leq g (AHead a a2) (asucc g a)) \to (\forall (P: Prop).P)))) (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (a2: A).(\lambda (H: (leq g (AHead 
(ASort n n0) a2) (match n with [O \Rightarrow (ASort O (next g n0)) | (S h) 
\Rightarrow (ASort h n0)]))).(\lambda (P: Prop).(nat_ind (\lambda (n1: 
nat).((leq g (AHead (ASort n1 n0) a2) (match n1 with [O \Rightarrow (ASort O 
(next g n0)) | (S h) \Rightarrow (ASort h n0)])) \to P)) (\lambda (H0: (leq g 
(AHead (ASort O n0) a2) (ASort O (next g n0)))).(let H1 \def (match H0 in leq 
return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a 
(AHead (ASort O n0) a2)) \to ((eq A a0 (ASort O (next g n0))) \to P))))) with 
[(leq_sort h1 h2 n1 n2 k H1) \Rightarrow (\lambda (H2: (eq A (ASort h1 n1) 
(AHead (ASort O n0) a2))).(\lambda (H3: (eq A (ASort h2 n2) (ASort O (next g 
n0)))).((let H4 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead (ASort O n0) a2) H2) in (False_ind ((eq A 
(ASort h2 n2) (ASort O (next g n0))) \to ((eq A (aplus g (ASort h1 n1) k) 
(aplus g (ASort h2 n2) k)) \to P)) H4)) H3 H1))) | (leq_head a0 a3 H1 a4 a5 
H2) \Rightarrow (\lambda (H3: (eq A (AHead a0 a4) (AHead (ASort O n0) 
a2))).(\lambda (H4: (eq A (AHead a3 a5) (ASort O (next g n0)))).((let H5 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a4 | (AHead _ a) \Rightarrow a])) (AHead a0 a4) 
(AHead (ASort O n0) a2) H3) in ((let H6 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | 
(AHead a _) \Rightarrow a])) (AHead a0 a4) (AHead (ASort O n0) a2) H3) in 
(eq_ind A (ASort O n0) (\lambda (a: A).((eq A a4 a2) \to ((eq A (AHead a3 a5) 
(ASort O (next g n0))) \to ((leq g a a3) \to ((leq g a4 a5) \to P))))) 
(\lambda (H7: (eq A a4 a2)).(eq_ind A a2 (\lambda (a: A).((eq A (AHead a3 a5) 
(ASort O (next g n0))) \to ((leq g (ASort O n0) a3) \to ((leq g a a5) \to 
P)))) (\lambda (H8: (eq A (AHead a3 a5) (ASort O (next g n0)))).(let H9 \def 
(eq_ind A (AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort O (next g n0)) H8) in (False_ind ((leq g (ASort O n0) a3) 
\to ((leq g a2 a5) \to P)) H9))) a4 (sym_eq A a4 a2 H7))) a0 (sym_eq A a0 
(ASort O n0) H6))) H5)) H4 H1 H2)))]) in (H1 (refl_equal A (AHead (ASort O 
n0) a2)) (refl_equal A (ASort O (next g n0)))))) (\lambda (n1: nat).(\lambda 
(_: (((leq g (AHead (ASort n1 n0) a2) (match n1 with [O \Rightarrow (ASort O 
(next g n0)) | (S h) \Rightarrow (ASort h n0)])) \to P))).(\lambda (H0: (leq 
g (AHead (ASort (S n1) n0) a2) (ASort n1 n0))).(let H1 \def (match H0 in leq 
return (\lambda (a: A).(\lambda (a0: A).(\lambda (_: (leq ? a a0)).((eq A a 
(AHead (ASort (S n1) n0) a2)) \to ((eq A a0 (ASort n1 n0)) \to P))))) with 
[(leq_sort h1 h2 n2 n3 k H1) \Rightarrow (\lambda (H2: (eq A (ASort h1 n2) 
(AHead (ASort (S n1) n0) a2))).(\lambda (H3: (eq A (ASort h2 n3) (ASort n1 
n0))).((let H4 \def (eq_ind A (ASort h1 n2) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead (ASort (S n1) n0) a2) H2) in (False_ind ((eq A 
(ASort h2 n3) (ASort n1 n0)) \to ((eq A (aplus g (ASort h1 n2) k) (aplus g 
(ASort h2 n3) k)) \to P)) H4)) H3 H1))) | (leq_head a0 a3 H1 a4 a5 H2) 
\Rightarrow (\lambda (H3: (eq A (AHead a0 a4) (AHead (ASort (S n1) n0) 
a2))).(\lambda (H4: (eq A (AHead a3 a5) (ASort n1 n0))).((let H5 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a4 | (AHead _ a) \Rightarrow a])) (AHead a0 a4) 
(AHead (ASort (S n1) n0) a2) H3) in ((let H6 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | 
(AHead a _) \Rightarrow a])) (AHead a0 a4) (AHead (ASort (S n1) n0) a2) H3) 
in (eq_ind A (ASort (S n1) n0) (\lambda (a: A).((eq A a4 a2) \to ((eq A 
(AHead a3 a5) (ASort n1 n0)) \to ((leq g a a3) \to ((leq g a4 a5) \to P))))) 
(\lambda (H7: (eq A a4 a2)).(eq_ind A a2 (\lambda (a: A).((eq A (AHead a3 a5) 
(ASort n1 n0)) \to ((leq g (ASort (S n1) n0) a3) \to ((leq g a a5) \to P)))) 
(\lambda (H8: (eq A (AHead a3 a5) (ASort n1 n0))).(let H9 \def (eq_ind A 
(AHead a3 a5) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort n1 
n0) H8) in (False_ind ((leq g (ASort (S n1) n0) a3) \to ((leq g a2 a5) \to 
P)) H9))) a4 (sym_eq A a4 a2 H7))) a0 (sym_eq A a0 (ASort (S n1) n0) H6))) 
H5)) H4 H1 H2)))]) in (H1 (refl_equal A (AHead (ASort (S n1) n0) a2)) 
(refl_equal A (ASort n1 n0))))))) n H)))))) (\lambda (a: A).(\lambda (_: 
((\forall (a2: A).((leq g (AHead a a2) (asucc g a)) \to (\forall (P: 
Prop).P))))).(\lambda (a0: A).(\lambda (_: ((\forall (a2: A).((leq g (AHead 
a0 a2) (asucc g a0)) \to (\forall (P: Prop).P))))).(\lambda (a2: A).(\lambda 
(H1: (leq g (AHead (AHead a a0) a2) (AHead a (asucc g a0)))).(\lambda (P: 
Prop).(let H2 \def (match H1 in leq return (\lambda (a3: A).(\lambda (a4: 
A).(\lambda (_: (leq ? a3 a4)).((eq A a3 (AHead (AHead a a0) a2)) \to ((eq A 
a4 (AHead a (asucc g a0))) \to P))))) with [(leq_sort h1 h2 n1 n2 k H2) 
\Rightarrow (\lambda (H3: (eq A (ASort h1 n1) (AHead (AHead a a0) 
a2))).(\lambda (H4: (eq A (ASort h2 n2) (AHead a (asucc g a0)))).((let H5 
\def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A return (\lambda 
(_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead (AHead a a0) a2) H3) in (False_ind ((eq A (ASort h2 n2) 
(AHead a (asucc g a0))) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort 
h2 n2) k)) \to P)) H5)) H4 H2))) | (leq_head a3 a4 H2 a5 a6 H3) \Rightarrow 
(\lambda (H4: (eq A (AHead a3 a5) (AHead (AHead a a0) a2))).(\lambda (H5: (eq 
A (AHead a4 a6) (AHead a (asucc g a0)))).((let H6 \def (f_equal A A (\lambda 
(e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow 
a5 | (AHead _ a7) \Rightarrow a7])) (AHead a3 a5) (AHead (AHead a a0) a2) H4) 
in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda 
(_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead a7 _) \Rightarrow a7])) 
(AHead a3 a5) (AHead (AHead a a0) a2) H4) in (eq_ind A (AHead a a0) (\lambda 
(a7: A).((eq A a5 a2) \to ((eq A (AHead a4 a6) (AHead a (asucc g a0))) \to 
((leq g a7 a4) \to ((leq g a5 a6) \to P))))) (\lambda (H8: (eq A a5 
a2)).(eq_ind A a2 (\lambda (a7: A).((eq A (AHead a4 a6) (AHead a (asucc g 
a0))) \to ((leq g (AHead a a0) a4) \to ((leq g a7 a6) \to P)))) (\lambda (H9: 
(eq A (AHead a4 a6) (AHead a (asucc g a0)))).(let H10 \def (f_equal A A 
(\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a6 | (AHead _ a7) \Rightarrow a7])) (AHead a4 a6) (AHead a (asucc 
g a0)) H9) in ((let H11 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a4 | (AHead a7 _) 
\Rightarrow a7])) (AHead a4 a6) (AHead a (asucc g a0)) H9) in (eq_ind A a 
(\lambda (a7: A).((eq A a6 (asucc g a0)) \to ((leq g (AHead a a0) a7) \to 
((leq g a2 a6) \to P)))) (\lambda (H12: (eq A a6 (asucc g a0))).(eq_ind A 
(asucc g a0) (\lambda (a7: A).((leq g (AHead a a0) a) \to ((leq g a2 a7) \to 
P))) (\lambda (H13: (leq g (AHead a a0) a)).(\lambda (_: (leq g a2 (asucc g 
a0))).(leq_ahead_false_1 g a a0 H13 P))) a6 (sym_eq A a6 (asucc g a0) H12))) 
a4 (sym_eq A a4 a H11))) H10))) a5 (sym_eq A a5 a2 H8))) a3 (sym_eq A a3 
(AHead a a0) H7))) H6)) H5 H2 H3)))]) in (H2 (refl_equal A (AHead (AHead a 
a0) a2)) (refl_equal A (AHead a (asucc g a0)))))))))))) a1)).

theorem leq_asucc_false:
 \forall (g: G).(\forall (a: A).((leq g (asucc g a) a) \to (\forall (P: 
Prop).P)))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).((leq g (asucc g a0) 
a0) \to (\forall (P: Prop).P))) (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(H: (leq g (match n with [O \Rightarrow (ASort O (next g n0)) | (S h) 
\Rightarrow (ASort h n0)]) (ASort n n0))).(\lambda (P: Prop).(nat_ind 
(\lambda (n1: nat).((leq g (match n1 with [O \Rightarrow (ASort O (next g 
n0)) | (S h) \Rightarrow (ASort h n0)]) (ASort n1 n0)) \to P)) (\lambda (H0: 
(leq g (ASort O (next g n0)) (ASort O n0))).(let H1 \def (match H0 in leq 
return (\lambda (a0: A).(\lambda (a1: A).(\lambda (_: (leq ? a0 a1)).((eq A 
a0 (ASort O (next g n0))) \to ((eq A a1 (ASort O n0)) \to P))))) with 
[(leq_sort h1 h2 n1 n2 k H1) \Rightarrow (\lambda (H2: (eq A (ASort h1 n1) 
(ASort O (next g n0)))).(\lambda (H3: (eq A (ASort h2 n2) (ASort O 
n0))).((let H4 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n3) \Rightarrow n3 | (AHead _ _) 
\Rightarrow n1])) (ASort h1 n1) (ASort O (next g n0)) H2) in ((let H5 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n3 _) \Rightarrow n3 | (AHead _ _) \Rightarrow h1])) (ASort h1 n1) 
(ASort O (next g n0)) H2) in (eq_ind nat O (\lambda (n3: nat).((eq nat n1 
(next g n0)) \to ((eq A (ASort h2 n2) (ASort O n0)) \to ((eq A (aplus g 
(ASort n3 n1) k) (aplus g (ASort h2 n2) k)) \to P)))) (\lambda (H6: (eq nat 
n1 (next g n0))).(eq_ind nat (next g n0) (\lambda (n3: nat).((eq A (ASort h2 
n2) (ASort O n0)) \to ((eq A (aplus g (ASort O n3) k) (aplus g (ASort h2 n2) 
k)) \to P))) (\lambda (H7: (eq A (ASort h2 n2) (ASort O n0))).(let H8 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n3) \Rightarrow n3 | (AHead _ _) \Rightarrow n2])) (ASort h2 n2) 
(ASort O n0) H7) in ((let H9 \def (f_equal A nat (\lambda (e: A).(match e in 
A return (\lambda (_: A).nat) with [(ASort n3 _) \Rightarrow n3 | (AHead _ _) 
\Rightarrow h2])) (ASort h2 n2) (ASort O n0) H7) in (eq_ind nat O (\lambda 
(n3: nat).((eq nat n2 n0) \to ((eq A (aplus g (ASort O (next g n0)) k) (aplus 
g (ASort n3 n2) k)) \to P))) (\lambda (H10: (eq nat n2 n0)).(eq_ind nat n0 
(\lambda (n3: nat).((eq A (aplus g (ASort O (next g n0)) k) (aplus g (ASort O 
n3) k)) \to P)) (\lambda (H11: (eq A (aplus g (ASort O (next g n0)) k) (aplus 
g (ASort O n0) k))).(let H12 \def (eq_ind_r A (aplus g (ASort O (next g n0)) 
k) (\lambda (a0: A).(eq A a0 (aplus g (ASort O n0) k))) H11 (aplus g (ASort O 
n0) (S k)) (aplus_sort_O_S_simpl g n0 k)) in (let H_y \def (aplus_inj g (S k) 
k (ASort O n0) H12) in (le_Sx_x k (eq_ind_r nat k (\lambda (n3: nat).(le n3 
k)) (le_n k) (S k) H_y) P)))) n2 (sym_eq nat n2 n0 H10))) h2 (sym_eq nat h2 O 
H9))) H8))) n1 (sym_eq nat n1 (next g n0) H6))) h1 (sym_eq nat h1 O H5))) 
H4)) H3 H1))) | (leq_head a1 a2 H1 a3 a4 H2) \Rightarrow (\lambda (H3: (eq A 
(AHead a1 a3) (ASort O (next g n0)))).(\lambda (H4: (eq A (AHead a2 a4) 
(ASort O n0))).((let H5 \def (eq_ind A (AHead a1 a3) (\lambda (e: A).(match e 
in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) I (ASort O (next g n0)) H3) in (False_ind 
((eq A (AHead a2 a4) (ASort O n0)) \to ((leq g a1 a2) \to ((leq g a3 a4) \to 
P))) H5)) H4 H1 H2)))]) in (H1 (refl_equal A (ASort O (next g n0))) 
(refl_equal A (ASort O n0))))) (\lambda (n1: nat).(\lambda (_: (((leq g 
(match n1 with [O \Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow 
(ASort h n0)]) (ASort n1 n0)) \to P))).(\lambda (H0: (leq g (ASort n1 n0) 
(ASort (S n1) n0))).(let H1 \def (match H0 in leq return (\lambda (a0: 
A).(\lambda (a1: A).(\lambda (_: (leq ? a0 a1)).((eq A a0 (ASort n1 n0)) \to 
((eq A a1 (ASort (S n1) n0)) \to P))))) with [(leq_sort h1 h2 n2 n3 k H1) 
\Rightarrow (\lambda (H2: (eq A (ASort h1 n2) (ASort n1 n0))).(\lambda (H3: 
(eq A (ASort h2 n3) (ASort (S n1) n0))).((let H4 \def (f_equal A nat (\lambda 
(e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n4) 
\Rightarrow n4 | (AHead _ _) \Rightarrow n2])) (ASort h1 n2) (ASort n1 n0) 
H2) in ((let H5 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort n4 _) \Rightarrow n4 | (AHead _ _) 
\Rightarrow h1])) (ASort h1 n2) (ASort n1 n0) H2) in (eq_ind nat n1 (\lambda 
(n4: nat).((eq nat n2 n0) \to ((eq A (ASort h2 n3) (ASort (S n1) n0)) \to 
((eq A (aplus g (ASort n4 n2) k) (aplus g (ASort h2 n3) k)) \to P)))) 
(\lambda (H6: (eq nat n2 n0)).(eq_ind nat n0 (\lambda (n4: nat).((eq A (ASort 
h2 n3) (ASort (S n1) n0)) \to ((eq A (aplus g (ASort n1 n4) k) (aplus g 
(ASort h2 n3) k)) \to P))) (\lambda (H7: (eq A (ASort h2 n3) (ASort (S n1) 
n0))).(let H8 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n4) \Rightarrow n4 | (AHead _ _) 
\Rightarrow n3])) (ASort h2 n3) (ASort (S n1) n0) H7) in ((let H9 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n4 _) \Rightarrow n4 | (AHead _ _) \Rightarrow h2])) (ASort h2 n3) 
(ASort (S n1) n0) H7) in (eq_ind nat (S n1) (\lambda (n4: nat).((eq nat n3 
n0) \to ((eq A (aplus g (ASort n1 n0) k) (aplus g (ASort n4 n3) k)) \to P))) 
(\lambda (H10: (eq nat n3 n0)).(eq_ind nat n0 (\lambda (n4: nat).((eq A 
(aplus g (ASort n1 n0) k) (aplus g (ASort (S n1) n4) k)) \to P)) (\lambda 
(H11: (eq A (aplus g (ASort n1 n0) k) (aplus g (ASort (S n1) n0) k))).(let 
H12 \def (eq_ind_r A (aplus g (ASort n1 n0) k) (\lambda (a0: A).(eq A a0 
(aplus g (ASort (S n1) n0) k))) H11 (aplus g (ASort (S n1) n0) (S k)) 
(aplus_sort_S_S_simpl g n0 n1 k)) in (let H_y \def (aplus_inj g (S k) k 
(ASort (S n1) n0) H12) in (le_Sx_x k (eq_ind_r nat k (\lambda (n4: nat).(le 
n4 k)) (le_n k) (S k) H_y) P)))) n3 (sym_eq nat n3 n0 H10))) h2 (sym_eq nat 
h2 (S n1) H9))) H8))) n2 (sym_eq nat n2 n0 H6))) h1 (sym_eq nat h1 n1 H5))) 
H4)) H3 H1))) | (leq_head a1 a2 H1 a3 a4 H2) \Rightarrow (\lambda (H3: (eq A 
(AHead a1 a3) (ASort n1 n0))).(\lambda (H4: (eq A (AHead a2 a4) (ASort (S n1) 
n0))).((let H5 \def (eq_ind A (AHead a1 a3) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ 
_) \Rightarrow True])) I (ASort n1 n0) H3) in (False_ind ((eq A (AHead a2 a4) 
(ASort (S n1) n0)) \to ((leq g a1 a2) \to ((leq g a3 a4) \to P))) H5)) H4 H1 
H2)))]) in (H1 (refl_equal A (ASort n1 n0)) (refl_equal A (ASort (S n1) 
n0))))))) n H))))) (\lambda (a0: A).(\lambda (_: (((leq g (asucc g a0) a0) 
\to (\forall (P: Prop).P)))).(\lambda (a1: A).(\lambda (H0: (((leq g (asucc g 
a1) a1) \to (\forall (P: Prop).P)))).(\lambda (H1: (leq g (AHead a0 (asucc g 
a1)) (AHead a0 a1))).(\lambda (P: Prop).(let H2 \def (match H1 in leq return 
(\lambda (a2: A).(\lambda (a3: A).(\lambda (_: (leq ? a2 a3)).((eq A a2 
(AHead a0 (asucc g a1))) \to ((eq A a3 (AHead a0 a1)) \to P))))) with 
[(leq_sort h1 h2 n1 n2 k H2) \Rightarrow (\lambda (H3: (eq A (ASort h1 n1) 
(AHead a0 (asucc g a1)))).(\lambda (H4: (eq A (ASort h2 n2) (AHead a0 
a1))).((let H5 \def (eq_ind A (ASort h1 n1) (\lambda (e: A).(match e in A 
return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) I (AHead a0 (asucc g a1)) H3) in (False_ind ((eq A 
(ASort h2 n2) (AHead a0 a1)) \to ((eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k)) \to P)) H5)) H4 H2))) | (leq_head a2 a3 H2 a4 a5 H3) 
\Rightarrow (\lambda (H4: (eq A (AHead a2 a4) (AHead a0 (asucc g 
a1)))).(\lambda (H5: (eq A (AHead a3 a5) (AHead a0 a1))).((let H6 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a4 | (AHead _ a6) \Rightarrow a6])) (AHead a2 a4) 
(AHead a0 (asucc g a1)) H4) in ((let H7 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a2 | 
(AHead a6 _) \Rightarrow a6])) (AHead a2 a4) (AHead a0 (asucc g a1)) H4) in 
(eq_ind A a0 (\lambda (a6: A).((eq A a4 (asucc g a1)) \to ((eq A (AHead a3 
a5) (AHead a0 a1)) \to ((leq g a6 a3) \to ((leq g a4 a5) \to P))))) (\lambda 
(H8: (eq A a4 (asucc g a1))).(eq_ind A (asucc g a1) (\lambda (a6: A).((eq A 
(AHead a3 a5) (AHead a0 a1)) \to ((leq g a0 a3) \to ((leq g a6 a5) \to P)))) 
(\lambda (H9: (eq A (AHead a3 a5) (AHead a0 a1))).(let H10 \def (f_equal A A 
(\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a5 | (AHead _ a6) \Rightarrow a6])) (AHead a3 a5) (AHead a0 a1) 
H9) in ((let H11 \def (f_equal A A (\lambda (e: A).(match e in A return 
(\lambda (_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead a6 _) 
\Rightarrow a6])) (AHead a3 a5) (AHead a0 a1) H9) in (eq_ind A a0 (\lambda 
(a6: A).((eq A a5 a1) \to ((leq g a0 a6) \to ((leq g (asucc g a1) a5) \to 
P)))) (\lambda (H12: (eq A a5 a1)).(eq_ind A a1 (\lambda (a6: A).((leq g a0 
a0) \to ((leq g (asucc g a1) a6) \to P))) (\lambda (_: (leq g a0 
a0)).(\lambda (H14: (leq g (asucc g a1) a1)).(H0 H14 P))) a5 (sym_eq A a5 a1 
H12))) a3 (sym_eq A a3 a0 H11))) H10))) a4 (sym_eq A a4 (asucc g a1) H8))) a2 
(sym_eq A a2 a0 H7))) H6)) H5 H2 H3)))]) in (H2 (refl_equal A (AHead a0 
(asucc g a1))) (refl_equal A (AHead a0 a1)))))))))) a)).

