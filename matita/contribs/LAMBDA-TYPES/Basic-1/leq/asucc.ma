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

include "Basic-1/leq/props.ma".

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
(* COMMENTS
Initial nodes: 1907
END *)

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
(asucc g (ASort O n0)) (asucc g (ASort O n2)))).(let H_x \def (leq_gen_sort1 
g O (next g n0) (ASort O (next g n2)) H1) in (let H2 \def H_x in (ex2_3_ind 
nat nat nat (\lambda (n3: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A 
(aplus g (ASort O (next g n0)) k) (aplus g (ASort h2 n3) k))))) (\lambda (n3: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A (ASort O (next g n2)) (ASort 
h2 n3))))) (leq g (ASort O n0) (ASort O n2)) (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort O (next g n0)) 
x2) (aplus g (ASort x1 x0) x2))).(\lambda (H4: (eq A (ASort O (next g n2)) 
(ASort x1 x0))).(let H5 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort n3 _) \Rightarrow n3 | (AHead _ _) 
\Rightarrow O])) (ASort O (next g n2)) (ASort x1 x0) H4) in ((let H6 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n3) \Rightarrow n3 | (AHead _ _) \Rightarrow ((match g with [(mk_G 
next _) \Rightarrow next]) n2)])) (ASort O (next g n2)) (ASort x1 x0) H4) in 
(\lambda (H7: (eq nat O x1)).(let H8 \def (eq_ind_r nat x1 (\lambda (n3: 
nat).(eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort n3 x0) x2))) H3 
O H7) in (let H9 \def (eq_ind_r nat x0 (\lambda (n3: nat).(eq A (aplus g 
(ASort O (next g n0)) x2) (aplus g (ASort O n3) x2))) H8 (next g n2) H6) in 
(let H10 \def (eq_ind_r A (aplus g (ASort O (next g n0)) x2) (\lambda (a: 
A).(eq A a (aplus g (ASort O (next g n2)) x2))) H9 (aplus g (ASort O n0) (S 
x2)) (aplus_sort_O_S_simpl g n0 x2)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort O (next g n2)) x2) (\lambda (a: A).(eq A (aplus g (ASort O n0) (S x2)) 
a)) H10 (aplus g (ASort O n2) (S x2)) (aplus_sort_O_S_simpl g n2 x2)) in 
(leq_sort g O O n0 n2 (S x2) H11))))))) H5))))))) H2)))) (\lambda (n3: 
nat).(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g (ASort n3 n2))) 
\to (leq g (ASort O n0) (ASort n3 n2))))).(\lambda (H1: (leq g (asucc g 
(ASort O n0)) (asucc g (ASort (S n3) n2)))).(let H_x \def (leq_gen_sort1 g O 
(next g n0) (ASort n3 n2) H1) in (let H2 \def H_x in (ex2_3_ind nat nat nat 
(\lambda (n4: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
O (next g n0)) k) (aplus g (ASort h2 n4) k))))) (\lambda (n4: nat).(\lambda 
(h2: nat).(\lambda (_: nat).(eq A (ASort n3 n2) (ASort h2 n4))))) (leq g 
(ASort O n0) (ASort (S n3) n2)) (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort O (next g n0)) 
x2) (aplus g (ASort x1 x0) x2))).(\lambda (H4: (eq A (ASort n3 n2) (ASort x1 
x0))).(let H5 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort n4 _) \Rightarrow n4 | (AHead _ _) 
\Rightarrow n3])) (ASort n3 n2) (ASort x1 x0) H4) in ((let H6 \def (f_equal A 
nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ 
n4) \Rightarrow n4 | (AHead _ _) \Rightarrow n2])) (ASort n3 n2) (ASort x1 
x0) H4) in (\lambda (H7: (eq nat n3 x1)).(let H8 \def (eq_ind_r nat x1 
(\lambda (n4: nat).(eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort 
n4 x0) x2))) H3 n3 H7) in (let H9 \def (eq_ind_r nat x0 (\lambda (n4: 
nat).(eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort n3 n4) x2))) H8 
n2 H6) in (let H10 \def (eq_ind_r A (aplus g (ASort O (next g n0)) x2) 
(\lambda (a: A).(eq A a (aplus g (ASort n3 n2) x2))) H9 (aplus g (ASort O n0) 
(S x2)) (aplus_sort_O_S_simpl g n0 x2)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort n3 n2) x2) (\lambda (a: A).(eq A (aplus g (ASort O n0) (S x2)) a)) H10 
(aplus g (ASort (S n3) n2) (S x2)) (aplus_sort_S_S_simpl g n2 n3 x2)) in 
(leq_sort g O (S n3) n0 n2 (S x2) H11))))))) H5))))))) H2)))))) n1 H0)) 
(\lambda (n3: nat).(\lambda (IHn: (((leq g (asucc g (ASort n3 n0)) (asucc g 
(ASort n1 n2))) \to (leq g (ASort n3 n0) (ASort n1 n2))))).(\lambda (H0: (leq 
g (asucc g (ASort (S n3) n0)) (asucc g (ASort n1 n2)))).(nat_ind (\lambda 
(n4: nat).((leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n4 n2))) \to 
((((leq g (asucc g (ASort n3 n0)) (asucc g (ASort n4 n2))) \to (leq g (ASort 
n3 n0) (ASort n4 n2)))) \to (leq g (ASort (S n3) n0) (ASort n4 n2))))) 
(\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort O 
n2)))).(\lambda (_: (((leq g (asucc g (ASort n3 n0)) (asucc g (ASort O n2))) 
\to (leq g (ASort n3 n0) (ASort O n2))))).(let H_x \def (leq_gen_sort1 g n3 
n0 (ASort O (next g n2)) H1) in (let H2 \def H_x in (ex2_3_ind nat nat nat 
(\lambda (n4: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
n3 n0) k) (aplus g (ASort h2 n4) k))))) (\lambda (n4: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A (ASort O (next g n2)) (ASort h2 n4))))) (leq g 
(ASort (S n3) n0) (ASort O n2)) (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort n3 n0) x2) (aplus 
g (ASort x1 x0) x2))).(\lambda (H4: (eq A (ASort O (next g n2)) (ASort x1 
x0))).(let H5 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort n4 _) \Rightarrow n4 | (AHead _ _) 
\Rightarrow O])) (ASort O (next g n2)) (ASort x1 x0) H4) in ((let H6 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n4) \Rightarrow n4 | (AHead _ _) \Rightarrow ((match g with [(mk_G 
next _) \Rightarrow next]) n2)])) (ASort O (next g n2)) (ASort x1 x0) H4) in 
(\lambda (H7: (eq nat O x1)).(let H8 \def (eq_ind_r nat x1 (\lambda (n4: 
nat).(eq A (aplus g (ASort n3 n0) x2) (aplus g (ASort n4 x0) x2))) H3 O H7) 
in (let H9 \def (eq_ind_r nat x0 (\lambda (n4: nat).(eq A (aplus g (ASort n3 
n0) x2) (aplus g (ASort O n4) x2))) H8 (next g n2) H6) in (let H10 \def 
(eq_ind_r A (aplus g (ASort n3 n0) x2) (\lambda (a: A).(eq A a (aplus g 
(ASort O (next g n2)) x2))) H9 (aplus g (ASort (S n3) n0) (S x2)) 
(aplus_sort_S_S_simpl g n0 n3 x2)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort O (next g n2)) x2) (\lambda (a: A).(eq A (aplus g (ASort (S n3) n0) (S 
x2)) a)) H10 (aplus g (ASort O n2) (S x2)) (aplus_sort_O_S_simpl g n2 x2)) in 
(leq_sort g (S n3) O n0 n2 (S x2) H11))))))) H5))))))) H2))))) (\lambda (n4: 
nat).(\lambda (_: (((leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort n4 
n2))) \to ((((leq g (asucc g (ASort n3 n0)) (asucc g (ASort n4 n2))) \to (leq 
g (ASort n3 n0) (ASort n4 n2)))) \to (leq g (ASort (S n3) n0) (ASort n4 
n2)))))).(\lambda (H1: (leq g (asucc g (ASort (S n3) n0)) (asucc g (ASort (S 
n4) n2)))).(\lambda (_: (((leq g (asucc g (ASort n3 n0)) (asucc g (ASort (S 
n4) n2))) \to (leq g (ASort n3 n0) (ASort (S n4) n2))))).(let H_x \def 
(leq_gen_sort1 g n3 n0 (ASort n4 n2) H1) in (let H2 \def H_x in (ex2_3_ind 
nat nat nat (\lambda (n5: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A 
(aplus g (ASort n3 n0) k) (aplus g (ASort h2 n5) k))))) (\lambda (n5: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A (ASort n4 n2) (ASort h2 
n5))))) (leq g (ASort (S n3) n0) (ASort (S n4) n2)) (\lambda (x0: 
nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g 
(ASort n3 n0) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H4: (eq A (ASort n4 
n2) (ASort x1 x0))).(let H5 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort n5 _) \Rightarrow n5 | (AHead _ _) 
\Rightarrow n4])) (ASort n4 n2) (ASort x1 x0) H4) in ((let H6 \def (f_equal A 
nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ 
n5) \Rightarrow n5 | (AHead _ _) \Rightarrow n2])) (ASort n4 n2) (ASort x1 
x0) H4) in (\lambda (H7: (eq nat n4 x1)).(let H8 \def (eq_ind_r nat x1 
(\lambda (n5: nat).(eq A (aplus g (ASort n3 n0) x2) (aplus g (ASort n5 x0) 
x2))) H3 n4 H7) in (let H9 \def (eq_ind_r nat x0 (\lambda (n5: nat).(eq A 
(aplus g (ASort n3 n0) x2) (aplus g (ASort n4 n5) x2))) H8 n2 H6) in (let H10 
\def (eq_ind_r A (aplus g (ASort n3 n0) x2) (\lambda (a: A).(eq A a (aplus g 
(ASort n4 n2) x2))) H9 (aplus g (ASort (S n3) n0) (S x2)) 
(aplus_sort_S_S_simpl g n0 n3 x2)) in (let H11 \def (eq_ind_r A (aplus g 
(ASort n4 n2) x2) (\lambda (a: A).(eq A (aplus g (ASort (S n3) n0) (S x2)) 
a)) H10 (aplus g (ASort (S n4) n2) (S x2)) (aplus_sort_S_S_simpl g n2 n4 x2)) 
in (leq_sort g (S n3) (S n4) n0 n2 (S x2) H11))))))) H5))))))) H2))))))) n1 
H0 IHn)))) n H)))) (\lambda (a: A).(\lambda (H: (((leq g (asucc g (ASort n 
n0)) (asucc g a)) \to (leq g (ASort n n0) a)))).(\lambda (a0: A).(\lambda 
(H0: (((leq g (asucc g (ASort n n0)) (asucc g a0)) \to (leq g (ASort n n0) 
a0)))).(\lambda (H1: (leq g (asucc g (ASort n n0)) (asucc g (AHead a 
a0)))).(nat_ind (\lambda (n1: nat).((((leq g (asucc g (ASort n1 n0)) (asucc g 
a)) \to (leq g (ASort n1 n0) a))) \to ((((leq g (asucc g (ASort n1 n0)) 
(asucc g a0)) \to (leq g (ASort n1 n0) a0))) \to ((leq g (asucc g (ASort n1 
n0)) (asucc g (AHead a a0))) \to (leq g (ASort n1 n0) (AHead a a0)))))) 
(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g a)) \to (leq g (ASort O 
n0) a)))).(\lambda (_: (((leq g (asucc g (ASort O n0)) (asucc g a0)) \to (leq 
g (ASort O n0) a0)))).(\lambda (H4: (leq g (asucc g (ASort O n0)) (asucc g 
(AHead a a0)))).(let H_x \def (leq_gen_sort1 g O (next g n0) (AHead a (asucc 
g a0)) H4) in (let H5 \def H_x in (ex2_3_ind nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort O (next g 
n0)) k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A (AHead a (asucc g a0)) (ASort h2 n2))))) (leq g 
(ASort O n0) (AHead a a0)) (\lambda (x0: nat).(\lambda (x1: nat).(\lambda 
(x2: nat).(\lambda (_: (eq A (aplus g (ASort O (next g n0)) x2) (aplus g 
(ASort x1 x0) x2))).(\lambda (H7: (eq A (AHead a (asucc g a0)) (ASort x1 
x0))).(let H8 \def (eq_ind A (AHead a (asucc g a0)) (\lambda (ee: A).(match 
ee in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) I (ASort x1 x0) H7) in (False_ind (leq g 
(ASort O n0) (AHead a a0)) H8))))))) H5)))))) (\lambda (n1: nat).(\lambda (_: 
(((((leq g (asucc g (ASort n1 n0)) (asucc g a)) \to (leq g (ASort n1 n0) a))) 
\to ((((leq g (asucc g (ASort n1 n0)) (asucc g a0)) \to (leq g (ASort n1 n0) 
a0))) \to ((leq g (asucc g (ASort n1 n0)) (asucc g (AHead a a0))) \to (leq g 
(ASort n1 n0) (AHead a a0))))))).(\lambda (_: (((leq g (asucc g (ASort (S n1) 
n0)) (asucc g a)) \to (leq g (ASort (S n1) n0) a)))).(\lambda (_: (((leq g 
(asucc g (ASort (S n1) n0)) (asucc g a0)) \to (leq g (ASort (S n1) n0) 
a0)))).(\lambda (H4: (leq g (asucc g (ASort (S n1) n0)) (asucc g (AHead a 
a0)))).(let H_x \def (leq_gen_sort1 g n1 n0 (AHead a (asucc g a0)) H4) in 
(let H5 \def H_x in (ex2_3_ind nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort n1 n0) k) (aplus g (ASort h2 n2) 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A (AHead a 
(asucc g a0)) (ASort h2 n2))))) (leq g (ASort (S n1) n0) (AHead a a0)) 
(\lambda (x0: nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (_: (eq A 
(aplus g (ASort n1 n0) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H7: (eq A 
(AHead a (asucc g a0)) (ASort x1 x0))).(let H8 \def (eq_ind A (AHead a (asucc 
g a0)) (\lambda (ee: A).(match ee in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort x1 
x0) H7) in (False_ind (leq g (ASort (S n1) n0) (AHead a a0)) H8))))))) 
H5)))))))) n H H0 H1)))))) a2)))) (\lambda (a: A).(\lambda (_: ((\forall (a2: 
A).((leq g (asucc g a) (asucc g a2)) \to (leq g a a2))))).(\lambda (a0: 
A).(\lambda (H0: ((\forall (a2: A).((leq g (asucc g a0) (asucc g a2)) \to 
(leq g a0 a2))))).(\lambda (a2: A).(A_ind (\lambda (a3: A).((leq g (asucc g 
(AHead a a0)) (asucc g a3)) \to (leq g (AHead a a0) a3))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (H1: (leq g (asucc g (AHead a a0)) (asucc g 
(ASort n n0)))).(nat_ind (\lambda (n1: nat).((leq g (asucc g (AHead a a0)) 
(asucc g (ASort n1 n0))) \to (leq g (AHead a a0) (ASort n1 n0)))) (\lambda 
(H2: (leq g (asucc g (AHead a a0)) (asucc g (ASort O n0)))).(let H_x \def 
(leq_gen_head1 g a (asucc g a0) (ASort O (next g n0)) H2) in (let H3 \def H_x 
in (ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq g a a3))) (\lambda 
(_: A).(\lambda (a4: A).(leq g (asucc g a0) a4))) (\lambda (a3: A).(\lambda 
(a4: A).(eq A (ASort O (next g n0)) (AHead a3 a4)))) (leq g (AHead a a0) 
(ASort O n0)) (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g a 
x0)).(\lambda (_: (leq g (asucc g a0) x1)).(\lambda (H6: (eq A (ASort O (next 
g n0)) (AHead x0 x1))).(let H7 \def (eq_ind A (ASort O (next g n0)) (\lambda 
(ee: A).(match ee in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead x0 x1) H6) in 
(False_ind (leq g (AHead a a0) (ASort O n0)) H7))))))) H3)))) (\lambda (n1: 
nat).(\lambda (_: (((leq g (asucc g (AHead a a0)) (asucc g (ASort n1 n0))) 
\to (leq g (AHead a a0) (ASort n1 n0))))).(\lambda (H2: (leq g (asucc g 
(AHead a a0)) (asucc g (ASort (S n1) n0)))).(let H_x \def (leq_gen_head1 g a 
(asucc g a0) (ASort n1 n0) H2) in (let H3 \def H_x in (ex3_2_ind A A (\lambda 
(a3: A).(\lambda (_: A).(leq g a a3))) (\lambda (_: A).(\lambda (a4: A).(leq 
g (asucc g a0) a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort n1 n0) 
(AHead a3 a4)))) (leq g (AHead a a0) (ASort (S n1) n0)) (\lambda (x0: 
A).(\lambda (x1: A).(\lambda (_: (leq g a x0)).(\lambda (_: (leq g (asucc g 
a0) x1)).(\lambda (H6: (eq A (ASort n1 n0) (AHead x0 x1))).(let H7 \def 
(eq_ind A (ASort n1 n0) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead x0 x1) H6) in (False_ind (leq g (AHead a a0) (ASort (S n1) 
n0)) H7))))))) H3)))))) n H1)))) (\lambda (a3: A).(\lambda (_: (((leq g 
(asucc g (AHead a a0)) (asucc g a3)) \to (leq g (AHead a a0) a3)))).(\lambda 
(a4: A).(\lambda (_: (((leq g (asucc g (AHead a a0)) (asucc g a4)) \to (leq g 
(AHead a a0) a4)))).(\lambda (H3: (leq g (asucc g (AHead a a0)) (asucc g 
(AHead a3 a4)))).(let H_x \def (leq_gen_head1 g a (asucc g a0) (AHead a3 
(asucc g a4)) H3) in (let H4 \def H_x in (ex3_2_ind A A (\lambda (a5: 
A).(\lambda (_: A).(leq g a a5))) (\lambda (_: A).(\lambda (a6: A).(leq g 
(asucc g a0) a6))) (\lambda (a5: A).(\lambda (a6: A).(eq A (AHead a3 (asucc g 
a4)) (AHead a5 a6)))) (leq g (AHead a a0) (AHead a3 a4)) (\lambda (x0: 
A).(\lambda (x1: A).(\lambda (H5: (leq g a x0)).(\lambda (H6: (leq g (asucc g 
a0) x1)).(\lambda (H7: (eq A (AHead a3 (asucc g a4)) (AHead x0 x1))).(let H8 
\def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a3 | (AHead a5 _) \Rightarrow a5])) (AHead a3 
(asucc g a4)) (AHead x0 x1) H7) in ((let H9 \def (f_equal A A (\lambda (e: 
A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow 
((let rec asucc (g0: G) (l: A) on l: A \def (match l with [(ASort n0 n) 
\Rightarrow (match n0 with [O \Rightarrow (ASort O (next g0 n)) | (S h) 
\Rightarrow (ASort h n)]) | (AHead a5 a6) \Rightarrow (AHead a5 (asucc g0 
a6))]) in asucc) g a4) | (AHead _ a5) \Rightarrow a5])) (AHead a3 (asucc g 
a4)) (AHead x0 x1) H7) in (\lambda (H10: (eq A a3 x0)).(let H11 \def 
(eq_ind_r A x1 (\lambda (a5: A).(leq g (asucc g a0) a5)) H6 (asucc g a4) H9) 
in (let H12 \def (eq_ind_r A x0 (\lambda (a5: A).(leq g a a5)) H5 a3 H10) in 
(leq_head g a a3 H12 a0 a4 (H0 a4 H11)))))) H8))))))) H4)))))))) a2)))))) 
a1)).
(* COMMENTS
Initial nodes: 4697
END *)

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
(* COMMENTS
Initial nodes: 221
END *)

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
(AHead (ASort O n0) a2) (ASort O (next g n0)))).(let H_x \def (leq_gen_head1 
g (ASort O n0) a2 (ASort O (next g n0)) H0) in (let H1 \def H_x in (ex3_2_ind 
A A (\lambda (a3: A).(\lambda (_: A).(leq g (ASort O n0) a3))) (\lambda (_: 
A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A 
(ASort O (next g n0)) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (_: (leq g (ASort O n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda 
(H4: (eq A (ASort O (next g n0)) (AHead x0 x1))).(let H5 \def (eq_ind A 
(ASort O (next g n0)) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead x0 x1) H4) in (False_ind P H5))))))) H1)))) (\lambda (n1: 
nat).(\lambda (_: (((leq g (AHead (ASort n1 n0) a2) (match n1 with [O 
\Rightarrow (ASort O (next g n0)) | (S h) \Rightarrow (ASort h n0)])) \to 
P))).(\lambda (H0: (leq g (AHead (ASort (S n1) n0) a2) (ASort n1 n0))).(let 
H_x \def (leq_gen_head1 g (ASort (S n1) n0) a2 (ASort n1 n0) H0) in (let H1 
\def H_x in (ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq g (ASort (S 
n1) n0) a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A (ASort n1 n0) (AHead a3 a4)))) P (\lambda (x0: 
A).(\lambda (x1: A).(\lambda (_: (leq g (ASort (S n1) n0) x0)).(\lambda (_: 
(leq g a2 x1)).(\lambda (H4: (eq A (ASort n1 n0) (AHead x0 x1))).(let H5 \def 
(eq_ind A (ASort n1 n0) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead x0 x1) H4) in (False_ind P H5))))))) H1)))))) n H)))))) 
(\lambda (a: A).(\lambda (_: ((\forall (a2: A).((leq g (AHead a a2) (asucc g 
a)) \to (\forall (P: Prop).P))))).(\lambda (a0: A).(\lambda (_: ((\forall 
(a2: A).((leq g (AHead a0 a2) (asucc g a0)) \to (\forall (P: 
Prop).P))))).(\lambda (a2: A).(\lambda (H1: (leq g (AHead (AHead a a0) a2) 
(AHead a (asucc g a0)))).(\lambda (P: Prop).(let H_x \def (leq_gen_head1 g 
(AHead a a0) a2 (AHead a (asucc g a0)) H1) in (let H2 \def H_x in (ex3_2_ind 
A A (\lambda (a3: A).(\lambda (_: A).(leq g (AHead a a0) a3))) (\lambda (_: 
A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A 
(AHead a (asucc g a0)) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (leq g (AHead a a0) x0)).(\lambda (H4: (leq g a2 
x1)).(\lambda (H5: (eq A (AHead a (asucc g a0)) (AHead x0 x1))).(let H6 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a | (AHead a3 _) \Rightarrow a3])) (AHead a (asucc g 
a0)) (AHead x0 x1) H5) in ((let H7 \def (f_equal A A (\lambda (e: A).(match e 
in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow ((let rec asucc 
(g0: G) (l: A) on l: A \def (match l with [(ASort n0 n) \Rightarrow (match n0 
with [O \Rightarrow (ASort O (next g0 n)) | (S h) \Rightarrow (ASort h n)]) | 
(AHead a3 a4) \Rightarrow (AHead a3 (asucc g0 a4))]) in asucc) g a0) | (AHead 
_ a3) \Rightarrow a3])) (AHead a (asucc g a0)) (AHead x0 x1) H5) in (\lambda 
(H8: (eq A a x0)).(let H9 \def (eq_ind_r A x1 (\lambda (a3: A).(leq g a2 a3)) 
H4 (asucc g a0) H7) in (let H10 \def (eq_ind_r A x0 (\lambda (a3: A).(leq g 
(AHead a a0) a3)) H3 a H8) in (leq_ahead_false_1 g a a0 H10 P))))) H6))))))) 
H2)))))))))) a1)).
(* COMMENTS
Initial nodes: 927
END *)

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
(leq g (ASort O (next g n0)) (ASort O n0))).(let H_x \def (leq_gen_sort1 g O 
(next g n0) (ASort O n0) H0) in (let H1 \def H_x in (ex2_3_ind nat nat nat 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
O (next g n0)) k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda 
(h2: nat).(\lambda (_: nat).(eq A (ASort O n0) (ASort h2 n2))))) P (\lambda 
(x0: nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H2: (eq A (aplus g 
(ASort O (next g n0)) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H3: (eq A 
(ASort O n0) (ASort x1 x0))).(let H4 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort n1 _) \Rightarrow 
n1 | (AHead _ _) \Rightarrow O])) (ASort O n0) (ASort x1 x0) H3) in ((let H5 
\def (f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) 
with [(ASort _ n1) \Rightarrow n1 | (AHead _ _) \Rightarrow n0])) (ASort O 
n0) (ASort x1 x0) H3) in (\lambda (H6: (eq nat O x1)).(let H7 \def (eq_ind_r 
nat x1 (\lambda (n1: nat).(eq A (aplus g (ASort O (next g n0)) x2) (aplus g 
(ASort n1 x0) x2))) H2 O H6) in (let H8 \def (eq_ind_r nat x0 (\lambda (n1: 
nat).(eq A (aplus g (ASort O (next g n0)) x2) (aplus g (ASort O n1) x2))) H7 
n0 H5) in (let H9 \def (eq_ind_r A (aplus g (ASort O (next g n0)) x2) 
(\lambda (a0: A).(eq A a0 (aplus g (ASort O n0) x2))) H8 (aplus g (ASort O 
n0) (S x2)) (aplus_sort_O_S_simpl g n0 x2)) in (let H_y \def (aplus_inj g (S 
x2) x2 (ASort O n0) H9) in (le_Sx_x x2 (eq_ind_r nat x2 (\lambda (n1: 
nat).(le n1 x2)) (le_n x2) (S x2) H_y) P))))))) H4))))))) H1)))) (\lambda 
(n1: nat).(\lambda (_: (((leq g (match n1 with [O \Rightarrow (ASort O (next 
g n0)) | (S h) \Rightarrow (ASort h n0)]) (ASort n1 n0)) \to P))).(\lambda 
(H0: (leq g (ASort n1 n0) (ASort (S n1) n0))).(let H_x \def (leq_gen_sort1 g 
n1 n0 (ASort (S n1) n0) H0) in (let H1 \def H_x in (ex2_3_ind nat nat nat 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
n1 n0) k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A (ASort (S n1) n0) (ASort h2 n2))))) P (\lambda 
(x0: nat).(\lambda (x1: nat).(\lambda (x2: nat).(\lambda (H2: (eq A (aplus g 
(ASort n1 n0) x2) (aplus g (ASort x1 x0) x2))).(\lambda (H3: (eq A (ASort (S 
n1) n0) (ASort x1 x0))).(let H4 \def (f_equal A nat (\lambda (e: A).(match e 
in A return (\lambda (_: A).nat) with [(ASort n2 _) \Rightarrow n2 | (AHead _ 
_) \Rightarrow (S n1)])) (ASort (S n1) n0) (ASort x1 x0) H3) in ((let H5 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort _ n2) \Rightarrow n2 | (AHead _ _) \Rightarrow n0])) (ASort (S n1) 
n0) (ASort x1 x0) H3) in (\lambda (H6: (eq nat (S n1) x1)).(let H7 \def 
(eq_ind_r nat x1 (\lambda (n2: nat).(eq A (aplus g (ASort n1 n0) x2) (aplus g 
(ASort n2 x0) x2))) H2 (S n1) H6) in (let H8 \def (eq_ind_r nat x0 (\lambda 
(n2: nat).(eq A (aplus g (ASort n1 n0) x2) (aplus g (ASort (S n1) n2) x2))) 
H7 n0 H5) in (let H9 \def (eq_ind_r A (aplus g (ASort n1 n0) x2) (\lambda 
(a0: A).(eq A a0 (aplus g (ASort (S n1) n0) x2))) H8 (aplus g (ASort (S n1) 
n0) (S x2)) (aplus_sort_S_S_simpl g n0 n1 x2)) in (let H_y \def (aplus_inj g 
(S x2) x2 (ASort (S n1) n0) H9) in (le_Sx_x x2 (eq_ind_r nat x2 (\lambda (n2: 
nat).(le n2 x2)) (le_n x2) (S x2) H_y) P))))))) H4))))))) H1)))))) n H))))) 
(\lambda (a0: A).(\lambda (_: (((leq g (asucc g a0) a0) \to (\forall (P: 
Prop).P)))).(\lambda (a1: A).(\lambda (H0: (((leq g (asucc g a1) a1) \to 
(\forall (P: Prop).P)))).(\lambda (H1: (leq g (AHead a0 (asucc g a1)) (AHead 
a0 a1))).(\lambda (P: Prop).(let H_x \def (leq_gen_head1 g a0 (asucc g a1) 
(AHead a0 a1) H1) in (let H2 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g a0 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g 
(asucc g a1) a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (AHead a0 a1) 
(AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: A).(\lambda (H3: (leq g a0 
x0)).(\lambda (H4: (leq g (asucc g a1) x1)).(\lambda (H5: (eq A (AHead a0 a1) 
(AHead x0 x1))).(let H6 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead a2 _) 
\Rightarrow a2])) (AHead a0 a1) (AHead x0 x1) H5) in ((let H7 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a1 | (AHead _ a2) \Rightarrow a2])) (AHead a0 a1) (AHead x0 x1) 
H5) in (\lambda (H8: (eq A a0 x0)).(let H9 \def (eq_ind_r A x1 (\lambda (a2: 
A).(leq g (asucc g a1) a2)) H4 a1 H7) in (let H10 \def (eq_ind_r A x0 
(\lambda (a2: A).(leq g a0 a2)) H3 a0 H8) in (H0 H9 P))))) H6))))))) 
H2))))))))) a)).
(* COMMENTS
Initial nodes: 1327
END *)

