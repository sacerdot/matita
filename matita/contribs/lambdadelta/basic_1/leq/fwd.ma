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

include "Basic-1/leq/defs.ma".

theorem leq_gen_sort1:
 \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq 
g (ASort h1 n1) a2) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a2 
(ASort h2 n2))))))))))
\def
 \lambda (g: G).(\lambda (h1: nat).(\lambda (n1: nat).(\lambda (a2: 
A).(\lambda (H: (leq g (ASort h1 n1) a2)).(insert_eq A (ASort h1 n1) (\lambda 
(a: A).(leq g a a2)) (\lambda (a: A).(ex2_3 nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g a k) (aplus g (ASort 
h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A 
a2 (ASort h2 n2))))))) (\lambda (y: A).(\lambda (H0: (leq g y a2)).(leq_ind g 
(\lambda (a: A).(\lambda (a0: A).((eq A a (ASort h1 n1)) \to (ex2_3 nat nat 
nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g a 
k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A a0 (ASort h2 n2))))))))) (\lambda (h0: 
nat).(\lambda (h2: nat).(\lambda (n0: nat).(\lambda (n2: nat).(\lambda (k: 
nat).(\lambda (H1: (eq A (aplus g (ASort h0 n0) k) (aplus g (ASort h2 n2) 
k))).(\lambda (H2: (eq A (ASort h0 n0) (ASort h1 n1))).(let H3 \def (f_equal 
A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort 
n _) \Rightarrow n | (AHead _ _) \Rightarrow h0])) (ASort h0 n0) (ASort h1 
n1) H2) in ((let H4 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n0])) (ASort h0 n0) (ASort h1 n1) H2) in (\lambda (H5: (eq nat h0 
h1)).(let H6 \def (eq_ind nat n0 (\lambda (n: nat).(eq A (aplus g (ASort h0 
n) k) (aplus g (ASort h2 n2) k))) H1 n1 H4) in (eq_ind_r nat n1 (\lambda (n: 
nat).(ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (k0: 
nat).(eq A (aplus g (ASort h0 n) k0) (aplus g (ASort h3 n3) k0))))) (\lambda 
(n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A (ASort h2 n2) (ASort h3 
n3))))))) (let H7 \def (eq_ind nat h0 (\lambda (n: nat).(eq A (aplus g (ASort 
n n1) k) (aplus g (ASort h2 n2) k))) H6 h1 H5) in (eq_ind_r nat h1 (\lambda 
(n: nat).(ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda 
(k0: nat).(eq A (aplus g (ASort n n1) k0) (aplus g (ASort h3 n3) k0))))) 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A (ASort h2 n2) 
(ASort h3 n3))))))) (ex2_3_intro nat nat nat (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (k0: nat).(eq A (aplus g (ASort h1 n1) k0) (aplus g (ASort h3 
n3) k0))))) (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A 
(ASort h2 n2) (ASort h3 n3))))) n2 h2 k H7 (refl_equal A (ASort h2 n2))) h0 
H5)) n0 H4)))) H3))))))))) (\lambda (a1: A).(\lambda (a3: A).(\lambda (_: 
(leq g a1 a3)).(\lambda (_: (((eq A a1 (ASort h1 n1)) \to (ex2_3 nat nat nat 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g a1 k) 
(aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A a3 (ASort h2 n2))))))))).(\lambda (a4: A).(\lambda (a5: 
A).(\lambda (_: (leq g a4 a5)).(\lambda (_: (((eq A a4 (ASort h1 n1)) \to 
(ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(eq A (aplus g a4 k) (aplus g (ASort h2 n2) k))))) (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a5 (ASort h2 
n2))))))))).(\lambda (H5: (eq A (AHead a1 a4) (ASort h1 n1))).(let H6 \def 
(eq_ind A (AHead a1 a4) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort h1 n1) H5) in (False_ind (ex2_3 nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (AHead a1 a4) k) 
(aplus g (ASort h2 n2) k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A (AHead a3 a5) (ASort h2 n2)))))) H6))))))))))) y a2 H0))) 
H))))).
(* COMMENTS
Initial nodes: 913
END *)

theorem leq_gen_head1:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g 
(AHead a1 a2) a) \to (ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g a1 
a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(\lambda 
(H: (leq g (AHead a1 a2) a)).(insert_eq A (AHead a1 a2) (\lambda (a0: A).(leq 
g a0 a)) (\lambda (_: A).(ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g 
a1 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))) (\lambda (y: A).(\lambda (H0: 
(leq g y a)).(leq_ind g (\lambda (a0: A).(\lambda (a3: A).((eq A a0 (AHead a1 
a2)) \to (ex3_2 A A (\lambda (a4: A).(\lambda (_: A).(leq g a1 a4))) (\lambda 
(_: A).(\lambda (a5: A).(leq g a2 a5))) (\lambda (a4: A).(\lambda (a5: A).(eq 
A a3 (AHead a4 a5)))))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (H2: (eq A (ASort h1 n1) 
(AHead a1 a2))).(let H3 \def (eq_ind A (ASort h1 n1) (\lambda (ee: A).(match 
ee in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | 
(AHead _ _) \Rightarrow False])) I (AHead a1 a2) H2) in (False_ind (ex3_2 A A 
(\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) (\lambda (_: A).(\lambda 
(a4: A).(leq g a2 a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort h2 n2) 
(AHead a3 a4))))) H3))))))))) (\lambda (a0: A).(\lambda (a3: A).(\lambda (H1: 
(leq g a0 a3)).(\lambda (H2: (((eq A a0 (AHead a1 a2)) \to (ex3_2 A A 
(\lambda (a4: A).(\lambda (_: A).(leq g a1 a4))) (\lambda (_: A).(\lambda 
(a5: A).(leq g a2 a5))) (\lambda (a4: A).(\lambda (a5: A).(eq A a3 (AHead a4 
a5)))))))).(\lambda (a4: A).(\lambda (a5: A).(\lambda (H3: (leq g a4 
a5)).(\lambda (H4: (((eq A a4 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a6: 
A).(\lambda (_: A).(leq g a1 a6))) (\lambda (_: A).(\lambda (a7: A).(leq g a2 
a7))) (\lambda (a6: A).(\lambda (a7: A).(eq A a5 (AHead a6 
a7)))))))).(\lambda (H5: (eq A (AHead a0 a4) (AHead a1 a2))).(let H6 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a0 | (AHead a6 _) \Rightarrow a6])) (AHead a0 a4) 
(AHead a1 a2) H5) in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a4 | (AHead _ a6) 
\Rightarrow a6])) (AHead a0 a4) (AHead a1 a2) H5) in (\lambda (H8: (eq A a0 
a1)).(let H9 \def (eq_ind A a4 (\lambda (a6: A).((eq A a6 (AHead a1 a2)) \to 
(ex3_2 A A (\lambda (a7: A).(\lambda (_: A).(leq g a1 a7))) (\lambda (_: 
A).(\lambda (a8: A).(leq g a2 a8))) (\lambda (a7: A).(\lambda (a8: A).(eq A 
a5 (AHead a7 a8))))))) H4 a2 H7) in (let H10 \def (eq_ind A a4 (\lambda (a6: 
A).(leq g a6 a5)) H3 a2 H7) in (let H11 \def (eq_ind A a0 (\lambda (a6: 
A).((eq A a6 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a7: A).(\lambda (_: 
A).(leq g a1 a7))) (\lambda (_: A).(\lambda (a8: A).(leq g a2 a8))) (\lambda 
(a7: A).(\lambda (a8: A).(eq A a3 (AHead a7 a8))))))) H2 a1 H8) in (let H12 
\def (eq_ind A a0 (\lambda (a6: A).(leq g a6 a3)) H1 a1 H8) in (ex3_2_intro A 
A (\lambda (a6: A).(\lambda (_: A).(leq g a1 a6))) (\lambda (_: A).(\lambda 
(a7: A).(leq g a2 a7))) (\lambda (a6: A).(\lambda (a7: A).(eq A (AHead a3 a5) 
(AHead a6 a7)))) a3 a5 H12 H10 (refl_equal A (AHead a3 a5))))))))) 
H6))))))))))) y a H0))) H))))).
(* COMMENTS
Initial nodes: 797
END *)

theorem leq_gen_sort2:
 \forall (g: G).(\forall (h1: nat).(\forall (n1: nat).(\forall (a2: A).((leq 
g a2 (ASort h1 n1)) \to (ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (k: nat).(eq A (aplus g (ASort h2 n2) k) (aplus g (ASort h1 n1) 
k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a2 
(ASort h2 n2))))))))))
\def
 \lambda (g: G).(\lambda (h1: nat).(\lambda (n1: nat).(\lambda (a2: 
A).(\lambda (H: (leq g a2 (ASort h1 n1))).(insert_eq A (ASort h1 n1) (\lambda 
(a: A).(leq g a2 a)) (\lambda (a: A).(ex2_3 nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h2 n2) k) 
(aplus g a k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (_: nat).(eq 
A a2 (ASort h2 n2))))))) (\lambda (y: A).(\lambda (H0: (leq g a2 y)).(leq_ind 
g (\lambda (a: A).(\lambda (a0: A).((eq A a0 (ASort h1 n1)) \to (ex2_3 nat 
nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus 
g (ASort h2 n2) k) (aplus g a0 k))))) (\lambda (n2: nat).(\lambda (h2: 
nat).(\lambda (_: nat).(eq A a (ASort h2 n2))))))))) (\lambda (h0: 
nat).(\lambda (h2: nat).(\lambda (n0: nat).(\lambda (n2: nat).(\lambda (k: 
nat).(\lambda (H1: (eq A (aplus g (ASort h0 n0) k) (aplus g (ASort h2 n2) 
k))).(\lambda (H2: (eq A (ASort h2 n2) (ASort h1 n1))).(let H3 \def (f_equal 
A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort 
n _) \Rightarrow n | (AHead _ _) \Rightarrow h2])) (ASort h2 n2) (ASort h1 
n1) H2) in ((let H4 \def (f_equal A nat (\lambda (e: A).(match e in A return 
(\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n2])) (ASort h2 n2) (ASort h1 n1) H2) in (\lambda (H5: (eq nat h2 
h1)).(let H6 \def (eq_ind nat n2 (\lambda (n: nat).(eq A (aplus g (ASort h0 
n0) k) (aplus g (ASort h2 n) k))) H1 n1 H4) in (eq_ind_r nat n1 (\lambda (n: 
nat).(ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (k0: 
nat).(eq A (aplus g (ASort h3 n3) k0) (aplus g (ASort h2 n) k0))))) (\lambda 
(n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A (ASort h0 n0) (ASort h3 
n3))))))) (let H7 \def (eq_ind nat h2 (\lambda (n: nat).(eq A (aplus g (ASort 
h0 n0) k) (aplus g (ASort n n1) k))) H6 h1 H5) in (eq_ind_r nat h1 (\lambda 
(n: nat).(ex2_3 nat nat nat (\lambda (n3: nat).(\lambda (h3: nat).(\lambda 
(k0: nat).(eq A (aplus g (ASort h3 n3) k0) (aplus g (ASort n n1) k0))))) 
(\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A (ASort h0 n0) 
(ASort h3 n3))))))) (ex2_3_intro nat nat nat (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (k0: nat).(eq A (aplus g (ASort h3 n3) k0) (aplus g (ASort h1 
n1) k0))))) (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A 
(ASort h0 n0) (ASort h3 n3))))) n0 h0 k H7 (refl_equal A (ASort h0 n0))) h2 
H5)) n2 H4)))) H3))))))))) (\lambda (a1: A).(\lambda (a3: A).(\lambda (_: 
(leq g a1 a3)).(\lambda (_: (((eq A a3 (ASort h1 n1)) \to (ex2_3 nat nat nat 
(\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort 
h2 n2) k) (aplus g a3 k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A a1 (ASort h2 n2))))))))).(\lambda (a4: A).(\lambda (a5: 
A).(\lambda (_: (leq g a4 a5)).(\lambda (_: (((eq A a5 (ASort h1 n1)) \to 
(ex2_3 nat nat nat (\lambda (n2: nat).(\lambda (h2: nat).(\lambda (k: 
nat).(eq A (aplus g (ASort h2 n2) k) (aplus g a5 k))))) (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (_: nat).(eq A a4 (ASort h2 
n2))))))))).(\lambda (H5: (eq A (AHead a3 a5) (ASort h1 n1))).(let H6 \def 
(eq_ind A (AHead a3 a5) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow 
True])) I (ASort h1 n1) H5) in (False_ind (ex2_3 nat nat nat (\lambda (n2: 
nat).(\lambda (h2: nat).(\lambda (k: nat).(eq A (aplus g (ASort h2 n2) k) 
(aplus g (AHead a3 a5) k))))) (\lambda (n2: nat).(\lambda (h2: nat).(\lambda 
(_: nat).(eq A (AHead a1 a4) (ASort h2 n2)))))) H6))))))))))) a2 y H0))) 
H))))).
(* COMMENTS
Initial nodes: 913
END *)

theorem leq_gen_head2:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((leq g a 
(AHead a1 a2)) \to (ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g a3 
a1))) (\lambda (_: A).(\lambda (a4: A).(leq g a4 a2))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(\lambda 
(H: (leq g a (AHead a1 a2))).(insert_eq A (AHead a1 a2) (\lambda (a0: A).(leq 
g a a0)) (\lambda (_: A).(ex3_2 A A (\lambda (a3: A).(\lambda (_: A).(leq g 
a3 a1))) (\lambda (_: A).(\lambda (a4: A).(leq g a4 a2))) (\lambda (a3: 
A).(\lambda (a4: A).(eq A a (AHead a3 a4)))))) (\lambda (y: A).(\lambda (H0: 
(leq g a y)).(leq_ind g (\lambda (a0: A).(\lambda (a3: A).((eq A a3 (AHead a1 
a2)) \to (ex3_2 A A (\lambda (a4: A).(\lambda (_: A).(leq g a4 a1))) (\lambda 
(_: A).(\lambda (a5: A).(leq g a5 a2))) (\lambda (a4: A).(\lambda (a5: A).(eq 
A a0 (AHead a4 a5)))))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (H2: (eq A (ASort h2 n2) 
(AHead a1 a2))).(let H3 \def (eq_ind A (ASort h2 n2) (\lambda (ee: A).(match 
ee in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | 
(AHead _ _) \Rightarrow False])) I (AHead a1 a2) H2) in (False_ind (ex3_2 A A 
(\lambda (a3: A).(\lambda (_: A).(leq g a3 a1))) (\lambda (_: A).(\lambda 
(a4: A).(leq g a4 a2))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort h1 n1) 
(AHead a3 a4))))) H3))))))))) (\lambda (a0: A).(\lambda (a3: A).(\lambda (H1: 
(leq g a0 a3)).(\lambda (H2: (((eq A a3 (AHead a1 a2)) \to (ex3_2 A A 
(\lambda (a4: A).(\lambda (_: A).(leq g a4 a1))) (\lambda (_: A).(\lambda 
(a5: A).(leq g a5 a2))) (\lambda (a4: A).(\lambda (a5: A).(eq A a0 (AHead a4 
a5)))))))).(\lambda (a4: A).(\lambda (a5: A).(\lambda (H3: (leq g a4 
a5)).(\lambda (H4: (((eq A a5 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a6: 
A).(\lambda (_: A).(leq g a6 a1))) (\lambda (_: A).(\lambda (a7: A).(leq g a7 
a2))) (\lambda (a6: A).(\lambda (a7: A).(eq A a4 (AHead a6 
a7)))))))).(\lambda (H5: (eq A (AHead a3 a5) (AHead a1 a2))).(let H6 \def 
(f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with 
[(ASort _ _) \Rightarrow a3 | (AHead a6 _) \Rightarrow a6])) (AHead a3 a5) 
(AHead a1 a2) H5) in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A 
return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a5 | (AHead _ a6) 
\Rightarrow a6])) (AHead a3 a5) (AHead a1 a2) H5) in (\lambda (H8: (eq A a3 
a1)).(let H9 \def (eq_ind A a5 (\lambda (a6: A).((eq A a6 (AHead a1 a2)) \to 
(ex3_2 A A (\lambda (a7: A).(\lambda (_: A).(leq g a7 a1))) (\lambda (_: 
A).(\lambda (a8: A).(leq g a8 a2))) (\lambda (a7: A).(\lambda (a8: A).(eq A 
a4 (AHead a7 a8))))))) H4 a2 H7) in (let H10 \def (eq_ind A a5 (\lambda (a6: 
A).(leq g a4 a6)) H3 a2 H7) in (let H11 \def (eq_ind A a3 (\lambda (a6: 
A).((eq A a6 (AHead a1 a2)) \to (ex3_2 A A (\lambda (a7: A).(\lambda (_: 
A).(leq g a7 a1))) (\lambda (_: A).(\lambda (a8: A).(leq g a8 a2))) (\lambda 
(a7: A).(\lambda (a8: A).(eq A a0 (AHead a7 a8))))))) H2 a1 H8) in (let H12 
\def (eq_ind A a3 (\lambda (a6: A).(leq g a0 a6)) H1 a1 H8) in (ex3_2_intro A 
A (\lambda (a6: A).(\lambda (_: A).(leq g a6 a1))) (\lambda (_: A).(\lambda 
(a7: A).(leq g a7 a2))) (\lambda (a6: A).(\lambda (a7: A).(eq A (AHead a0 a4) 
(AHead a6 a7)))) a0 a4 H12 H10 (refl_equal A (AHead a0 a4))))))))) 
H6))))))))))) a y H0))) H))))).
(* COMMENTS
Initial nodes: 797
END *)

