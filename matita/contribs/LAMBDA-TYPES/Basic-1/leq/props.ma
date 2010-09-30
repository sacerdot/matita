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

include "Basic-1/leq/fwd.ma".

include "Basic-1/aplus/props.ma".

theorem ahead_inj_snd:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a3: A).(\forall 
(a4: A).((leq g (AHead a1 a2) (AHead a3 a4)) \to (leq g a2 a4))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda 
(a4: A).(\lambda (H: (leq g (AHead a1 a2) (AHead a3 a4))).(let H_x \def 
(leq_gen_head1 g a1 a2 (AHead a3 a4) H) in (let H0 \def H_x in (ex3_2_ind A A 
(\lambda (a5: A).(\lambda (_: A).(leq g a1 a5))) (\lambda (_: A).(\lambda 
(a6: A).(leq g a2 a6))) (\lambda (a5: A).(\lambda (a6: A).(eq A (AHead a3 a4) 
(AHead a5 a6)))) (leq g a2 a4) (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H1: (leq g a1 x0)).(\lambda (H2: (leq g a2 x1)).(\lambda (H3: (eq A (AHead 
a3 a4) (AHead x0 x1))).(let H4 \def (f_equal A A (\lambda (e: A).(match e in 
A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a3 | (AHead a _) 
\Rightarrow a])) (AHead a3 a4) (AHead x0 x1) H3) in ((let H5 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a4 | (AHead _ a) \Rightarrow a])) (AHead a3 a4) (AHead x0 x1) H3) 
in (\lambda (H6: (eq A a3 x0)).(let H7 \def (eq_ind_r A x1 (\lambda (a: 
A).(leq g a2 a)) H2 a4 H5) in (let H8 \def (eq_ind_r A x0 (\lambda (a: 
A).(leq g a1 a)) H1 a3 H6) in H7)))) H4))))))) H0)))))))).
(* COMMENTS
Initial nodes: 259
END *)

theorem leq_refl:
 \forall (g: G).(\forall (a: A).(leq g a a))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(leq g a0 a0)) 
(\lambda (n: nat).(\lambda (n0: nat).(leq_sort g n n n0 n0 O (refl_equal A 
(aplus g (ASort n n0) O))))) (\lambda (a0: A).(\lambda (H: (leq g a0 
a0)).(\lambda (a1: A).(\lambda (H0: (leq g a1 a1)).(leq_head g a0 a0 H a1 a1 
H0))))) a)).
(* COMMENTS
Initial nodes: 87
END *)

theorem leq_eq:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((eq A a1 a2) \to (leq g a1 
a2))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (eq A a1 
a2)).(eq_ind A a1 (\lambda (a: A).(leq g a1 a)) (leq_refl g a1) a2 H)))).
(* COMMENTS
Initial nodes: 39
END *)

theorem leq_sym:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (leq g 
a2 a1))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(leq g a0 a))) (\lambda (h1: 
nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: 
nat).(\lambda (H0: (eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) 
k))).(leq_sort g h2 h1 n2 n1 k (sym_eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k) H0)))))))) (\lambda (a3: A).(\lambda (a4: A).(\lambda (_: 
(leq g a3 a4)).(\lambda (H1: (leq g a4 a3)).(\lambda (a5: A).(\lambda (a6: 
A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: (leq g a6 a5)).(leq_head g a4 a3 
H1 a6 a5 H3))))))))) a1 a2 H)))).
(* COMMENTS
Initial nodes: 173
END *)

theorem leq_trans:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((leq g a2 a3) \to (leq g a1 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(\forall (a3: A).((leq g a0 
a3) \to (leq g a a3))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (H0: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (a3: A).(\lambda (H1: (leq g 
(ASort h2 n2) a3)).(let H_x \def (leq_gen_sort1 g h2 n2 a3 H1) in (let H2 
\def H_x in (ex2_3_ind nat nat nat (\lambda (n3: nat).(\lambda (h3: 
nat).(\lambda (k0: nat).(eq A (aplus g (ASort h2 n2) k0) (aplus g (ASort h3 
n3) k0))))) (\lambda (n3: nat).(\lambda (h3: nat).(\lambda (_: nat).(eq A a3 
(ASort h3 n3))))) (leq g (ASort h1 n1) a3) (\lambda (x0: nat).(\lambda (x1: 
nat).(\lambda (x2: nat).(\lambda (H3: (eq A (aplus g (ASort h2 n2) x2) (aplus 
g (ASort x1 x0) x2))).(\lambda (H4: (eq A a3 (ASort x1 x0))).(let H5 \def 
(f_equal A A (\lambda (e: A).e) a3 (ASort x1 x0) H4) in (eq_ind_r A (ASort x1 
x0) (\lambda (a: A).(leq g (ASort h1 n1) a)) (lt_le_e k x2 (leq g (ASort h1 
n1) (ASort x1 x0)) (\lambda (H6: (lt k x2)).(let H_y \def (aplus_reg_r g 
(ASort h1 n1) (ASort h2 n2) k k H0 (minus x2 k)) in (let H7 \def (eq_ind_r 
nat (plus (minus x2 k) k) (\lambda (n: nat).(eq A (aplus g (ASort h1 n1) n) 
(aplus g (ASort h2 n2) n))) H_y x2 (le_plus_minus_sym k x2 (le_trans k (S k) 
x2 (le_S k k (le_n k)) H6))) in (leq_sort g h1 x1 n1 x0 x2 (trans_eq A (aplus 
g (ASort h1 n1) x2) (aplus g (ASort h2 n2) x2) (aplus g (ASort x1 x0) x2) H7 
H3))))) (\lambda (H6: (le x2 k)).(let H_y \def (aplus_reg_r g (ASort h2 n2) 
(ASort x1 x0) x2 x2 H3 (minus k x2)) in (let H7 \def (eq_ind_r nat (plus 
(minus k x2) x2) (\lambda (n: nat).(eq A (aplus g (ASort h2 n2) n) (aplus g 
(ASort x1 x0) n))) H_y k (le_plus_minus_sym x2 k H6)) in (leq_sort g h1 x1 n1 
x0 k (trans_eq A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k) (aplus g 
(ASort x1 x0) k) H0 H7)))))) a3 H5))))))) H2))))))))))) (\lambda (a3: 
A).(\lambda (a4: A).(\lambda (_: (leq g a3 a4)).(\lambda (H1: ((\forall (a5: 
A).((leq g a4 a5) \to (leq g a3 a5))))).(\lambda (a5: A).(\lambda (a6: 
A).(\lambda (_: (leq g a5 a6)).(\lambda (H3: ((\forall (a7: A).((leq g a6 a7) 
\to (leq g a5 a7))))).(\lambda (a0: A).(\lambda (H4: (leq g (AHead a4 a6) 
a0)).(let H_x \def (leq_gen_head1 g a4 a6 a0 H4) in (let H5 \def H_x in 
(ex3_2_ind A A (\lambda (a7: A).(\lambda (_: A).(leq g a4 a7))) (\lambda (_: 
A).(\lambda (a8: A).(leq g a6 a8))) (\lambda (a7: A).(\lambda (a8: A).(eq A 
a0 (AHead a7 a8)))) (leq g (AHead a3 a5) a0) (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H6: (leq g a4 x0)).(\lambda (H7: (leq g a6 x1)).(\lambda (H8: 
(eq A a0 (AHead x0 x1))).(let H9 \def (f_equal A A (\lambda (e: A).e) a0 
(AHead x0 x1) H8) in (eq_ind_r A (AHead x0 x1) (\lambda (a: A).(leq g (AHead 
a3 a5) a)) (leq_head g a3 x0 (H1 x0 H6) a5 x1 (H3 x1 H7)) a0 H9))))))) 
H5))))))))))))) a1 a2 H)))).
(* COMMENTS
Initial nodes: 869
END *)

theorem leq_ahead_false_1:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g (AHead a1 a2) a1) 
\to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a1: A).(A_ind (\lambda (a: A).(\forall (a2: 
A).((leq g (AHead a a2) a) \to (\forall (P: Prop).P)))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (a2: A).(\lambda (H: (leq g (AHead (ASort n 
n0) a2) (ASort n n0))).(\lambda (P: Prop).(nat_ind (\lambda (n1: nat).((leq g 
(AHead (ASort n1 n0) a2) (ASort n1 n0)) \to P)) (\lambda (H0: (leq g (AHead 
(ASort O n0) a2) (ASort O n0))).(let H_x \def (leq_gen_head1 g (ASort O n0) 
a2 (ASort O n0) H0) in (let H1 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g (ASort O n0) a3))) (\lambda (_: A).(\lambda (a4: 
A).(leq g a2 a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort O n0) 
(AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g 
(ASort O n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H4: (eq A (ASort O 
n0) (AHead x0 x1))).(let H5 \def (eq_ind A (ASort O n0) (\lambda (ee: 
A).(match ee in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow 
True | (AHead _ _) \Rightarrow False])) I (AHead x0 x1) H4) in (False_ind P 
H5))))))) H1)))) (\lambda (n1: nat).(\lambda (_: (((leq g (AHead (ASort n1 
n0) a2) (ASort n1 n0)) \to P))).(\lambda (H0: (leq g (AHead (ASort (S n1) n0) 
a2) (ASort (S n1) n0))).(let H_x \def (leq_gen_head1 g (ASort (S n1) n0) a2 
(ASort (S n1) n0) H0) in (let H1 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g (ASort (S n1) n0) a3))) (\lambda (_: A).(\lambda 
(a4: A).(leq g a2 a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort (S n1) 
n0) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g 
(ASort (S n1) n0) x0)).(\lambda (_: (leq g a2 x1)).(\lambda (H4: (eq A (ASort 
(S n1) n0) (AHead x0 x1))).(let H5 \def (eq_ind A (ASort (S n1) n0) (\lambda 
(ee: A).(match ee in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead x0 x1) H4) in 
(False_ind P H5))))))) H1)))))) n H)))))) (\lambda (a: A).(\lambda (H: 
((\forall (a2: A).((leq g (AHead a a2) a) \to (\forall (P: 
Prop).P))))).(\lambda (a0: A).(\lambda (_: ((\forall (a2: A).((leq g (AHead 
a0 a2) a0) \to (\forall (P: Prop).P))))).(\lambda (a2: A).(\lambda (H1: (leq 
g (AHead (AHead a a0) a2) (AHead a a0))).(\lambda (P: Prop).(let H_x \def 
(leq_gen_head1 g (AHead a a0) a2 (AHead a a0) H1) in (let H2 \def H_x in 
(ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq g (AHead a a0) a3))) 
(\lambda (_: A).(\lambda (a4: A).(leq g a2 a4))) (\lambda (a3: A).(\lambda 
(a4: A).(eq A (AHead a a0) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (leq g (AHead a a0) x0)).(\lambda (H4: (leq g a2 
x1)).(\lambda (H5: (eq A (AHead a a0) (AHead x0 x1))).(let H6 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a | (AHead a3 _) \Rightarrow a3])) (AHead a a0) (AHead x0 x1) H5) 
in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda 
(_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead _ a3) \Rightarrow a3])) 
(AHead a a0) (AHead x0 x1) H5) in (\lambda (H8: (eq A a x0)).(let H9 \def 
(eq_ind_r A x1 (\lambda (a3: A).(leq g a2 a3)) H4 a0 H7) in (let H10 \def 
(eq_ind_r A x0 (\lambda (a3: A).(leq g (AHead a a0) a3)) H3 a H8) in (H a0 
H10 P))))) H6))))))) H2)))))))))) a1)).
(* COMMENTS
Initial nodes: 797
END *)

theorem leq_ahead_false_2:
 \forall (g: G).(\forall (a2: A).(\forall (a1: A).((leq g (AHead a1 a2) a2) 
\to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a2: A).(A_ind (\lambda (a: A).(\forall (a1: 
A).((leq g (AHead a1 a) a) \to (\forall (P: Prop).P)))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (a1: A).(\lambda (H: (leq g (AHead a1 (ASort 
n n0)) (ASort n n0))).(\lambda (P: Prop).(nat_ind (\lambda (n1: nat).((leq g 
(AHead a1 (ASort n1 n0)) (ASort n1 n0)) \to P)) (\lambda (H0: (leq g (AHead 
a1 (ASort O n0)) (ASort O n0))).(let H_x \def (leq_gen_head1 g a1 (ASort O 
n0) (ASort O n0) H0) in (let H1 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g a1 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g 
(ASort O n0) a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort O n0) 
(AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g a1 
x0)).(\lambda (_: (leq g (ASort O n0) x1)).(\lambda (H4: (eq A (ASort O n0) 
(AHead x0 x1))).(let H5 \def (eq_ind A (ASort O n0) (\lambda (ee: A).(match 
ee in A return (\lambda (_: A).Prop) with [(ASort _ _) \Rightarrow True | 
(AHead _ _) \Rightarrow False])) I (AHead x0 x1) H4) in (False_ind P 
H5))))))) H1)))) (\lambda (n1: nat).(\lambda (_: (((leq g (AHead a1 (ASort n1 
n0)) (ASort n1 n0)) \to P))).(\lambda (H0: (leq g (AHead a1 (ASort (S n1) 
n0)) (ASort (S n1) n0))).(let H_x \def (leq_gen_head1 g a1 (ASort (S n1) n0) 
(ASort (S n1) n0) H0) in (let H1 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g a1 a3))) (\lambda (_: A).(\lambda (a4: A).(leq g 
(ASort (S n1) n0) a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort (S n1) 
n0) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g 
a1 x0)).(\lambda (_: (leq g (ASort (S n1) n0) x1)).(\lambda (H4: (eq A (ASort 
(S n1) n0) (AHead x0 x1))).(let H5 \def (eq_ind A (ASort (S n1) n0) (\lambda 
(ee: A).(match ee in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead x0 x1) H4) in 
(False_ind P H5))))))) H1)))))) n H)))))) (\lambda (a: A).(\lambda (_: 
((\forall (a1: A).((leq g (AHead a1 a) a) \to (\forall (P: 
Prop).P))))).(\lambda (a0: A).(\lambda (H0: ((\forall (a1: A).((leq g (AHead 
a1 a0) a0) \to (\forall (P: Prop).P))))).(\lambda (a1: A).(\lambda (H1: (leq 
g (AHead a1 (AHead a a0)) (AHead a a0))).(\lambda (P: Prop).(let H_x \def 
(leq_gen_head1 g a1 (AHead a a0) (AHead a a0) H1) in (let H2 \def H_x in 
(ex3_2_ind A A (\lambda (a3: A).(\lambda (_: A).(leq g a1 a3))) (\lambda (_: 
A).(\lambda (a4: A).(leq g (AHead a a0) a4))) (\lambda (a3: A).(\lambda (a4: 
A).(eq A (AHead a a0) (AHead a3 a4)))) P (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (leq g a1 x0)).(\lambda (H4: (leq g (AHead a a0) 
x1)).(\lambda (H5: (eq A (AHead a a0) (AHead x0 x1))).(let H6 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a | (AHead a3 _) \Rightarrow a3])) (AHead a a0) (AHead x0 x1) H5) 
in ((let H7 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda 
(_: A).A) with [(ASort _ _) \Rightarrow a0 | (AHead _ a3) \Rightarrow a3])) 
(AHead a a0) (AHead x0 x1) H5) in (\lambda (H8: (eq A a x0)).(let H9 \def 
(eq_ind_r A x1 (\lambda (a3: A).(leq g (AHead a a0) a3)) H4 a0 H7) in (let 
H10 \def (eq_ind_r A x0 (\lambda (a3: A).(leq g a1 a3)) H3 a H8) in (H0 a H9 
P))))) H6))))))) H2)))))))))) a2)).
(* COMMENTS
Initial nodes: 797
END *)

