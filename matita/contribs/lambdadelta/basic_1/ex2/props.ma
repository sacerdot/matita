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

include "Basic-1/ex2/defs.ma".

include "Basic-1/nf2/defs.ma".

include "Basic-1/pr2/fwd.ma".

include "Basic-1/arity/fwd.ma".

theorem ex2_nf2:
 nf2 ex2_c ex2_t
\def
 \lambda (t2: T).(\lambda (H: (pr2 (CSort O) (THead (Flat Appl) (TSort O) 
(TSort O)) t2)).(let H0 \def (pr2_gen_appl (CSort O) (TSort O) (TSort O) t2 
H) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 (CSort O) (TSort 
O) u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 (CSort O) (TSort O) t3)))) 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (TSort O) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 (CSort O) (TSort O) u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead (CSort O) 
(Bind b) u) z1 t3)))))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (TSort O) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 (CSort O) (TSort 
O) u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CSort O) y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead (CSort O) (Bind b) y2) z1 z2)))))))) (eq T (THead (Flat 
Appl) (TSort O) (TSort O)) t2) (\lambda (H1: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 (CSort O) (TSort O) t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr2 (CSort O) (TSort O) t3))) (eq T (THead (Flat Appl) (TSort O) 
(TSort O)) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H2: (eq T t2 
(THead (Flat Appl) x0 x1))).(\lambda (H3: (pr2 (CSort O) (TSort O) 
x0)).(\lambda (H4: (pr2 (CSort O) (TSort O) x1)).(let H5 \def (eq_ind T x1 
(\lambda (t: T).(eq T t2 (THead (Flat Appl) x0 t))) H2 (TSort O) 
(pr2_gen_sort (CSort O) x1 O H4)) in (let H6 \def (eq_ind T x0 (\lambda (t: 
T).(eq T t2 (THead (Flat Appl) t (TSort O)))) H5 (TSort O) (pr2_gen_sort 
(CSort O) x0 O H3)) in (eq_ind_r T (THead (Flat Appl) (TSort O) (TSort O)) 
(\lambda (t: T).(eq T (THead (Flat Appl) (TSort O) (TSort O)) t)) (refl_equal 
T (THead (Flat Appl) (TSort O) (TSort O))) t2 H6)))))))) H1)) (\lambda (H1: 
(ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(eq T (TSort O) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr2 (CSort O) (TSort O) u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead (CSort O) 
(Bind b) u) z1 t3))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (TSort O) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: 
B).(\forall (u: T).(pr2 (CHead (CSort O) (Bind b) u) z1 t3))))))) (eq T 
(THead (Flat Appl) (TSort O) (TSort O)) t2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H2: (eq T (TSort O) (THead 
(Bind Abst) x0 x1))).(\lambda (H3: (eq T t2 (THead (Bind Abbr) x2 
x3))).(\lambda (H4: (pr2 (CSort O) (TSort O) x2)).(\lambda (_: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead (CSort O) (Bind b) u) x1 x3))))).(let H6 \def 
(eq_ind T x2 (\lambda (t: T).(eq T t2 (THead (Bind Abbr) t x3))) H3 (TSort O) 
(pr2_gen_sort (CSort O) x2 O H4)) in (eq_ind_r T (THead (Bind Abbr) (TSort O) 
x3) (\lambda (t: T).(eq T (THead (Flat Appl) (TSort O) (TSort O)) t)) (let H7 
\def (eq_ind T (TSort O) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) x0 x1) H2) in 
(False_ind (eq T (THead (Flat Appl) (TSort O) (TSort O)) (THead (Bind Abbr) 
(TSort O) x3)) H7)) t2 H6)))))))))) H1)) (\lambda (H1: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TSort O) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 (CSort O) (TSort O) u2))))))) (\lambda (_: 
B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CSort O) y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda 
(z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead (CSort 
O) (Bind b) y2) z1 z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (TSort O) 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind 
b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 (CSort O) (TSort O) u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CSort O) y1 y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead (CSort O) 
(Bind b) y2) z1 z2))))))) (eq T (THead (Flat Appl) (TSort O) (TSort O)) t2) 
(\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda 
(x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 Abst))).(\lambda (H3: (eq 
T (TSort O) (THead (Bind x0) x1 x2))).(\lambda (H4: (eq T t2 (THead (Bind x0) 
x5 (THead (Flat Appl) (lift (S O) O x4) x3)))).(\lambda (H5: (pr2 (CSort O) 
(TSort O) x4)).(\lambda (H6: (pr2 (CSort O) x1 x5)).(\lambda (_: (pr2 (CHead 
(CSort O) (Bind x0) x5) x2 x3)).(let H_y \def (pr2_gen_csort x1 x5 O H6) in 
(let H8 \def (eq_ind T x4 (\lambda (t: T).(eq T t2 (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O t) x3)))) H4 (TSort O) (pr2_gen_sort (CSort O) x4 O 
H5)) in (eq_ind_r T (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O 
(TSort O)) x3)) (\lambda (t: T).(eq T (THead (Flat Appl) (TSort O) (TSort O)) 
t)) (let H9 \def (eq_ind T (TSort O) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead (Bind x0) x1 
x2) H3) in (False_ind (eq T (THead (Flat Appl) (TSort O) (TSort O)) (THead 
(Bind x0) x5 (THead (Flat Appl) (lift (S O) O (TSort O)) x3))) H9)) t2 
H8))))))))))))))) H1)) H0))).
(* COMMENTS
Initial nodes: 1939
END *)

theorem ex2_arity:
 \forall (g: G).(\forall (a: A).((arity g ex2_c ex2_t a) \to (\forall (P: 
Prop).P)))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (H: (arity g (CSort O) (THead (Flat 
Appl) (TSort O) (TSort O)) a)).(\lambda (P: Prop).(let H0 \def 
(arity_gen_appl g (CSort O) (TSort O) (TSort O) a H) in (ex2_ind A (\lambda 
(a1: A).(arity g (CSort O) (TSort O) a1)) (\lambda (a1: A).(arity g (CSort O) 
(TSort O) (AHead a1 a))) P (\lambda (x: A).(\lambda (_: (arity g (CSort O) 
(TSort O) x)).(\lambda (H2: (arity g (CSort O) (TSort O) (AHead x a))).(let 
H_x \def (leq_gen_head1 g x a (ASort O O) (arity_gen_sort g (CSort O) O 
(AHead x a) H2)) in (let H3 \def H_x in (ex3_2_ind A A (\lambda (a3: 
A).(\lambda (_: A).(leq g x a3))) (\lambda (_: A).(\lambda (a4: A).(leq g a 
a4))) (\lambda (a3: A).(\lambda (a4: A).(eq A (ASort O O) (AHead a3 a4)))) P 
(\lambda (x0: A).(\lambda (x1: A).(\lambda (_: (leq g x x0)).(\lambda (_: 
(leq g a x1)).(\lambda (H6: (eq A (ASort O O) (AHead x0 x1))).(let H7 \def 
(eq_ind A (ASort O O) (\lambda (ee: A).(match ee in A return (\lambda (_: 
A).Prop) with [(ASort _ _) \Rightarrow True | (AHead _ _) \Rightarrow 
False])) I (AHead x0 x1) H6) in (False_ind P H7))))))) H3)))))) H0))))).
(* COMMENTS
Initial nodes: 289
END *)

