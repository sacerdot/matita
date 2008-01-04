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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ex2/props".

include "ex2/defs.ma".

include "nf2/defs.ma".

include "pr2/fwd.ma".

include "arity/fwd.ma".

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
H3 \def (match (arity_gen_sort g (CSort O) O (AHead x a) H2) in leq return 
(\lambda (a0: A).(\lambda (a1: A).(\lambda (_: (leq ? a0 a1)).((eq A a0 
(AHead x a)) \to ((eq A a1 (ASort O O)) \to P))))) with [(leq_sort h1 h2 n1 
n2 k H3) \Rightarrow (\lambda (H4: (eq A (ASort h1 n1) (AHead x a))).(\lambda 
(H5: (eq A (ASort h2 n2) (ASort O O))).((let H6 \def (eq_ind A (ASort h1 n1) 
(\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with [(ASort _ _) 
\Rightarrow True | (AHead _ _) \Rightarrow False])) I (AHead x a) H4) in 
(False_ind ((eq A (ASort h2 n2) (ASort O O)) \to ((eq A (aplus g (ASort h1 
n1) k) (aplus g (ASort h2 n2) k)) \to P)) H6)) H5 H3))) | (leq_head a1 a2 H3 
a3 a4 H4) \Rightarrow (\lambda (H5: (eq A (AHead a1 a3) (AHead x 
a))).(\lambda (H6: (eq A (AHead a2 a4) (ASort O O))).((let H7 \def (f_equal A 
A (\lambda (e: A).(match e in A return (\lambda (_: A).A) with [(ASort _ _) 
\Rightarrow a3 | (AHead _ a0) \Rightarrow a0])) (AHead a1 a3) (AHead x a) H5) 
in ((let H8 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda 
(_: A).A) with [(ASort _ _) \Rightarrow a1 | (AHead a0 _) \Rightarrow a0])) 
(AHead a1 a3) (AHead x a) H5) in (eq_ind A x (\lambda (a0: A).((eq A a3 a) 
\to ((eq A (AHead a2 a4) (ASort O O)) \to ((leq g a0 a2) \to ((leq g a3 a4) 
\to P))))) (\lambda (H9: (eq A a3 a)).(eq_ind A a (\lambda (a0: A).((eq A 
(AHead a2 a4) (ASort O O)) \to ((leq g x a2) \to ((leq g a0 a4) \to P)))) 
(\lambda (H10: (eq A (AHead a2 a4) (ASort O O))).(let H11 \def (eq_ind A 
(AHead a2 a4) (\lambda (e: A).(match e in A return (\lambda (_: A).Prop) with 
[(ASort _ _) \Rightarrow False | (AHead _ _) \Rightarrow True])) I (ASort O 
O) H10) in (False_ind ((leq g x a2) \to ((leq g a a4) \to P)) H11))) a3 
(sym_eq A a3 a H9))) a1 (sym_eq A a1 x H8))) H7)) H6 H3 H4)))]) in (H3 
(refl_equal A (AHead x a)) (refl_equal A (ASort O O))))))) H0))))).

