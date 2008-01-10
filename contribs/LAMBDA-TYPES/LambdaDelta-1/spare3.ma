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



include "theory.ma".

inductive sort: T \to Prop \def
| sort_sort: \forall (n: nat).(sort (TSort n))
| sort_abst: \forall (u: T).((sort u) \to (\forall (t: T).((sort t) \to (sort 
(THead (Bind Abst) u t))))).

theorem sort_nf2:
 \forall (t: T).((sort t) \to (\forall (c: C).(nf2 c t)))
\def
 \lambda (t: T).(\lambda (H: (sort t)).(sort_ind (\lambda (t0: T).(\forall 
(c: C).(nf2 c t0))) (\lambda (n: nat).(\lambda (c: C).(nf2_sort c n))) 
(\lambda (u: T).(\lambda (_: (sort u)).(\lambda (H1: ((\forall (c: C).(nf2 c 
u)))).(\lambda (t0: T).(\lambda (_: (sort t0)).(\lambda (H3: ((\forall (c: 
C).(nf2 c t0)))).(\lambda (c: C).(let H_y \def (H3 (CHead c (Bind Abst) u)) 
in (nf2_abst_shift c u (H1 c) t0 H_y))))))))) t H)).

theorem sort_pc3:
 \forall (t1: T).((sort t1) \to (\forall (t2: T).((sort t2) \to (\forall (c: 
C).((pc3 c t1 t2) \to (eq T t1 t2))))))
\def
 \lambda (t1: T).(\lambda (H: (sort t1)).(sort_ind (\lambda (t: T).(\forall 
(t2: T).((sort t2) \to (\forall (c: C).((pc3 c t t2) \to (eq T t t2)))))) 
(\lambda (n: nat).(\lambda (t2: T).(\lambda (H0: (sort t2)).(sort_ind 
(\lambda (t: T).(\forall (c: C).((pc3 c (TSort n) t) \to (eq T (TSort n) 
t)))) (\lambda (n0: nat).(\lambda (c: C).(\lambda (H1: (pc3 c (TSort n) 
(TSort n0))).(eq_ind nat n (\lambda (n1: nat).(eq T (TSort n) (TSort n1))) 
(refl_equal T (TSort n)) n0 (pc3_gen_sort c n n0 H1))))) (\lambda (u: 
T).(\lambda (_: (sort u)).(\lambda (_: ((\forall (c: C).((pc3 c (TSort n) u) 
\to (eq T (TSort n) u))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda 
(_: ((\forall (c: C).((pc3 c (TSort n) t) \to (eq T (TSort n) t))))).(\lambda 
(c: C).(\lambda (H5: (pc3 c (TSort n) (THead (Bind Abst) u 
t))).(pc3_gen_sort_abst c u t n H5 (eq T (TSort n) (THead (Bind Abst) u 
t))))))))))) t2 H0)))) (\lambda (u: T).(\lambda (_: (sort u)).(\lambda (H1: 
((\forall (t2: T).((sort t2) \to (\forall (c: C).((pc3 c u t2) \to (eq T u 
t2))))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda (H3: ((\forall (t2: 
T).((sort t2) \to (\forall (c: C).((pc3 c t t2) \to (eq T t 
t2))))))).(\lambda (t2: T).(\lambda (H4: (sort t2)).(sort_ind (\lambda (t0: 
T).(\forall (c: C).((pc3 c (THead (Bind Abst) u t) t0) \to (eq T (THead (Bind 
Abst) u t) t0)))) (\lambda (n: nat).(\lambda (c: C).(\lambda (H5: (pc3 c 
(THead (Bind Abst) u t) (TSort n))).(pc3_gen_sort_abst c u t n (pc3_s c 
(TSort n) (THead (Bind Abst) u t) H5) (eq T (THead (Bind Abst) u t) (TSort 
n)))))) (\lambda (u0: T).(\lambda (H5: (sort u0)).(\lambda (_: ((\forall (c: 
C).((pc3 c (THead (Bind Abst) u t) u0) \to (eq T (THead (Bind Abst) u t) 
u0))))).(\lambda (t0: T).(\lambda (H7: (sort t0)).(\lambda (_: ((\forall (c: 
C).((pc3 c (THead (Bind Abst) u t) t0) \to (eq T (THead (Bind Abst) u t) 
t0))))).(\lambda (c: C).(\lambda (H9: (pc3 c (THead (Bind Abst) u t) (THead 
(Bind Abst) u0 t0))).(and_ind (pc3 c u u0) (\forall (b: B).(\forall (u1: 
T).(pc3 (CHead c (Bind b) u1) t t0))) (eq T (THead (Bind Abst) u t) (THead 
(Bind Abst) u0 t0)) (\lambda (H10: (pc3 c u u0)).(\lambda (H11: ((\forall (b: 
B).(\forall (u1: T).(pc3 (CHead c (Bind b) u1) t t0))))).(let H_y \def (H11 
Abbr u) in (let H_y0 \def (H1 u0 H5 c H10) in (let H_y1 \def (H3 t0 H7 (CHead 
c (Bind Abbr) u) H_y) in (let H12 \def (eq_ind_r T t0 (\lambda (t3: T).(pc3 
(CHead c (Bind Abbr) u) t t3)) H_y t H_y1) in (let H13 \def (eq_ind_r T t0 
(\lambda (t3: T).(sort t3)) H7 t H_y1) in (eq_ind T t (\lambda (t3: T).(eq T 
(THead (Bind Abst) u t) (THead (Bind Abst) u0 t3))) (let H14 \def (eq_ind_r T 
u0 (\lambda (t3: T).(pc3 c u t3)) H10 u H_y0) in (let H15 \def (eq_ind_r T u0 
(\lambda (t3: T).(sort t3)) H5 u H_y0) in (eq_ind T u (\lambda (t3: T).(eq T 
(THead (Bind Abst) u t) (THead (Bind Abst) t3 t))) (refl_equal T (THead (Bind 
Abst) u t)) u0 H_y0))) t0 H_y1)))))))) (pc3_gen_abst c u u0 t t0 H9)))))))))) 
t2 H4))))))))) t1 H)).

theorem sort_correct:
 \forall (g: G).(\forall (t1: T).((sort t1) \to (\forall (c: C).(ex3 T 
(\lambda (t2: T).(tau0 g c t1 t2)) (\lambda (t2: T).(ty3 g c t1 t2)) (\lambda 
(t2: T).(sort t2))))))
\def
 \lambda (g: G).(\lambda (t1: T).(\lambda (H: (sort t1)).(sort_ind (\lambda 
(t: T).(\forall (c: C).(ex3 T (\lambda (t2: T).(tau0 g c t t2)) (\lambda (t2: 
T).(ty3 g c t t2)) (\lambda (t2: T).(sort t2))))) (\lambda (n: nat).(\lambda 
(c: C).(ex3_intro T (\lambda (t2: T).(tau0 g c (TSort n) t2)) (\lambda (t2: 
T).(ty3 g c (TSort n) t2)) (\lambda (t2: T).(sort t2)) (TSort (next g n)) 
(tau0_sort g c n) (ty3_sort g c n) (sort_sort (next g n))))) (\lambda (u: 
T).(\lambda (H0: (sort u)).(\lambda (H1: ((\forall (c: C).(ex3 T (\lambda 
(t2: T).(tau0 g c u t2)) (\lambda (t2: T).(ty3 g c u t2)) (\lambda (t2: 
T).(sort t2)))))).(\lambda (t: T).(\lambda (_: (sort t)).(\lambda (H3: 
((\forall (c: C).(ex3 T (\lambda (t2: T).(tau0 g c t t2)) (\lambda (t2: 
T).(ty3 g c t t2)) (\lambda (t2: T).(sort t2)))))).(\lambda (c: C).(let H_x 
\def (H1 c) in (let H4 \def H_x in (ex3_ind T (\lambda (t2: T).(tau0 g c u 
t2)) (\lambda (t2: T).(ty3 g c u t2)) (\lambda (t2: T).(sort t2)) (ex3 T 
(\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(ty3 
g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) (\lambda (x0: 
T).(\lambda (_: (tau0 g c u x0)).(\lambda (H6: (ty3 g c u x0)).(\lambda (_: 
(sort x0)).(let H_x0 \def (H3 (CHead c (Bind Abst) u)) in (let H8 \def H_x0 
in (ex3_ind T (\lambda (t2: T).(tau0 g (CHead c (Bind Abst) u) t t2)) 
(\lambda (t2: T).(ty3 g (CHead c (Bind Abst) u) t t2)) (\lambda (t2: T).(sort 
t2)) (ex3 T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda 
(t2: T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) 
(\lambda (x1: T).(\lambda (H9: (tau0 g (CHead c (Bind Abst) u) t 
x1)).(\lambda (H10: (ty3 g (CHead c (Bind Abst) u) t x1)).(\lambda (H11: 
(sort x1)).(ex_ind T (\lambda (t0: T).(ty3 g (CHead c (Bind Abst) u) x1 t0)) 
(ex3 T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: 
T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort t2))) 
(\lambda (x: T).(\lambda (H12: (ty3 g (CHead c (Bind Abst) u) x1 
x)).(ex3_intro T (\lambda (t2: T).(tau0 g c (THead (Bind Abst) u t) t2)) 
(\lambda (t2: T).(ty3 g c (THead (Bind Abst) u t) t2)) (\lambda (t2: T).(sort 
t2)) (THead (Bind Abst) u x1) (tau0_bind g Abst c u t x1 H9) (ty3_bind g c u 
x0 H6 Abst t x1 H10 x H12) (sort_abst u H0 x1 H11)))) (ty3_correct g (CHead c 
(Bind Abst) u) t x1 H10)))))) H8))))))) H4)))))))))) t1 H))).

