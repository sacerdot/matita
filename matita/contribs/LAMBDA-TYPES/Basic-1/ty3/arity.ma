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

include "Basic-1/ty3/pr3_props.ma".

include "Basic-1/arity/pr3.ma".

include "Basic-1/asucc/fwd.ma".

theorem ty3_arity:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (ex2 A (\lambda (a1: A).(arity g c t1 a1)) (\lambda (a1: A).(arity 
g c t2 (asucc g a1))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda 
(t0: T).(ex2 A (\lambda (a1: A).(arity g c0 t a1)) (\lambda (a1: A).(arity g 
c0 t0 (asucc g a1))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 t3 t)).(\lambda (H1: (ex2 A (\lambda (a1: A).(arity 
g c0 t3 a1)) (\lambda (a1: A).(arity g c0 t (asucc g a1))))).(\lambda (u: 
T).(\lambda (t4: T).(\lambda (_: (ty3 g c0 u t4)).(\lambda (H3: (ex2 A 
(\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t4 (asucc g 
a1))))).(\lambda (H4: (pc3 c0 t4 t3)).(let H5 \def H1 in (ex2_ind A (\lambda 
(a1: A).(arity g c0 t3 a1)) (\lambda (a1: A).(arity g c0 t (asucc g a1))) 
(ex2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t3 
(asucc g a1)))) (\lambda (x: A).(\lambda (H6: (arity g c0 t3 x)).(\lambda (_: 
(arity g c0 t (asucc g x))).(let H8 \def H3 in (ex2_ind A (\lambda (a1: 
A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t4 (asucc g a1))) (ex2 A 
(\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t3 (asucc g 
a1)))) (\lambda (x0: A).(\lambda (H9: (arity g c0 u x0)).(\lambda (H10: 
(arity g c0 t4 (asucc g x0))).(let H11 \def H4 in (ex2_ind T (\lambda (t0: 
T).(pr3 c0 t4 t0)) (\lambda (t0: T).(pr3 c0 t3 t0)) (ex2 A (\lambda (a1: 
A).(arity g c0 u a1)) (\lambda (a1: A).(arity g c0 t3 (asucc g a1)))) 
(\lambda (x1: T).(\lambda (H12: (pr3 c0 t4 x1)).(\lambda (H13: (pr3 c0 t3 
x1)).(ex_intro2 A (\lambda (a1: A).(arity g c0 u a1)) (\lambda (a1: A).(arity 
g c0 t3 (asucc g a1))) x0 H9 (arity_repl g c0 t3 x H6 (asucc g x0) (leq_sym g 
(asucc g x0) x (arity_mono g c0 x1 (asucc g x0) (arity_sred_pr3 c0 t4 x1 H12 
g (asucc g x0) H10) x (arity_sred_pr3 c0 t3 x1 H13 g x H6)))))))) H11))))) 
H8))))) H5)))))))))))) (\lambda (c0: C).(\lambda (m: nat).(ex_intro2 A 
(\lambda (a1: A).(arity g c0 (TSort m) a1)) (\lambda (a1: A).(arity g c0 
(TSort (next g m)) (asucc g a1))) (ASort O m) (arity_sort g c0 m) (arity_sort 
g c0 (next g m))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) 
u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: (ex2 A 
(\lambda (a1: A).(arity g d u a1)) (\lambda (a1: A).(arity g d t (asucc g 
a1))))).(let H3 \def H2 in (ex2_ind A (\lambda (a1: A).(arity g d u a1)) 
(\lambda (a1: A).(arity g d t (asucc g a1))) (ex2 A (\lambda (a1: A).(arity g 
c0 (TLRef n) a1)) (\lambda (a1: A).(arity g c0 (lift (S n) O t) (asucc g 
a1)))) (\lambda (x: A).(\lambda (H4: (arity g d u x)).(\lambda (H5: (arity g 
d t (asucc g x))).(ex_intro2 A (\lambda (a1: A).(arity g c0 (TLRef n) a1)) 
(\lambda (a1: A).(arity g c0 (lift (S n) O t) (asucc g a1))) x (arity_abbr g 
c0 d u n H0 x H4) (arity_lift g d t (asucc g x) H5 c0 (S n) O (getl_drop Abbr 
c0 d u n H0)))))) H3)))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abst) 
u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: (ex2 A 
(\lambda (a1: A).(arity g d u a1)) (\lambda (a1: A).(arity g d t (asucc g 
a1))))).(let H3 \def H2 in (ex2_ind A (\lambda (a1: A).(arity g d u a1)) 
(\lambda (a1: A).(arity g d t (asucc g a1))) (ex2 A (\lambda (a1: A).(arity g 
c0 (TLRef n) a1)) (\lambda (a1: A).(arity g c0 (lift (S n) O u) (asucc g 
a1)))) (\lambda (x: A).(\lambda (H4: (arity g d u x)).(\lambda (_: (arity g d 
t (asucc g x))).(let H_x \def (leq_asucc g x) in (let H6 \def H_x in (ex_ind 
A (\lambda (a0: A).(leq g x (asucc g a0))) (ex2 A (\lambda (a1: A).(arity g 
c0 (TLRef n) a1)) (\lambda (a1: A).(arity g c0 (lift (S n) O u) (asucc g 
a1)))) (\lambda (x0: A).(\lambda (H7: (leq g x (asucc g x0))).(ex_intro2 A 
(\lambda (a1: A).(arity g c0 (TLRef n) a1)) (\lambda (a1: A).(arity g c0 
(lift (S n) O u) (asucc g a1))) x0 (arity_abst g c0 d u n H0 x0 (arity_repl g 
d u x H4 (asucc g x0) H7)) (arity_repl g c0 (lift (S n) O u) x (arity_lift g 
d u x H4 c0 (S n) O (getl_drop Abst c0 d u n H0)) (asucc g x0) H7)))) 
H6)))))) H3)))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 u t)).(\lambda (H1: (ex2 A (\lambda (a1: A).(arity 
g c0 u a1)) (\lambda (a1: A).(arity g c0 t (asucc g a1))))).(\lambda (b: 
B).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u) t3 t4)).(\lambda (H3: (ex2 A (\lambda (a1: A).(arity g (CHead c0 (Bind b) 
u) t3 a1)) (\lambda (a1: A).(arity g (CHead c0 (Bind b) u) t4 (asucc g 
a1))))).(let H4 \def H1 in (ex2_ind A (\lambda (a1: A).(arity g c0 u a1)) 
(\lambda (a1: A).(arity g c0 t (asucc g a1))) (ex2 A (\lambda (a1: A).(arity 
g c0 (THead (Bind b) u t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Bind b) 
u t4) (asucc g a1)))) (\lambda (x: A).(\lambda (H5: (arity g c0 u 
x)).(\lambda (_: (arity g c0 t (asucc g x))).(let H7 \def H3 in (ex2_ind A 
(\lambda (a1: A).(arity g (CHead c0 (Bind b) u) t3 a1)) (\lambda (a1: 
A).(arity g (CHead c0 (Bind b) u) t4 (asucc g a1))) (ex2 A (\lambda (a1: 
A).(arity g c0 (THead (Bind b) u t3) a1)) (\lambda (a1: A).(arity g c0 (THead 
(Bind b) u t4) (asucc g a1)))) (\lambda (x0: A).(\lambda (H8: (arity g (CHead 
c0 (Bind b) u) t3 x0)).(\lambda (H9: (arity g (CHead c0 (Bind b) u) t4 (asucc 
g x0))).(let H_x \def (leq_asucc g x) in (let H10 \def H_x in (ex_ind A 
(\lambda (a0: A).(leq g x (asucc g a0))) (ex2 A (\lambda (a1: A).(arity g c0 
(THead (Bind b) u t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Bind b) u t4) 
(asucc g a1)))) (\lambda (x1: A).(\lambda (H11: (leq g x (asucc g 
x1))).(B_ind (\lambda (b0: B).((arity g (CHead c0 (Bind b0) u) t3 x0) \to 
((arity g (CHead c0 (Bind b0) u) t4 (asucc g x0)) \to (ex2 A (\lambda (a1: 
A).(arity g c0 (THead (Bind b0) u t3) a1)) (\lambda (a1: A).(arity g c0 
(THead (Bind b0) u t4) (asucc g a1))))))) (\lambda (H12: (arity g (CHead c0 
(Bind Abbr) u) t3 x0)).(\lambda (H13: (arity g (CHead c0 (Bind Abbr) u) t4 
(asucc g x0))).(ex_intro2 A (\lambda (a1: A).(arity g c0 (THead (Bind Abbr) u 
t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Bind Abbr) u t4) (asucc g a1))) 
x0 (arity_bind g Abbr not_abbr_abst c0 u x H5 t3 x0 H12) (arity_bind g Abbr 
not_abbr_abst c0 u x H5 t4 (asucc g x0) H13)))) (\lambda (H12: (arity g 
(CHead c0 (Bind Abst) u) t3 x0)).(\lambda (H13: (arity g (CHead c0 (Bind 
Abst) u) t4 (asucc g x0))).(ex_intro2 A (\lambda (a1: A).(arity g c0 (THead 
(Bind Abst) u t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Bind Abst) u t4) 
(asucc g a1))) (AHead x1 x0) (arity_head g c0 u x1 (arity_repl g c0 u x H5 
(asucc g x1) H11) t3 x0 H12) (arity_repl g c0 (THead (Bind Abst) u t4) (AHead 
x1 (asucc g x0)) (arity_head g c0 u x1 (arity_repl g c0 u x H5 (asucc g x1) 
H11) t4 (asucc g x0) H13) (asucc g (AHead x1 x0)) (leq_refl g (asucc g (AHead 
x1 x0))))))) (\lambda (H12: (arity g (CHead c0 (Bind Void) u) t3 
x0)).(\lambda (H13: (arity g (CHead c0 (Bind Void) u) t4 (asucc g 
x0))).(ex_intro2 A (\lambda (a1: A).(arity g c0 (THead (Bind Void) u t3) a1)) 
(\lambda (a1: A).(arity g c0 (THead (Bind Void) u t4) (asucc g a1))) x0 
(arity_bind g Void (sym_not_eq B Abst Void not_abst_void) c0 u x H5 t3 x0 
H12) (arity_bind g Void (sym_not_eq B Abst Void not_abst_void) c0 u x H5 t4 
(asucc g x0) H13)))) b H8 H9))) H10)))))) H7))))) H4)))))))))))) (\lambda 
(c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c0 w u)).(\lambda 
(H1: (ex2 A (\lambda (a1: A).(arity g c0 w a1)) (\lambda (a1: A).(arity g c0 
u (asucc g a1))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v 
(THead (Bind Abst) u t))).(\lambda (H3: (ex2 A (\lambda (a1: A).(arity g c0 v 
a1)) (\lambda (a1: A).(arity g c0 (THead (Bind Abst) u t) (asucc g 
a1))))).(let H4 \def H1 in (ex2_ind A (\lambda (a1: A).(arity g c0 w a1)) 
(\lambda (a1: A).(arity g c0 u (asucc g a1))) (ex2 A (\lambda (a1: A).(arity 
g c0 (THead (Flat Appl) w v) a1)) (\lambda (a1: A).(arity g c0 (THead (Flat 
Appl) w (THead (Bind Abst) u t)) (asucc g a1)))) (\lambda (x: A).(\lambda 
(H5: (arity g c0 w x)).(\lambda (H6: (arity g c0 u (asucc g x))).(let H7 \def 
H3 in (ex2_ind A (\lambda (a1: A).(arity g c0 v a1)) (\lambda (a1: A).(arity 
g c0 (THead (Bind Abst) u t) (asucc g a1))) (ex2 A (\lambda (a1: A).(arity g 
c0 (THead (Flat Appl) w v) a1)) (\lambda (a1: A).(arity g c0 (THead (Flat 
Appl) w (THead (Bind Abst) u t)) (asucc g a1)))) (\lambda (x0: A).(\lambda 
(H8: (arity g c0 v x0)).(\lambda (H9: (arity g c0 (THead (Bind Abst) u t) 
(asucc g x0))).(let H10 \def (arity_gen_abst g c0 u t (asucc g x0) H9) in 
(ex3_2_ind A A (\lambda (a1: A).(\lambda (a2: A).(eq A (asucc g x0) (AHead a1 
a2)))) (\lambda (a1: A).(\lambda (_: A).(arity g c0 u (asucc g a1)))) 
(\lambda (_: A).(\lambda (a2: A).(arity g (CHead c0 (Bind Abst) u) t a2))) 
(ex2 A (\lambda (a1: A).(arity g c0 (THead (Flat Appl) w v) a1)) (\lambda 
(a1: A).(arity g c0 (THead (Flat Appl) w (THead (Bind Abst) u t)) (asucc g 
a1)))) (\lambda (x1: A).(\lambda (x2: A).(\lambda (H11: (eq A (asucc g x0) 
(AHead x1 x2))).(\lambda (H12: (arity g c0 u (asucc g x1))).(\lambda (H13: 
(arity g (CHead c0 (Bind Abst) u) t x2)).(let H14 \def (sym_eq A (asucc g x0) 
(AHead x1 x2) H11) in (let H15 \def (asucc_gen_head g x1 x2 x0 H14) in 
(ex2_ind A (\lambda (a0: A).(eq A x0 (AHead x1 a0))) (\lambda (a0: A).(eq A 
x2 (asucc g a0))) (ex2 A (\lambda (a1: A).(arity g c0 (THead (Flat Appl) w v) 
a1)) (\lambda (a1: A).(arity g c0 (THead (Flat Appl) w (THead (Bind Abst) u 
t)) (asucc g a1)))) (\lambda (x3: A).(\lambda (H16: (eq A x0 (AHead x1 
x3))).(\lambda (H17: (eq A x2 (asucc g x3))).(let H18 \def (eq_ind A x2 
(\lambda (a: A).(arity g (CHead c0 (Bind Abst) u) t a)) H13 (asucc g x3) H17) 
in (let H19 \def (eq_ind A x0 (\lambda (a: A).(arity g c0 v a)) H8 (AHead x1 
x3) H16) in (ex_intro2 A (\lambda (a1: A).(arity g c0 (THead (Flat Appl) w v) 
a1)) (\lambda (a1: A).(arity g c0 (THead (Flat Appl) w (THead (Bind Abst) u 
t)) (asucc g a1))) x3 (arity_appl g c0 w x1 (arity_repl g c0 w x H5 x1 
(leq_sym g x1 x (asucc_inj g x1 x (arity_mono g c0 u (asucc g x1) H12 (asucc 
g x) H6)))) v x3 H19) (arity_appl g c0 w x H5 (THead (Bind Abst) u t) (asucc 
g x3) (arity_head g c0 u x H6 t (asucc g x3) H18)))))))) H15)))))))) H10))))) 
H7))))) H4))))))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (ty3 g c0 t3 t4)).(\lambda (H1: (ex2 A (\lambda (a1: 
A).(arity g c0 t3 a1)) (\lambda (a1: A).(arity g c0 t4 (asucc g 
a1))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t4 t0)).(\lambda (H3: (ex2 A 
(\lambda (a1: A).(arity g c0 t4 a1)) (\lambda (a1: A).(arity g c0 t0 (asucc g 
a1))))).(let H4 \def H1 in (ex2_ind A (\lambda (a1: A).(arity g c0 t3 a1)) 
(\lambda (a1: A).(arity g c0 t4 (asucc g a1))) (ex2 A (\lambda (a1: A).(arity 
g c0 (THead (Flat Cast) t4 t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Flat 
Cast) t0 t4) (asucc g a1)))) (\lambda (x: A).(\lambda (H5: (arity g c0 t3 
x)).(\lambda (H6: (arity g c0 t4 (asucc g x))).(let H7 \def H3 in (ex2_ind A 
(\lambda (a1: A).(arity g c0 t4 a1)) (\lambda (a1: A).(arity g c0 t0 (asucc g 
a1))) (ex2 A (\lambda (a1: A).(arity g c0 (THead (Flat Cast) t4 t3) a1)) 
(\lambda (a1: A).(arity g c0 (THead (Flat Cast) t0 t4) (asucc g a1)))) 
(\lambda (x0: A).(\lambda (H8: (arity g c0 t4 x0)).(\lambda (H9: (arity g c0 
t0 (asucc g x0))).(ex_intro2 A (\lambda (a1: A).(arity g c0 (THead (Flat 
Cast) t4 t3) a1)) (\lambda (a1: A).(arity g c0 (THead (Flat Cast) t0 t4) 
(asucc g a1))) x (arity_cast g c0 t4 x H6 t3 H5) (arity_cast g c0 t0 (asucc g 
x) (arity_repl g c0 t0 (asucc g x0) H9 (asucc g (asucc g x)) (asucc_repl g x0 
(asucc g x) (arity_mono g c0 t4 x0 H8 (asucc g x) H6))) t4 H6))))) H7))))) 
H4)))))))))) c t1 t2 H))))).
(* COMMENTS
Initial nodes: 3761
END *)

