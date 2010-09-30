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

include "Basic-1/pr0/fwd.ma".

include "Basic-1/subst0/dec.ma".

include "Basic-1/T/dec.ma".

include "Basic-1/T/props.ma".

theorem nf0_dec:
 \forall (t1: T).(or (\forall (t2: T).((pr0 t1 t2) \to (eq T t1 t2))) (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 t1 t2))))
\def
 \lambda (t1: T).(T_ind (\lambda (t: T).(or (\forall (t2: T).((pr0 t t2) \to 
(eq T t t2))) (ex2 T (\lambda (t2: T).((eq T t t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 t t2))))) (\lambda (n: nat).(or_introl 
(\forall (t2: T).((pr0 (TSort n) t2) \to (eq T (TSort n) t2))) (ex2 T 
(\lambda (t2: T).((eq T (TSort n) t2) \to (\forall (P: Prop).P))) (\lambda 
(t2: T).(pr0 (TSort n) t2))) (\lambda (t2: T).(\lambda (H: (pr0 (TSort n) 
t2)).(eq_ind_r T (TSort n) (\lambda (t: T).(eq T (TSort n) t)) (refl_equal T 
(TSort n)) t2 (pr0_gen_sort t2 n H)))))) (\lambda (n: nat).(or_introl 
(\forall (t2: T).((pr0 (TLRef n) t2) \to (eq T (TLRef n) t2))) (ex2 T 
(\lambda (t2: T).((eq T (TLRef n) t2) \to (\forall (P: Prop).P))) (\lambda 
(t2: T).(pr0 (TLRef n) t2))) (\lambda (t2: T).(\lambda (H: (pr0 (TLRef n) 
t2)).(eq_ind_r T (TLRef n) (\lambda (t: T).(eq T (TLRef n) t)) (refl_equal T 
(TLRef n)) t2 (pr0_gen_lref t2 n H)))))) (\lambda (k: K).(\lambda (t: 
T).(\lambda (H: (or (\forall (t2: T).((pr0 t t2) \to (eq T t t2))) (ex2 T 
(\lambda (t2: T).((eq T t t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 t t2))))).(\lambda (t0: T).(\lambda (H0: (or (\forall (t2: T).((pr0 
t0 t2) \to (eq T t0 t2))) (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2))))).(K_ind (\lambda (k0: K).(or 
(\forall (t2: T).((pr0 (THead k0 t t0) t2) \to (eq T (THead k0 t t0) t2))) 
(ex2 T (\lambda (t2: T).((eq T (THead k0 t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead k0 t t0) t2))))) (\lambda (b: 
B).(B_ind (\lambda (b0: B).(or (\forall (t2: T).((pr0 (THead (Bind b0) t t0) 
t2) \to (eq T (THead (Bind b0) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T 
(THead (Bind b0) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Bind b0) t t0) t2))))) (or_intror (\forall (t2: T).((pr0 (THead (Bind 
Abbr) t t0) t2) \to (eq T (THead (Bind Abbr) t t0) t2))) (ex2 T (\lambda (t2: 
T).((eq T (THead (Bind Abbr) t t0) t2) \to (\forall (P: Prop).P))) (\lambda 
(t2: T).(pr0 (THead (Bind Abbr) t t0) t2))) (let H_x \def (dnf_dec t t0 O) in 
(let H1 \def H_x in (ex_ind T (\lambda (v: T).(or (subst0 O t t0 (lift (S O) 
O v)) (eq T t0 (lift (S O) O v)))) (ex2 T (\lambda (t2: T).((eq T (THead 
(Bind Abbr) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Bind Abbr) t t0) t2))) (\lambda (x: T).(\lambda (H2: (or (subst0 O t 
t0 (lift (S O) O x)) (eq T t0 (lift (S O) O x)))).(or_ind (subst0 O t t0 
(lift (S O) O x)) (eq T t0 (lift (S O) O x)) (ex2 T (\lambda (t2: T).((eq T 
(THead (Bind Abbr) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 (THead (Bind Abbr) t t0) t2))) (\lambda (H3: (subst0 O t t0 (lift (S 
O) O x))).(ex_intro2 T (\lambda (t2: T).((eq T (THead (Bind Abbr) t t0) t2) 
\to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abbr) t t0) 
t2)) (THead (Bind Abbr) t (lift (S O) O x)) (\lambda (H4: (eq T (THead (Bind 
Abbr) t t0) (THead (Bind Abbr) t (lift (S O) O x)))).(\lambda (P: Prop).(let 
H5 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t2) 
\Rightarrow t2])) (THead (Bind Abbr) t t0) (THead (Bind Abbr) t (lift (S O) O 
x)) H4) in (let H6 \def (eq_ind T t0 (\lambda (t2: T).(subst0 O t t2 (lift (S 
O) O x))) H3 (lift (S O) O x) H5) in (subst0_refl t (lift (S O) O x) O H6 
P))))) (pr0_delta t t (pr0_refl t) t0 t0 (pr0_refl t0) (lift (S O) O x) H3))) 
(\lambda (H3: (eq T t0 (lift (S O) O x))).(eq_ind_r T (lift (S O) O x) 
(\lambda (t2: T).(ex2 T (\lambda (t3: T).((eq T (THead (Bind Abbr) t t2) t3) 
\to (\forall (P: Prop).P))) (\lambda (t3: T).(pr0 (THead (Bind Abbr) t t2) 
t3)))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Bind Abbr) t (lift (S O) 
O x)) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind 
Abbr) t (lift (S O) O x)) t2)) x (\lambda (H4: (eq T (THead (Bind Abbr) t 
(lift (S O) O x)) x)).(\lambda (P: Prop).(thead_x_lift_y_y (Bind Abbr) x t (S 
O) O H4 P))) (pr0_zeta Abbr not_abbr_abst x x (pr0_refl x) t)) t0 H3)) H2))) 
H1)))) (let H1 \def H in (or_ind (\forall (t2: T).((pr0 t t2) \to (eq T t 
t2))) (ex2 T (\lambda (t2: T).((eq T t t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr0 t t2))) (or (\forall (t2: T).((pr0 (THead (Bind Abst) t 
t0) t2) \to (eq T (THead (Bind Abst) t t0) t2))) (ex2 T (\lambda (t2: T).((eq 
T (THead (Bind Abst) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 (THead (Bind Abst) t t0) t2)))) (\lambda (H2: ((\forall (t2: T).((pr0 
t t2) \to (eq T t t2))))).(let H3 \def H0 in (or_ind (\forall (t2: T).((pr0 
t0 t2) \to (eq T t0 t2))) (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2))) (or (\forall (t2: T).((pr0 
(THead (Bind Abst) t t0) t2) \to (eq T (THead (Bind Abst) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2)))) (\lambda 
(H4: ((\forall (t2: T).((pr0 t0 t2) \to (eq T t0 t2))))).(or_introl (\forall 
(t2: T).((pr0 (THead (Bind Abst) t t0) t2) \to (eq T (THead (Bind Abst) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2))) 
(\lambda (t2: T).(\lambda (H5: (pr0 (THead (Bind Abst) t t0) t2)).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 t u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t0 t3))) (eq T (THead (Bind Abst) t t0) t2) (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H6: (eq T t2 (THead (Bind Abst) x0 x1))).(\lambda (H7: (pr0 
t x0)).(\lambda (H8: (pr0 t0 x1)).(let H_y \def (H4 x1 H8) in (let H_y0 \def 
(H2 x0 H7) in (let H9 \def (eq_ind_r T x1 (\lambda (t3: T).(pr0 t0 t3)) H8 t0 
H_y) in (let H10 \def (eq_ind_r T x1 (\lambda (t3: T).(eq T t2 (THead (Bind 
Abst) x0 t3))) H6 t0 H_y) in (let H11 \def (eq_ind_r T x0 (\lambda (t3: 
T).(pr0 t t3)) H7 t H_y0) in (let H12 \def (eq_ind_r T x0 (\lambda (t3: 
T).(eq T t2 (THead (Bind Abst) t3 t0))) H10 t H_y0) in (eq_ind_r T (THead 
(Bind Abst) t t0) (\lambda (t3: T).(eq T (THead (Bind Abst) t t0) t3)) 
(refl_equal T (THead (Bind Abst) t t0)) t2 H12)))))))))))) (pr0_gen_abst t t0 
t2 H5)))))) (\lambda (H4: (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2)))).(ex2_ind T (\lambda (t2: 
T).((eq T t0 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2)) 
(or (\forall (t2: T).((pr0 (THead (Bind Abst) t t0) t2) \to (eq T (THead 
(Bind Abst) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Abst) t 
t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) 
t t0) t2)))) (\lambda (x: T).(\lambda (H5: (((eq T t0 x) \to (\forall (P: 
Prop).P)))).(\lambda (H6: (pr0 t0 x)).(or_intror (\forall (t2: T).((pr0 
(THead (Bind Abst) t t0) t2) \to (eq T (THead (Bind Abst) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2))) (ex_intro2 T 
(\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2)) (THead (Bind 
Abst) t x) (\lambda (H7: (eq T (THead (Bind Abst) t t0) (THead (Bind Abst) t 
x))).(\lambda (P: Prop).(let H8 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) (THead (Bind Abst) t t0) 
(THead (Bind Abst) t x) H7) in (let H9 \def (eq_ind_r T x (\lambda (t2: 
T).(pr0 t0 t2)) H6 t0 H8) in (let H10 \def (eq_ind_r T x (\lambda (t2: 
T).((eq T t0 t2) \to (\forall (P0: Prop).P0))) H5 t0 H8) in (H10 (refl_equal 
T t0) P)))))) (pr0_comp t t (pr0_refl t) t0 x H6 (Bind Abst))))))) H4)) H3))) 
(\lambda (H2: (ex2 T (\lambda (t2: T).((eq T t t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 t t2)))).(ex2_ind T (\lambda (t2: T).((eq T 
t t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t t2)) (or (\forall 
(t2: T).((pr0 (THead (Bind Abst) t t0) t2) \to (eq T (THead (Bind Abst) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2)))) 
(\lambda (x: T).(\lambda (H3: (((eq T t x) \to (\forall (P: 
Prop).P)))).(\lambda (H4: (pr0 t x)).(or_intror (\forall (t2: T).((pr0 (THead 
(Bind Abst) t t0) t2) \to (eq T (THead (Bind Abst) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2))) (ex_intro2 T 
(\lambda (t2: T).((eq T (THead (Bind Abst) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Abst) t t0) t2)) (THead (Bind 
Abst) x t0) (\lambda (H5: (eq T (THead (Bind Abst) t t0) (THead (Bind Abst) x 
t0))).(\lambda (P: Prop).(let H6 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ t2 _) \Rightarrow t2])) (THead (Bind Abst) t t0) 
(THead (Bind Abst) x t0) H5) in (let H7 \def (eq_ind_r T x (\lambda (t2: 
T).(pr0 t t2)) H4 t H6) in (let H8 \def (eq_ind_r T x (\lambda (t2: T).((eq T 
t t2) \to (\forall (P0: Prop).P0))) H3 t H6) in (H8 (refl_equal T t) P)))))) 
(pr0_comp t x H4 t0 t0 (pr0_refl t0) (Bind Abst))))))) H2)) H1)) (let H_x 
\def (dnf_dec t t0 O) in (let H1 \def H_x in (ex_ind T (\lambda (v: T).(or 
(subst0 O t t0 (lift (S O) O v)) (eq T t0 (lift (S O) O v)))) (or (\forall 
(t2: T).((pr0 (THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)))) 
(\lambda (x: T).(\lambda (H2: (or (subst0 O t t0 (lift (S O) O x)) (eq T t0 
(lift (S O) O x)))).(or_ind (subst0 O t t0 (lift (S O) O x)) (eq T t0 (lift 
(S O) O x)) (or (\forall (t2: T).((pr0 (THead (Bind Void) t t0) t2) \to (eq T 
(THead (Bind Void) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind 
Void) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead 
(Bind Void) t t0) t2)))) (\lambda (H3: (subst0 O t t0 (lift (S O) O x))).(let 
H4 \def H in (or_ind (\forall (t2: T).((pr0 t t2) \to (eq T t t2))) (ex2 T 
(\lambda (t2: T).((eq T t t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 t t2))) (or (\forall (t2: T).((pr0 (THead (Bind Void) t t0) t2) \to 
(eq T (THead (Bind Void) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead 
(Bind Void) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Bind Void) t t0) t2)))) (\lambda (H5: ((\forall (t2: T).((pr0 t t2) 
\to (eq T t t2))))).(let H6 \def H0 in (or_ind (\forall (t2: T).((pr0 t0 t2) 
\to (eq T t0 t2))) (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 t0 t2))) (or (\forall (t2: T).((pr0 (THead 
(Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)))) (\lambda 
(H7: ((\forall (t2: T).((pr0 t0 t2) \to (eq T t0 t2))))).(or_introl (\forall 
(t2: T).((pr0 (THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2))) 
(\lambda (t2: T).(\lambda (H8: (pr0 (THead (Bind Void) t t0) t2)).(or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 t u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr0 t0 t3)))) (pr0 t0 (lift (S O) O t2)) (eq T (THead (Bind Void) t 
t0) t2) (\lambda (H9: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 t u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t0 t3))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 t u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t0 
t3))) (eq T (THead (Bind Void) t t0) t2) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H10: (eq T t2 (THead (Bind Void) x0 x1))).(\lambda (H11: (pr0 t 
x0)).(\lambda (H12: (pr0 t0 x1)).(let H_y \def (H7 x1 H12) in (let H_y0 \def 
(H5 x0 H11) in (let H13 \def (eq_ind_r T x1 (\lambda (t3: T).(pr0 t0 t3)) H12 
t0 H_y) in (let H14 \def (eq_ind_r T x1 (\lambda (t3: T).(eq T t2 (THead 
(Bind Void) x0 t3))) H10 t0 H_y) in (let H15 \def (eq_ind_r T x0 (\lambda 
(t3: T).(pr0 t t3)) H11 t H_y0) in (let H16 \def (eq_ind_r T x0 (\lambda (t3: 
T).(eq T t2 (THead (Bind Void) t3 t0))) H14 t H_y0) in (eq_ind_r T (THead 
(Bind Void) t t0) (\lambda (t3: T).(eq T (THead (Bind Void) t t0) t3)) 
(refl_equal T (THead (Bind Void) t t0)) t2 H16)))))))))))) H9)) (\lambda (H9: 
(pr0 t0 (lift (S O) O t2))).(let H_y \def (H7 (lift (S O) O t2) H9) in (let 
H10 \def (eq_ind T t0 (\lambda (t3: T).(subst0 O t t3 (lift (S O) O x))) H3 
(lift (S O) O t2) H_y) in (eq_ind_r T (lift (S O) O t2) (\lambda (t3: T).(eq 
T (THead (Bind Void) t t3) t2)) (subst0_gen_lift_false t2 t (lift (S O) O x) 
(S O) O O (le_n O) (eq_ind_r nat (plus (S O) O) (\lambda (n: nat).(lt O n)) 
(le_n (plus (S O) O)) (plus O (S O)) (plus_sym O (S O))) H10 (eq T (THead 
(Bind Void) t (lift (S O) O t2)) t2)) t0 H_y)))) (pr0_gen_void t t0 t2 
H8)))))) (\lambda (H7: (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 t0 t2)))).(ex2_ind T (\lambda (t2: T).((eq T 
t0 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2)) (or (\forall 
(t2: T).((pr0 (THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)))) 
(\lambda (x0: T).(\lambda (H8: (((eq T t0 x0) \to (\forall (P: 
Prop).P)))).(\lambda (H9: (pr0 t0 x0)).(or_intror (\forall (t2: T).((pr0 
(THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2))) (ex_intro2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)) (THead (Bind 
Void) t x0) (\lambda (H10: (eq T (THead (Bind Void) t t0) (THead (Bind Void) 
t x0))).(\lambda (P: Prop).(let H11 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) (THead (Bind Void) t t0) 
(THead (Bind Void) t x0) H10) in (let H12 \def (eq_ind_r T x0 (\lambda (t2: 
T).(pr0 t0 t2)) H9 t0 H11) in (let H13 \def (eq_ind_r T x0 (\lambda (t2: 
T).((eq T t0 t2) \to (\forall (P0: Prop).P0))) H8 t0 H11) in (H13 (refl_equal 
T t0) P)))))) (pr0_comp t t (pr0_refl t) t0 x0 H9 (Bind Void))))))) H7)) 
H6))) (\lambda (H5: (ex2 T (\lambda (t2: T).((eq T t t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 t t2)))).(ex2_ind T (\lambda (t2: T).((eq T 
t t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t t2)) (or (\forall 
(t2: T).((pr0 (THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)))) 
(\lambda (x0: T).(\lambda (H6: (((eq T t x0) \to (\forall (P: 
Prop).P)))).(\lambda (H7: (pr0 t x0)).(or_intror (\forall (t2: T).((pr0 
(THead (Bind Void) t t0) t2) \to (eq T (THead (Bind Void) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2))) (ex_intro2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t t0) t2)) (THead (Bind 
Void) x0 t0) (\lambda (H8: (eq T (THead (Bind Void) t t0) (THead (Bind Void) 
x0 t0))).(\lambda (P: Prop).(let H9 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ t2 _) \Rightarrow t2])) (THead (Bind Void) t t0) 
(THead (Bind Void) x0 t0) H8) in (let H10 \def (eq_ind_r T x0 (\lambda (t2: 
T).(pr0 t t2)) H7 t H9) in (let H11 \def (eq_ind_r T x0 (\lambda (t2: T).((eq 
T t t2) \to (\forall (P0: Prop).P0))) H6 t H9) in (H11 (refl_equal T t) 
P)))))) (pr0_comp t x0 H7 t0 t0 (pr0_refl t0) (Bind Void))))))) H5)) H4))) 
(\lambda (H3: (eq T t0 (lift (S O) O x))).(let H4 \def (eq_ind T t0 (\lambda 
(t2: T).(or (\forall (t3: T).((pr0 t2 t3) \to (eq T t2 t3))) (ex2 T (\lambda 
(t3: T).((eq T t2 t3) \to (\forall (P: Prop).P))) (\lambda (t3: T).(pr0 t2 
t3))))) H0 (lift (S O) O x) H3) in (eq_ind_r T (lift (S O) O x) (\lambda (t2: 
T).(or (\forall (t3: T).((pr0 (THead (Bind Void) t t2) t3) \to (eq T (THead 
(Bind Void) t t2) t3))) (ex2 T (\lambda (t3: T).((eq T (THead (Bind Void) t 
t2) t3) \to (\forall (P: Prop).P))) (\lambda (t3: T).(pr0 (THead (Bind Void) 
t t2) t3))))) (or_intror (\forall (t2: T).((pr0 (THead (Bind Void) t (lift (S 
O) O x)) t2) \to (eq T (THead (Bind Void) t (lift (S O) O x)) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Bind Void) t (lift (S O) O x)) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) t (lift (S 
O) O x)) t2))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Bind Void) t 
(lift (S O) O x)) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Bind Void) t (lift (S O) O x)) t2)) x (\lambda (H5: (eq T (THead 
(Bind Void) t (lift (S O) O x)) x)).(\lambda (P: Prop).(thead_x_lift_y_y 
(Bind Void) x t (S O) O H5 P))) (pr0_zeta Void (sym_not_eq B Abst Void 
not_abst_void) x x (pr0_refl x) t))) t0 H3))) H2))) H1))) b)) (\lambda (f: 
F).(F_ind (\lambda (f0: F).(or (\forall (t2: T).((pr0 (THead (Flat f0) t t0) 
t2) \to (eq T (THead (Flat f0) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T 
(THead (Flat f0) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Flat f0) t t0) t2))))) (let H_x \def (binder_dec t0) in (let H1 \def 
H_x in (or_ind (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T t0 (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))) (or (\forall (t2: T).((pr0 (THead (Flat Appl) t t0) t2) \to (eq 
T (THead (Flat Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat 
Appl) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead 
(Flat Appl) t t0) t2)))) (\lambda (H2: (ex_3 B T T (\lambda (b: B).(\lambda 
(w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w u))))))).(ex_3_ind B T T 
(\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w 
u))))) (or (\forall (t2: T).((pr0 (THead (Flat Appl) t t0) t2) \to (eq T 
(THead (Flat Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat 
Appl) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead 
(Flat Appl) t t0) t2)))) (\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (H3: (eq T t0 (THead (Bind x0) x1 x2))).(let H4 \def (eq_ind T t0 
(\lambda (t2: T).(or (\forall (t3: T).((pr0 t2 t3) \to (eq T t2 t3))) (ex2 T 
(\lambda (t3: T).((eq T t2 t3) \to (\forall (P: Prop).P))) (\lambda (t3: 
T).(pr0 t2 t3))))) H0 (THead (Bind x0) x1 x2) H3) in (eq_ind_r T (THead (Bind 
x0) x1 x2) (\lambda (t2: T).(or (\forall (t3: T).((pr0 (THead (Flat Appl) t 
t2) t3) \to (eq T (THead (Flat Appl) t t2) t3))) (ex2 T (\lambda (t3: T).((eq 
T (THead (Flat Appl) t t2) t3) \to (\forall (P: Prop).P))) (\lambda (t3: 
T).(pr0 (THead (Flat Appl) t t2) t3))))) (B_ind (\lambda (b: B).((or (\forall 
(t2: T).((pr0 (THead (Bind b) x1 x2) t2) \to (eq T (THead (Bind b) x1 x2) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind b) x1 x2) t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind b) x1 x2) t2)))) \to (or 
(\forall (t2: T).((pr0 (THead (Flat Appl) t (THead (Bind b) x1 x2)) t2) \to 
(eq T (THead (Flat Appl) t (THead (Bind b) x1 x2)) t2))) (ex2 T (\lambda (t2: 
T).((eq T (THead (Flat Appl) t (THead (Bind b) x1 x2)) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t (THead (Bind b) x1 x2)) 
t2)))))) (\lambda (_: (or (\forall (t2: T).((pr0 (THead (Bind Abbr) x1 x2) 
t2) \to (eq T (THead (Bind Abbr) x1 x2) t2))) (ex2 T (\lambda (t2: T).((eq T 
(THead (Bind Abbr) x1 x2) t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 (THead (Bind Abbr) x1 x2) t2))))).(or_intror (\forall (t2: T).((pr0 
(THead (Flat Appl) t (THead (Bind Abbr) x1 x2)) t2) \to (eq T (THead (Flat 
Appl) t (THead (Bind Abbr) x1 x2)) t2))) (ex2 T (\lambda (t2: T).((eq T 
(THead (Flat Appl) t (THead (Bind Abbr) x1 x2)) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t (THead (Bind Abbr) x1 
x2)) t2))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t (THead 
(Bind Abbr) x1 x2)) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Flat Appl) t (THead (Bind Abbr) x1 x2)) t2)) (THead (Bind Abbr) x1 
(THead (Flat Appl) (lift (S O) O t) x2)) (\lambda (H6: (eq T (THead (Flat 
Appl) t (THead (Bind Abbr) x1 x2)) (THead (Bind Abbr) x1 (THead (Flat Appl) 
(lift (S O) O t) x2)))).(\lambda (P: Prop).(let H7 \def (eq_ind T (THead 
(Flat Appl) t (THead (Bind Abbr) x1 x2)) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ t2) \Rightarrow (match t2 in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])])) I (THead (Bind 
Abbr) x1 (THead (Flat Appl) (lift (S O) O t) x2)) H6) in (False_ind P H7)))) 
(pr0_upsilon Abbr not_abbr_abst t t (pr0_refl t) x1 x1 (pr0_refl x1) x2 x2 
(pr0_refl x2))))) (\lambda (_: (or (\forall (t2: T).((pr0 (THead (Bind Abst) 
x1 x2) t2) \to (eq T (THead (Bind Abst) x1 x2) t2))) (ex2 T (\lambda (t2: 
T).((eq T (THead (Bind Abst) x1 x2) t2) \to (\forall (P: Prop).P))) (\lambda 
(t2: T).(pr0 (THead (Bind Abst) x1 x2) t2))))).(or_intror (\forall (t2: 
T).((pr0 (THead (Flat Appl) t (THead (Bind Abst) x1 x2)) t2) \to (eq T (THead 
(Flat Appl) t (THead (Bind Abst) x1 x2)) t2))) (ex2 T (\lambda (t2: T).((eq T 
(THead (Flat Appl) t (THead (Bind Abst) x1 x2)) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t (THead (Bind Abst) x1 
x2)) t2))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t (THead 
(Bind Abst) x1 x2)) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 
(THead (Flat Appl) t (THead (Bind Abst) x1 x2)) t2)) (THead (Bind Abbr) t x2) 
(\lambda (H6: (eq T (THead (Flat Appl) t (THead (Bind Abst) x1 x2)) (THead 
(Bind Abbr) t x2))).(\lambda (P: Prop).(let H7 \def (eq_ind T (THead (Flat 
Appl) t (THead (Bind Abst) x1 x2)) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abbr) t x2) H6) in (False_ind P H7)))) (pr0_beta x1 
t t (pr0_refl t) x2 x2 (pr0_refl x2))))) (\lambda (_: (or (\forall (t2: 
T).((pr0 (THead (Bind Void) x1 x2) t2) \to (eq T (THead (Bind Void) x1 x2) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Bind Void) x1 x2) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Bind Void) x1 x2) 
t2))))).(or_intror (\forall (t2: T).((pr0 (THead (Flat Appl) t (THead (Bind 
Void) x1 x2)) t2) \to (eq T (THead (Flat Appl) t (THead (Bind Void) x1 x2)) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t (THead (Bind Void) 
x1 x2)) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat 
Appl) t (THead (Bind Void) x1 x2)) t2))) (ex_intro2 T (\lambda (t2: T).((eq T 
(THead (Flat Appl) t (THead (Bind Void) x1 x2)) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t (THead (Bind Void) x1 
x2)) t2)) (THead (Bind Void) x1 (THead (Flat Appl) (lift (S O) O t) x2)) 
(\lambda (H6: (eq T (THead (Flat Appl) t (THead (Bind Void) x1 x2)) (THead 
(Bind Void) x1 (THead (Flat Appl) (lift (S O) O t) x2)))).(\lambda (P: 
Prop).(let H7 \def (eq_ind T (THead (Flat Appl) t (THead (Bind Void) x1 x2)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ t2) \Rightarrow 
(match t2 in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False 
| (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) 
\Rightarrow False])])])) I (THead (Bind Void) x1 (THead (Flat Appl) (lift (S 
O) O t) x2)) H6) in (False_ind P H7)))) (pr0_upsilon Void (sym_not_eq B Abst 
Void not_abst_void) t t (pr0_refl t) x1 x1 (pr0_refl x1) x2 x2 (pr0_refl 
x2))))) x0 H4) t0 H3)))))) H2)) (\lambda (H2: ((\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))))).(let H3 \def H in (or_ind (\forall (t2: T).((pr0 t t2) \to (eq 
T t t2))) (ex2 T (\lambda (t2: T).((eq T t t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr0 t t2))) (or (\forall (t2: T).((pr0 (THead (Flat Appl) t 
t0) t2) \to (eq T (THead (Flat Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq 
T (THead (Flat Appl) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 (THead (Flat Appl) t t0) t2)))) (\lambda (H4: ((\forall (t2: T).((pr0 
t t2) \to (eq T t t2))))).(let H5 \def H0 in (or_ind (\forall (t2: T).((pr0 
t0 t2) \to (eq T t0 t2))) (ex2 T (\lambda (t2: T).((eq T t0 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr0 t0 t2))) (or (\forall (t2: T).((pr0 
(THead (Flat Appl) t t0) t2) \to (eq T (THead (Flat Appl) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) t2)))) (\lambda 
(H6: ((\forall (t2: T).((pr0 t0 t2) \to (eq T t0 t2))))).(or_introl (\forall 
(t2: T).((pr0 (THead (Flat Appl) t t0) t2) \to (eq T (THead (Flat Appl) t t0) 
t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) t2))) 
(\lambda (t2: T).(\lambda (H7: (pr0 (THead (Flat Appl) t t0) t2)).(or3_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 t u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr0 t0 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t0 (THead (Bind Abst) y1 z1)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr0 t u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t0 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 t 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))) (eq T (THead (Flat Appl) t t0) t2) (\lambda (H8: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 t u2))) (\lambda (_: T).(\lambda 
(t3: T).(pr0 t0 t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 t 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t0 t3))) (eq T (THead (Flat Appl) 
t t0) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H9: (eq T t2 (THead 
(Flat Appl) x0 x1))).(\lambda (H10: (pr0 t x0)).(\lambda (H11: (pr0 t0 
x1)).(let H_y \def (H6 x1 H11) in (let H_y0 \def (H4 x0 H10) in (let H12 \def 
(eq_ind_r T x1 (\lambda (t3: T).(pr0 t0 t3)) H11 t0 H_y) in (let H13 \def 
(eq_ind_r T x1 (\lambda (t3: T).(eq T t2 (THead (Flat Appl) x0 t3))) H9 t0 
H_y) in (let H14 \def (eq_ind_r T x0 (\lambda (t3: T).(pr0 t t3)) H10 t H_y0) 
in (let H15 \def (eq_ind_r T x0 (\lambda (t3: T).(eq T t2 (THead (Flat Appl) 
t3 t0))) H13 t H_y0) in (eq_ind_r T (THead (Flat Appl) t t0) (\lambda (t3: 
T).(eq T (THead (Flat Appl) t t0) t3)) (refl_equal T (THead (Flat Appl) t 
t0)) t2 H15)))))))))))) H8)) (\lambda (H8: (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t0 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 t u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))))).(ex4_4_ind T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t0 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 t u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))) (eq 
T (THead (Flat Appl) t t0) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (H9: (eq T t0 (THead (Bind Abst) x0 
x1))).(\lambda (H10: (eq T t2 (THead (Bind Abbr) x2 x3))).(\lambda (_: (pr0 t 
x2)).(\lambda (_: (pr0 x1 x3)).(eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda 
(t3: T).(eq T (THead (Flat Appl) t t0) t3)) (let H13 \def (eq_ind T t0 
(\lambda (t3: T).(\forall (t4: T).((pr0 t3 t4) \to (eq T t3 t4)))) H6 (THead 
(Bind Abst) x0 x1) H9) in (let H14 \def (eq_ind T t0 (\lambda (t3: 
T).(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t3 (THead (Bind b) 
w u)) \to (\forall (P: Prop).P)))))) H2 (THead (Bind Abst) x0 x1) H9) in 
(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t3: T).(eq T (THead (Flat 
Appl) t t3) (THead (Bind Abbr) x2 x3))) (H14 Abst x0 x1 (H13 (THead (Bind 
Abst) x0 x1) (pr0_refl (THead (Bind Abst) x0 x1))) (eq T (THead (Flat Appl) t 
(THead (Bind Abst) x0 x1)) (THead (Bind Abbr) x2 x3))) t0 H9))) t2 
H10))))))))) H8)) (\lambda (H8: (ex6_6 B T T T T T (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not 
(eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t0 (THead (Bind b) 
y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead (Flat 
Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 t u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t0 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead (Flat Appl) (lift 
(S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 t u2))))))) (\lambda 
(_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: 
T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))))) 
(eq T (THead (Flat Appl) t t0) t2) (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not 
(eq B x0 Abst))).(\lambda (H10: (eq T t0 (THead (Bind x0) x1 x2))).(\lambda 
(H11: (eq T t2 (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) 
x5)))).(\lambda (_: (pr0 t x3)).(\lambda (_: (pr0 x1 x4)).(\lambda (_: (pr0 
x2 x5)).(eq_ind_r T (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) 
x5)) (\lambda (t3: T).(eq T (THead (Flat Appl) t t0) t3)) (let H15 \def 
(eq_ind T t0 (\lambda (t3: T).(\forall (t4: T).((pr0 t3 t4) \to (eq T t3 
t4)))) H6 (THead (Bind x0) x1 x2) H10) in (let H16 \def (eq_ind T t0 (\lambda 
(t3: T).(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t3 (THead 
(Bind b) w u)) \to (\forall (P: Prop).P)))))) H2 (THead (Bind x0) x1 x2) H10) 
in (eq_ind_r T (THead (Bind x0) x1 x2) (\lambda (t3: T).(eq T (THead (Flat 
Appl) t t3) (THead (Bind x0) x4 (THead (Flat Appl) (lift (S O) O x3) x5)))) 
(H16 x0 x1 x2 (H15 (THead (Bind x0) x1 x2) (pr0_refl (THead (Bind x0) x1 
x2))) (eq T (THead (Flat Appl) t (THead (Bind x0) x1 x2)) (THead (Bind x0) x4 
(THead (Flat Appl) (lift (S O) O x3) x5)))) t0 H10))) t2 H11))))))))))))) 
H8)) (pr0_gen_appl t t0 t2 H7)))))) (\lambda (H6: (ex2 T (\lambda (t2: 
T).((eq T t0 t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t0 
t2)))).(ex2_ind T (\lambda (t2: T).((eq T t0 t2) \to (\forall (P: Prop).P))) 
(\lambda (t2: T).(pr0 t0 t2)) (or (\forall (t2: T).((pr0 (THead (Flat Appl) t 
t0) t2) \to (eq T (THead (Flat Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq 
T (THead (Flat Appl) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr0 (THead (Flat Appl) t t0) t2)))) (\lambda (x: T).(\lambda (H7: (((eq T 
t0 x) \to (\forall (P: Prop).P)))).(\lambda (H8: (pr0 t0 x)).(or_intror 
(\forall (t2: T).((pr0 (THead (Flat Appl) t t0) t2) \to (eq T (THead (Flat 
Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) 
\to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) 
t2))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) t2)) 
(THead (Flat Appl) t x) (\lambda (H9: (eq T (THead (Flat Appl) t t0) (THead 
(Flat Appl) t x))).(\lambda (P: Prop).(let H10 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) (THead (Flat 
Appl) t t0) (THead (Flat Appl) t x) H9) in (let H11 \def (eq_ind_r T x 
(\lambda (t2: T).(pr0 t0 t2)) H8 t0 H10) in (let H12 \def (eq_ind_r T x 
(\lambda (t2: T).((eq T t0 t2) \to (\forall (P0: Prop).P0))) H7 t0 H10) in 
(H12 (refl_equal T t0) P)))))) (pr0_comp t t (pr0_refl t) t0 x H8 (Flat 
Appl))))))) H6)) H5))) (\lambda (H4: (ex2 T (\lambda (t2: T).((eq T t t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t t2)))).(ex2_ind T (\lambda 
(t2: T).((eq T t t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 t t2)) 
(or (\forall (t2: T).((pr0 (THead (Flat Appl) t t0) t2) \to (eq T (THead 
(Flat Appl) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat Appl) t 
t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) 
t t0) t2)))) (\lambda (x: T).(\lambda (H5: (((eq T t x) \to (\forall (P: 
Prop).P)))).(\lambda (H6: (pr0 t x)).(or_intror (\forall (t2: T).((pr0 (THead 
(Flat Appl) t t0) t2) \to (eq T (THead (Flat Appl) t t0) t2))) (ex2 T 
(\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) t2))) (ex_intro2 T 
(\lambda (t2: T).((eq T (THead (Flat Appl) t t0) t2) \to (\forall (P: 
Prop).P))) (\lambda (t2: T).(pr0 (THead (Flat Appl) t t0) t2)) (THead (Flat 
Appl) x t0) (\lambda (H7: (eq T (THead (Flat Appl) t t0) (THead (Flat Appl) x 
t0))).(\lambda (P: Prop).(let H8 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ t2 _) \Rightarrow t2])) (THead (Flat Appl) t t0) 
(THead (Flat Appl) x t0) H7) in (let H9 \def (eq_ind_r T x (\lambda (t2: 
T).(pr0 t t2)) H6 t H8) in (let H10 \def (eq_ind_r T x (\lambda (t2: T).((eq 
T t t2) \to (\forall (P0: Prop).P0))) H5 t H8) in (H10 (refl_equal T t) 
P)))))) (pr0_comp t x H6 t0 t0 (pr0_refl t0) (Flat Appl))))))) H4)) H3))) 
H1))) (or_intror (\forall (t2: T).((pr0 (THead (Flat Cast) t t0) t2) \to (eq 
T (THead (Flat Cast) t t0) t2))) (ex2 T (\lambda (t2: T).((eq T (THead (Flat 
Cast) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead 
(Flat Cast) t t0) t2))) (ex_intro2 T (\lambda (t2: T).((eq T (THead (Flat 
Cast) t t0) t2) \to (\forall (P: Prop).P))) (\lambda (t2: T).(pr0 (THead 
(Flat Cast) t t0) t2)) t0 (\lambda (H1: (eq T (THead (Flat Cast) t t0) 
t0)).(\lambda (P: Prop).(thead_x_y_y (Flat Cast) t t0 H1 P))) (pr0_tau t0 t0 
(pr0_refl t0) t))) f)) k)))))) t1).
(* COMMENTS
Initial nodes: 10459
END *)

