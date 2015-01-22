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

include "Basic-1/subst1/fwd.ma".

include "Basic-1/subst0/subst0.ma".

theorem subst1_subst1:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i 
u u1 u2) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: 
T).(subst1 (S (plus i j)) u t t2)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst1 j u2 t1 t2)).(subst1_ind j u2 t1 (\lambda (t: T).(\forall (u1: 
T).(\forall (u: T).(\forall (i: nat).((subst1 i u u1 u2) \to (ex2 T (\lambda 
(t0: T).(subst1 j u1 t1 t0)) (\lambda (t0: T).(subst1 (S (plus i j)) u t0 
t)))))))) (\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: 
(subst1 i u u1 u2)).(ex_intro2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda 
(t: T).(subst1 (S (plus i j)) u t t1)) t1 (subst1_refl j u1 t1) (subst1_refl 
(S (plus i j)) u t1)))))) (\lambda (t3: T).(\lambda (H0: (subst0 j u2 t1 
t3)).(\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (subst1 
i u u1 u2)).(insert_eq T u2 (\lambda (t: T).(subst1 i u u1 t)) (\lambda (_: 
T).(ex2 T (\lambda (t0: T).(subst1 j u1 t1 t0)) (\lambda (t0: T).(subst1 (S 
(plus i j)) u t0 t3)))) (\lambda (y: T).(\lambda (H2: (subst1 i u u1 
y)).(subst1_ind i u u1 (\lambda (t: T).((eq T t u2) \to (ex2 T (\lambda (t0: 
T).(subst1 j u1 t1 t0)) (\lambda (t0: T).(subst1 (S (plus i j)) u t0 t3))))) 
(\lambda (H3: (eq T u1 u2)).(eq_ind_r T u2 (\lambda (t: T).(ex2 T (\lambda 
(t0: T).(subst1 j t t1 t0)) (\lambda (t0: T).(subst1 (S (plus i j)) u t0 
t3)))) (ex_intro2 T (\lambda (t: T).(subst1 j u2 t1 t)) (\lambda (t: 
T).(subst1 (S (plus i j)) u t t3)) t3 (subst1_single j u2 t1 t3 H0) 
(subst1_refl (S (plus i j)) u t3)) u1 H3)) (\lambda (t0: T).(\lambda (H3: 
(subst0 i u u1 t0)).(\lambda (H4: (eq T t0 u2)).(let H5 \def (eq_ind T t0 
(\lambda (t: T).(subst0 i u u1 t)) H3 u2 H4) in (ex2_ind T (\lambda (t: 
T).(subst0 j u1 t1 t)) (\lambda (t: T).(subst0 (S (plus i j)) u t t3)) (ex2 T 
(\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: T).(subst1 (S (plus i j)) u 
t t3))) (\lambda (x: T).(\lambda (H6: (subst0 j u1 t1 x)).(\lambda (H7: 
(subst0 (S (plus i j)) u x t3)).(ex_intro2 T (\lambda (t: T).(subst1 j u1 t1 
t)) (\lambda (t: T).(subst1 (S (plus i j)) u t t3)) x (subst1_single j u1 t1 
x H6) (subst1_single (S (plus i j)) u x t3 H7))))) (subst0_subst0 t1 t3 u2 j 
H0 u1 u i H5)))))) y H2))) H1))))))) t2 H))))).
(* COMMENTS
Initial nodes: 649
END *)

theorem subst1_subst1_back:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst1 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst1 i 
u u2 u1) \to (ex2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda (t: 
T).(subst1 (S (plus i j)) u t2 t)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst1 j u2 t1 t2)).(subst1_ind j u2 t1 (\lambda (t: T).(\forall (u1: 
T).(\forall (u: T).(\forall (i: nat).((subst1 i u u2 u1) \to (ex2 T (\lambda 
(t0: T).(subst1 j u1 t1 t0)) (\lambda (t0: T).(subst1 (S (plus i j)) u t 
t0)))))))) (\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (_: 
(subst1 i u u2 u1)).(ex_intro2 T (\lambda (t: T).(subst1 j u1 t1 t)) (\lambda 
(t: T).(subst1 (S (plus i j)) u t1 t)) t1 (subst1_refl j u1 t1) (subst1_refl 
(S (plus i j)) u t1)))))) (\lambda (t3: T).(\lambda (H0: (subst0 j u2 t1 
t3)).(\lambda (u1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (subst1 
i u u2 u1)).(subst1_ind i u u2 (\lambda (t: T).(ex2 T (\lambda (t0: 
T).(subst1 j t t1 t0)) (\lambda (t0: T).(subst1 (S (plus i j)) u t3 t0)))) 
(ex_intro2 T (\lambda (t: T).(subst1 j u2 t1 t)) (\lambda (t: T).(subst1 (S 
(plus i j)) u t3 t)) t3 (subst1_single j u2 t1 t3 H0) (subst1_refl (S (plus i 
j)) u t3)) (\lambda (t0: T).(\lambda (H2: (subst0 i u u2 t0)).(ex2_ind T 
(\lambda (t: T).(subst0 j t0 t1 t)) (\lambda (t: T).(subst0 (S (plus i j)) u 
t3 t)) (ex2 T (\lambda (t: T).(subst1 j t0 t1 t)) (\lambda (t: T).(subst1 (S 
(plus i j)) u t3 t))) (\lambda (x: T).(\lambda (H3: (subst0 j t0 t1 
x)).(\lambda (H4: (subst0 (S (plus i j)) u t3 x)).(ex_intro2 T (\lambda (t: 
T).(subst1 j t0 t1 t)) (\lambda (t: T).(subst1 (S (plus i j)) u t3 t)) x 
(subst1_single j t0 t1 x H3) (subst1_single (S (plus i j)) u t3 x H4))))) 
(subst0_subst0_back t1 t3 u2 j H0 t0 u i H2)))) u1 H1))))))) t2 H))))).
(* COMMENTS
Initial nodes: 487
END *)

theorem subst1_trans:
 \forall (t2: T).(\forall (t1: T).(\forall (v: T).(\forall (i: nat).((subst1 
i v t1 t2) \to (\forall (t3: T).((subst1 i v t2 t3) \to (subst1 i v t1 
t3)))))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i v t1 t2)).(subst1_ind i v t1 (\lambda (t: T).(\forall (t3: 
T).((subst1 i v t t3) \to (subst1 i v t1 t3)))) (\lambda (t3: T).(\lambda 
(H0: (subst1 i v t1 t3)).H0)) (\lambda (t3: T).(\lambda (H0: (subst0 i v t1 
t3)).(\lambda (t4: T).(\lambda (H1: (subst1 i v t3 t4)).(subst1_ind i v t3 
(\lambda (t: T).(subst1 i v t1 t)) (subst1_single i v t1 t3 H0) (\lambda (t0: 
T).(\lambda (H2: (subst0 i v t3 t0)).(subst1_single i v t1 t0 (subst0_trans 
t3 t1 v i H0 t0 H2)))) t4 H1))))) t2 H))))).
(* COMMENTS
Initial nodes: 165
END *)

theorem subst1_confluence_neq:
 \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: 
nat).((subst1 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall 
(i2: nat).((subst1 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda 
(t: T).(subst1 i2 u2 t1 t)) (\lambda (t: T).(subst1 i1 u1 t2 t))))))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u1: T).(\lambda (i1: 
nat).(\lambda (H: (subst1 i1 u1 t0 t1)).(subst1_ind i1 u1 t0 (\lambda (t: 
T).(\forall (t2: T).(\forall (u2: T).(\forall (i2: nat).((subst1 i2 u2 t0 t2) 
\to ((not (eq nat i1 i2)) \to (ex2 T (\lambda (t3: T).(subst1 i2 u2 t t3)) 
(\lambda (t3: T).(subst1 i1 u1 t2 t3))))))))) (\lambda (t2: T).(\lambda (u2: 
T).(\lambda (i2: nat).(\lambda (H0: (subst1 i2 u2 t0 t2)).(\lambda (_: (not 
(eq nat i1 i2))).(ex_intro2 T (\lambda (t: T).(subst1 i2 u2 t0 t)) (\lambda 
(t: T).(subst1 i1 u1 t2 t)) t2 H0 (subst1_refl i1 u1 t2))))))) (\lambda (t2: 
T).(\lambda (H0: (subst0 i1 u1 t0 t2)).(\lambda (t3: T).(\lambda (u2: 
T).(\lambda (i2: nat).(\lambda (H1: (subst1 i2 u2 t0 t3)).(\lambda (H2: (not 
(eq nat i1 i2))).(subst1_ind i2 u2 t0 (\lambda (t: T).(ex2 T (\lambda (t4: 
T).(subst1 i2 u2 t2 t4)) (\lambda (t4: T).(subst1 i1 u1 t t4)))) (ex_intro2 T 
(\lambda (t: T).(subst1 i2 u2 t2 t)) (\lambda (t: T).(subst1 i1 u1 t0 t)) t2 
(subst1_refl i2 u2 t2) (subst1_single i1 u1 t0 t2 H0)) (\lambda (t4: 
T).(\lambda (H3: (subst0 i2 u2 t0 t4)).(ex2_ind T (\lambda (t: T).(subst0 i1 
u1 t4 t)) (\lambda (t: T).(subst0 i2 u2 t2 t)) (ex2 T (\lambda (t: T).(subst1 
i2 u2 t2 t)) (\lambda (t: T).(subst1 i1 u1 t4 t))) (\lambda (x: T).(\lambda 
(H4: (subst0 i1 u1 t4 x)).(\lambda (H5: (subst0 i2 u2 t2 x)).(ex_intro2 T 
(\lambda (t: T).(subst1 i2 u2 t2 t)) (\lambda (t: T).(subst1 i1 u1 t4 t)) x 
(subst1_single i2 u2 t2 x H5) (subst1_single i1 u1 t4 x H4))))) 
(subst0_confluence_neq t0 t4 u2 i2 H3 t2 u1 i1 H0 (sym_not_eq nat i1 i2 
H2))))) t3 H1)))))))) t1 H))))).
(* COMMENTS
Initial nodes: 455
END *)

theorem subst1_confluence_eq:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t0 t1) \to (\forall (t2: T).((subst1 i u t0 t2) \to (ex2 T (\lambda (t: 
T).(subst1 i u t1 t)) (\lambda (t: T).(subst1 i u t2 t)))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t0 t1)).(subst1_ind i u t0 (\lambda (t: T).(\forall (t2: 
T).((subst1 i u t0 t2) \to (ex2 T (\lambda (t3: T).(subst1 i u t t3)) 
(\lambda (t3: T).(subst1 i u t2 t3)))))) (\lambda (t2: T).(\lambda (H0: 
(subst1 i u t0 t2)).(ex_intro2 T (\lambda (t: T).(subst1 i u t0 t)) (\lambda 
(t: T).(subst1 i u t2 t)) t2 H0 (subst1_refl i u t2)))) (\lambda (t2: 
T).(\lambda (H0: (subst0 i u t0 t2)).(\lambda (t3: T).(\lambda (H1: (subst1 i 
u t0 t3)).(subst1_ind i u t0 (\lambda (t: T).(ex2 T (\lambda (t4: T).(subst1 
i u t2 t4)) (\lambda (t4: T).(subst1 i u t t4)))) (ex_intro2 T (\lambda (t: 
T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 i u t0 t)) t2 (subst1_refl i u 
t2) (subst1_single i u t0 t2 H0)) (\lambda (t4: T).(\lambda (H2: (subst0 i u 
t0 t4)).(or4_ind (eq T t4 t2) (ex2 T (\lambda (t: T).(subst0 i u t4 t)) 
(\lambda (t: T).(subst0 i u t2 t))) (subst0 i u t4 t2) (subst0 i u t2 t4) 
(ex2 T (\lambda (t: T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 i u t4 t))) 
(\lambda (H3: (eq T t4 t2)).(eq_ind_r T t2 (\lambda (t: T).(ex2 T (\lambda 
(t5: T).(subst1 i u t2 t5)) (\lambda (t5: T).(subst1 i u t t5)))) (ex_intro2 
T (\lambda (t: T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 i u t2 t)) t2 
(subst1_refl i u t2) (subst1_refl i u t2)) t4 H3)) (\lambda (H3: (ex2 T 
(\lambda (t: T).(subst0 i u t4 t)) (\lambda (t: T).(subst0 i u t2 
t)))).(ex2_ind T (\lambda (t: T).(subst0 i u t4 t)) (\lambda (t: T).(subst0 i 
u t2 t)) (ex2 T (\lambda (t: T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 i 
u t4 t))) (\lambda (x: T).(\lambda (H4: (subst0 i u t4 x)).(\lambda (H5: 
(subst0 i u t2 x)).(ex_intro2 T (\lambda (t: T).(subst1 i u t2 t)) (\lambda 
(t: T).(subst1 i u t4 t)) x (subst1_single i u t2 x H5) (subst1_single i u t4 
x H4))))) H3)) (\lambda (H3: (subst0 i u t4 t2)).(ex_intro2 T (\lambda (t: 
T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 i u t4 t)) t2 (subst1_refl i u 
t2) (subst1_single i u t4 t2 H3))) (\lambda (H3: (subst0 i u t2 
t4)).(ex_intro2 T (\lambda (t: T).(subst1 i u t2 t)) (\lambda (t: T).(subst1 
i u t4 t)) t4 (subst1_single i u t2 t4 H3) (subst1_refl i u t4))) 
(subst0_confluence_eq t0 t4 u i H2 t2 H0)))) t3 H1))))) t1 H))))).
(* COMMENTS
Initial nodes: 729
END *)

theorem subst1_confluence_lift:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t0 (lift (S O) i t1)) \to (\forall (t2: T).((subst1 i u t0 (lift (S O) i 
t2)) \to (eq T t1 t2)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t0 (lift (S O) i t1))).(insert_eq T (lift (S O) i t1) 
(\lambda (t: T).(subst1 i u t0 t)) (\lambda (_: T).(\forall (t2: T).((subst1 
i u t0 (lift (S O) i t2)) \to (eq T t1 t2)))) (\lambda (y: T).(\lambda (H0: 
(subst1 i u t0 y)).(subst1_ind i u t0 (\lambda (t: T).((eq T t (lift (S O) i 
t1)) \to (\forall (t2: T).((subst1 i u t0 (lift (S O) i t2)) \to (eq T t1 
t2))))) (\lambda (H1: (eq T t0 (lift (S O) i t1))).(\lambda (t2: T).(\lambda 
(H2: (subst1 i u t0 (lift (S O) i t2))).(let H3 \def (eq_ind T t0 (\lambda 
(t: T).(subst1 i u t (lift (S O) i t2))) H2 (lift (S O) i t1) H1) in (let H4 
\def (sym_eq T (lift (S O) i t2) (lift (S O) i t1) (subst1_gen_lift_eq t1 u 
(lift (S O) i t2) (S O) i i (le_n i) (eq_ind_r nat (plus (S O) i) (\lambda 
(n: nat).(lt i n)) (le_n (plus (S O) i)) (plus i (S O)) (plus_sym i (S O))) 
H3)) in (lift_inj t1 t2 (S O) i H4)))))) (\lambda (t2: T).(\lambda (H1: 
(subst0 i u t0 t2)).(\lambda (H2: (eq T t2 (lift (S O) i t1))).(\lambda (t3: 
T).(\lambda (H3: (subst1 i u t0 (lift (S O) i t3))).(let H4 \def (eq_ind T t2 
(\lambda (t: T).(subst0 i u t0 t)) H1 (lift (S O) i t1) H2) in (insert_eq T 
(lift (S O) i t3) (\lambda (t: T).(subst1 i u t0 t)) (\lambda (_: T).(eq T t1 
t3)) (\lambda (y0: T).(\lambda (H5: (subst1 i u t0 y0)).(subst1_ind i u t0 
(\lambda (t: T).((eq T t (lift (S O) i t3)) \to (eq T t1 t3))) (\lambda (H6: 
(eq T t0 (lift (S O) i t3))).(let H7 \def (eq_ind T t0 (\lambda (t: 
T).(subst0 i u t (lift (S O) i t1))) H4 (lift (S O) i t3) H6) in 
(subst0_gen_lift_false t3 u (lift (S O) i t1) (S O) i i (le_n i) (eq_ind_r 
nat (plus (S O) i) (\lambda (n: nat).(lt i n)) (le_n (plus (S O) i)) (plus i 
(S O)) (plus_sym i (S O))) H7 (eq T t1 t3)))) (\lambda (t4: T).(\lambda (H6: 
(subst0 i u t0 t4)).(\lambda (H7: (eq T t4 (lift (S O) i t3))).(let H8 \def 
(eq_ind T t4 (\lambda (t: T).(subst0 i u t0 t)) H6 (lift (S O) i t3) H7) in 
(sym_eq T t3 t1 (subst0_confluence_lift t0 t3 u i H8 t1 H4)))))) y0 H5))) 
H3))))))) y H0))) H))))).
(* COMMENTS
Initial nodes: 735
END *)

