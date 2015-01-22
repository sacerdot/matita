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

include "Basic-1/subst0/props.ma".

theorem subst0_subst0:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst0 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst0 i 
u u1 u2) \to (ex2 T (\lambda (t: T).(subst0 j u1 t1 t)) (\lambda (t: 
T).(subst0 (S (plus i j)) u t t2)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst0 j u2 t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (u1: T).(\forall (u: 
T).(\forall (i: nat).((subst0 i u u1 t) \to (ex2 T (\lambda (t4: T).(subst0 n 
u1 t0 t4)) (\lambda (t4: T).(subst0 (S (plus i n)) u t4 t3))))))))))) 
(\lambda (v: T).(\lambda (i: nat).(\lambda (u1: T).(\lambda (u: T).(\lambda 
(i0: nat).(\lambda (H0: (subst0 i0 u u1 v)).(eq_ind nat (plus i0 (S i)) 
(\lambda (n: nat).(ex2 T (\lambda (t: T).(subst0 i u1 (TLRef i) t)) (\lambda 
(t: T).(subst0 n u t (lift (S i) O v))))) (ex_intro2 T (\lambda (t: 
T).(subst0 i u1 (TLRef i) t)) (\lambda (t: T).(subst0 (plus i0 (S i)) u t 
(lift (S i) O v))) (lift (S i) O u1) (subst0_lref u1 i) (subst0_lift_ge u1 v 
u i0 (S i) H0 O (le_O_n i0))) (S (plus i0 i)) (sym_eq nat (S (plus i0 i)) 
(plus i0 (S i)) (plus_n_Sm i0 i))))))))) (\lambda (v: T).(\lambda (u0: 
T).(\lambda (u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 
u0)).(\lambda (H1: ((\forall (u3: T).(\forall (u: T).(\forall (i0: 
nat).((subst0 i0 u u3 v) \to (ex2 T (\lambda (t: T).(subst0 i u3 u1 t)) 
(\lambda (t: T).(subst0 (S (plus i0 i)) u t u0))))))))).(\lambda (t: 
T).(\lambda (k: K).(\lambda (u3: T).(\lambda (u: T).(\lambda (i0: 
nat).(\lambda (H2: (subst0 i0 u u3 v)).(ex2_ind T (\lambda (t0: T).(subst0 i 
u3 u1 t0)) (\lambda (t0: T).(subst0 (S (plus i0 i)) u t0 u0)) (ex2 T (\lambda 
(t0: T).(subst0 i u3 (THead k u1 t) t0)) (\lambda (t0: T).(subst0 (S (plus i0 
i)) u t0 (THead k u0 t)))) (\lambda (x: T).(\lambda (H3: (subst0 i u3 u1 
x)).(\lambda (H4: (subst0 (S (plus i0 i)) u x u0)).(ex_intro2 T (\lambda (t0: 
T).(subst0 i u3 (THead k u1 t) t0)) (\lambda (t0: T).(subst0 (S (plus i0 i)) 
u t0 (THead k u0 t))) (THead k x t) (subst0_fst u3 x u1 i H3 t k) (subst0_fst 
u u0 x (S (plus i0 i)) H4 t k))))) (H1 u3 u i0 H2)))))))))))))) (\lambda (k: 
K).(\lambda (v: T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i: 
nat).(\lambda (_: (subst0 (s k i) v t3 t0)).(\lambda (H1: ((\forall (u1: 
T).(\forall (u: T).(\forall (i0: nat).((subst0 i0 u u1 v) \to (ex2 T (\lambda 
(t: T).(subst0 (s k i) u1 t3 t)) (\lambda (t: T).(subst0 (S (plus i0 (s k 
i))) u t t0))))))))).(\lambda (u: T).(\lambda (u1: T).(\lambda (u0: 
T).(\lambda (i0: nat).(\lambda (H2: (subst0 i0 u0 u1 v)).(ex2_ind T (\lambda 
(t: T).(subst0 (s k i) u1 t3 t)) (\lambda (t: T).(subst0 (S (plus i0 (s k 
i))) u0 t t0)) (ex2 T (\lambda (t: T).(subst0 i u1 (THead k u t3) t)) 
(\lambda (t: T).(subst0 (S (plus i0 i)) u0 t (THead k u t0)))) (\lambda (x: 
T).(\lambda (H3: (subst0 (s k i) u1 t3 x)).(\lambda (H4: (subst0 (S (plus i0 
(s k i))) u0 x t0)).(let H5 \def (eq_ind_r nat (plus i0 (s k i)) (\lambda (n: 
nat).(subst0 (S n) u0 x t0)) H4 (s k (plus i0 i)) (s_plus_sym k i0 i)) in 
(let H6 \def (eq_ind_r nat (S (s k (plus i0 i))) (\lambda (n: nat).(subst0 n 
u0 x t0)) H5 (s k (S (plus i0 i))) (s_S k (plus i0 i))) in (ex_intro2 T 
(\lambda (t: T).(subst0 i u1 (THead k u t3) t)) (\lambda (t: T).(subst0 (S 
(plus i0 i)) u0 t (THead k u t0))) (THead k u x) (subst0_snd k u1 x t3 i H3 
u) (subst0_snd k u0 t0 x (S (plus i0 i)) H6 u))))))) (H1 u1 u0 i0 
H2)))))))))))))) (\lambda (v: T).(\lambda (u1: T).(\lambda (u0: T).(\lambda 
(i: nat).(\lambda (_: (subst0 i v u1 u0)).(\lambda (H1: ((\forall (u3: 
T).(\forall (u: T).(\forall (i0: nat).((subst0 i0 u u3 v) \to (ex2 T (\lambda 
(t: T).(subst0 i u3 u1 t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u t 
u0))))))))).(\lambda (k: K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: 
(subst0 (s k i) v t0 t3)).(\lambda (H3: ((\forall (u3: T).(\forall (u: 
T).(\forall (i0: nat).((subst0 i0 u u3 v) \to (ex2 T (\lambda (t: T).(subst0 
(s k i) u3 t0 t)) (\lambda (t: T).(subst0 (S (plus i0 (s k i))) u t 
t3))))))))).(\lambda (u3: T).(\lambda (u: T).(\lambda (i0: nat).(\lambda (H4: 
(subst0 i0 u u3 v)).(ex2_ind T (\lambda (t: T).(subst0 (s k i) u3 t0 t)) 
(\lambda (t: T).(subst0 (S (plus i0 (s k i))) u t t3)) (ex2 T (\lambda (t: 
T).(subst0 i u3 (THead k u1 t0) t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u 
t (THead k u0 t3)))) (\lambda (x: T).(\lambda (H5: (subst0 (s k i) u3 t0 
x)).(\lambda (H6: (subst0 (S (plus i0 (s k i))) u x t3)).(ex2_ind T (\lambda 
(t: T).(subst0 i u3 u1 t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u t u0)) 
(ex2 T (\lambda (t: T).(subst0 i u3 (THead k u1 t0) t)) (\lambda (t: 
T).(subst0 (S (plus i0 i)) u t (THead k u0 t3)))) (\lambda (x0: T).(\lambda 
(H7: (subst0 i u3 u1 x0)).(\lambda (H8: (subst0 (S (plus i0 i)) u x0 
u0)).(let H9 \def (eq_ind_r nat (plus i0 (s k i)) (\lambda (n: nat).(subst0 
(S n) u x t3)) H6 (s k (plus i0 i)) (s_plus_sym k i0 i)) in (let H10 \def 
(eq_ind_r nat (S (s k (plus i0 i))) (\lambda (n: nat).(subst0 n u x t3)) H9 
(s k (S (plus i0 i))) (s_S k (plus i0 i))) in (ex_intro2 T (\lambda (t: 
T).(subst0 i u3 (THead k u1 t0) t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u 
t (THead k u0 t3))) (THead k x0 x) (subst0_both u3 u1 x0 i H7 k t0 x H5) 
(subst0_both u x0 u0 (S (plus i0 i)) H8 k x t3 H10))))))) (H1 u3 u i0 H4))))) 
(H3 u3 u i0 H4))))))))))))))))) j u2 t1 t2 H))))).
(* COMMENTS
Initial nodes: 1613
END *)

theorem subst0_subst0_back:
 \forall (t1: T).(\forall (t2: T).(\forall (u2: T).(\forall (j: nat).((subst0 
j u2 t1 t2) \to (\forall (u1: T).(\forall (u: T).(\forall (i: nat).((subst0 i 
u u2 u1) \to (ex2 T (\lambda (t: T).(subst0 j u1 t1 t)) (\lambda (t: 
T).(subst0 (S (plus i j)) u t2 t)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda (j: nat).(\lambda 
(H: (subst0 j u2 t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (u1: T).(\forall (u: 
T).(\forall (i: nat).((subst0 i u t u1) \to (ex2 T (\lambda (t4: T).(subst0 n 
u1 t0 t4)) (\lambda (t4: T).(subst0 (S (plus i n)) u t3 t4))))))))))) 
(\lambda (v: T).(\lambda (i: nat).(\lambda (u1: T).(\lambda (u: T).(\lambda 
(i0: nat).(\lambda (H0: (subst0 i0 u v u1)).(eq_ind nat (plus i0 (S i)) 
(\lambda (n: nat).(ex2 T (\lambda (t: T).(subst0 i u1 (TLRef i) t)) (\lambda 
(t: T).(subst0 n u (lift (S i) O v) t)))) (ex_intro2 T (\lambda (t: 
T).(subst0 i u1 (TLRef i) t)) (\lambda (t: T).(subst0 (plus i0 (S i)) u (lift 
(S i) O v) t)) (lift (S i) O u1) (subst0_lref u1 i) (subst0_lift_ge v u1 u i0 
(S i) H0 O (le_O_n i0))) (S (plus i0 i)) (sym_eq nat (S (plus i0 i)) (plus i0 
(S i)) (plus_n_Sm i0 i))))))))) (\lambda (v: T).(\lambda (u0: T).(\lambda 
(u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 u0)).(\lambda (H1: 
((\forall (u3: T).(\forall (u: T).(\forall (i0: nat).((subst0 i0 u v u3) \to 
(ex2 T (\lambda (t: T).(subst0 i u3 u1 t)) (\lambda (t: T).(subst0 (S (plus 
i0 i)) u u0 t))))))))).(\lambda (t: T).(\lambda (k: K).(\lambda (u3: 
T).(\lambda (u: T).(\lambda (i0: nat).(\lambda (H2: (subst0 i0 u v 
u3)).(ex2_ind T (\lambda (t0: T).(subst0 i u3 u1 t0)) (\lambda (t0: 
T).(subst0 (S (plus i0 i)) u u0 t0)) (ex2 T (\lambda (t0: T).(subst0 i u3 
(THead k u1 t) t0)) (\lambda (t0: T).(subst0 (S (plus i0 i)) u (THead k u0 t) 
t0))) (\lambda (x: T).(\lambda (H3: (subst0 i u3 u1 x)).(\lambda (H4: (subst0 
(S (plus i0 i)) u u0 x)).(ex_intro2 T (\lambda (t0: T).(subst0 i u3 (THead k 
u1 t) t0)) (\lambda (t0: T).(subst0 (S (plus i0 i)) u (THead k u0 t) t0)) 
(THead k x t) (subst0_fst u3 x u1 i H3 t k) (subst0_fst u x u0 (S (plus i0 
i)) H4 t k))))) (H1 u3 u i0 H2)))))))))))))) (\lambda (k: K).(\lambda (v: 
T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i: nat).(\lambda (_: (subst0 
(s k i) v t3 t0)).(\lambda (H1: ((\forall (u1: T).(\forall (u: T).(\forall 
(i0: nat).((subst0 i0 u v u1) \to (ex2 T (\lambda (t: T).(subst0 (s k i) u1 
t3 t)) (\lambda (t: T).(subst0 (S (plus i0 (s k i))) u t0 t))))))))).(\lambda 
(u: T).(\lambda (u1: T).(\lambda (u0: T).(\lambda (i0: nat).(\lambda (H2: 
(subst0 i0 u0 v u1)).(ex2_ind T (\lambda (t: T).(subst0 (s k i) u1 t3 t)) 
(\lambda (t: T).(subst0 (S (plus i0 (s k i))) u0 t0 t)) (ex2 T (\lambda (t: 
T).(subst0 i u1 (THead k u t3) t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u0 
(THead k u t0) t))) (\lambda (x: T).(\lambda (H3: (subst0 (s k i) u1 t3 
x)).(\lambda (H4: (subst0 (S (plus i0 (s k i))) u0 t0 x)).(let H5 \def 
(eq_ind_r nat (plus i0 (s k i)) (\lambda (n: nat).(subst0 (S n) u0 t0 x)) H4 
(s k (plus i0 i)) (s_plus_sym k i0 i)) in (let H6 \def (eq_ind_r nat (S (s k 
(plus i0 i))) (\lambda (n: nat).(subst0 n u0 t0 x)) H5 (s k (S (plus i0 i))) 
(s_S k (plus i0 i))) in (ex_intro2 T (\lambda (t: T).(subst0 i u1 (THead k u 
t3) t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u0 (THead k u t0) t)) (THead 
k u x) (subst0_snd k u1 x t3 i H3 u) (subst0_snd k u0 x t0 (S (plus i0 i)) H6 
u))))))) (H1 u1 u0 i0 H2)))))))))))))) (\lambda (v: T).(\lambda (u1: 
T).(\lambda (u0: T).(\lambda (i: nat).(\lambda (_: (subst0 i v u1 
u0)).(\lambda (H1: ((\forall (u3: T).(\forall (u: T).(\forall (i0: 
nat).((subst0 i0 u v u3) \to (ex2 T (\lambda (t: T).(subst0 i u3 u1 t)) 
(\lambda (t: T).(subst0 (S (plus i0 i)) u u0 t))))))))).(\lambda (k: 
K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (subst0 (s k i) v t0 
t3)).(\lambda (H3: ((\forall (u3: T).(\forall (u: T).(\forall (i0: 
nat).((subst0 i0 u v u3) \to (ex2 T (\lambda (t: T).(subst0 (s k i) u3 t0 t)) 
(\lambda (t: T).(subst0 (S (plus i0 (s k i))) u t3 t))))))))).(\lambda (u3: 
T).(\lambda (u: T).(\lambda (i0: nat).(\lambda (H4: (subst0 i0 u v 
u3)).(ex2_ind T (\lambda (t: T).(subst0 (s k i) u3 t0 t)) (\lambda (t: 
T).(subst0 (S (plus i0 (s k i))) u t3 t)) (ex2 T (\lambda (t: T).(subst0 i u3 
(THead k u1 t0) t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u (THead k u0 t3) 
t))) (\lambda (x: T).(\lambda (H5: (subst0 (s k i) u3 t0 x)).(\lambda (H6: 
(subst0 (S (plus i0 (s k i))) u t3 x)).(ex2_ind T (\lambda (t: T).(subst0 i 
u3 u1 t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u u0 t)) (ex2 T (\lambda 
(t: T).(subst0 i u3 (THead k u1 t0) t)) (\lambda (t: T).(subst0 (S (plus i0 
i)) u (THead k u0 t3) t))) (\lambda (x0: T).(\lambda (H7: (subst0 i u3 u1 
x0)).(\lambda (H8: (subst0 (S (plus i0 i)) u u0 x0)).(let H9 \def (eq_ind_r 
nat (plus i0 (s k i)) (\lambda (n: nat).(subst0 (S n) u t3 x)) H6 (s k (plus 
i0 i)) (s_plus_sym k i0 i)) in (let H10 \def (eq_ind_r nat (S (s k (plus i0 
i))) (\lambda (n: nat).(subst0 n u t3 x)) H9 (s k (S (plus i0 i))) (s_S k 
(plus i0 i))) in (ex_intro2 T (\lambda (t: T).(subst0 i u3 (THead k u1 t0) 
t)) (\lambda (t: T).(subst0 (S (plus i0 i)) u (THead k u0 t3) t)) (THead k x0 
x) (subst0_both u3 u1 x0 i H7 k t0 x H5) (subst0_both u u0 x0 (S (plus i0 i)) 
H8 k t3 x H10))))))) (H1 u3 u i0 H4))))) (H3 u3 u i0 H4))))))))))))))))) j u2 
t1 t2 H))))).
(* COMMENTS
Initial nodes: 1613
END *)

theorem subst0_trans:
 \forall (t2: T).(\forall (t1: T).(\forall (v: T).(\forall (i: nat).((subst0 
i v t1 t2) \to (\forall (t3: T).((subst0 i v t2 t3) \to (subst0 i v t1 
t3)))))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i v t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (t4: T).((subst0 n t t3 t4) \to 
(subst0 n t t0 t4))))))) (\lambda (v0: T).(\lambda (i0: nat).(\lambda (t3: 
T).(\lambda (H0: (subst0 i0 v0 (lift (S i0) O v0) t3)).(subst0_gen_lift_false 
v0 v0 t3 (S i0) O i0 (le_O_n i0) (le_n (plus O (S i0))) H0 (subst0 i0 v0 
(TLRef i0) t3)))))) (\lambda (v0: T).(\lambda (u2: T).(\lambda (u1: 
T).(\lambda (i0: nat).(\lambda (H0: (subst0 i0 v0 u1 u2)).(\lambda (H1: 
((\forall (t3: T).((subst0 i0 v0 u2 t3) \to (subst0 i0 v0 u1 t3))))).(\lambda 
(t: T).(\lambda (k: K).(\lambda (t3: T).(\lambda (H2: (subst0 i0 v0 (THead k 
u2 t) t3)).(or3_ind (ex2 T (\lambda (u3: T).(eq T t3 (THead k u3 t))) 
(\lambda (u3: T).(subst0 i0 v0 u2 u3))) (ex2 T (\lambda (t4: T).(eq T t3 
(THead k u2 t4))) (\lambda (t4: T).(subst0 (s k i0) v0 t t4))) (ex3_2 T T 
(\lambda (u3: T).(\lambda (t4: T).(eq T t3 (THead k u3 t4)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i0 v0 u2 u3))) (\lambda (_: T).(\lambda (t4: 
T).(subst0 (s k i0) v0 t t4)))) (subst0 i0 v0 (THead k u1 t) t3) (\lambda 
(H3: (ex2 T (\lambda (u3: T).(eq T t3 (THead k u3 t))) (\lambda (u3: 
T).(subst0 i0 v0 u2 u3)))).(ex2_ind T (\lambda (u3: T).(eq T t3 (THead k u3 
t))) (\lambda (u3: T).(subst0 i0 v0 u2 u3)) (subst0 i0 v0 (THead k u1 t) t3) 
(\lambda (x: T).(\lambda (H4: (eq T t3 (THead k x t))).(\lambda (H5: (subst0 
i0 v0 u2 x)).(eq_ind_r T (THead k x t) (\lambda (t0: T).(subst0 i0 v0 (THead 
k u1 t) t0)) (subst0_fst v0 x u1 i0 (H1 x H5) t k) t3 H4)))) H3)) (\lambda 
(H3: (ex2 T (\lambda (t4: T).(eq T t3 (THead k u2 t4))) (\lambda (t4: 
T).(subst0 (s k i0) v0 t t4)))).(ex2_ind T (\lambda (t4: T).(eq T t3 (THead k 
u2 t4))) (\lambda (t4: T).(subst0 (s k i0) v0 t t4)) (subst0 i0 v0 (THead k 
u1 t) t3) (\lambda (x: T).(\lambda (H4: (eq T t3 (THead k u2 x))).(\lambda 
(H5: (subst0 (s k i0) v0 t x)).(eq_ind_r T (THead k u2 x) (\lambda (t0: 
T).(subst0 i0 v0 (THead k u1 t) t0)) (subst0_both v0 u1 u2 i0 H0 k t x H5) t3 
H4)))) H3)) (\lambda (H3: (ex3_2 T T (\lambda (u3: T).(\lambda (t4: T).(eq T 
t3 (THead k u3 t4)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v0 u2 u3))) 
(\lambda (_: T).(\lambda (t4: T).(subst0 (s k i0) v0 t t4))))).(ex3_2_ind T T 
(\lambda (u3: T).(\lambda (t4: T).(eq T t3 (THead k u3 t4)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i0 v0 u2 u3))) (\lambda (_: T).(\lambda (t4: 
T).(subst0 (s k i0) v0 t t4))) (subst0 i0 v0 (THead k u1 t) t3) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H4: (eq T t3 (THead k x0 x1))).(\lambda (H5: 
(subst0 i0 v0 u2 x0)).(\lambda (H6: (subst0 (s k i0) v0 t x1)).(eq_ind_r T 
(THead k x0 x1) (\lambda (t0: T).(subst0 i0 v0 (THead k u1 t) t0)) 
(subst0_both v0 u1 x0 i0 (H1 x0 H5) k t x1 H6) t3 H4)))))) H3)) 
(subst0_gen_head k v0 u2 t t3 i0 H2)))))))))))) (\lambda (k: K).(\lambda (v0: 
T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i0: nat).(\lambda (H0: (subst0 
(s k i0) v0 t3 t0)).(\lambda (H1: ((\forall (t4: T).((subst0 (s k i0) v0 t0 
t4) \to (subst0 (s k i0) v0 t3 t4))))).(\lambda (u: T).(\lambda (t4: 
T).(\lambda (H2: (subst0 i0 v0 (THead k u t0) t4)).(or3_ind (ex2 T (\lambda 
(u2: T).(eq T t4 (THead k u2 t0))) (\lambda (u2: T).(subst0 i0 v0 u u2))) 
(ex2 T (\lambda (t5: T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s 
k i0) v0 t0 t5))) (ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 
(THead k u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i0 v0 u u2))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s k i0) v0 t0 t5)))) (subst0 i0 v0 
(THead k u t3) t4) (\lambda (H3: (ex2 T (\lambda (u2: T).(eq T t4 (THead k u2 
t0))) (\lambda (u2: T).(subst0 i0 v0 u u2)))).(ex2_ind T (\lambda (u2: T).(eq 
T t4 (THead k u2 t0))) (\lambda (u2: T).(subst0 i0 v0 u u2)) (subst0 i0 v0 
(THead k u t3) t4) (\lambda (x: T).(\lambda (H4: (eq T t4 (THead k x 
t0))).(\lambda (H5: (subst0 i0 v0 u x)).(eq_ind_r T (THead k x t0) (\lambda 
(t: T).(subst0 i0 v0 (THead k u t3) t)) (subst0_both v0 u x i0 H5 k t3 t0 H0) 
t4 H4)))) H3)) (\lambda (H3: (ex2 T (\lambda (t5: T).(eq T t4 (THead k u 
t5))) (\lambda (t5: T).(subst0 (s k i0) v0 t0 t5)))).(ex2_ind T (\lambda (t5: 
T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s k i0) v0 t0 t5)) 
(subst0 i0 v0 (THead k u t3) t4) (\lambda (x: T).(\lambda (H4: (eq T t4 
(THead k u x))).(\lambda (H5: (subst0 (s k i0) v0 t0 x)).(eq_ind_r T (THead k 
u x) (\lambda (t: T).(subst0 i0 v0 (THead k u t3) t)) (subst0_snd k v0 x t3 
i0 (H1 x H5) u) t4 H4)))) H3)) (\lambda (H3: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t5: T).(eq T t4 (THead k u2 t5)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i0 v0 u u2))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i0) v0 
t0 t5))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead k 
u2 t5)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i0 v0 u u2))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i0) v0 t0 t5))) (subst0 i0 v0 (THead k u t3) 
t4) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t4 (THead k x0 
x1))).(\lambda (H5: (subst0 i0 v0 u x0)).(\lambda (H6: (subst0 (s k i0) v0 t0 
x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(subst0 i0 v0 (THead k u t3) 
t)) (subst0_both v0 u x0 i0 H5 k t3 x1 (H1 x1 H6)) t4 H4)))))) H3)) 
(subst0_gen_head k v0 u t0 t4 i0 H2)))))))))))) (\lambda (v0: T).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (i0: nat).(\lambda (H0: (subst0 i0 v0 u1 
u2)).(\lambda (H1: ((\forall (t3: T).((subst0 i0 v0 u2 t3) \to (subst0 i0 v0 
u1 t3))))).(\lambda (k: K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (H2: 
(subst0 (s k i0) v0 t0 t3)).(\lambda (H3: ((\forall (t4: T).((subst0 (s k i0) 
v0 t3 t4) \to (subst0 (s k i0) v0 t0 t4))))).(\lambda (t4: T).(\lambda (H4: 
(subst0 i0 v0 (THead k u2 t3) t4)).(or3_ind (ex2 T (\lambda (u3: T).(eq T t4 
(THead k u3 t3))) (\lambda (u3: T).(subst0 i0 v0 u2 u3))) (ex2 T (\lambda 
(t5: T).(eq T t4 (THead k u2 t5))) (\lambda (t5: T).(subst0 (s k i0) v0 t3 
t5))) (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 
t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v0 u2 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i0) v0 t3 t5)))) (subst0 i0 v0 (THead k u1 
t0) t4) (\lambda (H5: (ex2 T (\lambda (u3: T).(eq T t4 (THead k u3 t3))) 
(\lambda (u3: T).(subst0 i0 v0 u2 u3)))).(ex2_ind T (\lambda (u3: T).(eq T t4 
(THead k u3 t3))) (\lambda (u3: T).(subst0 i0 v0 u2 u3)) (subst0 i0 v0 (THead 
k u1 t0) t4) (\lambda (x: T).(\lambda (H6: (eq T t4 (THead k x t3))).(\lambda 
(H7: (subst0 i0 v0 u2 x)).(eq_ind_r T (THead k x t3) (\lambda (t: T).(subst0 
i0 v0 (THead k u1 t0) t)) (subst0_both v0 u1 x i0 (H1 x H7) k t0 t3 H2) t4 
H6)))) H5)) (\lambda (H5: (ex2 T (\lambda (t5: T).(eq T t4 (THead k u2 t5))) 
(\lambda (t5: T).(subst0 (s k i0) v0 t3 t5)))).(ex2_ind T (\lambda (t5: 
T).(eq T t4 (THead k u2 t5))) (\lambda (t5: T).(subst0 (s k i0) v0 t3 t5)) 
(subst0 i0 v0 (THead k u1 t0) t4) (\lambda (x: T).(\lambda (H6: (eq T t4 
(THead k u2 x))).(\lambda (H7: (subst0 (s k i0) v0 t3 x)).(eq_ind_r T (THead 
k u2 x) (\lambda (t: T).(subst0 i0 v0 (THead k u1 t0) t)) (subst0_both v0 u1 
u2 i0 H0 k t0 x (H3 x H7)) t4 H6)))) H5)) (\lambda (H5: (ex3_2 T T (\lambda 
(u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i0 v0 u2 u3))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s k i0) v0 t3 t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda 
(t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 
i0 v0 u2 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i0) v0 t3 t5))) 
(subst0 i0 v0 (THead k u1 t0) t4) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H6: (eq T t4 (THead k x0 x1))).(\lambda (H7: (subst0 i0 v0 u2 x0)).(\lambda 
(H8: (subst0 (s k i0) v0 t3 x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: 
T).(subst0 i0 v0 (THead k u1 t0) t)) (subst0_both v0 u1 x0 i0 (H1 x0 H7) k t0 
x1 (H3 x1 H8)) t4 H6)))))) H5)) (subst0_gen_head k v0 u2 t3 t4 i0 
H4))))))))))))))) i v t1 t2 H))))).
(* COMMENTS
Initial nodes: 2555
END *)

theorem subst0_confluence_neq:
 \forall (t0: T).(\forall (t1: T).(\forall (u1: T).(\forall (i1: 
nat).((subst0 i1 u1 t0 t1) \to (\forall (t2: T).(\forall (u2: T).(\forall 
(i2: nat).((subst0 i2 u2 t0 t2) \to ((not (eq nat i1 i2)) \to (ex2 T (\lambda 
(t: T).(subst0 i2 u2 t1 t)) (\lambda (t: T).(subst0 i1 u1 t2 t))))))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u1: T).(\lambda (i1: 
nat).(\lambda (H: (subst0 i1 u1 t0 t1)).(subst0_ind (\lambda (n: 
nat).(\lambda (t: T).(\lambda (t2: T).(\lambda (t3: T).(\forall (t4: 
T).(\forall (u2: T).(\forall (i2: nat).((subst0 i2 u2 t2 t4) \to ((not (eq 
nat n i2)) \to (ex2 T (\lambda (t5: T).(subst0 i2 u2 t3 t5)) (\lambda (t5: 
T).(subst0 n t t4 t5)))))))))))) (\lambda (v: T).(\lambda (i: nat).(\lambda 
(t2: T).(\lambda (u2: T).(\lambda (i2: nat).(\lambda (H0: (subst0 i2 u2 
(TLRef i) t2)).(\lambda (H1: (not (eq nat i i2))).(land_ind (eq nat i i2) (eq 
T t2 (lift (S i) O u2)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (lift (S i) O v) 
t)) (\lambda (t: T).(subst0 i v t2 t))) (\lambda (H2: (eq nat i i2)).(\lambda 
(H3: (eq T t2 (lift (S i) O u2))).(let H4 \def (eq_ind nat i (\lambda (n: 
nat).(not (eq nat n i2))) H1 i2 H2) in (eq_ind_r T (lift (S i) O u2) (\lambda 
(t: T).(ex2 T (\lambda (t3: T).(subst0 i2 u2 (lift (S i) O v) t3)) (\lambda 
(t3: T).(subst0 i v t t3)))) (let H5 \def (match (H4 (refl_equal nat i2)) in 
False return (\lambda (_: False).(ex2 T (\lambda (t: T).(subst0 i2 u2 (lift 
(S i) O v) t)) (\lambda (t: T).(subst0 i v (lift (S i) O u2) t)))) with []) 
in H5) t2 H3)))) (subst0_gen_lref u2 t2 i2 i H0))))))))) (\lambda (v: 
T).(\lambda (u2: T).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H0: (subst0 
i v u0 u2)).(\lambda (H1: ((\forall (t2: T).(\forall (u3: T).(\forall (i2: 
nat).((subst0 i2 u3 u0 t2) \to ((not (eq nat i i2)) \to (ex2 T (\lambda (t: 
T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v t2 t)))))))))).(\lambda 
(t: T).(\lambda (k: K).(\lambda (t2: T).(\lambda (u3: T).(\lambda (i2: 
nat).(\lambda (H2: (subst0 i2 u3 (THead k u0 t) t2)).(\lambda (H3: (not (eq 
nat i i2))).(or3_ind (ex2 T (\lambda (u4: T).(eq T t2 (THead k u4 t))) 
(\lambda (u4: T).(subst0 i2 u3 u0 u4))) (ex2 T (\lambda (t3: T).(eq T t2 
(THead k u0 t3))) (\lambda (t3: T).(subst0 (s k i2) u3 t t3))) (ex3_2 T T 
(\lambda (u4: T).(\lambda (t3: T).(eq T t2 (THead k u4 t3)))) (\lambda (u4: 
T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s k i2) u3 t t3)))) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead 
k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (H4: (ex2 T 
(\lambda (u4: T).(eq T t2 (THead k u4 t))) (\lambda (u4: T).(subst0 i2 u3 u0 
u4)))).(ex2_ind T (\lambda (u4: T).(eq T t2 (THead k u4 t))) (\lambda (u4: 
T).(subst0 i2 u3 u0 u4)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) 
t3)) (\lambda (t3: T).(subst0 i v t2 t3))) (\lambda (x: T).(\lambda (H5: (eq 
T t2 (THead k x t))).(\lambda (H6: (subst0 i2 u3 u0 x)).(eq_ind_r T (THead k 
x t) (\lambda (t3: T).(ex2 T (\lambda (t4: T).(subst0 i2 u3 (THead k u2 t) 
t4)) (\lambda (t4: T).(subst0 i v t3 t4)))) (ex2_ind T (\lambda (t3: 
T).(subst0 i2 u3 u2 t3)) (\lambda (t3: T).(subst0 i v x t3)) (ex2 T (\lambda 
(t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead 
k x t) t3))) (\lambda (x0: T).(\lambda (H7: (subst0 i2 u3 u2 x0)).(\lambda 
(H8: (subst0 i v x x0)).(ex_intro2 T (\lambda (t3: T).(subst0 i2 u3 (THead k 
u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k x t) t3)) (THead k x0 t) 
(subst0_fst u3 x0 u2 i2 H7 t k) (subst0_fst v x0 x i H8 t k))))) (H1 x u3 i2 
H6 H3)) t2 H5)))) H4)) (\lambda (H4: (ex2 T (\lambda (t3: T).(eq T t2 (THead 
k u0 t3))) (\lambda (t3: T).(subst0 (s k i2) u3 t t3)))).(ex2_ind T (\lambda 
(t3: T).(eq T t2 (THead k u0 t3))) (\lambda (t3: T).(subst0 (s k i2) u3 t 
t3)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i v t2 t3))) (\lambda (x: T).(\lambda (H5: (eq T t2 (THead k u0 
x))).(\lambda (H6: (subst0 (s k i2) u3 t x)).(eq_ind_r T (THead k u0 x) 
(\lambda (t3: T).(ex2 T (\lambda (t4: T).(subst0 i2 u3 (THead k u2 t) t4)) 
(\lambda (t4: T).(subst0 i v t3 t4)))) (ex_intro2 T (\lambda (t3: T).(subst0 
i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead k u0 x) t3)) 
(THead k u2 x) (subst0_snd k u3 x t i2 H6 u2) (subst0_fst v u2 u0 i H0 x k)) 
t2 H5)))) H4)) (\lambda (H4: (ex3_2 T T (\lambda (u4: T).(\lambda (t3: T).(eq 
T t2 (THead k u4 t3)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 
u4))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i2) u3 t 
t3))))).(ex3_2_ind T T (\lambda (u4: T).(\lambda (t3: T).(eq T t2 (THead k u4 
t3)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s k i2) u3 t t3))) (ex2 T (\lambda (t3: 
T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v t2 t3))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t2 (THead k x0 
x1))).(\lambda (H6: (subst0 i2 u3 u0 x0)).(\lambda (H7: (subst0 (s k i2) u3 t 
x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t3: T).(ex2 T (\lambda (t4: 
T).(subst0 i2 u3 (THead k u2 t) t4)) (\lambda (t4: T).(subst0 i v t3 t4)))) 
(ex2_ind T (\lambda (t3: T).(subst0 i2 u3 u2 t3)) (\lambda (t3: T).(subst0 i 
v x0 t3)) (ex2 T (\lambda (t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda 
(t3: T).(subst0 i v (THead k x0 x1) t3))) (\lambda (x: T).(\lambda (H8: 
(subst0 i2 u3 u2 x)).(\lambda (H9: (subst0 i v x0 x)).(ex_intro2 T (\lambda 
(t3: T).(subst0 i2 u3 (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i v (THead 
k x0 x1) t3)) (THead k x x1) (subst0_both u3 u2 x i2 H8 k t x1 H7) 
(subst0_fst v x x0 i H9 x1 k))))) (H1 x0 u3 i2 H6 H3)) t2 H5)))))) H4)) 
(subst0_gen_head k u3 u0 t t2 i2 H2))))))))))))))) (\lambda (k: K).(\lambda 
(v: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (i: nat).(\lambda (H0: 
(subst0 (s k i) v t3 t2)).(\lambda (H1: ((\forall (t4: T).(\forall (u2: 
T).(\forall (i2: nat).((subst0 i2 u2 t3 t4) \to ((not (eq nat (s k i) i2)) 
\to (ex2 T (\lambda (t: T).(subst0 i2 u2 t2 t)) (\lambda (t: T).(subst0 (s k 
i) v t4 t)))))))))).(\lambda (u: T).(\lambda (t4: T).(\lambda (u2: 
T).(\lambda (i2: nat).(\lambda (H2: (subst0 i2 u2 (THead k u t3) 
t4)).(\lambda (H3: (not (eq nat i i2))).(or3_ind (ex2 T (\lambda (u3: T).(eq 
T t4 (THead k u3 t3))) (\lambda (u3: T).(subst0 i2 u2 u u3))) (ex2 T (\lambda 
(t5: T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s k i2) u2 t3 
t5))) (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 
t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i2) u2 t3 t5)))) (ex2 T (\lambda (t: 
T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) 
(\lambda (H4: (ex2 T (\lambda (u3: T).(eq T t4 (THead k u3 t3))) (\lambda 
(u3: T).(subst0 i2 u2 u u3)))).(ex2_ind T (\lambda (u3: T).(eq T t4 (THead k 
u3 t3))) (\lambda (u3: T).(subst0 i2 u2 u u3)) (ex2 T (\lambda (t: T).(subst0 
i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: 
T).(\lambda (H5: (eq T t4 (THead k x t3))).(\lambda (H6: (subst0 i2 u2 u 
x)).(eq_ind_r T (THead k x t3) (\lambda (t: T).(ex2 T (\lambda (t5: 
T).(subst0 i2 u2 (THead k u t2) t5)) (\lambda (t5: T).(subst0 i v t t5)))) 
(ex_intro2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: 
T).(subst0 i v (THead k x t3) t)) (THead k x t2) (subst0_fst u2 x u i2 H6 t2 
k) (subst0_snd k v t2 t3 i H0 x)) t4 H5)))) H4)) (\lambda (H4: (ex2 T 
(\lambda (t5: T).(eq T t4 (THead k u t5))) (\lambda (t5: T).(subst0 (s k i2) 
u2 t3 t5)))).(ex2_ind T (\lambda (t5: T).(eq T t4 (THead k u t5))) (\lambda 
(t5: T).(subst0 (s k i2) u2 t3 t5)) (ex2 T (\lambda (t: T).(subst0 i2 u2 
(THead k u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: 
T).(\lambda (H5: (eq T t4 (THead k u x))).(\lambda (H6: (subst0 (s k i2) u2 
t3 x)).(eq_ind_r T (THead k u x) (\lambda (t: T).(ex2 T (\lambda (t5: 
T).(subst0 i2 u2 (THead k u t2) t5)) (\lambda (t5: T).(subst0 i v t t5)))) 
(ex2_ind T (\lambda (t: T).(subst0 (s k i2) u2 t2 t)) (\lambda (t: T).(subst0 
(s k i) v x t)) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) 
(\lambda (t: T).(subst0 i v (THead k u x) t))) (\lambda (x0: T).(\lambda (H7: 
(subst0 (s k i2) u2 t2 x0)).(\lambda (H8: (subst0 (s k i) v x x0)).(ex_intro2 
T (\lambda (t: T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i 
v (THead k u x) t)) (THead k u x0) (subst0_snd k u2 x0 t2 i2 H7 u) 
(subst0_snd k v x0 x i H8 u))))) (H1 x u2 (s k i2) H6 (ex2_ind T (\lambda (t: 
T).(subst0 (s k i2) u2 t2 t)) (\lambda (t: T).(subst0 (s k i) v x t)) ((eq 
nat (s k i) (s k i2)) \to False) (\lambda (x0: T).(\lambda (_: (subst0 (s k 
i2) u2 t2 x0)).(\lambda (_: (subst0 (s k i) v x x0)).(\lambda (H9: (eq nat (s 
k i) (s k i2))).(H3 (s_inj k i i2 H9)))))) (H1 x u2 (s k i2) H6 (\lambda (H7: 
(eq nat (s k i) (s k i2))).(H3 (s_inj k i i2 H7))))))) t4 H5)))) H4)) 
(\lambda (H4: (ex3_2 T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k 
u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i2) u2 t3 t5))))).(ex3_2_ind T T (\lambda 
(u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i2 u2 u u3))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s k i2) u2 t3 t5))) (ex2 T (\lambda (t: T).(subst0 i2 u2 (THead k 
u t2) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T t4 (THead k x0 x1))).(\lambda (H6: (subst0 i2 u2 u 
x0)).(\lambda (H7: (subst0 (s k i2) u2 t3 x1)).(eq_ind_r T (THead k x0 x1) 
(\lambda (t: T).(ex2 T (\lambda (t5: T).(subst0 i2 u2 (THead k u t2) t5)) 
(\lambda (t5: T).(subst0 i v t t5)))) (ex2_ind T (\lambda (t: T).(subst0 (s k 
i2) u2 t2 t)) (\lambda (t: T).(subst0 (s k i) v x1 t)) (ex2 T (\lambda (t: 
T).(subst0 i2 u2 (THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k x0 
x1) t))) (\lambda (x: T).(\lambda (H8: (subst0 (s k i2) u2 t2 x)).(\lambda 
(H9: (subst0 (s k i) v x1 x)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u2 
(THead k u t2) t)) (\lambda (t: T).(subst0 i v (THead k x0 x1) t)) (THead k 
x0 x) (subst0_both u2 u x0 i2 H6 k t2 x H8) (subst0_snd k v x x1 i H9 x0))))) 
(H1 x1 u2 (s k i2) H7 (ex2_ind T (\lambda (t: T).(subst0 (s k i2) u2 t2 t)) 
(\lambda (t: T).(subst0 (s k i) v x1 t)) ((eq nat (s k i) (s k i2)) \to 
False) (\lambda (x: T).(\lambda (_: (subst0 (s k i2) u2 t2 x)).(\lambda (_: 
(subst0 (s k i) v x1 x)).(\lambda (H10: (eq nat (s k i) (s k i2))).(H3 (s_inj 
k i i2 H10)))))) (H1 x1 u2 (s k i2) H7 (\lambda (H8: (eq nat (s k i) (s k 
i2))).(H3 (s_inj k i i2 H8))))))) t4 H5)))))) H4)) (subst0_gen_head k u2 u t3 
t4 i2 H2))))))))))))))) (\lambda (v: T).(\lambda (u0: T).(\lambda (u2: 
T).(\lambda (i: nat).(\lambda (H0: (subst0 i v u0 u2)).(\lambda (H1: 
((\forall (t2: T).(\forall (u3: T).(\forall (i2: nat).((subst0 i2 u3 u0 t2) 
\to ((not (eq nat i i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u3 u2 t)) 
(\lambda (t: T).(subst0 i v t2 t)))))))))).(\lambda (k: K).(\lambda (t2: 
T).(\lambda (t3: T).(\lambda (H2: (subst0 (s k i) v t2 t3)).(\lambda (H3: 
((\forall (t4: T).(\forall (u3: T).(\forall (i2: nat).((subst0 i2 u3 t2 t4) 
\to ((not (eq nat (s k i) i2)) \to (ex2 T (\lambda (t: T).(subst0 i2 u3 t3 
t)) (\lambda (t: T).(subst0 (s k i) v t4 t)))))))))).(\lambda (t4: 
T).(\lambda (u3: T).(\lambda (i2: nat).(\lambda (H4: (subst0 i2 u3 (THead k 
u0 t2) t4)).(\lambda (H5: (not (eq nat i i2))).(or3_ind (ex2 T (\lambda (u4: 
T).(eq T t4 (THead k u4 t2))) (\lambda (u4: T).(subst0 i2 u3 u0 u4))) (ex2 T 
(\lambda (t5: T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i2) 
u3 t2 t5))) (ex3_2 T T (\lambda (u4: T).(\lambda (t5: T).(eq T t4 (THead k u4 
t5)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i2) u3 t2 t5)))) (ex2 T (\lambda (t: 
T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) 
(\lambda (H6: (ex2 T (\lambda (u4: T).(eq T t4 (THead k u4 t2))) (\lambda 
(u4: T).(subst0 i2 u3 u0 u4)))).(ex2_ind T (\lambda (u4: T).(eq T t4 (THead k 
u4 t2))) (\lambda (u4: T).(subst0 i2 u3 u0 u4)) (ex2 T (\lambda (t: 
T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) 
(\lambda (x: T).(\lambda (H7: (eq T t4 (THead k x t2))).(\lambda (H8: (subst0 
i2 u3 u0 x)).(eq_ind_r T (THead k x t2) (\lambda (t: T).(ex2 T (\lambda (t5: 
T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) 
(ex2_ind T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v x 
t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i v (THead k x t2) t))) (\lambda (x0: T).(\lambda (H9: (subst0 i2 
u3 u2 x0)).(\lambda (H10: (subst0 i v x x0)).(ex_intro2 T (\lambda (t: 
T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x 
t2) t)) (THead k x0 t3) (subst0_fst u3 x0 u2 i2 H9 t3 k) (subst0_both v x x0 
i H10 k t2 t3 H2))))) (H1 x u3 i2 H8 H5)) t4 H7)))) H6)) (\lambda (H6: (ex2 T 
(\lambda (t5: T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i2) 
u3 t2 t5)))).(ex2_ind T (\lambda (t5: T).(eq T t4 (THead k u0 t5))) (\lambda 
(t5: T).(subst0 (s k i2) u3 t2 t5)) (ex2 T (\lambda (t: T).(subst0 i2 u3 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) (\lambda (x: 
T).(\lambda (H7: (eq T t4 (THead k u0 x))).(\lambda (H8: (subst0 (s k i2) u3 
t2 x)).(eq_ind_r T (THead k u0 x) (\lambda (t: T).(ex2 T (\lambda (t5: 
T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) 
(ex2_ind T (\lambda (t: T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 
(s k i) v x t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i v (THead k u0 x) t))) (\lambda (x0: T).(\lambda 
(H9: (subst0 (s k i2) u3 t3 x0)).(\lambda (H10: (subst0 (s k i) v x 
x0)).(ex_intro2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda 
(t: T).(subst0 i v (THead k u0 x) t)) (THead k u2 x0) (subst0_snd k u3 x0 t3 
i2 H9 u2) (subst0_both v u0 u2 i H0 k x x0 H10))))) (H3 x u3 (s k i2) H8 
(ex2_ind T (\lambda (t: T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 
(s k i) v x t)) ((eq nat (s k i) (s k i2)) \to False) (\lambda (x0: 
T).(\lambda (_: (subst0 (s k i2) u3 t3 x0)).(\lambda (_: (subst0 (s k i) v x 
x0)).(\lambda (H11: (eq nat (s k i) (s k i2))).(H5 (s_inj k i i2 H11)))))) 
(H3 x u3 (s k i2) H8 (\lambda (H9: (eq nat (s k i) (s k i2))).(H5 (s_inj k i 
i2 H9))))))) t4 H7)))) H6)) (\lambda (H6: (ex3_2 T T (\lambda (u4: 
T).(\lambda (t5: T).(eq T t4 (THead k u4 t5)))) (\lambda (u4: T).(\lambda (_: 
T).(subst0 i2 u3 u0 u4))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) 
u3 t2 t5))))).(ex3_2_ind T T (\lambda (u4: T).(\lambda (t5: T).(eq T t4 
(THead k u4 t5)))) (\lambda (u4: T).(\lambda (_: T).(subst0 i2 u3 u0 u4))) 
(\lambda (_: T).(\lambda (t5: T).(subst0 (s k i2) u3 t2 t5))) (ex2 T (\lambda 
(t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v t4 t))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T t4 (THead k x0 
x1))).(\lambda (H8: (subst0 i2 u3 u0 x0)).(\lambda (H9: (subst0 (s k i2) u3 
t2 x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(ex2 T (\lambda (t5: 
T).(subst0 i2 u3 (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i v t t5)))) 
(ex2_ind T (\lambda (t: T).(subst0 i2 u3 u2 t)) (\lambda (t: T).(subst0 i v 
x0 t)) (ex2 T (\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i v (THead k x0 x1) t))) (\lambda (x: T).(\lambda (H10: (subst0 i2 
u3 u2 x)).(\lambda (H11: (subst0 i v x0 x)).(ex2_ind T (\lambda (t: 
T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 (s k i) v x1 t)) (ex2 T 
(\lambda (t: T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v 
(THead k x0 x1) t))) (\lambda (x2: T).(\lambda (H12: (subst0 (s k i2) u3 t3 
x2)).(\lambda (H13: (subst0 (s k i) v x1 x2)).(ex_intro2 T (\lambda (t: 
T).(subst0 i2 u3 (THead k u2 t3) t)) (\lambda (t: T).(subst0 i v (THead k x0 
x1) t)) (THead k x x2) (subst0_both u3 u2 x i2 H10 k t3 x2 H12) (subst0_both 
v x0 x i H11 k x1 x2 H13))))) (H3 x1 u3 (s k i2) H9 (ex2_ind T (\lambda (t: 
T).(subst0 (s k i2) u3 t3 t)) (\lambda (t: T).(subst0 (s k i) v x1 t)) ((eq 
nat (s k i) (s k i2)) \to False) (\lambda (x2: T).(\lambda (_: (subst0 (s k 
i2) u3 t3 x2)).(\lambda (_: (subst0 (s k i) v x1 x2)).(\lambda (H14: (eq nat 
(s k i) (s k i2))).(H5 (s_inj k i i2 H14)))))) (H3 x1 u3 (s k i2) H9 (\lambda 
(H12: (eq nat (s k i) (s k i2))).(H5 (s_inj k i i2 H12)))))))))) (H1 x0 u3 i2 
H8 H5)) t4 H7)))))) H6)) (subst0_gen_head k u3 u0 t2 t4 i2 
H4)))))))))))))))))) i1 u1 t0 t1 H))))).
(* COMMENTS
Initial nodes: 5375
END *)

theorem subst0_confluence_eq:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t0 t1) \to (\forall (t2: T).((subst0 i u t0 t2) \to (or4 (eq T t1 t2) 
(ex2 T (\lambda (t: T).(subst0 i u t1 t)) (\lambda (t: T).(subst0 i u t2 t))) 
(subst0 i u t1 t2) (subst0 i u t2 t1))))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t0 t1)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t2: T).(\lambda (t3: T).(\forall (t4: T).((subst0 n t t2 t4) \to 
(or4 (eq T t3 t4) (ex2 T (\lambda (t5: T).(subst0 n t t3 t5)) (\lambda (t5: 
T).(subst0 n t t4 t5))) (subst0 n t t3 t4) (subst0 n t t4 t3)))))))) (\lambda 
(v: T).(\lambda (i0: nat).(\lambda (t2: T).(\lambda (H0: (subst0 i0 v (TLRef 
i0) t2)).(land_ind (eq nat i0 i0) (eq T t2 (lift (S i0) O v)) (or4 (eq T 
(lift (S i0) O v) t2) (ex2 T (\lambda (t: T).(subst0 i0 v (lift (S i0) O v) 
t)) (\lambda (t: T).(subst0 i0 v t2 t))) (subst0 i0 v (lift (S i0) O v) t2) 
(subst0 i0 v t2 (lift (S i0) O v))) (\lambda (_: (eq nat i0 i0)).(\lambda 
(H2: (eq T t2 (lift (S i0) O v))).(or4_intro0 (eq T (lift (S i0) O v) t2) 
(ex2 T (\lambda (t: T).(subst0 i0 v (lift (S i0) O v) t)) (\lambda (t: 
T).(subst0 i0 v t2 t))) (subst0 i0 v (lift (S i0) O v) t2) (subst0 i0 v t2 
(lift (S i0) O v)) (sym_eq T t2 (lift (S i0) O v) H2)))) (subst0_gen_lref v 
t2 i0 i0 H0)))))) (\lambda (v: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda 
(i0: nat).(\lambda (H0: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (t2: 
T).((subst0 i0 v u1 t2) \to (or4 (eq T u2 t2) (ex2 T (\lambda (t: T).(subst0 
i0 v u2 t)) (\lambda (t: T).(subst0 i0 v t2 t))) (subst0 i0 v u2 t2) (subst0 
i0 v t2 u2)))))).(\lambda (t: T).(\lambda (k: K).(\lambda (t2: T).(\lambda 
(H2: (subst0 i0 v (THead k u1 t) t2)).(or3_ind (ex2 T (\lambda (u3: T).(eq T 
t2 (THead k u3 t))) (\lambda (u3: T).(subst0 i0 v u1 u3))) (ex2 T (\lambda 
(t3: T).(eq T t2 (THead k u1 t3))) (\lambda (t3: T).(subst0 (s k i0) v t 
t3))) (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead k u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s k i0) v t t3)))) (or4 (eq T (THead k u2 t) t2) 
(ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v t2 t3))) (subst0 i0 v (THead k u2 t) t2) (subst0 i0 v t2 
(THead k u2 t))) (\lambda (H3: (ex2 T (\lambda (u3: T).(eq T t2 (THead k u3 
t))) (\lambda (u3: T).(subst0 i0 v u1 u3)))).(ex2_ind T (\lambda (u3: T).(eq 
T t2 (THead k u3 t))) (\lambda (u3: T).(subst0 i0 v u1 u3)) (or4 (eq T (THead 
k u2 t) t2) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda 
(t3: T).(subst0 i0 v t2 t3))) (subst0 i0 v (THead k u2 t) t2) (subst0 i0 v t2 
(THead k u2 t))) (\lambda (x: T).(\lambda (H4: (eq T t2 (THead k x 
t))).(\lambda (H5: (subst0 i0 v u1 x)).(eq_ind_r T (THead k x t) (\lambda 
(t3: T).(or4 (eq T (THead k u2 t) t3) (ex2 T (\lambda (t4: T).(subst0 i0 v 
(THead k u2 t) t4)) (\lambda (t4: T).(subst0 i0 v t3 t4))) (subst0 i0 v 
(THead k u2 t) t3) (subst0 i0 v t3 (THead k u2 t)))) (or4_ind (eq T u2 x) 
(ex2 T (\lambda (t3: T).(subst0 i0 v u2 t3)) (\lambda (t3: T).(subst0 i0 v x 
t3))) (subst0 i0 v u2 x) (subst0 i0 v x u2) (or4 (eq T (THead k u2 t) (THead 
k x t)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda 
(t3: T).(subst0 i0 v (THead k x t) t3))) (subst0 i0 v (THead k u2 t) (THead k 
x t)) (subst0 i0 v (THead k x t) (THead k u2 t))) (\lambda (H6: (eq T u2 
x)).(eq_ind_r T x (\lambda (t3: T).(or4 (eq T (THead k t3 t) (THead k x t)) 
(ex2 T (\lambda (t4: T).(subst0 i0 v (THead k t3 t) t4)) (\lambda (t4: 
T).(subst0 i0 v (THead k x t) t4))) (subst0 i0 v (THead k t3 t) (THead k x 
t)) (subst0 i0 v (THead k x t) (THead k t3 t)))) (or4_intro0 (eq T (THead k x 
t) (THead k x t)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k x t) t3)) 
(\lambda (t3: T).(subst0 i0 v (THead k x t) t3))) (subst0 i0 v (THead k x t) 
(THead k x t)) (subst0 i0 v (THead k x t) (THead k x t)) (refl_equal T (THead 
k x t))) u2 H6)) (\lambda (H6: (ex2 T (\lambda (t3: T).(subst0 i0 v u2 t3)) 
(\lambda (t3: T).(subst0 i0 v x t3)))).(ex2_ind T (\lambda (t3: T).(subst0 i0 
v u2 t3)) (\lambda (t3: T).(subst0 i0 v x t3)) (or4 (eq T (THead k u2 t) 
(THead k x t)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) 
(\lambda (t3: T).(subst0 i0 v (THead k x t) t3))) (subst0 i0 v (THead k u2 t) 
(THead k x t)) (subst0 i0 v (THead k x t) (THead k u2 t))) (\lambda (x0: 
T).(\lambda (H7: (subst0 i0 v u2 x0)).(\lambda (H8: (subst0 i0 v x 
x0)).(or4_intro1 (eq T (THead k u2 t) (THead k x t)) (ex2 T (\lambda (t3: 
T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k x 
t) t3))) (subst0 i0 v (THead k u2 t) (THead k x t)) (subst0 i0 v (THead k x 
t) (THead k u2 t)) (ex_intro2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) 
t3)) (\lambda (t3: T).(subst0 i0 v (THead k x t) t3)) (THead k x0 t) 
(subst0_fst v x0 u2 i0 H7 t k) (subst0_fst v x0 x i0 H8 t k)))))) H6)) 
(\lambda (H6: (subst0 i0 v u2 x)).(or4_intro2 (eq T (THead k u2 t) (THead k x 
t)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v (THead k x t) t3))) (subst0 i0 v (THead k u2 t) (THead k x 
t)) (subst0 i0 v (THead k x t) (THead k u2 t)) (subst0_fst v x u2 i0 H6 t 
k))) (\lambda (H6: (subst0 i0 v x u2)).(or4_intro3 (eq T (THead k u2 t) 
(THead k x t)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) 
(\lambda (t3: T).(subst0 i0 v (THead k x t) t3))) (subst0 i0 v (THead k u2 t) 
(THead k x t)) (subst0 i0 v (THead k x t) (THead k u2 t)) (subst0_fst v u2 x 
i0 H6 t k))) (H1 x H5)) t2 H4)))) H3)) (\lambda (H3: (ex2 T (\lambda (t3: 
T).(eq T t2 (THead k u1 t3))) (\lambda (t3: T).(subst0 (s k i0) v t 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t2 (THead k u1 t3))) (\lambda (t3: 
T).(subst0 (s k i0) v t t3)) (or4 (eq T (THead k u2 t) t2) (ex2 T (\lambda 
(t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v t2 
t3))) (subst0 i0 v (THead k u2 t) t2) (subst0 i0 v t2 (THead k u2 t))) 
(\lambda (x: T).(\lambda (H4: (eq T t2 (THead k u1 x))).(\lambda (H5: (subst0 
(s k i0) v t x)).(eq_ind_r T (THead k u1 x) (\lambda (t3: T).(or4 (eq T 
(THead k u2 t) t3) (ex2 T (\lambda (t4: T).(subst0 i0 v (THead k u2 t) t4)) 
(\lambda (t4: T).(subst0 i0 v t3 t4))) (subst0 i0 v (THead k u2 t) t3) 
(subst0 i0 v t3 (THead k u2 t)))) (or4_ind (eq T u2 u2) (ex2 T (\lambda (t3: 
T).(subst0 i0 v u2 t3)) (\lambda (t3: T).(subst0 i0 v u2 t3))) (subst0 i0 v 
u2 u2) (subst0 i0 v u2 u2) (or4 (eq T (THead k u2 t) (THead k u1 x)) (ex2 T 
(\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 
v (THead k u1 x) t3))) (subst0 i0 v (THead k u2 t) (THead k u1 x)) (subst0 i0 
v (THead k u1 x) (THead k u2 t))) (\lambda (_: (eq T u2 u2)).(or4_intro1 (eq 
T (THead k u2 t) (THead k u1 x)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead 
k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 x) t3))) (subst0 i0 v 
(THead k u2 t) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t)) 
(ex_intro2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v (THead k u1 x) t3)) (THead k u2 x) (subst0_snd k v x t i0 H5 
u2) (subst0_fst v u2 u1 i0 H0 x k)))) (\lambda (H6: (ex2 T (\lambda (t3: 
T).(subst0 i0 v u2 t3)) (\lambda (t3: T).(subst0 i0 v u2 t3)))).(ex2_ind T 
(\lambda (t3: T).(subst0 i0 v u2 t3)) (\lambda (t3: T).(subst0 i0 v u2 t3)) 
(or4 (eq T (THead k u2 t) (THead k u1 x)) (ex2 T (\lambda (t3: T).(subst0 i0 
v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 x) t3))) 
(subst0 i0 v (THead k u2 t) (THead k u1 x)) (subst0 i0 v (THead k u1 x) 
(THead k u2 t))) (\lambda (x0: T).(\lambda (_: (subst0 i0 v u2 x0)).(\lambda 
(_: (subst0 i0 v u2 x0)).(or4_intro1 (eq T (THead k u2 t) (THead k u1 x)) 
(ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v (THead k u1 x) t3))) (subst0 i0 v (THead k u2 t) (THead k u1 
x)) (subst0 i0 v (THead k u1 x) (THead k u2 t)) (ex_intro2 T (\lambda (t3: 
T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 
x) t3)) (THead k u2 x) (subst0_snd k v x t i0 H5 u2) (subst0_fst v u2 u1 i0 
H0 x k)))))) H6)) (\lambda (_: (subst0 i0 v u2 u2)).(or4_intro1 (eq T (THead 
k u2 t) (THead k u1 x)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) 
t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 x) t3))) (subst0 i0 v (THead k 
u2 t) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t)) (ex_intro2 
T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 
i0 v (THead k u1 x) t3)) (THead k u2 x) (subst0_snd k v x t i0 H5 u2) 
(subst0_fst v u2 u1 i0 H0 x k)))) (\lambda (_: (subst0 i0 v u2 
u2)).(or4_intro1 (eq T (THead k u2 t) (THead k u1 x)) (ex2 T (\lambda (t3: 
T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 
x) t3))) (subst0 i0 v (THead k u2 t) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t)) (ex_intro2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) 
t3)) (\lambda (t3: T).(subst0 i0 v (THead k u1 x) t3)) (THead k u2 x) 
(subst0_snd k v x t i0 H5 u2) (subst0_fst v u2 u1 i0 H0 x k)))) (H1 u2 H0)) 
t2 H4)))) H3)) (\lambda (H3: (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq 
T t2 (THead k u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(subst0 (s k i0) v t 
t3))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead k u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s k i0) v t t3))) (or4 (eq T (THead k u2 t) t2) 
(ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v t2 t3))) (subst0 i0 v (THead k u2 t) t2) (subst0 i0 v t2 
(THead k u2 t))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t2 
(THead k x0 x1))).(\lambda (H5: (subst0 i0 v u1 x0)).(\lambda (H6: (subst0 (s 
k i0) v t x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t3: T).(or4 (eq T (THead 
k u2 t) t3) (ex2 T (\lambda (t4: T).(subst0 i0 v (THead k u2 t) t4)) (\lambda 
(t4: T).(subst0 i0 v t3 t4))) (subst0 i0 v (THead k u2 t) t3) (subst0 i0 v t3 
(THead k u2 t)))) (or4_ind (eq T u2 x0) (ex2 T (\lambda (t3: T).(subst0 i0 v 
u2 t3)) (\lambda (t3: T).(subst0 i0 v x0 t3))) (subst0 i0 v u2 x0) (subst0 i0 
v x0 u2) (or4 (eq T (THead k u2 t) (THead k x0 x1)) (ex2 T (\lambda (t3: 
T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k x0 
x1) t3))) (subst0 i0 v (THead k u2 t) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k u2 t))) (\lambda (H7: (eq T u2 x0)).(eq_ind_r T x0 (\lambda 
(t3: T).(or4 (eq T (THead k t3 t) (THead k x0 x1)) (ex2 T (\lambda (t4: 
T).(subst0 i0 v (THead k t3 t) t4)) (\lambda (t4: T).(subst0 i0 v (THead k x0 
x1) t4))) (subst0 i0 v (THead k t3 t) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k t3 t)))) (or4_intro2 (eq T (THead k x0 t) (THead k x0 x1)) 
(ex2 T (\lambda (t3: T).(subst0 i0 v (THead k x0 t) t3)) (\lambda (t3: 
T).(subst0 i0 v (THead k x0 x1) t3))) (subst0 i0 v (THead k x0 t) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k x0 t)) (subst0_snd k v x1 t i0 H6 
x0)) u2 H7)) (\lambda (H7: (ex2 T (\lambda (t3: T).(subst0 i0 v u2 t3)) 
(\lambda (t3: T).(subst0 i0 v x0 t3)))).(ex2_ind T (\lambda (t3: T).(subst0 
i0 v u2 t3)) (\lambda (t3: T).(subst0 i0 v x0 t3)) (or4 (eq T (THead k u2 t) 
(THead k x0 x1)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) 
(\lambda (t3: T).(subst0 i0 v (THead k x0 x1) t3))) (subst0 i0 v (THead k u2 
t) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t))) (\lambda 
(x: T).(\lambda (H8: (subst0 i0 v u2 x)).(\lambda (H9: (subst0 i0 v x0 
x)).(or4_intro1 (eq T (THead k u2 t) (THead k x0 x1)) (ex2 T (\lambda (t3: 
T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k x0 
x1) t3))) (subst0 i0 v (THead k u2 t) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k u2 t)) (ex_intro2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 
t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k x0 x1) t3)) (THead k x x1) 
(subst0_both v u2 x i0 H8 k t x1 H6) (subst0_fst v x x0 i0 H9 x1 k)))))) H7)) 
(\lambda (H7: (subst0 i0 v u2 x0)).(or4_intro2 (eq T (THead k u2 t) (THead k 
x0 x1)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda 
(t3: T).(subst0 i0 v (THead k x0 x1) t3))) (subst0 i0 v (THead k u2 t) (THead 
k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t)) (subst0_both v u2 x0 
i0 H7 k t x1 H6))) (\lambda (H7: (subst0 i0 v x0 u2)).(or4_intro1 (eq T 
(THead k u2 t) (THead k x0 x1)) (ex2 T (\lambda (t3: T).(subst0 i0 v (THead k 
u2 t) t3)) (\lambda (t3: T).(subst0 i0 v (THead k x0 x1) t3))) (subst0 i0 v 
(THead k u2 t) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t)) 
(ex_intro2 T (\lambda (t3: T).(subst0 i0 v (THead k u2 t) t3)) (\lambda (t3: 
T).(subst0 i0 v (THead k x0 x1) t3)) (THead k u2 x1) (subst0_snd k v x1 t i0 
H6 u2) (subst0_fst v u2 x0 i0 H7 x1 k)))) (H1 x0 H5)) t2 H4)))))) H3)) 
(subst0_gen_head k v u1 t t2 i0 H2)))))))))))) (\lambda (k: K).(\lambda (v: 
T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (i0: nat).(\lambda (H0: (subst0 
(s k i0) v t3 t2)).(\lambda (H1: ((\forall (t4: T).((subst0 (s k i0) v t3 t4) 
\to (or4 (eq T t2 t4) (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) 
(\lambda (t: T).(subst0 (s k i0) v t4 t))) (subst0 (s k i0) v t2 t4) (subst0 
(s k i0) v t4 t2)))))).(\lambda (u0: T).(\lambda (t4: T).(\lambda (H2: 
(subst0 i0 v (THead k u0 t3) t4)).(or3_ind (ex2 T (\lambda (u2: T).(eq T t4 
(THead k u2 t3))) (\lambda (u2: T).(subst0 i0 v u0 u2))) (ex2 T (\lambda (t5: 
T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i0) v t3 t5))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead k u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i0 v u0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i0) v t3 t5)))) (or4 (eq T (THead k u0 t2) 
t4) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: 
T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u0 t2) t4) (subst0 i0 v t4 
(THead k u0 t2))) (\lambda (H3: (ex2 T (\lambda (u2: T).(eq T t4 (THead k u2 
t3))) (\lambda (u2: T).(subst0 i0 v u0 u2)))).(ex2_ind T (\lambda (u2: T).(eq 
T t4 (THead k u2 t3))) (\lambda (u2: T).(subst0 i0 v u0 u2)) (or4 (eq T 
(THead k u0 t2) t4) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) 
(\lambda (t: T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u0 t2) t4) (subst0 
i0 v t4 (THead k u0 t2))) (\lambda (x: T).(\lambda (H4: (eq T t4 (THead k x 
t3))).(\lambda (H5: (subst0 i0 v u0 x)).(eq_ind_r T (THead k x t3) (\lambda 
(t: T).(or4 (eq T (THead k u0 t2) t) (ex2 T (\lambda (t5: T).(subst0 i0 v 
(THead k u0 t2) t5)) (\lambda (t5: T).(subst0 i0 v t t5))) (subst0 i0 v 
(THead k u0 t2) t) (subst0 i0 v t (THead k u0 t2)))) (or4_ind (eq T t2 t2) 
(ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) (\lambda (t: T).(subst0 (s k 
i0) v t2 t))) (subst0 (s k i0) v t2 t2) (subst0 (s k i0) v t2 t2) (or4 (eq T 
(THead k u0 t2) (THead k x t3)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x t3) t))) (subst0 i0 v 
(THead k u0 t2) (THead k x t3)) (subst0 i0 v (THead k x t3) (THead k u0 t2))) 
(\lambda (_: (eq T t2 t2)).(or4_intro1 (eq T (THead k u0 t2) (THead k x t3)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t3) t))) (subst0 i0 v (THead k u0 t2) (THead k x 
t3)) (subst0 i0 v (THead k x t3) (THead k u0 t2)) (ex_intro2 T (\lambda (t: 
T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t3) t)) (THead k x t2) (subst0_fst v x u0 i0 H5 t2 k) (subst0_snd k v t2 t3 
i0 H0 x)))) (\lambda (H6: (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) 
(\lambda (t: T).(subst0 (s k i0) v t2 t)))).(ex2_ind T (\lambda (t: 
T).(subst0 (s k i0) v t2 t)) (\lambda (t: T).(subst0 (s k i0) v t2 t)) (or4 
(eq T (THead k u0 t2) (THead k x t3)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x t3) t))) (subst0 
i0 v (THead k u0 t2) (THead k x t3)) (subst0 i0 v (THead k x t3) (THead k u0 
t2))) (\lambda (x0: T).(\lambda (_: (subst0 (s k i0) v t2 x0)).(\lambda (_: 
(subst0 (s k i0) v t2 x0)).(or4_intro1 (eq T (THead k u0 t2) (THead k x t3)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t3) t))) (subst0 i0 v (THead k u0 t2) (THead k x 
t3)) (subst0 i0 v (THead k x t3) (THead k u0 t2)) (ex_intro2 T (\lambda (t: 
T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t3) t)) (THead k x t2) (subst0_fst v x u0 i0 H5 t2 k) (subst0_snd k v t2 t3 
i0 H0 x)))))) H6)) (\lambda (_: (subst0 (s k i0) v t2 t2)).(or4_intro1 (eq T 
(THead k u0 t2) (THead k x t3)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x t3) t))) (subst0 i0 v 
(THead k u0 t2) (THead k x t3)) (subst0 i0 v (THead k x t3) (THead k u0 t2)) 
(ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t3) t)) (THead k x t2) (subst0_fst v x u0 i0 H5 t2 
k) (subst0_snd k v t2 t3 i0 H0 x)))) (\lambda (_: (subst0 (s k i0) v t2 
t2)).(or4_intro1 (eq T (THead k u0 t2) (THead k x t3)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t3) t))) (subst0 i0 v (THead k u0 t2) (THead k x t3)) (subst0 i0 v (THead k x 
t3) (THead k u0 t2)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u0 
t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x t3) t)) (THead k x t2) 
(subst0_fst v x u0 i0 H5 t2 k) (subst0_snd k v t2 t3 i0 H0 x)))) (H1 t2 H0)) 
t4 H4)))) H3)) (\lambda (H3: (ex2 T (\lambda (t5: T).(eq T t4 (THead k u0 
t5))) (\lambda (t5: T).(subst0 (s k i0) v t3 t5)))).(ex2_ind T (\lambda (t5: 
T).(eq T t4 (THead k u0 t5))) (\lambda (t5: T).(subst0 (s k i0) v t3 t5)) 
(or4 (eq T (THead k u0 t2) t4) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u0 t2) t)) (\lambda (t: T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u0 t2) 
t4) (subst0 i0 v t4 (THead k u0 t2))) (\lambda (x: T).(\lambda (H4: (eq T t4 
(THead k u0 x))).(\lambda (H5: (subst0 (s k i0) v t3 x)).(eq_ind_r T (THead k 
u0 x) (\lambda (t: T).(or4 (eq T (THead k u0 t2) t) (ex2 T (\lambda (t5: 
T).(subst0 i0 v (THead k u0 t2) t5)) (\lambda (t5: T).(subst0 i0 v t t5))) 
(subst0 i0 v (THead k u0 t2) t) (subst0 i0 v t (THead k u0 t2)))) (or4_ind 
(eq T t2 x) (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) (\lambda (t: 
T).(subst0 (s k i0) v x t))) (subst0 (s k i0) v t2 x) (subst0 (s k i0) v x 
t2) (or4 (eq T (THead k u0 t2) (THead k u0 x)) (ex2 T (\lambda (t: T).(subst0 
i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k u0 x) t))) 
(subst0 i0 v (THead k u0 t2) (THead k u0 x)) (subst0 i0 v (THead k u0 x) 
(THead k u0 t2))) (\lambda (H6: (eq T t2 x)).(eq_ind_r T x (\lambda (t: 
T).(or4 (eq T (THead k u0 t) (THead k u0 x)) (ex2 T (\lambda (t5: T).(subst0 
i0 v (THead k u0 t) t5)) (\lambda (t5: T).(subst0 i0 v (THead k u0 x) t5))) 
(subst0 i0 v (THead k u0 t) (THead k u0 x)) (subst0 i0 v (THead k u0 x) 
(THead k u0 t)))) (or4_intro0 (eq T (THead k u0 x) (THead k u0 x)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u0 x) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u0 x) t))) (subst0 i0 v (THead k u0 x) (THead k u0 x)) (subst0 i0 v 
(THead k u0 x) (THead k u0 x)) (refl_equal T (THead k u0 x))) t2 H6)) 
(\lambda (H6: (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) (\lambda (t: 
T).(subst0 (s k i0) v x t)))).(ex2_ind T (\lambda (t: T).(subst0 (s k i0) v 
t2 t)) (\lambda (t: T).(subst0 (s k i0) v x t)) (or4 (eq T (THead k u0 t2) 
(THead k u0 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u0 x) t))) (subst0 i0 v (THead k u0 t2) 
(THead k u0 x)) (subst0 i0 v (THead k u0 x) (THead k u0 t2))) (\lambda (x0: 
T).(\lambda (H7: (subst0 (s k i0) v t2 x0)).(\lambda (H8: (subst0 (s k i0) v 
x x0)).(or4_intro1 (eq T (THead k u0 t2) (THead k u0 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k u0 
x) t))) (subst0 i0 v (THead k u0 t2) (THead k u0 x)) (subst0 i0 v (THead k u0 
x) (THead k u0 t2)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) 
t)) (\lambda (t: T).(subst0 i0 v (THead k u0 x) t)) (THead k u0 x0) 
(subst0_snd k v x0 t2 i0 H7 u0) (subst0_snd k v x0 x i0 H8 u0)))))) H6)) 
(\lambda (H6: (subst0 (s k i0) v t2 x)).(or4_intro2 (eq T (THead k u0 t2) 
(THead k u0 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u0 x) t))) (subst0 i0 v (THead k u0 t2) 
(THead k u0 x)) (subst0 i0 v (THead k u0 x) (THead k u0 t2)) (subst0_snd k v 
x t2 i0 H6 u0))) (\lambda (H6: (subst0 (s k i0) v x t2)).(or4_intro3 (eq T 
(THead k u0 t2) (THead k u0 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k u0 x) t))) (subst0 i0 v 
(THead k u0 t2) (THead k u0 x)) (subst0 i0 v (THead k u0 x) (THead k u0 t2)) 
(subst0_snd k v t2 x i0 H6 u0))) (H1 x H5)) t4 H4)))) H3)) (\lambda (H3: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t5: T).(eq T t4 (THead k u2 t5)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i0 v u0 u2))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i0) v t3 t5))))).(ex3_2_ind T T (\lambda 
(u2: T).(\lambda (t5: T).(eq T t4 (THead k u2 t5)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i0 v u0 u2))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s k i0) v t3 t5))) (or4 (eq T (THead k u0 t2) t4) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v t4 t))) 
(subst0 i0 v (THead k u0 t2) t4) (subst0 i0 v t4 (THead k u0 t2))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H4: (eq T t4 (THead k x0 x1))).(\lambda 
(H5: (subst0 i0 v u0 x0)).(\lambda (H6: (subst0 (s k i0) v t3 x1)).(eq_ind_r 
T (THead k x0 x1) (\lambda (t: T).(or4 (eq T (THead k u0 t2) t) (ex2 T 
(\lambda (t5: T).(subst0 i0 v (THead k u0 t2) t5)) (\lambda (t5: T).(subst0 
i0 v t t5))) (subst0 i0 v (THead k u0 t2) t) (subst0 i0 v t (THead k u0 
t2)))) (or4_ind (eq T t2 x1) (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) 
(\lambda (t: T).(subst0 (s k i0) v x1 t))) (subst0 (s k i0) v t2 x1) (subst0 
(s k i0) v x1 t2) (or4 (eq T (THead k u0 t2) (THead k x0 x1)) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k 
x0 x1) t))) (subst0 i0 v (THead k u0 t2) (THead k x0 x1)) (subst0 i0 v (THead 
k x0 x1) (THead k u0 t2))) (\lambda (H7: (eq T t2 x1)).(eq_ind_r T x1 
(\lambda (t: T).(or4 (eq T (THead k u0 t) (THead k x0 x1)) (ex2 T (\lambda 
(t5: T).(subst0 i0 v (THead k u0 t) t5)) (\lambda (t5: T).(subst0 i0 v (THead 
k x0 x1) t5))) (subst0 i0 v (THead k u0 t) (THead k x0 x1)) (subst0 i0 v 
(THead k x0 x1) (THead k u0 t)))) (or4_intro2 (eq T (THead k u0 x1) (THead k 
x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 x1) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u0 x1) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k u0 x1)) (subst0_fst v x0 u0 i0 H5 
x1 k)) t2 H7)) (\lambda (H7: (ex2 T (\lambda (t: T).(subst0 (s k i0) v t2 t)) 
(\lambda (t: T).(subst0 (s k i0) v x1 t)))).(ex2_ind T (\lambda (t: 
T).(subst0 (s k i0) v t2 t)) (\lambda (t: T).(subst0 (s k i0) v x1 t)) (or4 
(eq T (THead k u0 t2) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 
i0 v (THead k u0 t2) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k 
u0 t2))) (\lambda (x: T).(\lambda (H8: (subst0 (s k i0) v t2 x)).(\lambda 
(H9: (subst0 (s k i0) v x1 x)).(or4_intro1 (eq T (THead k u0 t2) (THead k x0 
x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u0 t2) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k u0 t2)) (ex_intro2 T (\lambda (t: 
T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t)) (THead k x0 x) (subst0_both v u0 x0 i0 H5 k t2 x H8) (subst0_snd k v 
x x1 i0 H9 x0)))))) H7)) (\lambda (H7: (subst0 (s k i0) v t2 x1)).(or4_intro2 
(eq T (THead k u0 t2) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 
i0 v (THead k u0 t2) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k 
u0 t2)) (subst0_both v u0 x0 i0 H5 k t2 x1 H7))) (\lambda (H7: (subst0 (s k 
i0) v x1 t2)).(or4_intro1 (eq T (THead k u0 t2) (THead k x0 x1)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x0 x1) t))) (subst0 i0 v (THead k u0 t2) (THead k x0 x1)) (subst0 i0 
v (THead k x0 x1) (THead k u0 t2)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v 
(THead k u0 t2) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t)) (THead k 
x0 t2) (subst0_fst v x0 u0 i0 H5 t2 k) (subst0_snd k v t2 x1 i0 H7 x0)))) (H1 
x1 H6)) t4 H4)))))) H3)) (subst0_gen_head k v u0 t3 t4 i0 H2)))))))))))) 
(\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i0: nat).(\lambda 
(H0: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (t2: T).((subst0 i0 v u1 
t2) \to (or4 (eq T u2 t2) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda 
(t: T).(subst0 i0 v t2 t))) (subst0 i0 v u2 t2) (subst0 i0 v t2 
u2)))))).(\lambda (k: K).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H2: 
(subst0 (s k i0) v t2 t3)).(\lambda (H3: ((\forall (t4: T).((subst0 (s k i0) 
v t2 t4) \to (or4 (eq T t3 t4) (ex2 T (\lambda (t: T).(subst0 (s k i0) v t3 
t)) (\lambda (t: T).(subst0 (s k i0) v t4 t))) (subst0 (s k i0) v t3 t4) 
(subst0 (s k i0) v t4 t3)))))).(\lambda (t4: T).(\lambda (H4: (subst0 i0 v 
(THead k u1 t2) t4)).(or3_ind (ex2 T (\lambda (u3: T).(eq T t4 (THead k u3 
t2))) (\lambda (u3: T).(subst0 i0 v u1 u3))) (ex2 T (\lambda (t5: T).(eq T t4 
(THead k u1 t5))) (\lambda (t5: T).(subst0 (s k i0) v t2 t5))) (ex3_2 T T 
(\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i0 v u1 u3))) (\lambda (_: T).(\lambda (t5: 
T).(subst0 (s k i0) v t2 t5)))) (or4 (eq T (THead k u2 t3) t4) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
t4 t))) (subst0 i0 v (THead k u2 t3) t4) (subst0 i0 v t4 (THead k u2 t3))) 
(\lambda (H5: (ex2 T (\lambda (u3: T).(eq T t4 (THead k u3 t2))) (\lambda 
(u3: T).(subst0 i0 v u1 u3)))).(ex2_ind T (\lambda (u3: T).(eq T t4 (THead k 
u3 t2))) (\lambda (u3: T).(subst0 i0 v u1 u3)) (or4 (eq T (THead k u2 t3) t4) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u2 t3) t4) (subst0 i0 v t4 
(THead k u2 t3))) (\lambda (x: T).(\lambda (H6: (eq T t4 (THead k x 
t2))).(\lambda (H7: (subst0 i0 v u1 x)).(eq_ind_r T (THead k x t2) (\lambda 
(t: T).(or4 (eq T (THead k u2 t3) t) (ex2 T (\lambda (t5: T).(subst0 i0 v 
(THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i0 v t t5))) (subst0 i0 v 
(THead k u2 t3) t) (subst0 i0 v t (THead k u2 t3)))) (or4_ind (eq T t3 t3) 
(ex2 T (\lambda (t: T).(subst0 (s k i0) v t3 t)) (\lambda (t: T).(subst0 (s k 
i0) v t3 t))) (subst0 (s k i0) v t3 t3) (subst0 (s k i0) v t3 t3) (or4 (eq T 
(THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) 
(\lambda (_: (eq T t3 t3)).(or4_ind (eq T u2 x) (ex2 T (\lambda (t: 
T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x t))) (subst0 i0 v u2 x) 
(subst0 i0 v x u2) (or4 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k 
x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k 
x t2) (THead k u2 t3))) (\lambda (H9: (eq T u2 x)).(eq_ind_r T x (\lambda (t: 
T).(or4 (eq T (THead k t t3) (THead k x t2)) (ex2 T (\lambda (t5: T).(subst0 
i0 v (THead k t t3) t5)) (\lambda (t5: T).(subst0 i0 v (THead k x t2) t5))) 
(subst0 i0 v (THead k t t3) (THead k x t2)) (subst0 i0 v (THead k x t2) 
(THead k t t3)))) (or4_intro3 (eq T (THead k x t3) (THead k x t2)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k x t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x t2) t))) (subst0 i0 v (THead k x t3) (THead k x t2)) (subst0 i0 v 
(THead k x t2) (THead k x t3)) (subst0_snd k v t3 t2 i0 H2 x)) u2 H9)) 
(\lambda (H9: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v x t)) (or4 (eq T (THead k u2 t3) (THead k x t2)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) (\lambda (x0: T).(\lambda 
(H10: (subst0 i0 v u2 x0)).(\lambda (H11: (subst0 i0 v x x0)).(or4_intro1 (eq 
T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead 
k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) 
(ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t)) (THead k x0 t3) (subst0_fst v x0 u2 i0 H10 
t3 k) (subst0_both v x x0 i0 H11 k t2 t3 H2)))))) H9)) (\lambda (H9: (subst0 
i0 v u2 x)).(or4_intro1 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k 
x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k 
x t2) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 
t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t)) (THead k x t3) 
(subst0_fst v x u2 i0 H9 t3 k) (subst0_snd k v t3 t2 i0 H2 x)))) (\lambda 
(H9: (subst0 i0 v x u2)).(or4_intro3 (eq T (THead k u2 t3) (THead k x t2)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) (subst0_both v x u2 i0 H9 k 
t2 t3 H2))) (H1 x H7))) (\lambda (H8: (ex2 T (\lambda (t: T).(subst0 (s k i0) 
v t3 t)) (\lambda (t: T).(subst0 (s k i0) v t3 t)))).(ex2_ind T (\lambda (t: 
T).(subst0 (s k i0) v t3 t)) (\lambda (t: T).(subst0 (s k i0) v t3 t)) (or4 
(eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 
i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 
t3))) (\lambda (x0: T).(\lambda (_: (subst0 (s k i0) v t3 x0)).(\lambda (_: 
(subst0 (s k i0) v t3 x0)).(or4_ind (eq T u2 x) (ex2 T (\lambda (t: 
T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x t))) (subst0 i0 v u2 x) 
(subst0 i0 v x u2) (or4 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k 
x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k 
x t2) (THead k u2 t3))) (\lambda (H11: (eq T u2 x)).(eq_ind_r T x (\lambda 
(t: T).(or4 (eq T (THead k t t3) (THead k x t2)) (ex2 T (\lambda (t5: 
T).(subst0 i0 v (THead k t t3) t5)) (\lambda (t5: T).(subst0 i0 v (THead k x 
t2) t5))) (subst0 i0 v (THead k t t3) (THead k x t2)) (subst0 i0 v (THead k x 
t2) (THead k t t3)))) (or4_intro3 (eq T (THead k x t3) (THead k x t2)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k x t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x t2) t))) (subst0 i0 v (THead k x t3) (THead k x t2)) (subst0 i0 v 
(THead k x t2) (THead k x t3)) (subst0_snd k v t3 t2 i0 H2 x)) u2 H11)) 
(\lambda (H11: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v x t)) (or4 (eq T (THead k u2 t3) (THead k x t2)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) (\lambda (x1: T).(\lambda 
(H12: (subst0 i0 v u2 x1)).(\lambda (H13: (subst0 i0 v x x1)).(or4_intro1 (eq 
T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead 
k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) 
(ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t)) (THead k x1 t3) (subst0_fst v x1 u2 i0 H12 
t3 k) (subst0_both v x x1 i0 H13 k t2 t3 H2)))))) H11)) (\lambda (H11: 
(subst0 i0 v u2 x)).(or4_intro1 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v 
(THead k x t2) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t)) (THead k 
x t3) (subst0_fst v x u2 i0 H11 t3 k) (subst0_snd k v t3 t2 i0 H2 x)))) 
(\lambda (H11: (subst0 i0 v x u2)).(or4_intro3 (eq T (THead k u2 t3) (THead k 
x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) (subst0_both v x u2 i0 H11 
k t2 t3 H2))) (H1 x H7))))) H8)) (\lambda (_: (subst0 (s k i0) v t3 
t3)).(or4_ind (eq T u2 x) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda 
(t: T).(subst0 i0 v x t))) (subst0 i0 v u2 x) (subst0 i0 v x u2) (or4 (eq T 
(THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) 
(\lambda (H9: (eq T u2 x)).(eq_ind_r T x (\lambda (t: T).(or4 (eq T (THead k 
t t3) (THead k x t2)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k t t3) 
t5)) (\lambda (t5: T).(subst0 i0 v (THead k x t2) t5))) (subst0 i0 v (THead k 
t t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k t t3)))) 
(or4_intro3 (eq T (THead k x t3) (THead k x t2)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k x t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t2) t))) (subst0 i0 v (THead k x t3) (THead k x t2)) (subst0 i0 v (THead k x 
t2) (THead k x t3)) (subst0_snd k v t3 t2 i0 H2 x)) u2 H9)) (\lambda (H9: 
(ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x 
t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 
i0 v x t)) (or4 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x 
t2) (THead k u2 t3))) (\lambda (x0: T).(\lambda (H10: (subst0 i0 v u2 
x0)).(\lambda (H11: (subst0 i0 v x x0)).(or4_intro1 (eq T (THead k u2 t3) 
(THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) 
(THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) (ex_intro2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x t2) t)) (THead k x0 t3) (subst0_fst v x0 u2 i0 H10 t3 k) 
(subst0_both v x x0 i0 H11 k t2 t3 H2)))))) H9)) (\lambda (H9: (subst0 i0 v 
u2 x)).(or4_intro1 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x 
t2) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 
t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t)) (THead k x t3) 
(subst0_fst v x u2 i0 H9 t3 k) (subst0_snd k v t3 t2 i0 H2 x)))) (\lambda 
(H9: (subst0 i0 v x u2)).(or4_intro3 (eq T (THead k u2 t3) (THead k x t2)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) (subst0_both v x u2 i0 H9 k 
t2 t3 H2))) (H1 x H7))) (\lambda (_: (subst0 (s k i0) v t3 t3)).(or4_ind (eq 
T u2 x) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 
v x t))) (subst0 i0 v u2 x) (subst0 i0 v x u2) (or4 (eq T (THead k u2 t3) 
(THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) 
(THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) (\lambda (H9: 
(eq T u2 x)).(eq_ind_r T x (\lambda (t: T).(or4 (eq T (THead k t t3) (THead k 
x t2)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k t t3) t5)) (\lambda (t5: 
T).(subst0 i0 v (THead k x t2) t5))) (subst0 i0 v (THead k t t3) (THead k x 
t2)) (subst0 i0 v (THead k x t2) (THead k t t3)))) (or4_intro3 (eq T (THead k 
x t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k x t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k x t3) 
(THead k x t2)) (subst0 i0 v (THead k x t2) (THead k x t3)) (subst0_snd k v 
t3 t2 i0 H2 x)) u2 H9)) (\lambda (H9: (ex2 T (\lambda (t: T).(subst0 i0 v u2 
t)) (\lambda (t: T).(subst0 i0 v x t)))).(ex2_ind T (\lambda (t: T).(subst0 
i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x t)) (or4 (eq T (THead k u2 t3) 
(THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) 
(THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3))) (\lambda (x0: 
T).(\lambda (H10: (subst0 i0 v u2 x0)).(\lambda (H11: (subst0 i0 v x 
x0)).(or4_intro1 (eq T (THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x 
t2) t))) (subst0 i0 v (THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x 
t2) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 
t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t)) (THead k x0 t3) 
(subst0_fst v x0 u2 i0 H10 t3 k) (subst0_both v x x0 i0 H11 k t2 t3 H2)))))) 
H9)) (\lambda (H9: (subst0 i0 v u2 x)).(or4_intro1 (eq T (THead k u2 t3) 
(THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v (THead k u2 t3) 
(THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) (ex_intro2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x t2) t)) (THead k x t3) (subst0_fst v x u2 i0 H9 t3 k) (subst0_snd 
k v t3 t2 i0 H2 x)))) (\lambda (H9: (subst0 i0 v x u2)).(or4_intro3 (eq T 
(THead k u2 t3) (THead k x t2)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x t2) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x t2)) (subst0 i0 v (THead k x t2) (THead k u2 t3)) 
(subst0_both v x u2 i0 H9 k t2 t3 H2))) (H1 x H7))) (H3 t3 H2)) t4 H6)))) 
H5)) (\lambda (H5: (ex2 T (\lambda (t5: T).(eq T t4 (THead k u1 t5))) 
(\lambda (t5: T).(subst0 (s k i0) v t2 t5)))).(ex2_ind T (\lambda (t5: T).(eq 
T t4 (THead k u1 t5))) (\lambda (t5: T).(subst0 (s k i0) v t2 t5)) (or4 (eq T 
(THead k u2 t3) t4) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u2 t3) t4) (subst0 
i0 v t4 (THead k u2 t3))) (\lambda (x: T).(\lambda (H6: (eq T t4 (THead k u1 
x))).(\lambda (H7: (subst0 (s k i0) v t2 x)).(eq_ind_r T (THead k u1 x) 
(\lambda (t: T).(or4 (eq T (THead k u2 t3) t) (ex2 T (\lambda (t5: T).(subst0 
i0 v (THead k u2 t3) t5)) (\lambda (t5: T).(subst0 i0 v t t5))) (subst0 i0 v 
(THead k u2 t3) t) (subst0 i0 v t (THead k u2 t3)))) (or4_ind (eq T t3 x) 
(ex2 T (\lambda (t: T).(subst0 (s k i0) v t3 t)) (\lambda (t: T).(subst0 (s k 
i0) v x t))) (subst0 (s k i0) v t3 x) (subst0 (s k i0) v x t3) (or4 (eq T 
(THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v 
(THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3))) 
(\lambda (H8: (eq T t3 x)).(eq_ind_r T x (\lambda (t: T).(or4 (eq T (THead k 
u2 t) (THead k u1 x)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k u2 t) 
t5)) (\lambda (t5: T).(subst0 i0 v (THead k u1 x) t5))) (subst0 i0 v (THead k 
u2 t) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t)))) (or4_ind 
(eq T u2 u2) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v u2 t))) (subst0 i0 v u2 u2) (subst0 i0 v u2 u2) (or4 (eq T 
(THead k u2 x) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 x) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v 
(THead k u2 x) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 x))) 
(\lambda (_: (eq T u2 u2)).(or4_intro3 (eq T (THead k u2 x) (THead k u1 x)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 x) t)) (\lambda (t: 
T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 x) (THead k u1 
x)) (subst0 i0 v (THead k u1 x) (THead k u2 x)) (subst0_fst v u2 u1 i0 H0 x 
k))) (\lambda (H9: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v u2 t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v u2 t)) (or4 (eq T (THead k u2 x) (THead k u1 x)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 x) t)) (\lambda (t: 
T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 x) (THead k u1 
x)) (subst0 i0 v (THead k u1 x) (THead k u2 x))) (\lambda (x0: T).(\lambda 
(_: (subst0 i0 v u2 x0)).(\lambda (_: (subst0 i0 v u2 x0)).(or4_intro3 (eq T 
(THead k u2 x) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 x) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v 
(THead k u2 x) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 x)) 
(subst0_fst v u2 u1 i0 H0 x k))))) H9)) (\lambda (_: (subst0 i0 v u2 
u2)).(or4_intro3 (eq T (THead k u2 x) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 x) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 x) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 x)) (subst0_fst v u2 u1 i0 H0 x k))) (\lambda (_: (subst0 i0 v 
u2 u2)).(or4_intro3 (eq T (THead k u2 x) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 x) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 x) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 x)) (subst0_fst v u2 u1 i0 H0 x k))) (H1 u2 H0)) t3 H8)) 
(\lambda (H8: (ex2 T (\lambda (t: T).(subst0 (s k i0) v t3 t)) (\lambda (t: 
T).(subst0 (s k i0) v x t)))).(ex2_ind T (\lambda (t: T).(subst0 (s k i0) v 
t3 t)) (\lambda (t: T).(subst0 (s k i0) v x t)) (or4 (eq T (THead k u2 t3) 
(THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) 
(THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3))) (\lambda (x0: 
T).(\lambda (H9: (subst0 (s k i0) v t3 x0)).(\lambda (H10: (subst0 (s k i0) v 
x x0)).(or4_ind (eq T u2 u2) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v u2 t))) (subst0 i0 v u2 u2) (subst0 i0 v u2 u2) 
(or4 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 
v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) 
(subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) 
(THead k u2 t3))) (\lambda (_: (eq T u2 u2)).(or4_intro1 (eq T (THead k u2 
t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) 
(THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3)) (ex_intro2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u1 x) t)) (THead k u2 x0) (subst0_snd k v x0 t3 i0 H9 u2) 
(subst0_both v u1 u2 i0 H0 k x x0 H10)))) (\lambda (H11: (ex2 T (\lambda (t: 
T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v u2 t)))).(ex2_ind T 
(\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v u2 t)) (or4 
(eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 
i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 
t3))) (\lambda (x1: T).(\lambda (_: (subst0 i0 v u2 x1)).(\lambda (_: (subst0 
i0 v u2 x1)).(or4_intro1 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v 
(THead k u1 x) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t)) (THead k 
u2 x0) (subst0_snd k v x0 t3 i0 H9 u2) (subst0_both v u1 u2 i0 H0 k x x0 
H10)))))) H11)) (\lambda (_: (subst0 i0 v u2 u2)).(or4_intro1 (eq T (THead k 
u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) 
t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 
t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3)) (ex_intro2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u1 x) t)) (THead k u2 x0) (subst0_snd k v x0 t3 i0 H9 u2) 
(subst0_both v u1 u2 i0 H0 k x x0 H10)))) (\lambda (_: (subst0 i0 v u2 
u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) 
t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t)) (THead k u2 x0) 
(subst0_snd k v x0 t3 i0 H9 u2) (subst0_both v u1 u2 i0 H0 k x x0 H10)))) (H1 
u2 H0))))) H8)) (\lambda (H8: (subst0 (s k i0) v t3 x)).(or4_ind (eq T u2 u2) 
(ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v u2 
t))) (subst0 i0 v u2 u2) (subst0 i0 v u2 u2) (or4 (eq T (THead k u2 t3) 
(THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) 
(THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3))) (\lambda (_: 
(eq T u2 u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v 
(THead k u1 x) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t)) (THead k 
u2 x) (subst0_snd k v x t3 i0 H8 u2) (subst0_fst v u2 u1 i0 H0 x k)))) 
(\lambda (H9: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v u2 t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v u2 t)) (or4 (eq T (THead k u2 t3) (THead k u1 
x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 
x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3))) (\lambda (x0: T).(\lambda 
(_: (subst0 i0 v u2 x0)).(\lambda (_: (subst0 i0 v u2 x0)).(or4_intro1 (eq T 
(THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v 
(THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3)) 
(ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k u1 x) t)) (THead k u2 x) (subst0_snd k v x t3 i0 H8 
u2) (subst0_fst v u2 u1 i0 H0 x k)))))) H9)) (\lambda (_: (subst0 i0 v u2 
u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) 
t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t)) (THead k u2 x) 
(subst0_snd k v x t3 i0 H8 u2) (subst0_fst v u2 u1 i0 H0 x k)))) (\lambda (_: 
(subst0 i0 v u2 u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v 
(THead k u1 x) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t)) (THead k 
u2 x) (subst0_snd k v x t3 i0 H8 u2) (subst0_fst v u2 u1 i0 H0 x k)))) (H1 u2 
H0))) (\lambda (H8: (subst0 (s k i0) v x t3)).(or4_ind (eq T u2 u2) (ex2 T 
(\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v u2 t))) 
(subst0 i0 v u2 u2) (subst0 i0 v u2 u2) (or4 (eq T (THead k u2 t3) (THead k 
u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 
x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3))) (\lambda (_: (eq T u2 
u2)).(or4_intro3 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t3)) (subst0_both v u1 u2 i0 H0 k x t3 H8))) (\lambda (H9: 
(ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v u2 
t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 
i0 v u2 t)) (or4 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t3))) (\lambda (x0: T).(\lambda (_: (subst0 i0 v u2 
x0)).(\lambda (_: (subst0 i0 v u2 x0)).(or4_intro3 (eq T (THead k u2 t3) 
(THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 i0 v (THead k u2 t3) 
(THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 t3)) (subst0_both v 
u1 u2 i0 H0 k x t3 H8))))) H9)) (\lambda (_: (subst0 i0 v u2 u2)).(or4_intro3 
(eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 x) t))) (subst0 
i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 x) (THead k u2 
t3)) (subst0_both v u1 u2 i0 H0 k x t3 H8))) (\lambda (_: (subst0 i0 v u2 
u2)).(or4_intro3 (eq T (THead k u2 t3) (THead k u1 x)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k u1 
x) t))) (subst0 i0 v (THead k u2 t3) (THead k u1 x)) (subst0 i0 v (THead k u1 
x) (THead k u2 t3)) (subst0_both v u1 u2 i0 H0 k x t3 H8))) (H1 u2 H0))) (H3 
x H7)) t4 H6)))) H5)) (\lambda (H5: (ex3_2 T T (\lambda (u3: T).(\lambda (t5: 
T).(eq T t4 (THead k u3 t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v 
u1 u3))) (\lambda (_: T).(\lambda (t5: T).(subst0 (s k i0) v t2 
t5))))).(ex3_2_ind T T (\lambda (u3: T).(\lambda (t5: T).(eq T t4 (THead k u3 
t5)))) (\lambda (u3: T).(\lambda (_: T).(subst0 i0 v u1 u3))) (\lambda (_: 
T).(\lambda (t5: T).(subst0 (s k i0) v t2 t5))) (or4 (eq T (THead k u2 t3) 
t4) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v t4 t))) (subst0 i0 v (THead k u2 t3) t4) (subst0 i0 v t4 
(THead k u2 t3))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H6: (eq T t4 
(THead k x0 x1))).(\lambda (H7: (subst0 i0 v u1 x0)).(\lambda (H8: (subst0 (s 
k i0) v t2 x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t: T).(or4 (eq T (THead 
k u2 t3) t) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k u2 t3) t5)) 
(\lambda (t5: T).(subst0 i0 v t t5))) (subst0 i0 v (THead k u2 t3) t) (subst0 
i0 v t (THead k u2 t3)))) (or4_ind (eq T t3 x1) (ex2 T (\lambda (t: 
T).(subst0 (s k i0) v t3 t)) (\lambda (t: T).(subst0 (s k i0) v x1 t))) 
(subst0 (s k i0) v t3 x1) (subst0 (s k i0) v x1 t3) (or4 (eq T (THead k u2 
t3) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 
t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3))) (\lambda 
(H9: (eq T t3 x1)).(eq_ind_r T x1 (\lambda (t: T).(or4 (eq T (THead k u2 t) 
(THead k x0 x1)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k u2 t) t5)) 
(\lambda (t5: T).(subst0 i0 v (THead k x0 x1) t5))) (subst0 i0 v (THead k u2 
t) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t)))) (or4_ind 
(eq T u2 x0) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x0 t))) (subst0 i0 v u2 x0) (subst0 i0 v x0 u2) (or4 (eq T 
(THead k u2 x1) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 x1) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v 
(THead k u2 x1) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 
x1))) (\lambda (H10: (eq T u2 x0)).(eq_ind_r T x0 (\lambda (t: T).(or4 (eq T 
(THead k t x1) (THead k x0 x1)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k 
t x1) t5)) (\lambda (t5: T).(subst0 i0 v (THead k x0 x1) t5))) (subst0 i0 v 
(THead k t x1) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k t 
x1)))) (or4_intro0 (eq T (THead k x0 x1) (THead k x0 x1)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t))) (subst0 i0 v (THead k x0 x1) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k x0 x1)) (refl_equal T (THead k x0 x1))) u2 H10)) (\lambda 
(H10: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v 
x0 t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x0 t)) (or4 (eq T (THead k u2 x1) (THead k x0 x1)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 x1) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x0 x1) t))) (subst0 i0 v (THead k u2 x1) (THead k x0 x1)) (subst0 i0 
v (THead k x0 x1) (THead k u2 x1))) (\lambda (x: T).(\lambda (H11: (subst0 i0 
v u2 x)).(\lambda (H12: (subst0 i0 v x0 x)).(or4_intro1 (eq T (THead k u2 x1) 
(THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 x1) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 
x1) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 x1)) (ex_intro2 
T (\lambda (t: T).(subst0 i0 v (THead k u2 x1) t)) (\lambda (t: T).(subst0 i0 
v (THead k x0 x1) t)) (THead k x x1) (subst0_fst v x u2 i0 H11 x1 k) 
(subst0_fst v x x0 i0 H12 x1 k)))))) H10)) (\lambda (H10: (subst0 i0 v u2 
x0)).(or4_intro2 (eq T (THead k u2 x1) (THead k x0 x1)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 x1) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t))) (subst0 i0 v (THead k u2 x1) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k u2 x1)) (subst0_fst v x0 u2 i0 H10 x1 k))) (\lambda (H10: 
(subst0 i0 v x0 u2)).(or4_intro3 (eq T (THead k u2 x1) (THead k x0 x1)) (ex2 
T (\lambda (t: T).(subst0 i0 v (THead k u2 x1) t)) (\lambda (t: T).(subst0 i0 
v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 x1) (THead k x0 x1)) (subst0 
i0 v (THead k x0 x1) (THead k u2 x1)) (subst0_fst v u2 x0 i0 H10 x1 k))) (H1 
x0 H7)) t3 H9)) (\lambda (H9: (ex2 T (\lambda (t: T).(subst0 (s k i0) v t3 
t)) (\lambda (t: T).(subst0 (s k i0) v x1 t)))).(ex2_ind T (\lambda (t: 
T).(subst0 (s k i0) v t3 t)) (\lambda (t: T).(subst0 (s k i0) v x1 t)) (or4 
(eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v 
(THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 
i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k 
u2 t3))) (\lambda (x: T).(\lambda (H10: (subst0 (s k i0) v t3 x)).(\lambda 
(H11: (subst0 (s k i0) v x1 x)).(or4_ind (eq T u2 x0) (ex2 T (\lambda (t: 
T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x0 t))) (subst0 i0 v u2 
x0) (subst0 i0 v x0 u2) (or4 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 
v (THead k x0 x1) (THead k u2 t3))) (\lambda (H12: (eq T u2 x0)).(eq_ind_r T 
x0 (\lambda (t: T).(or4 (eq T (THead k t t3) (THead k x0 x1)) (ex2 T (\lambda 
(t5: T).(subst0 i0 v (THead k t t3) t5)) (\lambda (t5: T).(subst0 i0 v (THead 
k x0 x1) t5))) (subst0 i0 v (THead k t t3) (THead k x0 x1)) (subst0 i0 v 
(THead k x0 x1) (THead k t t3)))) (or4_intro1 (eq T (THead k x0 t3) (THead k 
x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k x0 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k x0 t3) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k x0 t3)) (ex_intro2 T (\lambda (t: 
T).(subst0 i0 v (THead k x0 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t)) (THead k x0 x) (subst0_snd k v x t3 i0 H10 x0) (subst0_snd k v x x1 
i0 H11 x0))) u2 H12)) (\lambda (H12: (ex2 T (\lambda (t: T).(subst0 i0 v u2 
t)) (\lambda (t: T).(subst0 i0 v x0 t)))).(ex2_ind T (\lambda (t: T).(subst0 
i0 v u2 t)) (\lambda (t: T).(subst0 i0 v x0 t)) (or4 (eq T (THead k u2 t3) 
(THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 
t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3))) (\lambda 
(x2: T).(\lambda (H13: (subst0 i0 v u2 x2)).(\lambda (H14: (subst0 i0 v x0 
x2)).(or4_intro1 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 
t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t)) (THead k x2 x) 
(subst0_both v u2 x2 i0 H13 k t3 x H10) (subst0_both v x0 x2 i0 H14 k x1 x 
H11)))))) H12)) (\lambda (H12: (subst0 i0 v u2 x0)).(or4_intro1 (eq T (THead 
k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) 
t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k 
u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3)) 
(ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t)) (THead k x0 x) (subst0_both v u2 x0 i0 
H12 k t3 x H10) (subst0_snd k v x x1 i0 H11 x0)))) (\lambda (H12: (subst0 i0 
v x0 u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda 
(t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k 
x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead 
k x0 x1) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k 
u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t)) (THead k u2 x) 
(subst0_snd k v x t3 i0 H10 u2) (subst0_both v x0 u2 i0 H12 k x1 x H11)))) 
(H1 x0 H7))))) H9)) (\lambda (H9: (subst0 (s k i0) v t3 x1)).(or4_ind (eq T 
u2 x0) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 
v x0 t))) (subst0 i0 v u2 x0) (subst0 i0 v x0 u2) (or4 (eq T (THead k u2 t3) 
(THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 
t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3))) (\lambda 
(H10: (eq T u2 x0)).(eq_ind_r T x0 (\lambda (t: T).(or4 (eq T (THead k t t3) 
(THead k x0 x1)) (ex2 T (\lambda (t5: T).(subst0 i0 v (THead k t t3) t5)) 
(\lambda (t5: T).(subst0 i0 v (THead k x0 x1) t5))) (subst0 i0 v (THead k t 
t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k t t3)))) 
(or4_intro2 (eq T (THead k x0 t3) (THead k x0 x1)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k x0 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t))) (subst0 i0 v (THead k x0 t3) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k x0 t3)) (subst0_snd k v x1 t3 i0 H9 x0)) u2 H10)) (\lambda 
(H10: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: T).(subst0 i0 v 
x0 t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x0 t)) (or4 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 
v (THead k x0 x1) (THead k u2 t3))) (\lambda (x: T).(\lambda (H11: (subst0 i0 
v u2 x)).(\lambda (H12: (subst0 i0 v x0 x)).(or4_intro1 (eq T (THead k u2 t3) 
(THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) 
(\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 
t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3)) (ex_intro2 
T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 
v (THead k x0 x1) t)) (THead k x x1) (subst0_both v u2 x i0 H11 k t3 x1 H9) 
(subst0_fst v x x0 i0 H12 x1 k)))))) H10)) (\lambda (H10: (subst0 i0 v u2 
x0)).(or4_intro2 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k 
x0 x1) (THead k u2 t3)) (subst0_both v u2 x0 i0 H10 k t3 x1 H9))) (\lambda 
(H10: (subst0 i0 v x0 u2)).(or4_intro1 (eq T (THead k u2 t3) (THead k x0 x1)) 
(ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3)) (ex_intro2 T (\lambda (t: 
T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 
x1) t)) (THead k u2 x1) (subst0_snd k v x1 t3 i0 H9 u2) (subst0_fst v u2 x0 
i0 H10 x1 k)))) (H1 x0 H7))) (\lambda (H9: (subst0 (s k i0) v x1 
t3)).(or4_ind (eq T u2 x0) (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v x0 t))) (subst0 i0 v u2 x0) (subst0 i0 v x0 u2) 
(or4 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 
v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) 
(subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) 
(THead k u2 t3))) (\lambda (H10: (eq T u2 x0)).(eq_ind_r T x0 (\lambda (t: 
T).(or4 (eq T (THead k t t3) (THead k x0 x1)) (ex2 T (\lambda (t5: T).(subst0 
i0 v (THead k t t3) t5)) (\lambda (t5: T).(subst0 i0 v (THead k x0 x1) t5))) 
(subst0 i0 v (THead k t t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) 
(THead k t t3)))) (or4_intro3 (eq T (THead k x0 t3) (THead k x0 x1)) (ex2 T 
(\lambda (t: T).(subst0 i0 v (THead k x0 t3) t)) (\lambda (t: T).(subst0 i0 v 
(THead k x0 x1) t))) (subst0 i0 v (THead k x0 t3) (THead k x0 x1)) (subst0 i0 
v (THead k x0 x1) (THead k x0 t3)) (subst0_snd k v t3 x1 i0 H9 x0)) u2 H10)) 
(\lambda (H10: (ex2 T (\lambda (t: T).(subst0 i0 v u2 t)) (\lambda (t: 
T).(subst0 i0 v x0 t)))).(ex2_ind T (\lambda (t: T).(subst0 i0 v u2 t)) 
(\lambda (t: T).(subst0 i0 v x0 t)) (or4 (eq T (THead k u2 t3) (THead k x0 
x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: 
T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 
x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3))) (\lambda (x: T).(\lambda 
(H11: (subst0 i0 v u2 x)).(\lambda (H12: (subst0 i0 v x0 x)).(or4_intro1 (eq 
T (THead k u2 t3) (THead k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead 
k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v 
(THead k u2 t3) (THead k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 
t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda 
(t: T).(subst0 i0 v (THead k x0 x1) t)) (THead k x t3) (subst0_fst v x u2 i0 
H11 t3 k) (subst0_both v x0 x i0 H12 k x1 t3 H9)))))) H10)) (\lambda (H10: 
(subst0 i0 v u2 x0)).(or4_intro1 (eq T (THead k u2 t3) (THead k x0 x1)) (ex2 
T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 
v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead k x0 x1)) (subst0 
i0 v (THead k x0 x1) (THead k u2 t3)) (ex_intro2 T (\lambda (t: T).(subst0 i0 
v (THead k u2 t3) t)) (\lambda (t: T).(subst0 i0 v (THead k x0 x1) t)) (THead 
k x0 t3) (subst0_fst v x0 u2 i0 H10 t3 k) (subst0_snd k v t3 x1 i0 H9 x0)))) 
(\lambda (H10: (subst0 i0 v x0 u2)).(or4_intro3 (eq T (THead k u2 t3) (THead 
k x0 x1)) (ex2 T (\lambda (t: T).(subst0 i0 v (THead k u2 t3) t)) (\lambda 
(t: T).(subst0 i0 v (THead k x0 x1) t))) (subst0 i0 v (THead k u2 t3) (THead 
k x0 x1)) (subst0 i0 v (THead k x0 x1) (THead k u2 t3)) (subst0_both v x0 u2 
i0 H10 k x1 t3 H9))) (H1 x0 H7))) (H3 x1 H8)) t4 H6)))))) H5)) 
(subst0_gen_head k v u1 t2 t4 i0 H4))))))))))))))) i u t0 t1 H))))).
(* COMMENTS
Initial nodes: 25595
END *)

theorem subst0_confluence_lift:
 \forall (t0: T).(\forall (t1: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t0 (lift (S O) i t1)) \to (\forall (t2: T).((subst0 i u t0 (lift (S O) i 
t2)) \to (eq T t1 t2)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t0 (lift (S O) i t1))).(\lambda (t2: T).(\lambda (H0: (subst0 
i u t0 (lift (S O) i t2))).(or4_ind (eq T (lift (S O) i t2) (lift (S O) i 
t1)) (ex2 T (\lambda (t: T).(subst0 i u (lift (S O) i t2) t)) (\lambda (t: 
T).(subst0 i u (lift (S O) i t1) t))) (subst0 i u (lift (S O) i t2) (lift (S 
O) i t1)) (subst0 i u (lift (S O) i t1) (lift (S O) i t2)) (eq T t1 t2) 
(\lambda (H1: (eq T (lift (S O) i t2) (lift (S O) i t1))).(let H2 \def 
(sym_eq T (lift (S O) i t2) (lift (S O) i t1) H1) in (lift_inj t1 t2 (S O) i 
H2))) (\lambda (H1: (ex2 T (\lambda (t: T).(subst0 i u (lift (S O) i t2) t)) 
(\lambda (t: T).(subst0 i u (lift (S O) i t1) t)))).(ex2_ind T (\lambda (t: 
T).(subst0 i u (lift (S O) i t2) t)) (\lambda (t: T).(subst0 i u (lift (S O) 
i t1) t)) (eq T t1 t2) (\lambda (x: T).(\lambda (_: (subst0 i u (lift (S O) i 
t2) x)).(\lambda (H3: (subst0 i u (lift (S O) i t1) 
x)).(subst0_gen_lift_false t1 u x (S O) i i (le_n i) (eq_ind_r nat (plus (S 
O) i) (\lambda (n: nat).(lt i n)) (le_n (plus (S O) i)) (plus i (S O)) 
(plus_sym i (S O))) H3 (eq T t1 t2))))) H1)) (\lambda (H1: (subst0 i u (lift 
(S O) i t2) (lift (S O) i t1))).(subst0_gen_lift_false t2 u (lift (S O) i t1) 
(S O) i i (le_n i) (eq_ind_r nat (plus (S O) i) (\lambda (n: nat).(lt i n)) 
(le_n (plus (S O) i)) (plus i (S O)) (plus_sym i (S O))) H1 (eq T t1 t2))) 
(\lambda (H1: (subst0 i u (lift (S O) i t1) (lift (S O) i 
t2))).(subst0_gen_lift_false t1 u (lift (S O) i t2) (S O) i i (le_n i) 
(eq_ind_r nat (plus (S O) i) (\lambda (n: nat).(lt i n)) (le_n (plus (S O) 
i)) (plus i (S O)) (plus_sym i (S O))) H1 (eq T t1 t2))) 
(subst0_confluence_eq t0 (lift (S O) i t2) u i H0 (lift (S O) i t1) H)))))))).
(* COMMENTS
Initial nodes: 703
END *)

