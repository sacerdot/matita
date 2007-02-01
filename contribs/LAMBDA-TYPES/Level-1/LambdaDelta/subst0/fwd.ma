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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/subst0/fwd".

include "subst0/defs.ma".

include "lift/props.ma".

theorem subst0_inv_coq:
 \forall (i: nat).(\forall (v: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(P: ((nat \to (T \to (T \to (T \to Prop)))))).((((subst0 i v t1 t2) \to 
(\forall (v0: T).(\forall (i0: nat).((eq nat i0 i) \to ((eq T v0 v) \to ((eq 
T (TLRef i0) t1) \to ((eq T (lift (S i0) O v0) t2) \to (P i v t1 t2))))))))) 
\to ((((subst0 i v t1 t2) \to (\forall (v0: T).(\forall (u2: T).(\forall (u1: 
T).(\forall (i0: nat).(\forall (t: T).(\forall (k: K).((eq nat i0 i) \to ((eq 
T v0 v) \to ((eq T (THead k u1 t) t1) \to ((eq T (THead k u2 t) t2) \to 
((subst0 i0 v0 u1 u2) \to (P i v t1 t2)))))))))))))) \to ((((subst0 i v t1 
t2) \to (\forall (k: K).(\forall (v0: T).(\forall (t0: T).(\forall (t3: 
T).(\forall (i0: nat).(\forall (u: T).((eq nat i0 i) \to ((eq T v0 v) \to 
((eq T (THead k u t3) t1) \to ((eq T (THead k u t0) t2) \to ((subst0 (s k i0) 
v0 t3 t0) \to (P i v t1 t2)))))))))))))) \to ((((subst0 i v t1 t2) \to 
(\forall (v0: T).(\forall (u1: T).(\forall (u2: T).(\forall (i0: 
nat).(\forall (k: K).(\forall (t0: T).(\forall (t3: T).((eq nat i0 i) \to 
((eq T v0 v) \to ((eq T (THead k u1 t0) t1) \to ((eq T (THead k u2 t3) t2) 
\to ((subst0 i0 v0 u1 u2) \to ((subst0 (s k i0) v0 t0 t3) \to (P i v t1 
t2)))))))))))))))) \to ((subst0 i v t1 t2) \to (P i v t1 t2))))))))))
\def
 \lambda (i: nat).(\lambda (v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(P: ((nat \to (T \to (T \to (T \to Prop)))))).(\lambda (H: (((subst0 i v t1 
t2) \to (\forall (v0: T).(\forall (i0: nat).((eq nat i0 i) \to ((eq T v0 v) 
\to ((eq T (TLRef i0) t1) \to ((eq T (lift (S i0) O v0) t2) \to (P i v t1 
t2)))))))))).(\lambda (H0: (((subst0 i v t1 t2) \to (\forall (v0: T).(\forall 
(u2: T).(\forall (u1: T).(\forall (i0: nat).(\forall (t: T).(\forall (k: 
K).((eq nat i0 i) \to ((eq T v0 v) \to ((eq T (THead k u1 t) t1) \to ((eq T 
(THead k u2 t) t2) \to ((subst0 i0 v0 u1 u2) \to (P i v t1 
t2))))))))))))))).(\lambda (H1: (((subst0 i v t1 t2) \to (\forall (k: 
K).(\forall (v0: T).(\forall (t0: T).(\forall (t3: T).(\forall (i0: 
nat).(\forall (u: T).((eq nat i0 i) \to ((eq T v0 v) \to ((eq T (THead k u 
t3) t1) \to ((eq T (THead k u t0) t2) \to ((subst0 (s k i0) v0 t3 t0) \to (P 
i v t1 t2))))))))))))))).(\lambda (H2: (((subst0 i v t1 t2) \to (\forall (v0: 
T).(\forall (u1: T).(\forall (u2: T).(\forall (i0: nat).(\forall (k: 
K).(\forall (t0: T).(\forall (t3: T).((eq nat i0 i) \to ((eq T v0 v) \to ((eq 
T (THead k u1 t0) t1) \to ((eq T (THead k u2 t3) t2) \to ((subst0 i0 v0 u1 
u2) \to ((subst0 (s k i0) v0 t0 t3) \to (P i v t1 
t2))))))))))))))))).(\lambda (H3: (subst0 i v t1 t2)).(let H4 \def (match H3 
in subst0 return (\lambda (n: nat).(\lambda (t: T).(\lambda (t0: T).(\lambda 
(t3: T).(\lambda (_: (subst0 n t t0 t3)).((eq nat n i) \to ((eq T t v) \to 
((eq T t0 t1) \to ((eq T t3 t2) \to (P i v t1 t2)))))))))) with [(subst0_lref 
v0 i0) \Rightarrow (\lambda (H4: (eq nat i0 i)).(\lambda (H5: (eq T v0 
v)).(\lambda (H6: (eq T (TLRef i0) t1)).(\lambda (H7: (eq T (lift (S i0) O 
v0) t2)).(H H3 v0 i0 H4 H5 H6 H7))))) | (subst0_fst v0 u2 u1 i0 H4 t k) 
\Rightarrow (\lambda (H5: (eq nat i0 i)).(\lambda (H6: (eq T v0 v)).(\lambda 
(H7: (eq T (THead k u1 t) t1)).(\lambda (H8: (eq T (THead k u2 t) t2)).(H0 H3 
v0 u2 u1 i0 t k H5 H6 H7 H8 H4))))) | (subst0_snd k v0 t0 t3 i0 H4 u) 
\Rightarrow (\lambda (H5: (eq nat i0 i)).(\lambda (H6: (eq T v0 v)).(\lambda 
(H7: (eq T (THead k u t3) t1)).(\lambda (H8: (eq T (THead k u t0) t2)).(H1 H3 
k v0 t0 t3 i0 u H5 H6 H7 H8 H4))))) | (subst0_both v0 u1 u2 i0 H4 k t0 t3 H5) 
\Rightarrow (\lambda (H6: (eq nat i0 i)).(\lambda (H7: (eq T v0 v)).(\lambda 
(H8: (eq T (THead k u1 t0) t1)).(\lambda (H9: (eq T (THead k u2 t3) t2)).(H2 
H3 v0 u1 u2 i0 k t0 t3 H6 H7 H8 H9 H4 H5)))))]) in (H4 (refl_equal nat i) 
(refl_equal T v) (refl_equal T t1) (refl_equal T t2)))))))))))).

theorem subst0_gen_sort:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 
i v (TSort n) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst0 i v (TSort n) x)).(\lambda (P: Prop).(subst0_inv_coq i v (TSort 
n) x (\lambda (_: nat).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).P)))) 
(\lambda (H0: (subst0 i v (TSort n) x)).(\lambda (v0: T).(\lambda (i0: 
nat).(\lambda (H1: (eq nat i0 i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: 
(eq T (TLRef i0) (TSort n))).(\lambda (H4: (eq T (lift (S i0) O v0) x)).(let 
H5 \def (eq_ind nat i0 (\lambda (n0: nat).(eq T (lift (S n0) O v0) x)) H4 i 
H1) in (let H6 \def (eq_ind nat i0 (\lambda (n0: nat).(eq T (TLRef n0) (TSort 
n))) H3 i H1) in (let H7 \def (eq_ind T v0 (\lambda (t: T).(eq T (lift (S i) 
O t) x)) H5 v H2) in (let H8 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v 
(TSort n) t)) H0 (lift (S i) O v) H7) in (let H9 \def (eq_ind_r T x (\lambda 
(t: T).(subst0 i v (TSort n) t)) H (lift (S i) O v) H7) in (let H10 \def 
(eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (TSort n) H6) in (False_ind P 
H10)))))))))))))) (\lambda (H0: (subst0 i v (TSort n) x)).(\lambda (v0: 
T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i0: nat).(\lambda (t: 
T).(\lambda (k: K).(\lambda (H1: (eq nat i0 i)).(\lambda (H2: (eq T v0 
v)).(\lambda (H3: (eq T (THead k u1 t) (TSort n))).(\lambda (H4: (eq T (THead 
k u2 t) x)).(\lambda (H5: (subst0 i0 v0 u1 u2)).(let H6 \def (eq_ind nat i0 
(\lambda (n0: nat).(subst0 n0 v0 u1 u2)) H5 i H1) in (let H7 \def (eq_ind T 
v0 (\lambda (t0: T).(subst0 i t0 u1 u2)) H6 v H2) in (let H8 \def (eq_ind_r T 
x (\lambda (t0: T).(subst0 i v (TSort n) t0)) H0 (THead k u2 t) H4) in (let 
H9 \def (eq_ind_r T x (\lambda (t0: T).(subst0 i v (TSort n) t0)) H (THead k 
u2 t) H4) in (let H10 \def (eq_ind T (THead k u1 t) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H3) in (False_ind P H10)))))))))))))))))) (\lambda (H0: (subst0 i v (TSort n) 
x)).(\lambda (k: K).(\lambda (v0: T).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (i0: nat).(\lambda (u: T).(\lambda (H1: (eq nat i0 i)).(\lambda 
(H2: (eq T v0 v)).(\lambda (H3: (eq T (THead k u t3) (TSort n))).(\lambda 
(H4: (eq T (THead k u t0) x)).(\lambda (H5: (subst0 (s k i0) v0 t3 t0)).(let 
H6 \def (eq_ind nat i0 (\lambda (n0: nat).(subst0 (s k n0) v0 t3 t0)) H5 i 
H1) in (let H7 \def (eq_ind T v0 (\lambda (t: T).(subst0 (s k i) t t3 t0)) H6 
v H2) in (let H8 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (TSort n) t)) 
H0 (THead k u t0) H4) in (let H9 \def (eq_ind_r T x (\lambda (t: T).(subst0 i 
v (TSort n) t)) H (THead k u t0) H4) in (let H10 \def (eq_ind T (THead k u 
t3) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TSort n) H3) in (False_ind P H10)))))))))))))))))) 
(\lambda (H0: (subst0 i v (TSort n) x)).(\lambda (v0: T).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (i0: nat).(\lambda (k: K).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H2: (eq nat i0 i)).(\lambda (H3: (eq T v0 
v)).(\lambda (H4: (eq T (THead k u1 t0) (TSort n))).(\lambda (H5: (eq T 
(THead k u2 t3) x)).(\lambda (H1: (subst0 i0 v0 u1 u2)).(\lambda (H6: (subst0 
(s k i0) v0 t0 t3)).(let H7 \def (eq_ind nat i0 (\lambda (n0: nat).(subst0 (s 
k n0) v0 t0 t3)) H6 i H2) in (let H8 \def (eq_ind nat i0 (\lambda (n0: 
nat).(subst0 n0 v0 u1 u2)) H1 i H2) in (let H9 \def (eq_ind T v0 (\lambda (t: 
T).(subst0 (s k i) t t0 t3)) H7 v H3) in (let H10 \def (eq_ind T v0 (\lambda 
(t: T).(subst0 i t u1 u2)) H8 v H3) in (let H11 \def (eq_ind_r T x (\lambda 
(t: T).(subst0 i v (TSort n) t)) H0 (THead k u2 t3) H5) in (let H12 \def 
(eq_ind_r T x (\lambda (t: T).(subst0 i v (TSort n) t)) H (THead k u2 t3) H5) 
in (let H13 \def (eq_ind T (THead k u1 t0) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H4) in 
(False_ind P H13)))))))))))))))))))))) H)))))).

theorem subst0_gen_lref:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst0 
i v (TLRef n) x) \to (land (eq nat n i) (eq T x (lift (S n) O v)))))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst0 i v (TLRef n) x)).(subst0_inv_coq i v (TLRef n) x (\lambda (n0: 
nat).(\lambda (t: T).(\lambda (_: T).(\lambda (t1: T).(land (eq nat n n0) (eq 
T t1 (lift (S n) O t))))))) (\lambda (H0: (subst0 i v (TLRef n) x)).(\lambda 
(v0: T).(\lambda (i0: nat).(\lambda (H1: (eq nat i0 i)).(\lambda (H2: (eq T 
v0 v)).(\lambda (H3: (eq T (TLRef i0) (TLRef n))).(\lambda (H4: (eq T (lift 
(S i0) O v0) x)).(let H5 \def (eq_ind nat i0 (\lambda (n0: nat).(eq T (lift 
(S n0) O v0) x)) H4 i H1) in (let H6 \def (eq_ind nat i0 (\lambda (n0: 
nat).(eq T (TLRef n0) (TLRef n))) H3 i H1) in (let H7 \def (eq_ind T v0 
(\lambda (t: T).(eq T (lift (S i) O t) x)) H5 v H2) in (let H8 \def (eq_ind_r 
T x (\lambda (t: T).(subst0 i v (TLRef n) t)) H0 (lift (S i) O v) H7) in (let 
H9 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (TLRef n) t)) H (lift (S i) 
O v) H7) in (eq_ind T (lift (S i) O v) (\lambda (t: T).(land (eq nat n i) (eq 
T t (lift (S n) O v)))) (let H10 \def (f_equal T nat (\lambda (e: T).(match e 
in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef n) H6) in 
(let H11 \def (eq_ind_r nat n (\lambda (n0: nat).(subst0 i v (TLRef n0) (lift 
(S i) O v))) H8 i H10) in (let H12 \def (eq_ind_r nat n (\lambda (n0: 
nat).(subst0 i v (TLRef n0) (lift (S i) O v))) H9 i H10) in (eq_ind nat i 
(\lambda (n0: nat).(land (eq nat n0 i) (eq T (lift (S i) O v) (lift (S n0) O 
v)))) (conj (eq nat i i) (eq T (lift (S i) O v) (lift (S i) O v)) (refl_equal 
nat i) (refl_equal T (lift (S i) O v))) n H10)))) x H7))))))))))))) (\lambda 
(H0: (subst0 i v (TLRef n) x)).(\lambda (v0: T).(\lambda (u2: T).(\lambda 
(u1: T).(\lambda (i0: nat).(\lambda (t: T).(\lambda (k: K).(\lambda (H1: (eq 
nat i0 i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: (eq T (THead k u1 t) 
(TLRef n))).(\lambda (H4: (eq T (THead k u2 t) x)).(\lambda (H5: (subst0 i0 
v0 u1 u2)).(let H6 \def (eq_ind nat i0 (\lambda (n0: nat).(subst0 n0 v0 u1 
u2)) H5 i H1) in (let H7 \def (eq_ind T v0 (\lambda (t0: T).(subst0 i t0 u1 
u2)) H6 v H2) in (let H8 \def (eq_ind_r T x (\lambda (t0: T).(subst0 i v 
(TLRef n) t0)) H0 (THead k u2 t) H4) in (let H9 \def (eq_ind_r T x (\lambda 
(t0: T).(subst0 i v (TLRef n) t0)) H (THead k u2 t) H4) in (eq_ind T (THead k 
u2 t) (\lambda (t0: T).(land (eq nat n i) (eq T t0 (lift (S n) O v)))) (let 
H10 \def (eq_ind T (THead k u1 t) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H3) in 
(False_ind (land (eq nat n i) (eq T (THead k u2 t) (lift (S n) O v))) H10)) x 
H4))))))))))))))))) (\lambda (H0: (subst0 i v (TLRef n) x)).(\lambda (k: 
K).(\lambda (v0: T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i0: 
nat).(\lambda (u: T).(\lambda (H1: (eq nat i0 i)).(\lambda (H2: (eq T v0 
v)).(\lambda (H3: (eq T (THead k u t3) (TLRef n))).(\lambda (H4: (eq T (THead 
k u t0) x)).(\lambda (H5: (subst0 (s k i0) v0 t3 t0)).(let H6 \def (eq_ind 
nat i0 (\lambda (n0: nat).(subst0 (s k n0) v0 t3 t0)) H5 i H1) in (let H7 
\def (eq_ind T v0 (\lambda (t: T).(subst0 (s k i) t t3 t0)) H6 v H2) in (let 
H8 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (TLRef n) t)) H0 (THead k u 
t0) H4) in (let H9 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (TLRef n) 
t)) H (THead k u t0) H4) in (eq_ind T (THead k u t0) (\lambda (t: T).(land 
(eq nat n i) (eq T t (lift (S n) O v)))) (let H10 \def (eq_ind T (THead k u 
t3) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H3) in (False_ind (land (eq nat n i) (eq T 
(THead k u t0) (lift (S n) O v))) H10)) x H4))))))))))))))))) (\lambda (H0: 
(subst0 i v (TLRef n) x)).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (i0: nat).(\lambda (k: K).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H2: (eq nat i0 i)).(\lambda (H3: (eq T v0 v)).(\lambda (H4: (eq 
T (THead k u1 t0) (TLRef n))).(\lambda (H5: (eq T (THead k u2 t3) 
x)).(\lambda (H1: (subst0 i0 v0 u1 u2)).(\lambda (H6: (subst0 (s k i0) v0 t0 
t3)).(let H7 \def (eq_ind nat i0 (\lambda (n0: nat).(subst0 (s k n0) v0 t0 
t3)) H6 i H2) in (let H8 \def (eq_ind nat i0 (\lambda (n0: nat).(subst0 n0 v0 
u1 u2)) H1 i H2) in (let H9 \def (eq_ind T v0 (\lambda (t: T).(subst0 (s k i) 
t t0 t3)) H7 v H3) in (let H10 \def (eq_ind T v0 (\lambda (t: T).(subst0 i t 
u1 u2)) H8 v H3) in (let H11 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v 
(TLRef n) t)) H0 (THead k u2 t3) H5) in (let H12 \def (eq_ind_r T x (\lambda 
(t: T).(subst0 i v (TLRef n) t)) H (THead k u2 t3) H5) in (eq_ind T (THead k 
u2 t3) (\lambda (t: T).(land (eq nat n i) (eq T t (lift (S n) O v)))) (let 
H13 \def (eq_ind T (THead k u1 t0) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H4) in 
(False_ind (land (eq nat n i) (eq T (THead k u2 t3) (lift (S n) O v))) H13)) 
x H5))))))))))))))))))))) H))))).

theorem subst0_gen_head:
 \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall 
(x: T).(\forall (i: nat).((subst0 i v (THead k u1 t1) x) \to (or3 (ex2 T 
(\lambda (u2: T).(eq T x (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 
u2))) (ex2 T (\lambda (t2: T).(eq T x (THead k u1 t2))) (\lambda (t2: 
T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))))))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(x: T).(\lambda (i: nat).(\lambda (H: (subst0 i v (THead k u1 t1) 
x)).(subst0_inv_coq i v (THead k u1 t1) x (\lambda (n: nat).(\lambda (t: 
T).(\lambda (_: T).(\lambda (t2: T).(or3 (ex2 T (\lambda (u2: T).(eq T t2 
(THead k u2 t1))) (\lambda (u2: T).(subst0 n t u1 u2))) (ex2 T (\lambda (t3: 
T).(eq T t2 (THead k u1 t3))) (\lambda (t3: T).(subst0 (s k n) t t1 t3))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 n t u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s k n) t t1 t3))))))))) (\lambda (H0: (subst0 i 
v (THead k u1 t1) x)).(\lambda (v0: T).(\lambda (i0: nat).(\lambda (H1: (eq 
nat i0 i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: (eq T (TLRef i0) (THead k 
u1 t1))).(\lambda (H4: (eq T (lift (S i0) O v0) x)).(let H5 \def (eq_ind nat 
i0 (\lambda (n: nat).(eq T (lift (S n) O v0) x)) H4 i H1) in (let H6 \def 
(eq_ind nat i0 (\lambda (n: nat).(eq T (TLRef n) (THead k u1 t1))) H3 i H1) 
in (let H7 \def (eq_ind T v0 (\lambda (t: T).(eq T (lift (S i) O t) x)) H5 v 
H2) in (let H8 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (THead k u1 t1) 
t)) H0 (lift (S i) O v) H7) in (let H9 \def (eq_ind_r T x (\lambda (t: 
T).(subst0 i v (THead k u1 t1) t)) H (lift (S i) O v) H7) in (eq_ind T (lift 
(S i) O v) (\lambda (t: T).(or3 (ex2 T (\lambda (u2: T).(eq T t (THead k u2 
t1))) (\lambda (u2: T).(subst0 i v u1 u2))) (ex2 T (\lambda (t2: T).(eq T t 
(THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t (THead k u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))))) (let H10 \def (eq_ind T (TLRef i) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead k u1 t1) H6) in (False_ind (or3 (ex2 T (\lambda (u2: T).(eq 
T (lift (S i) O v) (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 u2))) 
(ex2 T (\lambda (t2: T).(eq T (lift (S i) O v) (THead k u1 t2))) (\lambda 
(t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (lift (S i) O v) (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) v t1 
t2))))) H10)) x H7))))))))))))) (\lambda (H0: (subst0 i v (THead k u1 t1) 
x)).(\lambda (v0: T).(\lambda (u2: T).(\lambda (u0: T).(\lambda (i0: 
nat).(\lambda (t: T).(\lambda (k0: K).(\lambda (H1: (eq nat i0 i)).(\lambda 
(H2: (eq T v0 v)).(\lambda (H3: (eq T (THead k0 u0 t) (THead k u1 
t1))).(\lambda (H4: (eq T (THead k0 u2 t) x)).(\lambda (H5: (subst0 i0 v0 u0 
u2)).(let H6 \def (eq_ind nat i0 (\lambda (n: nat).(subst0 n v0 u0 u2)) H5 i 
H1) in (let H7 \def (eq_ind T v0 (\lambda (t0: T).(subst0 i t0 u0 u2)) H6 v 
H2) in (let H8 \def (eq_ind_r T x (\lambda (t0: T).(subst0 i v (THead k u1 
t1) t0)) H0 (THead k0 u2 t) H4) in (let H9 \def (eq_ind_r T x (\lambda (t0: 
T).(subst0 i v (THead k u1 t1) t0)) H (THead k0 u2 t) H4) in (eq_ind T (THead 
k0 u2 t) (\lambda (t0: T).(or3 (ex2 T (\lambda (u3: T).(eq T t0 (THead k u3 
t1))) (\lambda (u3: T).(subst0 i v u1 u3))) (ex2 T (\lambda (t2: T).(eq T t0 
(THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T t0 (THead k u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))))) (let H10 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k0 | 
(TLRef _) \Rightarrow k0 | (THead k1 _ _) \Rightarrow k1])) (THead k0 u0 t) 
(THead k u1 t1) H3) in ((let H11 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t0 _) \Rightarrow t0])) (THead k0 u0 t) (THead k u1 
t1) H3) in ((let H12 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | 
(THead _ _ t0) \Rightarrow t0])) (THead k0 u0 t) (THead k u1 t1) H3) in 
(\lambda (H13: (eq T u0 u1)).(\lambda (H14: (eq K k0 k)).(let H15 \def 
(eq_ind K k0 (\lambda (k1: K).(subst0 i v (THead k u1 t1) (THead k1 u2 t))) 
H9 k H14) in (let H16 \def (eq_ind K k0 (\lambda (k1: K).(subst0 i v (THead k 
u1 t1) (THead k1 u2 t))) H8 k H14) in (eq_ind_r K k (\lambda (k1: K).(or3 
(ex2 T (\lambda (u3: T).(eq T (THead k1 u2 t) (THead k u3 t1))) (\lambda (u3: 
T).(subst0 i v u1 u3))) (ex2 T (\lambda (t2: T).(eq T (THead k1 u2 t) (THead 
k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda 
(u3: T).(\lambda (t2: T).(eq T (THead k1 u2 t) (THead k u3 t2)))) (\lambda 
(u3: T).(\lambda (_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))))) (let H17 \def (eq_ind T t (\lambda (t0: 
T).(subst0 i v (THead k u1 t1) (THead k u2 t0))) H15 t1 H12) in (let H18 \def 
(eq_ind T t (\lambda (t0: T).(subst0 i v (THead k u1 t1) (THead k u2 t0))) 
H16 t1 H12) in (eq_ind_r T t1 (\lambda (t0: T).(or3 (ex2 T (\lambda (u3: 
T).(eq T (THead k u2 t0) (THead k u3 t1))) (\lambda (u3: T).(subst0 i v u1 
u3))) (ex2 T (\lambda (t2: T).(eq T (THead k u2 t0) (THead k u1 t2))) 
(\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead k u2 t0) (THead k u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))))) (let H19 \def (eq_ind T u0 (\lambda (t0: 
T).(subst0 i v t0 u2)) H7 u1 H13) in (or3_intro0 (ex2 T (\lambda (u3: T).(eq 
T (THead k u2 t1) (THead k u3 t1))) (\lambda (u3: T).(subst0 i v u1 u3))) 
(ex2 T (\lambda (t2: T).(eq T (THead k u2 t1) (THead k u1 t2))) (\lambda (t2: 
T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T (THead k u2 t1) (THead k u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) v t1 
t2)))) (ex_intro2 T (\lambda (u3: T).(eq T (THead k u2 t1) (THead k u3 t1))) 
(\lambda (u3: T).(subst0 i v u1 u3)) u2 (refl_equal T (THead k u2 t1)) H19))) 
t H12))) k0 H14)))))) H11)) H10)) x H4))))))))))))))))) (\lambda (H0: (subst0 
i v (THead k u1 t1) x)).(\lambda (k0: K).(\lambda (v0: T).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (i0: nat).(\lambda (u: T).(\lambda (H1: (eq nat 
i0 i)).(\lambda (H2: (eq T v0 v)).(\lambda (H3: (eq T (THead k0 u t3) (THead 
k u1 t1))).(\lambda (H4: (eq T (THead k0 u t0) x)).(\lambda (H5: (subst0 (s 
k0 i0) v0 t3 t0)).(let H6 \def (eq_ind nat i0 (\lambda (n: nat).(subst0 (s k0 
n) v0 t3 t0)) H5 i H1) in (let H7 \def (eq_ind T v0 (\lambda (t: T).(subst0 
(s k0 i) t t3 t0)) H6 v H2) in (let H8 \def (eq_ind_r T x (\lambda (t: 
T).(subst0 i v (THead k u1 t1) t)) H0 (THead k0 u t0) H4) in (let H9 \def 
(eq_ind_r T x (\lambda (t: T).(subst0 i v (THead k u1 t1) t)) H (THead k0 u 
t0) H4) in (eq_ind T (THead k0 u t0) (\lambda (t: T).(or3 (ex2 T (\lambda 
(u2: T).(eq T t (THead k u2 t1))) (\lambda (u2: T).(subst0 i v u1 u2))) (ex2 
T (\lambda (t2: T).(eq T t (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) 
v t1 t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t (THead k u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))) (let H10 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ _) \Rightarrow k1])) 
(THead k0 u t3) (THead k u1 t1) H3) in ((let H11 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u 
| (TLRef _) \Rightarrow u | (THead _ t _) \Rightarrow t])) (THead k0 u t3) 
(THead k u1 t1) H3) in ((let H12 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t) \Rightarrow t])) (THead k0 u t3) (THead k u1 
t1) H3) in (\lambda (H13: (eq T u u1)).(\lambda (H14: (eq K k0 k)).(let H15 
\def (eq_ind T u (\lambda (t: T).(subst0 i v (THead k u1 t1) (THead k0 t 
t0))) H9 u1 H13) in (let H16 \def (eq_ind T u (\lambda (t: T).(subst0 i v 
(THead k u1 t1) (THead k0 t t0))) H8 u1 H13) in (eq_ind_r T u1 (\lambda (t: 
T).(or3 (ex2 T (\lambda (u2: T).(eq T (THead k0 t t0) (THead k u2 t1))) 
(\lambda (u2: T).(subst0 i v u1 u2))) (ex2 T (\lambda (t2: T).(eq T (THead k0 
t t0) (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead k0 t t0) (THead k u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))) (let H17 \def (eq_ind T t3 
(\lambda (t: T).(subst0 (s k0 i) v t t0)) H7 t1 H12) in (let H18 \def (eq_ind 
K k0 (\lambda (k1: K).(subst0 i v (THead k u1 t1) (THead k1 u1 t0))) H15 k 
H14) in (let H19 \def (eq_ind K k0 (\lambda (k1: K).(subst0 i v (THead k u1 
t1) (THead k1 u1 t0))) H16 k H14) in (let H20 \def (eq_ind K k0 (\lambda (k1: 
K).(subst0 (s k1 i) v t1 t0)) H17 k H14) in (eq_ind_r K k (\lambda (k1: 
K).(or3 (ex2 T (\lambda (u2: T).(eq T (THead k1 u1 t0) (THead k u2 t1))) 
(\lambda (u2: T).(subst0 i v u1 u2))) (ex2 T (\lambda (t2: T).(eq T (THead k1 
u1 t0) (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead k1 u1 t0) (THead k u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))) (or3_intro1 (ex2 T (\lambda 
(u2: T).(eq T (THead k u1 t0) (THead k u2 t1))) (\lambda (u2: T).(subst0 i v 
u1 u2))) (ex2 T (\lambda (t2: T).(eq T (THead k u1 t0) (THead k u1 t2))) 
(\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T (THead k u1 t0) (THead k u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))) (ex_intro2 T (\lambda (t2: T).(eq T (THead k 
u1 t0) (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2)) t0 
(refl_equal T (THead k u1 t0)) H20)) k0 H14))))) u H13)))))) H11)) H10)) x 
H4))))))))))))))))) (\lambda (H0: (subst0 i v (THead k u1 t1) x)).(\lambda 
(v0: T).(\lambda (u0: T).(\lambda (u2: T).(\lambda (i0: nat).(\lambda (k0: 
K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (H2: (eq nat i0 i)).(\lambda 
(H3: (eq T v0 v)).(\lambda (H4: (eq T (THead k0 u0 t0) (THead k u1 
t1))).(\lambda (H5: (eq T (THead k0 u2 t3) x)).(\lambda (H1: (subst0 i0 v0 u0 
u2)).(\lambda (H6: (subst0 (s k0 i0) v0 t0 t3)).(let H7 \def (eq_ind nat i0 
(\lambda (n: nat).(subst0 (s k0 n) v0 t0 t3)) H6 i H2) in (let H8 \def 
(eq_ind nat i0 (\lambda (n: nat).(subst0 n v0 u0 u2)) H1 i H2) in (let H9 
\def (eq_ind T v0 (\lambda (t: T).(subst0 (s k0 i) t t0 t3)) H7 v H3) in (let 
H10 \def (eq_ind T v0 (\lambda (t: T).(subst0 i t u0 u2)) H8 v H3) in (let 
H11 \def (eq_ind_r T x (\lambda (t: T).(subst0 i v (THead k u1 t1) t)) H0 
(THead k0 u2 t3) H5) in (let H12 \def (eq_ind_r T x (\lambda (t: T).(subst0 i 
v (THead k u1 t1) t)) H (THead k0 u2 t3) H5) in (eq_ind T (THead k0 u2 t3) 
(\lambda (t: T).(or3 (ex2 T (\lambda (u3: T).(eq T t (THead k u3 t1))) 
(\lambda (u3: T).(subst0 i v u1 u3))) (ex2 T (\lambda (t2: T).(eq T t (THead 
k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda 
(u3: T).(\lambda (t2: T).(eq T t (THead k u3 t2)))) (\lambda (u3: T).(\lambda 
(_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) 
v t1 t2)))))) (let H13 \def (f_equal T K (\lambda (e: T).(match e in T return 
(\lambda (_: T).K) with [(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 
| (THead k1 _ _) \Rightarrow k1])) (THead k0 u0 t0) (THead k u1 t1) H4) in 
((let H14 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t 
_) \Rightarrow t])) (THead k0 u0 t0) (THead k u1 t1) H4) in ((let H15 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead k0 u0 t0) (THead k u1 t1) H4) in (\lambda (H16: (eq T 
u0 u1)).(\lambda (H17: (eq K k0 k)).(let H18 \def (eq_ind T t0 (\lambda (t: 
T).(subst0 (s k0 i) v t t3)) H9 t1 H15) in (let H19 \def (eq_ind K k0 
(\lambda (k1: K).(subst0 i v (THead k u1 t1) (THead k1 u2 t3))) H12 k H17) in 
(let H20 \def (eq_ind K k0 (\lambda (k1: K).(subst0 i v (THead k u1 t1) 
(THead k1 u2 t3))) H11 k H17) in (let H21 \def (eq_ind K k0 (\lambda (k1: 
K).(subst0 (s k1 i) v t1 t3)) H18 k H17) in (eq_ind_r K k (\lambda (k1: 
K).(or3 (ex2 T (\lambda (u3: T).(eq T (THead k1 u2 t3) (THead k u3 t1))) 
(\lambda (u3: T).(subst0 i v u1 u3))) (ex2 T (\lambda (t2: T).(eq T (THead k1 
u2 t3) (THead k u1 t2))) (\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T 
T (\lambda (u3: T).(\lambda (t2: T).(eq T (THead k1 u2 t3) (THead k u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(subst0 i v u1 u3))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) v t1 t2)))))) (let H22 \def (eq_ind T u0 
(\lambda (t: T).(subst0 i v t u2)) H10 u1 H16) in (or3_intro2 (ex2 T (\lambda 
(u3: T).(eq T (THead k u2 t3) (THead k u3 t1))) (\lambda (u3: T).(subst0 i v 
u1 u3))) (ex2 T (\lambda (t2: T).(eq T (THead k u2 t3) (THead k u1 t2))) 
(\lambda (t2: T).(subst0 (s k i) v t1 t2))) (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T (THead k u2 t3) (THead k u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k i) v t1 t2)))) (ex3_2_intro T T (\lambda (u3: T).(\lambda 
(t2: T).(eq T (THead k u2 t3) (THead k u3 t2)))) (\lambda (u3: T).(\lambda 
(_: T).(subst0 i v u1 u3))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) 
v t1 t2))) u2 t3 (refl_equal T (THead k u2 t3)) H22 H21))) k0 H17)))))))) 
H14)) H13)) x H5))))))))))))))))))))) H))))))).

theorem subst0_gen_lift_lt:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst0 i (lift h d u) (lift h (S (plus i d)) t1) 
x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst0 i u t1 t2)))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(T_ind (\lambda (t: T).(\forall (x: 
T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst0 i (lift h d 
u) (lift h (S (plus i d)) t) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h 
(S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u t t2))))))))) (\lambda (n: 
nat).(\lambda (x: T).(\lambda (i: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (subst0 i (lift h d u) (lift h (S (plus i d)) (TSort n)) 
x)).(let H0 \def (eq_ind T (lift h (S (plus i d)) (TSort n)) (\lambda (t: 
T).(subst0 i (lift h d u) t x)) H (TSort n) (lift_sort n h (S (plus i d)))) 
in (subst0_gen_sort (lift h d u) x i n H0 (ex2 T (\lambda (t2: T).(eq T x 
(lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (TSort n) 
t2))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (subst0 i (lift h d u) (lift h (S 
(plus i d)) (TLRef n)) x)).(lt_le_e n (S (plus i d)) (ex2 T (\lambda (t2: 
T).(eq T x (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (TLRef 
n) t2))) (\lambda (H0: (lt n (S (plus i d)))).(let H1 \def (eq_ind T (lift h 
(S (plus i d)) (TLRef n)) (\lambda (t: T).(subst0 i (lift h d u) t x)) H 
(TLRef n) (lift_lref_lt n h (S (plus i d)) H0)) in (and_ind (eq nat n i) (eq 
T x (lift (S n) O (lift h d u))) (ex2 T (\lambda (t2: T).(eq T x (lift h (S 
(plus i d)) t2))) (\lambda (t2: T).(subst0 i u (TLRef n) t2))) (\lambda (H2: 
(eq nat n i)).(\lambda (H3: (eq T x (lift (S n) O (lift h d u)))).(eq_ind_r T 
(lift (S n) O (lift h d u)) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t 
(lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (TLRef n) t2)))) 
(eq_ind_r nat i (\lambda (n0: nat).(ex2 T (\lambda (t2: T).(eq T (lift (S n0) 
O (lift h d u)) (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u 
(TLRef n0) t2)))) (eq_ind T (lift h (plus (S i) d) (lift (S i) O u)) (\lambda 
(t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst0 i u (TLRef i) t2)))) (ex_intro2 T (\lambda (t2: T).(eq T 
(lift h (S (plus i d)) (lift (S i) O u)) (lift h (S (plus i d)) t2))) 
(\lambda (t2: T).(subst0 i u (TLRef i) t2)) (lift (S i) O u) (refl_equal T 
(lift h (S (plus i d)) (lift (S i) O u))) (subst0_lref u i)) (lift (S i) O 
(lift h d u)) (lift_d u h (S i) d O (le_O_n d))) n H2) x H3))) 
(subst0_gen_lref (lift h d u) x i n H1)))) (\lambda (H0: (le (S (plus i d)) 
n)).(let H1 \def (eq_ind T (lift h (S (plus i d)) (TLRef n)) (\lambda (t: 
T).(subst0 i (lift h d u) t x)) H (TLRef (plus n h)) (lift_lref_ge n h (S 
(plus i d)) H0)) in (and_ind (eq nat (plus n h) i) (eq T x (lift (S (plus n 
h)) O (lift h d u))) (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) 
t2))) (\lambda (t2: T).(subst0 i u (TLRef n) t2))) (\lambda (H2: (eq nat 
(plus n h) i)).(\lambda (_: (eq T x (lift (S (plus n h)) O (lift h d 
u)))).(let H4 \def (eq_ind_r nat i (\lambda (n0: nat).(le (S (plus n0 d)) n)) 
H0 (plus n h) H2) in (le_false n (plus (plus n h) d) (ex2 T (\lambda (t2: 
T).(eq T x (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (TLRef 
n) t2))) (le_plus_trans n (plus n h) d (le_plus_l n h)) H4)))) 
(subst0_gen_lref (lift h d u) x i (plus n h) H1))))))))))) (\lambda (k: 
K).(\lambda (t: T).(\lambda (H: ((\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst0 i (lift h d u) (lift h (S (plus i d)) t) 
x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst0 i u t t2)))))))))).(\lambda (t0: T).(\lambda (H0: ((\forall 
(x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst0 i (lift 
h d u) (lift h (S (plus i d)) t0) x) \to (ex2 T (\lambda (t2: T).(eq T x 
(lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u t0 
t2)))))))))).(\lambda (x: T).(\lambda (i: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H1: (subst0 i (lift h d u) (lift h (S (plus i d)) (THead k t 
t0)) x)).(let H2 \def (eq_ind T (lift h (S (plus i d)) (THead k t t0)) 
(\lambda (t2: T).(subst0 i (lift h d u) t2 x)) H1 (THead k (lift h (S (plus i 
d)) t) (lift h (s k (S (plus i d))) t0)) (lift_head k t t0 h (S (plus i d)))) 
in (or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead k u2 (lift h (s k (S (plus 
i d))) t0)))) (\lambda (u2: T).(subst0 i (lift h d u) (lift h (S (plus i d)) 
t) u2))) (ex2 T (\lambda (t2: T).(eq T x (THead k (lift h (S (plus i d)) t) 
t2))) (\lambda (t2: T).(subst0 (s k i) (lift h d u) (lift h (s k (S (plus i 
d))) t0) t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i (lift h d u) (lift h (S 
(plus i d)) t) u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) (lift h 
d u) (lift h (s k (S (plus i d))) t0) t2)))) (ex2 T (\lambda (t2: T).(eq T x 
(lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) 
t2))) (\lambda (H3: (ex2 T (\lambda (u2: T).(eq T x (THead k u2 (lift h (s k 
(S (plus i d))) t0)))) (\lambda (u2: T).(subst0 i (lift h d u) (lift h (S 
(plus i d)) t) u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead k u2 (lift h 
(s k (S (plus i d))) t0)))) (\lambda (u2: T).(subst0 i (lift h d u) (lift h 
(S (plus i d)) t) u2)) (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) 
t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2))) (\lambda (x0: 
T).(\lambda (H4: (eq T x (THead k x0 (lift h (s k (S (plus i d))) 
t0)))).(\lambda (H5: (subst0 i (lift h d u) (lift h (S (plus i d)) t) 
x0)).(eq_ind_r T (THead k x0 (lift h (s k (S (plus i d))) t0)) (\lambda (t2: 
T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda 
(t3: T).(subst0 i u (THead k t t0) t3)))) (ex2_ind T (\lambda (t2: T).(eq T 
x0 (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u t t2)) (ex2 T 
(\lambda (t2: T).(eq T (THead k x0 (lift h (s k (S (plus i d))) t0)) (lift h 
(S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2))) 
(\lambda (x1: T).(\lambda (H6: (eq T x0 (lift h (S (plus i d)) x1))).(\lambda 
(H7: (subst0 i u t x1)).(eq_ind_r T (lift h (S (plus i d)) x1) (\lambda (t2: 
T).(ex2 T (\lambda (t3: T).(eq T (THead k t2 (lift h (s k (S (plus i d))) 
t0)) (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst0 i u (THead k t t0) 
t3)))) (eq_ind T (lift h (S (plus i d)) (THead k x1 t0)) (\lambda (t2: 
T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda 
(t3: T).(subst0 i u (THead k t t0) t3)))) (ex_intro2 T (\lambda (t2: T).(eq T 
(lift h (S (plus i d)) (THead k x1 t0)) (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst0 i u (THead k t t0) t2)) (THead k x1 t0) (refl_equal T (lift h 
(S (plus i d)) (THead k x1 t0))) (subst0_fst u x1 t i H7 t0 k)) (THead k 
(lift h (S (plus i d)) x1) (lift h (s k (S (plus i d))) t0)) (lift_head k x1 
t0 h (S (plus i d)))) x0 H6)))) (H x0 i h d H5)) x H4)))) H3)) (\lambda (H3: 
(ex2 T (\lambda (t2: T).(eq T x (THead k (lift h (S (plus i d)) t) t2))) 
(\lambda (t2: T).(subst0 (s k i) (lift h d u) (lift h (s k (S (plus i d))) 
t0) t2)))).(ex2_ind T (\lambda (t2: T).(eq T x (THead k (lift h (S (plus i 
d)) t) t2))) (\lambda (t2: T).(subst0 (s k i) (lift h d u) (lift h (s k (S 
(plus i d))) t0) t2)) (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) 
t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2))) (\lambda (x0: 
T).(\lambda (H4: (eq T x (THead k (lift h (S (plus i d)) t) x0))).(\lambda 
(H5: (subst0 (s k i) (lift h d u) (lift h (s k (S (plus i d))) t0) 
x0)).(eq_ind_r T (THead k (lift h (S (plus i d)) t) x0) (\lambda (t2: T).(ex2 
T (\lambda (t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda (t3: 
T).(subst0 i u (THead k t t0) t3)))) (let H6 \def (eq_ind nat (s k (S (plus i 
d))) (\lambda (n: nat).(subst0 (s k i) (lift h d u) (lift h n t0) x0)) H5 (S 
(s k (plus i d))) (s_S k (plus i d))) in (let H7 \def (eq_ind nat (s k (plus 
i d)) (\lambda (n: nat).(subst0 (s k i) (lift h d u) (lift h (S n) t0) x0)) 
H6 (plus (s k i) d) (s_plus k i d)) in (ex2_ind T (\lambda (t2: T).(eq T x0 
(lift h (S (plus (s k i) d)) t2))) (\lambda (t2: T).(subst0 (s k i) u t0 t2)) 
(ex2 T (\lambda (t2: T).(eq T (THead k (lift h (S (plus i d)) t) x0) (lift h 
(S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2))) 
(\lambda (x1: T).(\lambda (H8: (eq T x0 (lift h (S (plus (s k i) d)) 
x1))).(\lambda (H9: (subst0 (s k i) u t0 x1)).(eq_ind_r T (lift h (S (plus (s 
k i) d)) x1) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead k (lift h 
(S (plus i d)) t) t2) (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst0 i 
u (THead k t t0) t3)))) (eq_ind nat (s k (plus i d)) (\lambda (n: nat).(ex2 T 
(\lambda (t2: T).(eq T (THead k (lift h (S (plus i d)) t) (lift h (S n) x1)) 
(lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) 
t2)))) (eq_ind nat (s k (S (plus i d))) (\lambda (n: nat).(ex2 T (\lambda 
(t2: T).(eq T (THead k (lift h (S (plus i d)) t) (lift h n x1)) (lift h (S 
(plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2)))) (eq_ind 
T (lift h (S (plus i d)) (THead k t x1)) (\lambda (t2: T).(ex2 T (\lambda 
(t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst0 i u 
(THead k t t0) t3)))) (ex_intro2 T (\lambda (t2: T).(eq T (lift h (S (plus i 
d)) (THead k t x1)) (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u 
(THead k t t0) t2)) (THead k t x1) (refl_equal T (lift h (S (plus i d)) 
(THead k t x1))) (subst0_snd k u x1 t0 i H9 t)) (THead k (lift h (S (plus i 
d)) t) (lift h (s k (S (plus i d))) x1)) (lift_head k t x1 h (S (plus i d)))) 
(S (s k (plus i d))) (s_S k (plus i d))) (plus (s k i) d) (s_plus k i d)) x0 
H8)))) (H0 x0 (s k i) h d H7)))) x H4)))) H3)) (\lambda (H3: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i (lift h d u) (lift h (S (plus i d)) t) u2))) 
(\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) (lift h d u) (lift h (s k (S 
(plus i d))) t0) t2))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i (lift h d 
u) (lift h (S (plus i d)) t) u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 
(s k i) (lift h d u) (lift h (s k (S (plus i d))) t0) t2))) (ex2 T (\lambda 
(t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u 
(THead k t t0) t2))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T x 
(THead k x0 x1))).(\lambda (H5: (subst0 i (lift h d u) (lift h (S (plus i d)) 
t) x0)).(\lambda (H6: (subst0 (s k i) (lift h d u) (lift h (s k (S (plus i 
d))) t0) x1)).(eq_ind_r T (THead k x0 x1) (\lambda (t2: T).(ex2 T (\lambda 
(t3: T).(eq T t2 (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst0 i u 
(THead k t t0) t3)))) (let H7 \def (eq_ind nat (s k (S (plus i d))) (\lambda 
(n: nat).(subst0 (s k i) (lift h d u) (lift h n t0) x1)) H6 (S (s k (plus i 
d))) (s_S k (plus i d))) in (let H8 \def (eq_ind nat (s k (plus i d)) 
(\lambda (n: nat).(subst0 (s k i) (lift h d u) (lift h (S n) t0) x1)) H7 
(plus (s k i) d) (s_plus k i d)) in (ex2_ind T (\lambda (t2: T).(eq T x1 
(lift h (S (plus (s k i) d)) t2))) (\lambda (t2: T).(subst0 (s k i) u t0 t2)) 
(ex2 T (\lambda (t2: T).(eq T (THead k x0 x1) (lift h (S (plus i d)) t2))) 
(\lambda (t2: T).(subst0 i u (THead k t t0) t2))) (\lambda (x2: T).(\lambda 
(H9: (eq T x1 (lift h (S (plus (s k i) d)) x2))).(\lambda (H10: (subst0 (s k 
i) u t0 x2)).(ex2_ind T (\lambda (t2: T).(eq T x0 (lift h (S (plus i d)) 
t2))) (\lambda (t2: T).(subst0 i u t t2)) (ex2 T (\lambda (t2: T).(eq T 
(THead k x0 x1) (lift h (S (plus i d)) t2))) (\lambda (t2: T).(subst0 i u 
(THead k t t0) t2))) (\lambda (x3: T).(\lambda (H11: (eq T x0 (lift h (S 
(plus i d)) x3))).(\lambda (H12: (subst0 i u t x3)).(eq_ind_r T (lift h (S 
(plus i d)) x3) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead k t2 
x1) (lift h (S (plus i d)) t3))) (\lambda (t3: T).(subst0 i u (THead k t t0) 
t3)))) (eq_ind_r T (lift h (S (plus (s k i) d)) x2) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T (THead k (lift h (S (plus i d)) x3) t2) (lift h (S 
(plus i d)) t3))) (\lambda (t3: T).(subst0 i u (THead k t t0) t3)))) (eq_ind 
nat (s k (plus i d)) (\lambda (n: nat).(ex2 T (\lambda (t2: T).(eq T (THead k 
(lift h (S (plus i d)) x3) (lift h (S n) x2)) (lift h (S (plus i d)) t2))) 
(\lambda (t2: T).(subst0 i u (THead k t t0) t2)))) (eq_ind nat (s k (S (plus 
i d))) (\lambda (n: nat).(ex2 T (\lambda (t2: T).(eq T (THead k (lift h (S 
(plus i d)) x3) (lift h n x2)) (lift h (S (plus i d)) t2))) (\lambda (t2: 
T).(subst0 i u (THead k t t0) t2)))) (eq_ind T (lift h (S (plus i d)) (THead 
k x3 x2)) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h (S (plus 
i d)) t3))) (\lambda (t3: T).(subst0 i u (THead k t t0) t3)))) (ex_intro2 T 
(\lambda (t2: T).(eq T (lift h (S (plus i d)) (THead k x3 x2)) (lift h (S 
(plus i d)) t2))) (\lambda (t2: T).(subst0 i u (THead k t t0) t2)) (THead k 
x3 x2) (refl_equal T (lift h (S (plus i d)) (THead k x3 x2))) (subst0_both u 
t x3 i H12 k t0 x2 H10)) (THead k (lift h (S (plus i d)) x3) (lift h (s k (S 
(plus i d))) x2)) (lift_head k x3 x2 h (S (plus i d)))) (S (s k (plus i d))) 
(s_S k (plus i d))) (plus (s k i) d) (s_plus k i d)) x1 H9) x0 H11)))) (H x0 
i h d H5))))) (H0 x1 (s k i) h d H8)))) x H4)))))) H3)) (subst0_gen_head k 
(lift h d u) (lift h (S (plus i d)) t) (lift h (s k (S (plus i d))) t0) x i 
H2))))))))))))) t1)).

theorem subst0_gen_lift_false:
 \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst0 i u 
(lift h d t) x) \to (\forall (P: Prop).P)))))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (u: T).(\forall (x: 
T).(\forall (h: nat).(\forall (d: nat).(\forall (i: nat).((le d i) \to ((lt i 
(plus d h)) \to ((subst0 i u (lift h d t0) x) \to (\forall (P: 
Prop).P)))))))))) (\lambda (n: nat).(\lambda (u: T).(\lambda (x: T).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (i: nat).(\lambda (_: (le d i)).(\lambda 
(_: (lt i (plus d h))).(\lambda (H1: (subst0 i u (lift h d (TSort n)) 
x)).(\lambda (P: Prop).(let H2 \def (eq_ind T (lift h d (TSort n)) (\lambda 
(t0: T).(subst0 i u t0 x)) H1 (TSort n) (lift_sort n h d)) in 
(subst0_gen_sort u x i n H2 P)))))))))))) (\lambda (n: nat).(\lambda (u: 
T).(\lambda (x: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda (i: 
nat).(\lambda (H: (le d i)).(\lambda (H0: (lt i (plus d h))).(\lambda (H1: 
(subst0 i u (lift h d (TLRef n)) x)).(\lambda (P: Prop).(lt_le_e n d P 
(\lambda (H2: (lt n d)).(let H3 \def (eq_ind T (lift h d (TLRef n)) (\lambda 
(t0: T).(subst0 i u t0 x)) H1 (TLRef n) (lift_lref_lt n h d H2)) in (and_ind 
(eq nat n i) (eq T x (lift (S n) O u)) P (\lambda (H4: (eq nat n i)).(\lambda 
(_: (eq T x (lift (S n) O u))).(let H6 \def (eq_ind nat n (\lambda (n0: 
nat).(lt n0 d)) H2 i H4) in (le_false d i P H H6)))) (subst0_gen_lref u x i n 
H3)))) (\lambda (H2: (le d n)).(let H3 \def (eq_ind T (lift h d (TLRef n)) 
(\lambda (t0: T).(subst0 i u t0 x)) H1 (TLRef (plus n h)) (lift_lref_ge n h d 
H2)) in (and_ind (eq nat (plus n h) i) (eq T x (lift (S (plus n h)) O u)) P 
(\lambda (H4: (eq nat (plus n h) i)).(\lambda (_: (eq T x (lift (S (plus n 
h)) O u))).(let H6 \def (eq_ind_r nat i (\lambda (n0: nat).(lt n0 (plus d 
h))) H0 (plus n h) H4) in (le_false d n P H2 (lt_le_S n d (simpl_lt_plus_r h 
n d H6)))))) (subst0_gen_lref u x i (plus n h) H3))))))))))))))) (\lambda (k: 
K).(\lambda (t0: T).(\lambda (H: ((\forall (u: T).(\forall (x: T).(\forall 
(h: nat).(\forall (d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) 
\to ((subst0 i u (lift h d t0) x) \to (\forall (P: 
Prop).P))))))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (u: T).(\forall 
(x: T).(\forall (h: nat).(\forall (d: nat).(\forall (i: nat).((le d i) \to 
((lt i (plus d h)) \to ((subst0 i u (lift h d t1) x) \to (\forall (P: 
Prop).P))))))))))).(\lambda (u: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (i: nat).(\lambda (H1: (le d i)).(\lambda (H2: (lt i (plus 
d h))).(\lambda (H3: (subst0 i u (lift h d (THead k t0 t1)) x)).(\lambda (P: 
Prop).(let H4 \def (eq_ind T (lift h d (THead k t0 t1)) (\lambda (t2: 
T).(subst0 i u t2 x)) H3 (THead k (lift h d t0) (lift h (s k d) t1)) 
(lift_head k t0 t1 h d)) in (or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead k 
u2 (lift h (s k d) t1)))) (\lambda (u2: T).(subst0 i u (lift h d t0) u2))) 
(ex2 T (\lambda (t2: T).(eq T x (THead k (lift h d t0) t2))) (\lambda (t2: 
T).(subst0 (s k i) u (lift h (s k d) t1) t2))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u (lift h d t0) u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 
(s k i) u (lift h (s k d) t1) t2)))) P (\lambda (H5: (ex2 T (\lambda (u2: 
T).(eq T x (THead k u2 (lift h (s k d) t1)))) (\lambda (u2: T).(subst0 i u 
(lift h d t0) u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead k u2 (lift h 
(s k d) t1)))) (\lambda (u2: T).(subst0 i u (lift h d t0) u2)) P (\lambda 
(x0: T).(\lambda (_: (eq T x (THead k x0 (lift h (s k d) t1)))).(\lambda (H7: 
(subst0 i u (lift h d t0) x0)).(H u x0 h d i H1 H2 H7 P)))) H5)) (\lambda 
(H5: (ex2 T (\lambda (t2: T).(eq T x (THead k (lift h d t0) t2))) (\lambda 
(t2: T).(subst0 (s k i) u (lift h (s k d) t1) t2)))).(ex2_ind T (\lambda (t2: 
T).(eq T x (THead k (lift h d t0) t2))) (\lambda (t2: T).(subst0 (s k i) u 
(lift h (s k d) t1) t2)) P (\lambda (x0: T).(\lambda (_: (eq T x (THead k 
(lift h d t0) x0))).(\lambda (H7: (subst0 (s k i) u (lift h (s k d) t1) 
x0)).(H0 u x0 h (s k d) (s k i) (s_le k d i H1) (eq_ind nat (s k (plus d h)) 
(\lambda (n: nat).(lt (s k i) n)) (lt_le_S (s k i) (s k (plus d h)) (s_lt k i 
(plus d h) H2)) (plus (s k d) h) (s_plus k d h)) H7 P)))) H5)) (\lambda (H5: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u (lift h d t0) u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) t1) t2))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda 
(u2: T).(\lambda (_: T).(subst0 i u (lift h d t0) u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) t1) t2))) P (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (_: (eq T x (THead k x0 x1))).(\lambda (H7: 
(subst0 i u (lift h d t0) x0)).(\lambda (_: (subst0 (s k i) u (lift h (s k d) 
t1) x1)).(H u x0 h d i H1 H2 H7 P)))))) H5)) (subst0_gen_head k u (lift h d 
t0) (lift h (s k d) t1) x i H4))))))))))))))))) t).

theorem subst0_gen_lift_ge:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst0 i u (lift h d t1) x) \to ((le (plus d h) 
i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst0 (minus i h) u t1 t2))))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(T_ind (\lambda (t: T).(\forall (x: 
T).(\forall (i: nat).(\forall (h: nat).(\forall (d: nat).((subst0 i u (lift h 
d t) x) \to ((le (plus d h) i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d 
t2))) (\lambda (t2: T).(subst0 (minus i h) u t t2)))))))))) (\lambda (n: 
nat).(\lambda (x: T).(\lambda (i: nat).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H: (subst0 i u (lift h d (TSort n)) x)).(\lambda (_: (le (plus 
d h) i)).(let H1 \def (eq_ind T (lift h d (TSort n)) (\lambda (t: T).(subst0 
i u t x)) H (TSort n) (lift_sort n h d)) in (subst0_gen_sort u x i n H1 (ex2 
T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i 
h) u (TSort n) t2)))))))))))) (\lambda (n: nat).(\lambda (x: T).(\lambda (i: 
nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H: (subst0 i u (lift h d 
(TLRef n)) x)).(\lambda (H0: (le (plus d h) i)).(lt_le_e n d (ex2 T (\lambda 
(t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u (TLRef 
n) t2))) (\lambda (H1: (lt n d)).(let H2 \def (eq_ind T (lift h d (TLRef n)) 
(\lambda (t: T).(subst0 i u t x)) H (TLRef n) (lift_lref_lt n h d H1)) in 
(and_ind (eq nat n i) (eq T x (lift (S n) O u)) (ex2 T (\lambda (t2: T).(eq T 
x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u (TLRef n) t2))) 
(\lambda (H3: (eq nat n i)).(\lambda (_: (eq T x (lift (S n) O u))).(let H5 
\def (eq_ind nat n (\lambda (n0: nat).(lt n0 d)) H1 i H3) in (le_false (plus 
d h) i (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst0 (minus i h) u (TLRef n) t2))) H0 (le_plus_trans (S i) d h H5))))) 
(subst0_gen_lref u x i n H2)))) (\lambda (H1: (le d n)).(let H2 \def (eq_ind 
T (lift h d (TLRef n)) (\lambda (t: T).(subst0 i u t x)) H (TLRef (plus n h)) 
(lift_lref_ge n h d H1)) in (and_ind (eq nat (plus n h) i) (eq T x (lift (S 
(plus n h)) O u)) (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda 
(t2: T).(subst0 (minus i h) u (TLRef n) t2))) (\lambda (H3: (eq nat (plus n 
h) i)).(\lambda (H4: (eq T x (lift (S (plus n h)) O u))).(eq_ind nat (plus n 
h) (\lambda (n0: nat).(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) 
(\lambda (t2: T).(subst0 (minus n0 h) u (TLRef n) t2)))) (eq_ind_r T (lift (S 
(plus n h)) O u) (\lambda (t: T).(ex2 T (\lambda (t2: T).(eq T t (lift h d 
t2))) (\lambda (t2: T).(subst0 (minus (plus n h) h) u (TLRef n) t2)))) 
(eq_ind_r nat n (\lambda (n0: nat).(ex2 T (\lambda (t2: T).(eq T (lift (S 
(plus n h)) O u) (lift h d t2))) (\lambda (t2: T).(subst0 n0 u (TLRef n) 
t2)))) (ex_intro2 T (\lambda (t2: T).(eq T (lift (S (plus n h)) O u) (lift h 
d t2))) (\lambda (t2: T).(subst0 n u (TLRef n) t2)) (lift (S n) O u) 
(eq_ind_r T (lift (plus h (S n)) O u) (\lambda (t: T).(eq T (lift (S (plus n 
h)) O u) t)) (eq_ind_r nat (plus h n) (\lambda (n0: nat).(eq T (lift (S n0) O 
u) (lift (plus h (S n)) O u))) (eq_ind_r nat (plus h (S n)) (\lambda (n0: 
nat).(eq T (lift n0 O u) (lift (plus h (S n)) O u))) (refl_equal T (lift 
(plus h (S n)) O u)) (S (plus h n)) (plus_n_Sm h n)) (plus n h) (plus_comm n 
h)) (lift h d (lift (S n) O u)) (lift_free u (S n) h O d (le_trans d (S n) 
(plus O (S n)) (le_S d n H1) (le_n (plus O (S n)))) (le_O_n d))) (subst0_lref 
u n)) (minus (plus n h) h) (minus_plus_r n h)) x H4) i H3))) (subst0_gen_lref 
u x i (plus n h) H2)))))))))))) (\lambda (k: K).(\lambda (t: T).(\lambda (H: 
((\forall (x: T).(\forall (i: nat).(\forall (h: nat).(\forall (d: 
nat).((subst0 i u (lift h d t) x) \to ((le (plus d h) i) \to (ex2 T (\lambda 
(t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u t 
t2))))))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (x: T).(\forall (i: 
nat).(\forall (h: nat).(\forall (d: nat).((subst0 i u (lift h d t0) x) \to 
((le (plus d h) i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) 
(\lambda (t2: T).(subst0 (minus i h) u t0 t2))))))))))).(\lambda (x: 
T).(\lambda (i: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H1: 
(subst0 i u (lift h d (THead k t t0)) x)).(\lambda (H2: (le (plus d h) 
i)).(let H3 \def (eq_ind T (lift h d (THead k t t0)) (\lambda (t2: T).(subst0 
i u t2 x)) H1 (THead k (lift h d t) (lift h (s k d) t0)) (lift_head k t t0 h 
d)) in (or3_ind (ex2 T (\lambda (u2: T).(eq T x (THead k u2 (lift h (s k d) 
t0)))) (\lambda (u2: T).(subst0 i u (lift h d t) u2))) (ex2 T (\lambda (t2: 
T).(eq T x (THead k (lift h d t) t2))) (\lambda (t2: T).(subst0 (s k i) u 
(lift h (s k d) t0) t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T 
x (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u (lift h d 
t) u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) 
t0) t2)))) (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst0 (minus i h) u (THead k t t0) t2))) (\lambda (H4: (ex2 T (\lambda 
(u2: T).(eq T x (THead k u2 (lift h (s k d) t0)))) (\lambda (u2: T).(subst0 i 
u (lift h d t) u2)))).(ex2_ind T (\lambda (u2: T).(eq T x (THead k u2 (lift h 
(s k d) t0)))) (\lambda (u2: T).(subst0 i u (lift h d t) u2)) (ex2 T (\lambda 
(t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u (THead 
k t t0) t2))) (\lambda (x0: T).(\lambda (H5: (eq T x (THead k x0 (lift h (s k 
d) t0)))).(\lambda (H6: (subst0 i u (lift h d t) x0)).(eq_ind_r T (THead k x0 
(lift h (s k d) t0)) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift 
h d t3))) (\lambda (t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) 
(ex2_ind T (\lambda (t2: T).(eq T x0 (lift h d t2))) (\lambda (t2: T).(subst0 
(minus i h) u t t2)) (ex2 T (\lambda (t2: T).(eq T (THead k x0 (lift h (s k 
d) t0)) (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u (THead k t t0) 
t2))) (\lambda (x1: T).(\lambda (H7: (eq T x0 (lift h d x1))).(\lambda (H8: 
(subst0 (minus i h) u t x1)).(eq_ind_r T (lift h d x1) (\lambda (t2: T).(ex2 
T (\lambda (t3: T).(eq T (THead k t2 (lift h (s k d) t0)) (lift h d t3))) 
(\lambda (t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) (eq_ind T (lift 
h d (THead k x1 t0)) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift 
h d t3))) (\lambda (t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) 
(ex_intro2 T (\lambda (t2: T).(eq T (lift h d (THead k x1 t0)) (lift h d 
t2))) (\lambda (t2: T).(subst0 (minus i h) u (THead k t t0) t2)) (THead k x1 
t0) (refl_equal T (lift h d (THead k x1 t0))) (subst0_fst u x1 t (minus i h) 
H8 t0 k)) (THead k (lift h d x1) (lift h (s k d) t0)) (lift_head k x1 t0 h 
d)) x0 H7)))) (H x0 i h d H6 H2)) x H5)))) H4)) (\lambda (H4: (ex2 T (\lambda 
(t2: T).(eq T x (THead k (lift h d t) t2))) (\lambda (t2: T).(subst0 (s k i) 
u (lift h (s k d) t0) t2)))).(ex2_ind T (\lambda (t2: T).(eq T x (THead k 
(lift h d t) t2))) (\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) t0) 
t2)) (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 
(minus i h) u (THead k t t0) t2))) (\lambda (x0: T).(\lambda (H5: (eq T x 
(THead k (lift h d t) x0))).(\lambda (H6: (subst0 (s k i) u (lift h (s k d) 
t0) x0)).(eq_ind_r T (THead k (lift h d t) x0) (\lambda (t2: T).(ex2 T 
(\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(subst0 (minus i 
h) u (THead k t t0) t3)))) (ex2_ind T (\lambda (t2: T).(eq T x0 (lift h (s k 
d) t2))) (\lambda (t2: T).(subst0 (minus (s k i) h) u t0 t2)) (ex2 T (\lambda 
(t2: T).(eq T (THead k (lift h d t) x0) (lift h d t2))) (\lambda (t2: 
T).(subst0 (minus i h) u (THead k t t0) t2))) (\lambda (x1: T).(\lambda (H7: 
(eq T x0 (lift h (s k d) x1))).(\lambda (H8: (subst0 (minus (s k i) h) u t0 
x1)).(eq_ind_r T (lift h (s k d) x1) (\lambda (t2: T).(ex2 T (\lambda (t3: 
T).(eq T (THead k (lift h d t) t2) (lift h d t3))) (\lambda (t3: T).(subst0 
(minus i h) u (THead k t t0) t3)))) (eq_ind T (lift h d (THead k t x1)) 
(\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda 
(t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) (let H9 \def (eq_ind_r 
nat (minus (s k i) h) (\lambda (n: nat).(subst0 n u t0 x1)) H8 (s k (minus i 
h)) (s_minus k i h (le_trans_plus_r d h i H2))) in (ex_intro2 T (\lambda (t2: 
T).(eq T (lift h d (THead k t x1)) (lift h d t2))) (\lambda (t2: T).(subst0 
(minus i h) u (THead k t t0) t2)) (THead k t x1) (refl_equal T (lift h d 
(THead k t x1))) (subst0_snd k u x1 t0 (minus i h) H9 t))) (THead k (lift h d 
t) (lift h (s k d) x1)) (lift_head k t x1 h d)) x0 H7)))) (H0 x0 (s k i) h (s 
k d) H6 (eq_ind nat (s k (plus d h)) (\lambda (n: nat).(le n (s k i))) (s_le 
k (plus d h) i H2) (plus (s k d) h) (s_plus k d h)))) x H5)))) H4)) (\lambda 
(H4: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u (lift h d t) u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) t0) t2))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda 
(u2: T).(\lambda (_: T).(subst0 i u (lift h d t) u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s k i) u (lift h (s k d) t0) t2))) (ex2 T 
(\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) 
u (THead k t t0) t2))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T 
x (THead k x0 x1))).(\lambda (H6: (subst0 i u (lift h d t) x0)).(\lambda (H7: 
(subst0 (s k i) u (lift h (s k d) t0) x1)).(eq_ind_r T (THead k x0 x1) 
(\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda 
(t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) (ex2_ind T (\lambda (t2: 
T).(eq T x1 (lift h (s k d) t2))) (\lambda (t2: T).(subst0 (minus (s k i) h) 
u t0 t2)) (ex2 T (\lambda (t2: T).(eq T (THead k x0 x1) (lift h d t2))) 
(\lambda (t2: T).(subst0 (minus i h) u (THead k t t0) t2))) (\lambda (x2: 
T).(\lambda (H8: (eq T x1 (lift h (s k d) x2))).(\lambda (H9: (subst0 (minus 
(s k i) h) u t0 x2)).(ex2_ind T (\lambda (t2: T).(eq T x0 (lift h d t2))) 
(\lambda (t2: T).(subst0 (minus i h) u t t2)) (ex2 T (\lambda (t2: T).(eq T 
(THead k x0 x1) (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u (THead 
k t t0) t2))) (\lambda (x3: T).(\lambda (H10: (eq T x0 (lift h d 
x3))).(\lambda (H11: (subst0 (minus i h) u t x3)).(eq_ind_r T (lift h d x3) 
(\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead k t2 x1) (lift h d 
t3))) (\lambda (t3: T).(subst0 (minus i h) u (THead k t t0) t3)))) (eq_ind_r 
T (lift h (s k d) x2) (\lambda (t2: T).(ex2 T (\lambda (t3: T).(eq T (THead k 
(lift h d x3) t2) (lift h d t3))) (\lambda (t3: T).(subst0 (minus i h) u 
(THead k t t0) t3)))) (eq_ind T (lift h d (THead k x3 x2)) (\lambda (t2: 
T).(ex2 T (\lambda (t3: T).(eq T t2 (lift h d t3))) (\lambda (t3: T).(subst0 
(minus i h) u (THead k t t0) t3)))) (let H12 \def (eq_ind_r nat (minus (s k 
i) h) (\lambda (n: nat).(subst0 n u t0 x2)) H9 (s k (minus i h)) (s_minus k i 
h (le_trans_plus_r d h i H2))) in (ex_intro2 T (\lambda (t2: T).(eq T (lift h 
d (THead k x3 x2)) (lift h d t2))) (\lambda (t2: T).(subst0 (minus i h) u 
(THead k t t0) t2)) (THead k x3 x2) (refl_equal T (lift h d (THead k x3 x2))) 
(subst0_both u t x3 (minus i h) H11 k t0 x2 H12))) (THead k (lift h d x3) 
(lift h (s k d) x2)) (lift_head k x3 x2 h d)) x1 H8) x0 H10)))) (H x0 i h d 
H6 H2))))) (H0 x1 (s k i) h (s k d) H7 (eq_ind nat (s k (plus d h)) (\lambda 
(n: nat).(le n (s k i))) (s_le k (plus d h) i H2) (plus (s k d) h) (s_plus k 
d h)))) x H5)))))) H4)) (subst0_gen_head k u (lift h d t) (lift h (s k d) t0) 
x i H3)))))))))))))) t1)).

