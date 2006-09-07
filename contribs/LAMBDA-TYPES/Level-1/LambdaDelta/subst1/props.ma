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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst1/props".

include "subst1/defs.ma".

include "subst0/props.ma".

theorem subst1_head:
 \forall (v: T).(\forall (u1: T).(\forall (u2: T).(\forall (i: nat).((subst1 
i v u1 u2) \to (\forall (k: K).(\forall (t1: T).(\forall (t2: T).((subst1 (s 
k i) v t1 t2) \to (subst1 i v (THead k u1 t1) (THead k u2 t2))))))))))
\def
 \lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i v u1 u2)).(subst1_ind i v u1 (\lambda (t: T).(\forall (k: 
K).(\forall (t1: T).(\forall (t2: T).((subst1 (s k i) v t1 t2) \to (subst1 i 
v (THead k u1 t1) (THead k t t2))))))) (\lambda (k: K).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (subst1 (s k i) v t1 t2)).(subst1_ind (s k 
i) v t1 (\lambda (t: T).(subst1 i v (THead k u1 t1) (THead k u1 t))) 
(subst1_refl i v (THead k u1 t1)) (\lambda (t3: T).(\lambda (H1: (subst0 (s k 
i) v t1 t3)).(subst1_single i v (THead k u1 t1) (THead k u1 t3) (subst0_snd k 
v t3 t1 i H1 u1)))) t2 H0))))) (\lambda (t2: T).(\lambda (H0: (subst0 i v u1 
t2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t0: T).(\lambda (H1: (subst1 
(s k i) v t1 t0)).(subst1_ind (s k i) v t1 (\lambda (t: T).(subst1 i v (THead 
k u1 t1) (THead k t2 t))) (subst1_single i v (THead k u1 t1) (THead k t2 t1) 
(subst0_fst v t2 u1 i H0 t1 k)) (\lambda (t3: T).(\lambda (H2: (subst0 (s k 
i) v t1 t3)).(subst1_single i v (THead k u1 t1) (THead k t2 t3) (subst0_both 
v u1 t2 i H0 k t1 t3 H2)))) t0 H1))))))) u2 H))))).

theorem subst1_lift_lt:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst1 
i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst1 i 
(lift h (minus d (S i)) u) (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u t1 t2)).(subst1_ind i u t1 (\lambda (t: T).(\forall (d: 
nat).((lt i d) \to (\forall (h: nat).(subst1 i (lift h (minus d (S i)) u) 
(lift h d t1) (lift h d t)))))) (\lambda (d: nat).(\lambda (_: (lt i 
d)).(\lambda (h: nat).(subst1_refl i (lift h (minus d (S i)) u) (lift h d 
t1))))) (\lambda (t3: T).(\lambda (H0: (subst0 i u t1 t3)).(\lambda (d: 
nat).(\lambda (H1: (lt i d)).(\lambda (h: nat).(subst1_single i (lift h 
(minus d (S i)) u) (lift h d t1) (lift h d t3) (subst0_lift_lt t1 t3 u i H0 d 
H1 h))))))) t2 H))))).

theorem subst1_lift_ge:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall 
(h: nat).((subst1 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst1 
(plus i h) u (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (H: (subst1 i u t1 t2)).(subst1_ind i u t1 (\lambda (t: 
T).(\forall (d: nat).((le d i) \to (subst1 (plus i h) u (lift h d t1) (lift h 
d t))))) (\lambda (d: nat).(\lambda (_: (le d i)).(subst1_refl (plus i h) u 
(lift h d t1)))) (\lambda (t3: T).(\lambda (H0: (subst0 i u t1 t3)).(\lambda 
(d: nat).(\lambda (H1: (le d i)).(subst1_single (plus i h) u (lift h d t1) 
(lift h d t3) (subst0_lift_ge t1 t3 u i h H0 d H1)))))) t2 H)))))).

theorem subst1_ex:
 \forall (u: T).(\forall (t1: T).(\forall (d: nat).(ex T (\lambda (t2: 
T).(subst1 d u t1 (lift (S O) d t2))))))
\def
 \lambda (u: T).(\lambda (t1: T).(T_ind (\lambda (t: T).(\forall (d: nat).(ex 
T (\lambda (t2: T).(subst1 d u t (lift (S O) d t2)))))) (\lambda (n: 
nat).(\lambda (d: nat).(ex_intro T (\lambda (t2: T).(subst1 d u (TSort n) 
(lift (S O) d t2))) (TSort n) (eq_ind_r T (TSort n) (\lambda (t: T).(subst1 d 
u (TSort n) t)) (subst1_refl d u (TSort n)) (lift (S O) d (TSort n)) 
(lift_sort n (S O) d))))) (\lambda (n: nat).(\lambda (d: nat).(lt_eq_gt_e n d 
(ex T (\lambda (t2: T).(subst1 d u (TLRef n) (lift (S O) d t2)))) (\lambda 
(H: (lt n d)).(ex_intro T (\lambda (t2: T).(subst1 d u (TLRef n) (lift (S O) 
d t2))) (TLRef n) (eq_ind_r T (TLRef n) (\lambda (t: T).(subst1 d u (TLRef n) 
t)) (subst1_refl d u (TLRef n)) (lift (S O) d (TLRef n)) (lift_lref_lt n (S 
O) d H)))) (\lambda (H: (eq nat n d)).(eq_ind nat n (\lambda (n0: nat).(ex T 
(\lambda (t2: T).(subst1 n0 u (TLRef n) (lift (S O) n0 t2))))) (ex_intro T 
(\lambda (t2: T).(subst1 n u (TLRef n) (lift (S O) n t2))) (lift n O u) 
(eq_ind_r T (lift (plus (S O) n) O u) (\lambda (t: T).(subst1 n u (TLRef n) 
t)) (subst1_single n u (TLRef n) (lift (S n) O u) (subst0_lref u n)) (lift (S 
O) n (lift n O u)) (lift_free u n (S O) O n (le_n (plus O n)) (le_O_n n)))) d 
H)) (\lambda (H: (lt d n)).(ex_intro T (\lambda (t2: T).(subst1 d u (TLRef n) 
(lift (S O) d t2))) (TLRef (pred n)) (eq_ind_r T (TLRef n) (\lambda (t: 
T).(subst1 d u (TLRef n) t)) (subst1_refl d u (TLRef n)) (lift (S O) d (TLRef 
(pred n))) (lift_lref_gt d n H))))))) (\lambda (k: K).(\lambda (t: 
T).(\lambda (H: ((\forall (d: nat).(ex T (\lambda (t2: T).(subst1 d u t (lift 
(S O) d t2))))))).(\lambda (t0: T).(\lambda (H0: ((\forall (d: nat).(ex T 
(\lambda (t2: T).(subst1 d u t0 (lift (S O) d t2))))))).(\lambda (d: 
nat).(let H_x \def (H d) in (let H1 \def H_x in (ex_ind T (\lambda (t2: 
T).(subst1 d u t (lift (S O) d t2))) (ex T (\lambda (t2: T).(subst1 d u 
(THead k t t0) (lift (S O) d t2)))) (\lambda (x: T).(\lambda (H2: (subst1 d u 
t (lift (S O) d x))).(let H_x0 \def (H0 (s k d)) in (let H3 \def H_x0 in 
(ex_ind T (\lambda (t2: T).(subst1 (s k d) u t0 (lift (S O) (s k d) t2))) (ex 
T (\lambda (t2: T).(subst1 d u (THead k t t0) (lift (S O) d t2)))) (\lambda 
(x0: T).(\lambda (H4: (subst1 (s k d) u t0 (lift (S O) (s k d) 
x0))).(ex_intro T (\lambda (t2: T).(subst1 d u (THead k t t0) (lift (S O) d 
t2))) (THead k x x0) (eq_ind_r T (THead k (lift (S O) d x) (lift (S O) (s k 
d) x0)) (\lambda (t2: T).(subst1 d u (THead k t t0) t2)) (subst1_head u t 
(lift (S O) d x) d H2 k t0 (lift (S O) (s k d) x0) H4) (lift (S O) d (THead k 
x x0)) (lift_head k x x0 (S O) d))))) H3))))) H1))))))))) t1)).

