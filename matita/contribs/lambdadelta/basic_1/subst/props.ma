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

include "Basic-1/subst/fwd.ma".

include "Basic-1/subst0/defs.ma".

include "Basic-1/lift/props.ma".

theorem subst_lift_SO:
 \forall (v: T).(\forall (t: T).(\forall (d: nat).(eq T (subst d v (lift (S 
O) d t)) t)))
\def
 \lambda (v: T).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: nat).(eq 
T (subst d v (lift (S O) d t0)) t0))) (\lambda (n: nat).(\lambda (d: 
nat).(eq_ind_r T (TSort n) (\lambda (t0: T).(eq T (subst d v t0) (TSort n))) 
(eq_ind_r T (TSort n) (\lambda (t0: T).(eq T t0 (TSort n))) (refl_equal T 
(TSort n)) (subst d v (TSort n)) (subst_sort v d n)) (lift (S O) d (TSort n)) 
(lift_sort n (S O) d)))) (\lambda (n: nat).(\lambda (d: nat).(lt_le_e n d (eq 
T (subst d v (lift (S O) d (TLRef n))) (TLRef n)) (\lambda (H: (lt n 
d)).(eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T (subst d v t0) (TLRef n))) 
(eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T t0 (TLRef n))) (refl_equal T 
(TLRef n)) (subst d v (TLRef n)) (subst_lref_lt v d n H)) (lift (S O) d 
(TLRef n)) (lift_lref_lt n (S O) d H))) (\lambda (H: (le d n)).(eq_ind_r T 
(TLRef (plus n (S O))) (\lambda (t0: T).(eq T (subst d v t0) (TLRef n))) 
(eq_ind nat (S (plus n O)) (\lambda (n0: nat).(eq T (subst d v (TLRef n0)) 
(TLRef n))) (eq_ind_r T (TLRef (pred (S (plus n O)))) (\lambda (t0: T).(eq T 
t0 (TLRef n))) (eq_ind nat (plus n O) (\lambda (n0: nat).(eq T (TLRef n0) 
(TLRef n))) (f_equal nat T TLRef (plus n O) n (sym_eq nat n (plus n O) 
(plus_n_O n))) (pred (S (plus n O))) (pred_Sn (plus n O))) (subst d v (TLRef 
(S (plus n O)))) (subst_lref_gt v d (S (plus n O)) (le_n_S d (plus n O) 
(le_plus_trans d n O H)))) (plus n (S O)) (plus_n_Sm n O)) (lift (S O) d 
(TLRef n)) (lift_lref_ge n (S O) d H)))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (d: nat).(eq T (subst d v (lift (S O) d t0)) 
t0)))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: nat).(eq T (subst d v 
(lift (S O) d t1)) t1)))).(\lambda (d: nat).(eq_ind_r T (THead k (lift (S O) 
d t0) (lift (S O) (s k d) t1)) (\lambda (t2: T).(eq T (subst d v t2) (THead k 
t0 t1))) (eq_ind_r T (THead k (subst d v (lift (S O) d t0)) (subst (s k d) v 
(lift (S O) (s k d) t1))) (\lambda (t2: T).(eq T t2 (THead k t0 t1))) 
(f_equal3 K T T T THead k k (subst d v (lift (S O) d t0)) t0 (subst (s k d) v 
(lift (S O) (s k d) t1)) t1 (refl_equal K k) (H d) (H0 (s k d))) (subst d v 
(THead k (lift (S O) d t0) (lift (S O) (s k d) t1))) (subst_head k v (lift (S 
O) d t0) (lift (S O) (s k d) t1) d)) (lift (S O) d (THead k t0 t1)) 
(lift_head k t0 t1 (S O) d)))))))) t)).
(* COMMENTS
Initial nodes: 879
END *)

theorem subst_subst0:
 \forall (v: T).(\forall (t1: T).(\forall (t2: T).(\forall (d: nat).((subst0 
d v t1 t2) \to (eq T (subst d v t1) (subst d v t2))))))
\def
 \lambda (v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (d: nat).(\lambda 
(H: (subst0 d v t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(eq T (subst n t t0) (subst n t t3)))))) 
(\lambda (v0: T).(\lambda (i: nat).(eq_ind_r T (lift i O v0) (\lambda (t: 
T).(eq T t (subst i v0 (lift (S i) O v0)))) (eq_ind nat (plus (S O) i) 
(\lambda (n: nat).(eq T (lift i O v0) (subst i v0 (lift n O v0)))) (eq_ind T 
(lift (S O) i (lift i O v0)) (\lambda (t: T).(eq T (lift i O v0) (subst i v0 
t))) (eq_ind_r T (lift i O v0) (\lambda (t: T).(eq T (lift i O v0) t)) 
(refl_equal T (lift i O v0)) (subst i v0 (lift (S O) i (lift i O v0))) 
(subst_lift_SO v0 (lift i O v0) i)) (lift (plus (S O) i) O v0) (lift_free v0 
i (S O) O i (le_n (plus O i)) (le_O_n i))) (S i) (refl_equal nat (S i))) 
(subst i v0 (TLRef i)) (subst_lref_eq v0 i)))) (\lambda (v0: T).(\lambda (u2: 
T).(\lambda (u1: T).(\lambda (i: nat).(\lambda (_: (subst0 i v0 u1 
u2)).(\lambda (H1: (eq T (subst i v0 u1) (subst i v0 u2))).(\lambda (t: 
T).(\lambda (k: K).(eq_ind_r T (THead k (subst i v0 u1) (subst (s k i) v0 t)) 
(\lambda (t0: T).(eq T t0 (subst i v0 (THead k u2 t)))) (eq_ind_r T (THead k 
(subst i v0 u2) (subst (s k i) v0 t)) (\lambda (t0: T).(eq T (THead k (subst 
i v0 u1) (subst (s k i) v0 t)) t0)) (eq_ind_r T (subst i v0 u2) (\lambda (t0: 
T).(eq T (THead k t0 (subst (s k i) v0 t)) (THead k (subst i v0 u2) (subst (s 
k i) v0 t)))) (refl_equal T (THead k (subst i v0 u2) (subst (s k i) v0 t))) 
(subst i v0 u1) H1) (subst i v0 (THead k u2 t)) (subst_head k v0 u2 t i)) 
(subst i v0 (THead k u1 t)) (subst_head k v0 u1 t i)))))))))) (\lambda (k: 
K).(\lambda (v0: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (i: 
nat).(\lambda (_: (subst0 (s k i) v0 t4 t3)).(\lambda (H1: (eq T (subst (s k 
i) v0 t4) (subst (s k i) v0 t3))).(\lambda (u: T).(eq_ind_r T (THead k (subst 
i v0 u) (subst (s k i) v0 t4)) (\lambda (t: T).(eq T t (subst i v0 (THead k u 
t3)))) (eq_ind_r T (THead k (subst i v0 u) (subst (s k i) v0 t3)) (\lambda 
(t: T).(eq T (THead k (subst i v0 u) (subst (s k i) v0 t4)) t)) (eq_ind_r T 
(subst (s k i) v0 t3) (\lambda (t: T).(eq T (THead k (subst i v0 u) t) (THead 
k (subst i v0 u) (subst (s k i) v0 t3)))) (refl_equal T (THead k (subst i v0 
u) (subst (s k i) v0 t3))) (subst (s k i) v0 t4) H1) (subst i v0 (THead k u 
t3)) (subst_head k v0 u t3 i)) (subst i v0 (THead k u t4)) (subst_head k v0 u 
t4 i)))))))))) (\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(i: nat).(\lambda (_: (subst0 i v0 u1 u2)).(\lambda (H1: (eq T (subst i v0 
u1) (subst i v0 u2))).(\lambda (k: K).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (subst0 (s k i) v0 t3 t4)).(\lambda (H3: (eq T (subst (s k i) 
v0 t3) (subst (s k i) v0 t4))).(eq_ind_r T (THead k (subst i v0 u1) (subst (s 
k i) v0 t3)) (\lambda (t: T).(eq T t (subst i v0 (THead k u2 t4)))) (eq_ind_r 
T (THead k (subst i v0 u2) (subst (s k i) v0 t4)) (\lambda (t: T).(eq T 
(THead k (subst i v0 u1) (subst (s k i) v0 t3)) t)) (eq_ind_r T (subst i v0 
u2) (\lambda (t: T).(eq T (THead k t (subst (s k i) v0 t3)) (THead k (subst i 
v0 u2) (subst (s k i) v0 t4)))) (eq_ind_r T (subst (s k i) v0 t4) (\lambda 
(t: T).(eq T (THead k (subst i v0 u2) t) (THead k (subst i v0 u2) (subst (s k 
i) v0 t4)))) (refl_equal T (THead k (subst i v0 u2) (subst (s k i) v0 t4))) 
(subst (s k i) v0 t3) H3) (subst i v0 u1) H1) (subst i v0 (THead k u2 t4)) 
(subst_head k v0 u2 t4 i)) (subst i v0 (THead k u1 t3)) (subst_head k v0 u1 
t3 i))))))))))))) d v t1 t2 H))))).
(* COMMENTS
Initial nodes: 1363
END *)

