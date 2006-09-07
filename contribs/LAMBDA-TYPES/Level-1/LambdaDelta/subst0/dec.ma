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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/dec".

include "subst0/defs.ma".

include "lift/props.ma".

theorem dnf_dec:
 \forall (w: T).(\forall (t: T).(\forall (d: nat).(ex T (\lambda (v: T).(or 
(subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d v)))))))
\def
 \lambda (w: T).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: nat).(ex 
T (\lambda (v: T).(or (subst0 d w t0 (lift (S O) d v)) (eq T t0 (lift (S O) d 
v))))))) (\lambda (n: nat).(\lambda (d: nat).(ex_intro T (\lambda (v: T).(or 
(subst0 d w (TSort n) (lift (S O) d v)) (eq T (TSort n) (lift (S O) d v)))) 
(TSort n) (eq_ind_r T (TSort n) (\lambda (t0: T).(or (subst0 d w (TSort n) 
t0) (eq T (TSort n) t0))) (or_intror (subst0 d w (TSort n) (TSort n)) (eq T 
(TSort n) (TSort n)) (refl_equal T (TSort n))) (lift (S O) d (TSort n)) 
(lift_sort n (S O) d))))) (\lambda (n: nat).(\lambda (d: nat).(lt_eq_gt_e n d 
(ex T (\lambda (v: T).(or (subst0 d w (TLRef n) (lift (S O) d v)) (eq T 
(TLRef n) (lift (S O) d v))))) (\lambda (H: (lt n d)).(ex_intro T (\lambda 
(v: T).(or (subst0 d w (TLRef n) (lift (S O) d v)) (eq T (TLRef n) (lift (S 
O) d v)))) (TLRef n) (eq_ind_r T (TLRef n) (\lambda (t0: T).(or (subst0 d w 
(TLRef n) t0) (eq T (TLRef n) t0))) (or_intror (subst0 d w (TLRef n) (TLRef 
n)) (eq T (TLRef n) (TLRef n)) (refl_equal T (TLRef n))) (lift (S O) d (TLRef 
n)) (lift_lref_lt n (S O) d H)))) (\lambda (H: (eq nat n d)).(eq_ind nat n 
(\lambda (n0: nat).(ex T (\lambda (v: T).(or (subst0 n0 w (TLRef n) (lift (S 
O) n0 v)) (eq T (TLRef n) (lift (S O) n0 v)))))) (ex_intro T (\lambda (v: 
T).(or (subst0 n w (TLRef n) (lift (S O) n v)) (eq T (TLRef n) (lift (S O) n 
v)))) (lift n O w) (eq_ind_r T (lift (plus (S O) n) O w) (\lambda (t0: T).(or 
(subst0 n w (TLRef n) t0) (eq T (TLRef n) t0))) (or_introl (subst0 n w (TLRef 
n) (lift (S n) O w)) (eq T (TLRef n) (lift (S n) O w)) (subst0_lref w n)) 
(lift (S O) n (lift n O w)) (lift_free w n (S O) O n (le_n (plus O n)) 
(le_O_n n)))) d H)) (\lambda (H: (lt d n)).(ex_intro T (\lambda (v: T).(or 
(subst0 d w (TLRef n) (lift (S O) d v)) (eq T (TLRef n) (lift (S O) d v)))) 
(TLRef (pred n)) (eq_ind_r T (TLRef n) (\lambda (t0: T).(or (subst0 d w 
(TLRef n) t0) (eq T (TLRef n) t0))) (or_intror (subst0 d w (TLRef n) (TLRef 
n)) (eq T (TLRef n) (TLRef n)) (refl_equal T (TLRef n))) (lift (S O) d (TLRef 
(pred n))) (lift_lref_gt d n H))))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (d: nat).(ex T (\lambda (v: T).(or (subst0 d w t0 
(lift (S O) d v)) (eq T t0 (lift (S O) d v)))))))).(\lambda (t1: T).(\lambda 
(H0: ((\forall (d: nat).(ex T (\lambda (v: T).(or (subst0 d w t1 (lift (S O) 
d v)) (eq T t1 (lift (S O) d v)))))))).(\lambda (d: nat).(let H_x \def (H d) 
in (let H1 \def H_x in (ex_ind T (\lambda (v: T).(or (subst0 d w t0 (lift (S 
O) d v)) (eq T t0 (lift (S O) d v)))) (ex T (\lambda (v: T).(or (subst0 d w 
(THead k t0 t1) (lift (S O) d v)) (eq T (THead k t0 t1) (lift (S O) d v))))) 
(\lambda (x: T).(\lambda (H2: (or (subst0 d w t0 (lift (S O) d x)) (eq T t0 
(lift (S O) d x)))).(or_ind (subst0 d w t0 (lift (S O) d x)) (eq T t0 (lift 
(S O) d x)) (ex T (\lambda (v: T).(or (subst0 d w (THead k t0 t1) (lift (S O) 
d v)) (eq T (THead k t0 t1) (lift (S O) d v))))) (\lambda (H3: (subst0 d w t0 
(lift (S O) d x))).(let H_x0 \def (H0 (s k d)) in (let H4 \def H_x0 in 
(ex_ind T (\lambda (v: T).(or (subst0 (s k d) w t1 (lift (S O) (s k d) v)) 
(eq T t1 (lift (S O) (s k d) v)))) (ex T (\lambda (v: T).(or (subst0 d w 
(THead k t0 t1) (lift (S O) d v)) (eq T (THead k t0 t1) (lift (S O) d v))))) 
(\lambda (x0: T).(\lambda (H5: (or (subst0 (s k d) w t1 (lift (S O) (s k d) 
x0)) (eq T t1 (lift (S O) (s k d) x0)))).(or_ind (subst0 (s k d) w t1 (lift 
(S O) (s k d) x0)) (eq T t1 (lift (S O) (s k d) x0)) (ex T (\lambda (v: 
T).(or (subst0 d w (THead k t0 t1) (lift (S O) d v)) (eq T (THead k t0 t1) 
(lift (S O) d v))))) (\lambda (H6: (subst0 (s k d) w t1 (lift (S O) (s k d) 
x0))).(ex_intro T (\lambda (v: T).(or (subst0 d w (THead k t0 t1) (lift (S O) 
d v)) (eq T (THead k t0 t1) (lift (S O) d v)))) (THead k x x0) (eq_ind_r T 
(THead k (lift (S O) d x) (lift (S O) (s k d) x0)) (\lambda (t2: T).(or 
(subst0 d w (THead k t0 t1) t2) (eq T (THead k t0 t1) t2))) (or_introl 
(subst0 d w (THead k t0 t1) (THead k (lift (S O) d x) (lift (S O) (s k d) 
x0))) (eq T (THead k t0 t1) (THead k (lift (S O) d x) (lift (S O) (s k d) 
x0))) (subst0_both w t0 (lift (S O) d x) d H3 k t1 (lift (S O) (s k d) x0) 
H6)) (lift (S O) d (THead k x x0)) (lift_head k x x0 (S O) d)))) (\lambda 
(H6: (eq T t1 (lift (S O) (s k d) x0))).(eq_ind_r T (lift (S O) (s k d) x0) 
(\lambda (t2: T).(ex T (\lambda (v: T).(or (subst0 d w (THead k t0 t2) (lift 
(S O) d v)) (eq T (THead k t0 t2) (lift (S O) d v)))))) (ex_intro T (\lambda 
(v: T).(or (subst0 d w (THead k t0 (lift (S O) (s k d) x0)) (lift (S O) d v)) 
(eq T (THead k t0 (lift (S O) (s k d) x0)) (lift (S O) d v)))) (THead k x x0) 
(eq_ind_r T (THead k (lift (S O) d x) (lift (S O) (s k d) x0)) (\lambda (t2: 
T).(or (subst0 d w (THead k t0 (lift (S O) (s k d) x0)) t2) (eq T (THead k t0 
(lift (S O) (s k d) x0)) t2))) (or_introl (subst0 d w (THead k t0 (lift (S O) 
(s k d) x0)) (THead k (lift (S O) d x) (lift (S O) (s k d) x0))) (eq T (THead 
k t0 (lift (S O) (s k d) x0)) (THead k (lift (S O) d x) (lift (S O) (s k d) 
x0))) (subst0_fst w (lift (S O) d x) t0 d H3 (lift (S O) (s k d) x0) k)) 
(lift (S O) d (THead k x x0)) (lift_head k x x0 (S O) d))) t1 H6)) H5))) 
H4)))) (\lambda (H3: (eq T t0 (lift (S O) d x))).(let H_x0 \def (H0 (s k d)) 
in (let H4 \def H_x0 in (ex_ind T (\lambda (v: T).(or (subst0 (s k d) w t1 
(lift (S O) (s k d) v)) (eq T t1 (lift (S O) (s k d) v)))) (ex T (\lambda (v: 
T).(or (subst0 d w (THead k t0 t1) (lift (S O) d v)) (eq T (THead k t0 t1) 
(lift (S O) d v))))) (\lambda (x0: T).(\lambda (H5: (or (subst0 (s k d) w t1 
(lift (S O) (s k d) x0)) (eq T t1 (lift (S O) (s k d) x0)))).(or_ind (subst0 
(s k d) w t1 (lift (S O) (s k d) x0)) (eq T t1 (lift (S O) (s k d) x0)) (ex T 
(\lambda (v: T).(or (subst0 d w (THead k t0 t1) (lift (S O) d v)) (eq T 
(THead k t0 t1) (lift (S O) d v))))) (\lambda (H6: (subst0 (s k d) w t1 (lift 
(S O) (s k d) x0))).(eq_ind_r T (lift (S O) d x) (\lambda (t2: T).(ex T 
(\lambda (v: T).(or (subst0 d w (THead k t2 t1) (lift (S O) d v)) (eq T 
(THead k t2 t1) (lift (S O) d v)))))) (ex_intro T (\lambda (v: T).(or (subst0 
d w (THead k (lift (S O) d x) t1) (lift (S O) d v)) (eq T (THead k (lift (S 
O) d x) t1) (lift (S O) d v)))) (THead k x x0) (eq_ind_r T (THead k (lift (S 
O) d x) (lift (S O) (s k d) x0)) (\lambda (t2: T).(or (subst0 d w (THead k 
(lift (S O) d x) t1) t2) (eq T (THead k (lift (S O) d x) t1) t2))) (or_introl 
(subst0 d w (THead k (lift (S O) d x) t1) (THead k (lift (S O) d x) (lift (S 
O) (s k d) x0))) (eq T (THead k (lift (S O) d x) t1) (THead k (lift (S O) d 
x) (lift (S O) (s k d) x0))) (subst0_snd k w (lift (S O) (s k d) x0) t1 d H6 
(lift (S O) d x))) (lift (S O) d (THead k x x0)) (lift_head k x x0 (S O) d))) 
t0 H3)) (\lambda (H6: (eq T t1 (lift (S O) (s k d) x0))).(eq_ind_r T (lift (S 
O) (s k d) x0) (\lambda (t2: T).(ex T (\lambda (v: T).(or (subst0 d w (THead 
k t0 t2) (lift (S O) d v)) (eq T (THead k t0 t2) (lift (S O) d v)))))) 
(eq_ind_r T (lift (S O) d x) (\lambda (t2: T).(ex T (\lambda (v: T).(or 
(subst0 d w (THead k t2 (lift (S O) (s k d) x0)) (lift (S O) d v)) (eq T 
(THead k t2 (lift (S O) (s k d) x0)) (lift (S O) d v)))))) (ex_intro T 
(\lambda (v: T).(or (subst0 d w (THead k (lift (S O) d x) (lift (S O) (s k d) 
x0)) (lift (S O) d v)) (eq T (THead k (lift (S O) d x) (lift (S O) (s k d) 
x0)) (lift (S O) d v)))) (THead k x x0) (eq_ind_r T (THead k (lift (S O) d x) 
(lift (S O) (s k d) x0)) (\lambda (t2: T).(or (subst0 d w (THead k (lift (S 
O) d x) (lift (S O) (s k d) x0)) t2) (eq T (THead k (lift (S O) d x) (lift (S 
O) (s k d) x0)) t2))) (or_intror (subst0 d w (THead k (lift (S O) d x) (lift 
(S O) (s k d) x0)) (THead k (lift (S O) d x) (lift (S O) (s k d) x0))) (eq T 
(THead k (lift (S O) d x) (lift (S O) (s k d) x0)) (THead k (lift (S O) d x) 
(lift (S O) (s k d) x0))) (refl_equal T (THead k (lift (S O) d x) (lift (S O) 
(s k d) x0)))) (lift (S O) d (THead k x x0)) (lift_head k x x0 (S O) d))) t0 
H3) t1 H6)) H5))) H4)))) H2))) H1))))))))) t)).

