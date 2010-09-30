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

include "Basic-1/subst0/defs.ma".

include "Basic-1/lift/props.ma".

theorem dnf_dec2:
 \forall (t: T).(\forall (d: nat).(or (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w t (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t (lift (S 
O) d v))))))
\def
 \lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: nat).(or (\forall (w: 
T).(ex T (\lambda (v: T).(subst0 d w t0 (lift (S O) d v))))) (ex T (\lambda 
(v: T).(eq T t0 (lift (S O) d v))))))) (\lambda (n: nat).(\lambda (d: 
nat).(or_intror (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (TSort n) 
(lift (S O) d v))))) (ex T (\lambda (v: T).(eq T (TSort n) (lift (S O) d 
v)))) (ex_intro T (\lambda (v: T).(eq T (TSort n) (lift (S O) d v))) (TSort 
n) (eq_ind_r T (TSort n) (\lambda (t0: T).(eq T (TSort n) t0)) (refl_equal T 
(TSort n)) (lift (S O) d (TSort n)) (lift_sort n (S O) d)))))) (\lambda (n: 
nat).(\lambda (d: nat).(lt_eq_gt_e n d (or (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w (TLRef n) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T 
(TLRef n) (lift (S O) d v))))) (\lambda (H: (lt n d)).(or_intror (\forall (w: 
T).(ex T (\lambda (v: T).(subst0 d w (TLRef n) (lift (S O) d v))))) (ex T 
(\lambda (v: T).(eq T (TLRef n) (lift (S O) d v)))) (ex_intro T (\lambda (v: 
T).(eq T (TLRef n) (lift (S O) d v))) (TLRef n) (eq_ind_r T (TLRef n) 
(\lambda (t0: T).(eq T (TLRef n) t0)) (refl_equal T (TLRef n)) (lift (S O) d 
(TLRef n)) (lift_lref_lt n (S O) d H))))) (\lambda (H: (eq nat n d)).(eq_ind 
nat n (\lambda (n0: nat).(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 n0 
w (TLRef n) (lift (S O) n0 v))))) (ex T (\lambda (v: T).(eq T (TLRef n) (lift 
(S O) n0 v)))))) (or_introl (\forall (w: T).(ex T (\lambda (v: T).(subst0 n w 
(TLRef n) (lift (S O) n v))))) (ex T (\lambda (v: T).(eq T (TLRef n) (lift (S 
O) n v)))) (\lambda (w: T).(ex_intro T (\lambda (v: T).(subst0 n w (TLRef n) 
(lift (S O) n v))) (lift n O w) (eq_ind_r T (lift (plus (S O) n) O w) 
(\lambda (t0: T).(subst0 n w (TLRef n) t0)) (subst0_lref w n) (lift (S O) n 
(lift n O w)) (lift_free w n (S O) O n (le_n (plus O n)) (le_O_n n)))))) d 
H)) (\lambda (H: (lt d n)).(or_intror (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w (TLRef n) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T 
(TLRef n) (lift (S O) d v)))) (ex_intro T (\lambda (v: T).(eq T (TLRef n) 
(lift (S O) d v))) (TLRef (pred n)) (eq_ind_r T (TLRef n) (\lambda (t0: 
T).(eq T (TLRef n) t0)) (refl_equal T (TLRef n)) (lift (S O) d (TLRef (pred 
n))) (lift_lref_gt d n H)))))))) (\lambda (k: K).(\lambda (t0: T).(\lambda 
(H: ((\forall (d: nat).(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w 
t0 (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t0 (lift (S O) d 
v)))))))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: nat).(or (\forall (w: 
T).(ex T (\lambda (v: T).(subst0 d w t1 (lift (S O) d v))))) (ex T (\lambda 
(v: T).(eq T t1 (lift (S O) d v)))))))).(\lambda (d: nat).(let H_x \def (H d) 
in (let H1 \def H_x in (or_ind (\forall (w: T).(ex T (\lambda (v: T).(subst0 
d w t0 (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t0 (lift (S O) d 
v)))) (or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) 
(lift (S O) d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 t1) (lift (S O) 
d v))))) (\lambda (H2: ((\forall (w: T).(ex T (\lambda (v: T).(subst0 d w t0 
(lift (S O) d v))))))).(let H_x0 \def (H0 (s k d)) in (let H3 \def H_x0 in 
(or_ind (\forall (w: T).(ex T (\lambda (v: T).(subst0 (s k d) w t1 (lift (S 
O) (s k d) v))))) (ex T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) v)))) 
(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) (lift 
(S O) d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 t1) (lift (S O) d 
v))))) (\lambda (H4: ((\forall (w: T).(ex T (\lambda (v: T).(subst0 (s k d) w 
t1 (lift (S O) (s k d) v))))))).(or_introl (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w (THead k t0 t1) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq 
T (THead k t0 t1) (lift (S O) d v)))) (\lambda (w: T).(let H_x1 \def (H4 w) 
in (let H5 \def H_x1 in (ex_ind T (\lambda (v: T).(subst0 (s k d) w t1 (lift 
(S O) (s k d) v))) (ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) (lift (S 
O) d v)))) (\lambda (x: T).(\lambda (H6: (subst0 (s k d) w t1 (lift (S O) (s 
k d) x))).(let H_x2 \def (H2 w) in (let H7 \def H_x2 in (ex_ind T (\lambda 
(v: T).(subst0 d w t0 (lift (S O) d v))) (ex T (\lambda (v: T).(subst0 d w 
(THead k t0 t1) (lift (S O) d v)))) (\lambda (x0: T).(\lambda (H8: (subst0 d 
w t0 (lift (S O) d x0))).(ex_intro T (\lambda (v: T).(subst0 d w (THead k t0 
t1) (lift (S O) d v))) (THead k x0 x) (eq_ind_r T (THead k (lift (S O) d x0) 
(lift (S O) (s k d) x)) (\lambda (t2: T).(subst0 d w (THead k t0 t1) t2)) 
(subst0_both w t0 (lift (S O) d x0) d H8 k t1 (lift (S O) (s k d) x) H6) 
(lift (S O) d (THead k x0 x)) (lift_head k x0 x (S O) d))))) H7))))) H5)))))) 
(\lambda (H4: (ex T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) 
v))))).(ex_ind T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) v))) (or 
(\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) (lift (S O) 
d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 t1) (lift (S O) d v))))) 
(\lambda (x: T).(\lambda (H5: (eq T t1 (lift (S O) (s k d) x))).(eq_ind_r T 
(lift (S O) (s k d) x) (\lambda (t2: T).(or (\forall (w: T).(ex T (\lambda 
(v: T).(subst0 d w (THead k t0 t2) (lift (S O) d v))))) (ex T (\lambda (v: 
T).(eq T (THead k t0 t2) (lift (S O) d v)))))) (or_introl (\forall (w: T).(ex 
T (\lambda (v: T).(subst0 d w (THead k t0 (lift (S O) (s k d) x)) (lift (S O) 
d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 (lift (S O) (s k d) x)) 
(lift (S O) d v)))) (\lambda (w: T).(let H_x1 \def (H2 w) in (let H6 \def 
H_x1 in (ex_ind T (\lambda (v: T).(subst0 d w t0 (lift (S O) d v))) (ex T 
(\lambda (v: T).(subst0 d w (THead k t0 (lift (S O) (s k d) x)) (lift (S O) d 
v)))) (\lambda (x0: T).(\lambda (H7: (subst0 d w t0 (lift (S O) d 
x0))).(ex_intro T (\lambda (v: T).(subst0 d w (THead k t0 (lift (S O) (s k d) 
x)) (lift (S O) d v))) (THead k x0 x) (eq_ind_r T (THead k (lift (S O) d x0) 
(lift (S O) (s k d) x)) (\lambda (t2: T).(subst0 d w (THead k t0 (lift (S O) 
(s k d) x)) t2)) (subst0_fst w (lift (S O) d x0) t0 d H7 (lift (S O) (s k d) 
x) k) (lift (S O) d (THead k x0 x)) (lift_head k x0 x (S O) d))))) H6))))) t1 
H5))) H4)) H3)))) (\lambda (H2: (ex T (\lambda (v: T).(eq T t0 (lift (S O) d 
v))))).(ex_ind T (\lambda (v: T).(eq T t0 (lift (S O) d v))) (or (\forall (w: 
T).(ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) (lift (S O) d v))))) (ex 
T (\lambda (v: T).(eq T (THead k t0 t1) (lift (S O) d v))))) (\lambda (x: 
T).(\lambda (H3: (eq T t0 (lift (S O) d x))).(let H_x0 \def (H0 (s k d)) in 
(let H4 \def H_x0 in (or_ind (\forall (w: T).(ex T (\lambda (v: T).(subst0 (s 
k d) w t1 (lift (S O) (s k d) v))))) (ex T (\lambda (v: T).(eq T t1 (lift (S 
O) (s k d) v)))) (or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead 
k t0 t1) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 t1) 
(lift (S O) d v))))) (\lambda (H5: ((\forall (w: T).(ex T (\lambda (v: 
T).(subst0 (s k d) w t1 (lift (S O) (s k d) v))))))).(eq_ind_r T (lift (S O) 
d x) (\lambda (t2: T).(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w 
(THead k t2 t1) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T (THead k t2 
t1) (lift (S O) d v)))))) (or_introl (\forall (w: T).(ex T (\lambda (v: 
T).(subst0 d w (THead k (lift (S O) d x) t1) (lift (S O) d v))))) (ex T 
(\lambda (v: T).(eq T (THead k (lift (S O) d x) t1) (lift (S O) d v)))) 
(\lambda (w: T).(let H_x1 \def (H5 w) in (let H6 \def H_x1 in (ex_ind T 
(\lambda (v: T).(subst0 (s k d) w t1 (lift (S O) (s k d) v))) (ex T (\lambda 
(v: T).(subst0 d w (THead k (lift (S O) d x) t1) (lift (S O) d v)))) (\lambda 
(x0: T).(\lambda (H7: (subst0 (s k d) w t1 (lift (S O) (s k d) 
x0))).(ex_intro T (\lambda (v: T).(subst0 d w (THead k (lift (S O) d x) t1) 
(lift (S O) d v))) (THead k x x0) (eq_ind_r T (THead k (lift (S O) d x) (lift 
(S O) (s k d) x0)) (\lambda (t2: T).(subst0 d w (THead k (lift (S O) d x) t1) 
t2)) (subst0_snd k w (lift (S O) (s k d) x0) t1 d H7 (lift (S O) d x)) (lift 
(S O) d (THead k x x0)) (lift_head k x x0 (S O) d))))) H6))))) t0 H3)) 
(\lambda (H5: (ex T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) 
v))))).(ex_ind T (\lambda (v: T).(eq T t1 (lift (S O) (s k d) v))) (or 
(\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead k t0 t1) (lift (S O) 
d v))))) (ex T (\lambda (v: T).(eq T (THead k t0 t1) (lift (S O) d v))))) 
(\lambda (x0: T).(\lambda (H6: (eq T t1 (lift (S O) (s k d) x0))).(eq_ind_r T 
(lift (S O) (s k d) x0) (\lambda (t2: T).(or (\forall (w: T).(ex T (\lambda 
(v: T).(subst0 d w (THead k t0 t2) (lift (S O) d v))))) (ex T (\lambda (v: 
T).(eq T (THead k t0 t2) (lift (S O) d v)))))) (eq_ind_r T (lift (S O) d x) 
(\lambda (t2: T).(or (\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead 
k t2 (lift (S O) (s k d) x0)) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq 
T (THead k t2 (lift (S O) (s k d) x0)) (lift (S O) d v)))))) (or_intror 
(\forall (w: T).(ex T (\lambda (v: T).(subst0 d w (THead k (lift (S O) d x) 
(lift (S O) (s k d) x0)) (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T 
(THead k (lift (S O) d x) (lift (S O) (s k d) x0)) (lift (S O) d v)))) 
(ex_intro T (\lambda (v: T).(eq T (THead k (lift (S O) d x) (lift (S O) (s k 
d) x0)) (lift (S O) d v))) (THead k x x0) (eq_ind_r T (THead k (lift (S O) d 
x) (lift (S O) (s k d) x0)) (\lambda (t2: T).(eq T (THead k (lift (S O) d x) 
(lift (S O) (s k d) x0)) t2)) (refl_equal T (THead k (lift (S O) d x) (lift 
(S O) (s k d) x0))) (lift (S O) d (THead k x x0)) (lift_head k x x0 (S O) 
d)))) t0 H3) t1 H6))) H5)) H4))))) H2)) H1))))))))) t).
(* COMMENTS
Initial nodes: 3549
END *)

theorem dnf_dec:
 \forall (w: T).(\forall (t: T).(\forall (d: nat).(ex T (\lambda (v: T).(or 
(subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d v)))))))
\def
 \lambda (w: T).(\lambda (t: T).(\lambda (d: nat).(let H_x \def (dnf_dec2 t 
d) in (let H \def H_x in (or_ind (\forall (w0: T).(ex T (\lambda (v: 
T).(subst0 d w0 t (lift (S O) d v))))) (ex T (\lambda (v: T).(eq T t (lift (S 
O) d v)))) (ex T (\lambda (v: T).(or (subst0 d w t (lift (S O) d v)) (eq T t 
(lift (S O) d v))))) (\lambda (H0: ((\forall (w0: T).(ex T (\lambda (v: 
T).(subst0 d w0 t (lift (S O) d v))))))).(let H_x0 \def (H0 w) in (let H1 
\def H_x0 in (ex_ind T (\lambda (v: T).(subst0 d w t (lift (S O) d v))) (ex T 
(\lambda (v: T).(or (subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d 
v))))) (\lambda (x: T).(\lambda (H2: (subst0 d w t (lift (S O) d 
x))).(ex_intro T (\lambda (v: T).(or (subst0 d w t (lift (S O) d v)) (eq T t 
(lift (S O) d v)))) x (or_introl (subst0 d w t (lift (S O) d x)) (eq T t 
(lift (S O) d x)) H2)))) H1)))) (\lambda (H0: (ex T (\lambda (v: T).(eq T t 
(lift (S O) d v))))).(ex_ind T (\lambda (v: T).(eq T t (lift (S O) d v))) (ex 
T (\lambda (v: T).(or (subst0 d w t (lift (S O) d v)) (eq T t (lift (S O) d 
v))))) (\lambda (x: T).(\lambda (H1: (eq T t (lift (S O) d x))).(eq_ind_r T 
(lift (S O) d x) (\lambda (t0: T).(ex T (\lambda (v: T).(or (subst0 d w t0 
(lift (S O) d v)) (eq T t0 (lift (S O) d v)))))) (ex_intro T (\lambda (v: 
T).(or (subst0 d w (lift (S O) d x) (lift (S O) d v)) (eq T (lift (S O) d x) 
(lift (S O) d v)))) x (or_intror (subst0 d w (lift (S O) d x) (lift (S O) d 
x)) (eq T (lift (S O) d x) (lift (S O) d x)) (refl_equal T (lift (S O) d 
x)))) t H1))) H0)) H))))).
(* COMMENTS
Initial nodes: 603
END *)

