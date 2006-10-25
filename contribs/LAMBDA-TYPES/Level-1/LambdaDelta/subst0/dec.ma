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

