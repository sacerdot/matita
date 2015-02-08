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

include "basic_1/cnt/fwd.ma".

include "basic_1/lift/props.ma".

theorem cnt_lift:
 \forall (t: T).((cnt t) \to (\forall (i: nat).(\forall (d: nat).(cnt (lift i 
d t)))))
\def
 \lambda (t: T).(\lambda (H: (cnt t)).(let TMP_2 \def (\lambda (t0: 
T).(\forall (i: nat).(\forall (d: nat).(let TMP_1 \def (lift i d t0) in (cnt 
TMP_1))))) in (let TMP_9 \def (\lambda (n: nat).(\lambda (i: nat).(\lambda 
(d: nat).(let TMP_3 \def (TSort n) in (let TMP_4 \def (\lambda (t0: T).(cnt 
t0)) in (let TMP_5 \def (cnt_sort n) in (let TMP_6 \def (TSort n) in (let 
TMP_7 \def (lift i d TMP_6) in (let TMP_8 \def (lift_sort n i d) in (eq_ind_r 
T TMP_3 TMP_4 TMP_5 TMP_7 TMP_8)))))))))) in (let TMP_24 \def (\lambda (t0: 
T).(\lambda (_: (cnt t0)).(\lambda (H1: ((\forall (i: nat).(\forall (d: 
nat).(cnt (lift i d t0)))))).(\lambda (k: K).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (d: nat).(let TMP_10 \def (lift i d v) in (let TMP_11 \def (s k 
d) in (let TMP_12 \def (lift i TMP_11 t0) in (let TMP_13 \def (THead k TMP_10 
TMP_12) in (let TMP_14 \def (\lambda (t1: T).(cnt t1)) in (let TMP_15 \def (s 
k d) in (let TMP_16 \def (lift i TMP_15 t0) in (let TMP_17 \def (s k d) in 
(let TMP_18 \def (H1 i TMP_17) in (let TMP_19 \def (lift i d v) in (let 
TMP_20 \def (cnt_head TMP_16 TMP_18 k TMP_19) in (let TMP_21 \def (THead k v 
t0) in (let TMP_22 \def (lift i d TMP_21) in (let TMP_23 \def (lift_head k v 
t0 i d) in (eq_ind_r T TMP_13 TMP_14 TMP_20 TMP_22 
TMP_23)))))))))))))))))))))) in (cnt_ind TMP_2 TMP_9 TMP_24 t H))))).

